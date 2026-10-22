// SPDX-License-Identifier: MIT OR Apache-2.0
//! Recording a trace from a live program: a wrapper around an `Orisnitsa` that forwards
//! every call and writes it as a canonical trace line. Ports `orisnik`'s
//! `letopis/recorder.rs`.

const std = @import("std");
const orisnitsa = @import("orisnitsa.zig");
const allocator_mod = @import("allocator.zig");
const spomen = @import("spomen.zig");

/// Records every call made through it as a trace (`examples/traces/GRAMMAR.md` §1), then
/// forwards it to the wrapped `Orisnitsa(config)`.
///
/// Pointers become symbolic handles: each allocation gets the next `hN`, a realloc keeps
/// its pointer's handle, a free retires it. The written trace replays with
/// `letopis.replay` on any of the three implementations. `allocator()` hands the recorder
/// out as a `std.mem.Allocator`, so a program that takes one records with no other change.
///
/// What it does not do (the same as `orisnik`'s `Recorder`):
///
/// - **It is not a global allocator.** Its pointer-to-handle table allocates from `gpa`,
///   which must be some other allocator.
/// - **It does not check the semantic constraints** (`GRAMMAR.md` §1.3) that only a trace,
///   not a program, must meet. Such a call is recorded faithfully, and `letopis.replay`
///   then refuses the trace with the rule and line it breaks.
/// - **A null pointer passed to `free`, `resize` or `querySize`** is forwarded but not
///   recorded: the call does nothing, and a trace has no handle for it.
/// - **A pointer the recorder did not hand out** is forwarded unchanged and recorded under a
///   handle that was never bound — which the replayer rejects (constraint C2).
///
/// Neither a write error nor running out of memory for the table interrupts the program:
/// the first one is remembered, reported by `finish`, and nothing more is written after it.
pub fn Recorder(comptime config: spomen.Config) type {
    return struct {
        const Self = @This();

        /// The allocator every call is forwarded to.
        inner: *orisnitsa.Orisnitsa(config),
        /// Backs `handles`.
        gpa: std.mem.Allocator,
        /// Where the trace is written.
        out: *std.Io.Writer,
        /// The handle each live pointer was recorded under, by address.
        handles: std.AutoHashMapUnmanaged(usize, u64) = .empty,
        /// The handle the next allocation or unknown pointer gets.
        next_handle: u64 = 0,
        /// The first failure, after which nothing more is recorded.
        failure: ?error{ WriteFailed, OutOfMemory } = null,

        /// Starts recording calls to `inner` into `out`, beginning with the trace header.
        pub fn init(inner: *orisnitsa.Orisnitsa(config), gpa: std.mem.Allocator, out: *std.Io.Writer) Self {
            var self: Self = .{ .inner = inner, .gpa = gpa, .out = out };
            self.line("oris-trace 1", .{});
            return self;
        }

        /// Releases the handle table. Does not touch the wrapped allocator.
        pub fn deinit(self: *Self) void {
            self.handles.deinit(self.gpa);
        }

        /// Reports the first failure, if any (everything after it was not recorded). Does
        /// not flush `out`.
        pub fn finish(self: *const Self) error{ WriteFailed, OutOfMemory }!void {
            if (self.failure) |err| return err;
        }

        /// This recorder as a `std.mem.Allocator`: every call through it is recorded.
        pub fn allocator(self: *Self) std.mem.Allocator {
            return allocator_mod.allocator(self);
        }

        fn line(self: *Self, comptime fmt: []const u8, args: anytype) void {
            if (self.failure != null) return;
            self.out.print(fmt ++ "\n", args) catch {
                self.failure = error.WriteFailed;
            };
        }

        fn freshHandle(self: *Self) u64 {
            const h = self.next_handle;
            self.next_handle += 1;
            return h;
        }

        /// The handle `ptr` was recorded under, or a never-bound one (see the type's doc).
        fn handleOf(self: *Self, ptr: [*]u8) u64 {
            // PROVENANCE: address read for its value only, as a table key.
            return self.handles.get(@intFromPtr(ptr)) orelse self.freshHandle();
        }

        fn bind(self: *Self, h: u64, ptr: ?[*]u8) ?[*]u8 {
            if (ptr) |p| {
                // PROVENANCE: as in `handleOf`.
                self.handles.put(self.gpa, @intFromPtr(p), h) catch {
                    if (self.failure == null) self.failure = error.OutOfMemory;
                };
            }
            return ptr;
        }

        /// Retires `ptr`'s handle and returns it; `null` for a null `ptr`.
        fn unbind(self: *Self, ptr: ?[*]u8) ?u64 {
            const p = ptr orelse return null;
            const h = self.handleOf(p);
            // PROVENANCE: as in `handleOf`.
            _ = self.handles.remove(@intFromPtr(p));
            return h;
        }

        /// `Orisnitsa.alloc`, recorded as `alloc`.
        pub fn alloc(self: *Self, size: usize) ?[*]u8 {
            const h = self.freshHandle();
            self.line("alloc h{d} {d}", .{ h, size });
            return self.bind(h, self.inner.alloc(size));
        }

        /// `Orisnitsa.allocAligned`, recorded as `alloc_aligned`.
        pub fn allocAligned(self: *Self, size: usize, alignment: usize) ?[*]u8 {
            const h = self.freshHandle();
            self.line("alloc_aligned h{d} {d} {d}", .{ h, size, alignment });
            return self.bind(h, self.inner.allocAligned(size, alignment));
        }

        /// `Orisnitsa.calloc`, recorded as `calloc`.
        pub fn calloc(self: *Self, count: usize, size: usize) ?[*]u8 {
            const h = self.freshHandle();
            self.line("calloc h{d} {d} {d}", .{ h, count, size });
            return self.bind(h, self.inner.calloc(count, size));
        }

        /// `Orisnitsa.realloc`, recorded as `realloc`.
        pub fn realloc(self: *Self, ptr: ?[*]u8, size: usize) ?[*]u8 {
            const h = if (ptr) |p| self.handleOf(p) else self.freshHandle();
            self.line("realloc h{d} {d}", .{ h, size });
            return self.rebound(h, ptr, size, self.inner.realloc(ptr, size));
        }

        /// `Orisnitsa.reallocAligned`, recorded as `realloc_aligned`.
        pub fn reallocAligned(self: *Self, ptr: ?[*]u8, size: usize, alignment: usize) ?[*]u8 {
            const h = if (ptr) |p| self.handleOf(p) else self.freshHandle();
            self.line("realloc_aligned h{d} {d} {d}", .{ h, size, alignment });
            return self.rebound(h, ptr, size, self.inner.reallocAligned(ptr, size, alignment));
        }

        /// A realloc's binding update: the old pointer is gone unless the call failed.
        fn rebound(self: *Self, h: u64, old: ?[*]u8, size: usize, new: ?[*]u8) ?[*]u8 {
            if (new != null or size == 0) {
                // PROVENANCE: as in `handleOf`.
                if (old) |p| _ = self.handles.remove(@intFromPtr(p));
            }
            return self.bind(h, new);
        }

        /// `Orisnitsa.resize`, recorded as `resize`.
        pub fn resize(self: *Self, ptr: ?[*]u8, size: usize) usize {
            if (ptr) |p| self.line("resize h{d} {d}", .{ self.handleOf(p), size });
            return self.inner.resize(ptr, size);
        }

        /// `Orisnitsa.querySize`, recorded as `size`.
        pub fn querySize(self: *Self, ptr: ?[*]u8) usize {
            if (ptr) |p| self.line("size h{d}", .{self.handleOf(p)});
            return self.inner.querySize(ptr);
        }

        /// `Orisnitsa.free`, recorded as `free`.
        pub fn free(self: *Self, ptr: ?[*]u8) void {
            if (self.unbind(ptr)) |h| self.line("free h{d}", .{h});
            self.inner.free(ptr);
        }

        /// `Orisnitsa.freeWithSize`, recorded as `free_sized`.
        pub fn freeWithSize(self: *Self, ptr: ?[*]u8, orig_size: usize) void {
            if (self.unbind(ptr)) |h| self.line("free_sized h{d} {d}", .{ h, orig_size });
            self.inner.freeWithSize(ptr, orig_size);
        }

        /// `Orisnitsa.freeWithSizeAligned`, recorded as `free_sized_aligned`.
        pub fn freeWithSizeAligned(self: *Self, ptr: ?[*]u8, orig_size: usize, old_alignment: usize) void {
            if (self.unbind(ptr)) |h| self.line("free_sized_aligned h{d} {d} {d}", .{ h, orig_size, old_alignment });
            self.inner.freeWithSizeAligned(ptr, orig_size, old_alignment);
        }

        /// `Orisnitsa.purge`, recorded as `purge`.
        pub fn purge(self: *Self) void {
            self.line("purge", .{});
            self.inner.purge();
        }
    };
}
