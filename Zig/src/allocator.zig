// SPDX-License-Identifier: MIT OR Apache-2.0
//! `std.mem.Allocator` — the idiomatic-surface vtable over `Orisnitsa`. Every
//! function converts its `[]u8`/`std.mem.Alignment` arguments to/from
//! `Orisnitsa`'s own `?[*]u8`/byte-count core API and forwards; no new allocator
//! logic lives here.
//!
//! Collapses `orisnik`'s two idiomatic surfaces, `global_alloc.rs`
//! (`unsafe impl GlobalAlloc`) and `allocator_trait.rs`
//! (`unsafe impl core::alloc::Allocator`, nightly-only), into one: Zig has a
//! single blessed allocator interface, not Rust's stable/unstable pair, so there
//! is only one vtable to implement, not two trait impls.
//!
//! # `resize` vs `remap`
//! Per `std.mem.Allocator.VTable`'s own doc comments (verified directly against
//! the installed Zig 0.16.0 stdlib, not assumed): `resize` must never move the
//! allocation (`bool` result — `true` means "same address, new size"); `remap`
//! may move it (`?[*]u8` result — `null` means "no advantage over the caller
//! doing alloc+copy+free itself", *not* out-of-memory).
//!
//! - `resize` delegates to `Orisnitsa.resize` (`tree.zig`'s `Tree.resize` /
//!   the bucket path's fixed-`elemSize` query) — already exactly an
//!   in-place-only, never-moves operation; this is a direct match, not new logic.
//! - `remap` delegates to `Orisnitsa.realloc`/`reallocAligned` — the same
//!   dispatcher `oris_realloc`/`capi.zig`'s `oris_realloc` already uses. This
//!   mirrors `orisnik`'s own choice: `allocator_trait.rs`'s `grow`/`shrink` (the
//!   Rust `Allocator` trait's may-move primitives, closest to `remap` here) both
//!   call `self.realloc`/`self.realloc_aligned` too, not some separate
//!   move-only path. Routing `remap` through `resize` instead (unconditionally
//!   returning `null` otherwise) would silently make every generic
//!   `std.mem.Allocator` consumer (`std.ArrayList`, `std.HashMap`, ...) fall back
//!   to alloc+copy+free for growth this allocator could have done in place via
//!   `realloc`'s split/coalesce logic — a real, silent cross-port-invariant break
//!   for state transitions, not just a missed optimization.

const std = @import("std");
const block = @import("block.zig");
const orisnitsa = @import("orisnitsa.zig");

const Orisnitsa = orisnitsa.Orisnitsa;

/// Hands out a `std.mem.Allocator` backed by `self`. Not a method on `Orisnitsa`
/// itself (which would need this file to import `orisnitsa.zig` and be imported
/// back by it) — kept as a free function here so the dependency stays one-way:
/// `allocator.zig` depends on `orisnitsa.zig`, never the reverse.
pub fn allocator(self: *Orisnitsa) std.mem.Allocator {
    return .{ .ptr = self, .vtable = &vtable };
}

/// The single vtable every `allocator()`-returned `std.mem.Allocator` shares —
/// stateless (all state lives in the `.ptr` each call carries), so one instance
/// serves every `Orisnitsa`.
const vtable = std.mem.Allocator.VTable{
    .alloc = allocImpl,
    .resize = resizeImpl,
    .remap = remapImpl,
    .free = freeImpl,
};

/// `VTable.alloc` — see the module doc.
fn allocImpl(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
    _ = ret_addr; // spomen's future callstack hook (v0.2.0+); unused for v0.1.0.
    // ALIGN: `ctx` is always exactly the `*Orisnitsa` `allocator()` stored as
    // `.ptr` — a live, `@alignOf(Orisnitsa)`-aligned value before it was
    // type-erased to `*anyopaque`; `@alignCast` only re-establishes what the
    // type system lost, not a new guarantee.
    const self: *Orisnitsa = @ptrCast(@alignCast(ctx));
    const align_bytes = alignment.toByteUnits();
    if (align_bytes <= block.DEFAULT_ALIGNMENT) {
        return self.alloc(len);
    }
    return self.allocAligned(len, align_bytes);
}

/// `VTable.resize` — see the module doc's "`resize` vs `remap`" section.
fn resizeImpl(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
    // `Orisnitsa.resize` needs no alignment: it only ever grows/shrinks a block
    // already installed at its own (already-aligned) address, never
    // re-deriving alignment from scratch — matching HPHA's own `tree_resize`/
    // bucket `elemSize` query, neither of which takes an alignment parameter.
    _ = alignment;
    _ = ret_addr;
    // ALIGN: see `allocImpl`'s identical cast for why this is sound.
    const self: *Orisnitsa = @ptrCast(@alignCast(ctx));
    const actual = self.resize(memory.ptr, new_len);
    return actual >= new_len;
}

/// `VTable.remap` — see the module doc's "`resize` vs `remap`" section.
fn remapImpl(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    _ = ret_addr;
    // ALIGN: see `allocImpl`'s identical cast for why this is sound.
    const self: *Orisnitsa = @ptrCast(@alignCast(ctx));
    const align_bytes = alignment.toByteUnits();
    if (align_bytes <= block.DEFAULT_ALIGNMENT) {
        return self.realloc(memory.ptr, new_len);
    }
    return self.reallocAligned(memory.ptr, new_len, align_bytes);
}

/// `VTable.free`.
fn freeImpl(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
    // Deliberately routes through `Orisnitsa.free` (the page-marker/block-header
    // dispatch), not the `freeWithSize*` shortcuts: those require `orig_size` to
    // be the pointer's *original* allocation size, an invariant this vtable's
    // own contract does not provide — `memory.len` here only matches the
    // block's *current* size, which can differ after a `resize`/`remap` (a
    // large-then-shrunk block stays tree-allocated even once its current size
    // would fit a bucket, and `freeWithSize` has no way to tell the two cases
    // apart from size alone). `free`'s pointer-based dispatch is correct
    // regardless of any resize/remap history — mirrors `orisnik`'s own
    // `global_alloc.rs`/`allocator_trait.rs`, both of which make the identical
    // choice for the identical reason.
    _ = alignment;
    _ = ret_addr;
    // ALIGN: see `allocImpl`'s identical cast for why this is sound.
    const self: *Orisnitsa = @ptrCast(@alignCast(ctx));
    self.free(memory.ptr);
}

const testing = std.testing;

test "std.mem.Allocator round-trip at the default alignment" {
    var orisnitsa_instance: Orisnitsa = .init();
    const a = allocator(&orisnitsa_instance);
    const mem = try a.alloc(u8, 64);
    @memset(mem, 0xAB);
    a.free(mem);
    orisnitsa_instance.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa_instance.allocated());
}

test "std.mem.Allocator round-trip over-aligned" {
    var orisnitsa_instance: Orisnitsa = .init();
    const a = allocator(&orisnitsa_instance);
    const mem = try a.alignedAlloc(u8, comptime std.mem.Alignment.fromByteUnits(256), 96);
    try testing.expectEqual(@as(usize, 0), @intFromPtr(mem.ptr) % 256);
    @memset(mem, 0xCD);
    a.free(mem);
    orisnitsa_instance.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa_instance.allocated());
}

test "std.mem.Allocator resize never moves and reports failure honestly" {
    var orisnitsa_instance: Orisnitsa = .init();
    const a = allocator(&orisnitsa_instance);
    // Force the tree path so there's a following free block to grow into.
    const size = 4096;
    var mem = try a.alloc(u8, size);
    @memset(mem, 0xEF);
    try testing.expect(a.resize(mem, size + 64));
    mem = mem.ptr[0 .. size + 64];
    try testing.expect(std.mem.allEqual(u8, mem[0..size], 0xEF));
    a.free(mem);
    orisnitsa_instance.purge();
}

test "std.mem.Allocator smoke test via ArrayList" {
    var orisnitsa_instance: Orisnitsa = .init();
    const a = allocator(&orisnitsa_instance);
    var list: std.ArrayList(u32) = .empty;
    for (0..2000) |i| {
        try list.append(a, @intCast(i));
    }
    try testing.expectEqual(@as(usize, 2000), list.items.len);
    try testing.expectEqual(@as(u32, 1999), list.items[1999]);
    list.deinit(a);
    orisnitsa_instance.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa_instance.allocated());
}
