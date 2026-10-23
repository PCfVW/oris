// SPDX-License-Identifier: MIT OR Apache-2.0
//! `LD_PRELOAD` shim: the C allocation API over one process-wide `orisnitsa` instance, so
//! that mimalloc-bench can run its programs on Oris (allocator name `onit`). Linux only.
//! The twin of `../preload-rust`, with the same four additions to the allocator, stated
//! next to every result:
//!
//! - **One global lock.** Oris is single-threaded; calls from several threads are
//!   serialized behind one `pthread_mutex`.
//! - **16-byte alignment** for every request: `allocAligned(roundUp(size, 16), 16)`.
//! - **`malloc(0)` returns a unique pointer**, as glibc's does.
//! - **`fork` keeps the lock consistent** (`pthread_atfork`).

const std = @import("std");
const orisnitsa = @import("orisnitsa");

var oris: orisnitsa.Orisnitsa = .init();
var lock: std.c.pthread_mutex_t = .{};

const min_align: usize = 16;

extern "c" fn pthread_atfork(prepare: ?*const fn () callconv(.c) void, parent: ?*const fn () callconv(.c) void, child: ?*const fn () callconv(.c) void) c_int;

fn lockForFork() callconv(.c) void {
    _ = std.c.pthread_mutex_lock(&lock);
}

fn unlockAfterFork() callconv(.c) void {
    _ = std.c.pthread_mutex_unlock(&lock);
}

fn registerForkHandlers() callconv(.c) void {
    _ = pthread_atfork(lockForFork, unlockAfterFork, unlockAfterFork);
}

/// Runs `registerForkHandlers` when the library is loaded.
export const init_array: [1]*const fn () callconv(.c) void linksection(".init_array") = .{registerForkHandlers};

fn roundUp(size: usize, alignment: usize) ?usize {
    const s = @max(size, 1);
    const bumped = std.math.add(usize, s, alignment - 1) catch return null;
    return bumped & ~(alignment - 1);
}

fn aligned(size: usize, alignment: usize) ?*anyopaque {
    const a = @max(alignment, min_align);
    const s = roundUp(size, min_align) orelse return null;
    _ = std.c.pthread_mutex_lock(&lock);
    defer _ = std.c.pthread_mutex_unlock(&lock);
    return @ptrCast(oris.allocAligned(s, a));
}

fn bytes(p: ?*anyopaque) ?[*]u8 {
    return @ptrCast(p);
}

export fn malloc(size: usize) ?*anyopaque {
    return aligned(size, min_align);
}

export fn calloc(count: usize, size: usize) ?*anyopaque {
    const total = std.math.mul(usize, count, size) catch return null;
    const p = aligned(total, min_align) orelse return null;
    @memset(bytes(p).?[0..total], 0);
    return p;
}

export fn realloc(p: ?*anyopaque, size: usize) ?*anyopaque {
    if (p == null) return aligned(size, min_align);
    if (size == 0) {
        free(p);
        return null;
    }
    const s = roundUp(size, min_align) orelse return null;
    _ = std.c.pthread_mutex_lock(&lock);
    defer _ = std.c.pthread_mutex_unlock(&lock);
    return @ptrCast(oris.reallocAligned(bytes(p), s, min_align));
}

export fn free(p: ?*anyopaque) void {
    if (p == null) return;
    _ = std.c.pthread_mutex_lock(&lock);
    defer _ = std.c.pthread_mutex_unlock(&lock);
    oris.free(bytes(p));
}

export fn posix_memalign(out: *?*anyopaque, alignment: usize, size: usize) c_int {
    if (!std.math.isPowerOfTwo(alignment) or alignment % @sizeOf(usize) != 0) return @intFromEnum(std.c.E.INVAL);
    out.* = aligned(size, alignment) orelse return @intFromEnum(std.c.E.NOMEM);
    return 0;
}

export fn aligned_alloc(alignment: usize, size: usize) ?*anyopaque {
    if (!std.math.isPowerOfTwo(alignment)) return null;
    return aligned(size, alignment);
}

export fn memalign(alignment: usize, size: usize) ?*anyopaque {
    if (!std.math.isPowerOfTwo(alignment)) return null;
    return aligned(size, alignment);
}

export fn valloc(size: usize) ?*anyopaque {
    return aligned(size, 4096);
}

export fn pvalloc(size: usize) ?*anyopaque {
    return aligned(roundUp(size, 4096) orelse return null, 4096);
}

export fn malloc_usable_size(p: ?*anyopaque) usize {
    _ = std.c.pthread_mutex_lock(&lock);
    defer _ = std.c.pthread_mutex_unlock(&lock);
    return oris.querySize(bytes(p));
}
