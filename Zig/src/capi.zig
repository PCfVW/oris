// SPDX-License-Identifier: MIT OR Apache-2.0
//! `oris_*` — the C-ABI surface. Every function takes an explicit `*Orisnitsa`
//! handle, mirroring HPHA's own instantiable `class allocator` rather than a
//! hidden global singleton (`BRIEF.md`'s explicit-opt-in stance) — a C caller
//! creates one with `oris_new`, threads the handle through every other call, and
//! destroys it with `oris_destroy` when done. Naming and behaviour otherwise
//! mirror `Orisnitsa`'s own public methods one-to-one, `?[*]u8`/`null` in place of
//! `orisnik`'s `Option<NonNull<u8>>`.
//!
//! Ports `orisnik`'s `capi.rs`. Named in `snake_case` throughout, unlike this
//! project's own `camelCase`-function convention (`Zig/CONVENTIONS.md`) — a
//! deliberate exception, not an oversight: these are C symbol names HPHA's own
//! callers expect verbatim, the same class of exception this project already
//! makes for the Bulgarian terms of art (`orisnitsa`, `spomen`, `stopanstvo`).
//! `export fn` gives each one C linkage under its own Zig identifier, with no
//! separate `#[unsafe(no_mangle)]`-style attribute needed (Zig's analog of
//! Rust's edition-2024 unsafe-attribute syntax `Rust/CONVENTIONS.md`'s MSRV lint
//! guard note mentions).

const std = @import("std");
const orisnitsa_mod = @import("orisnitsa.zig");

const Orisnitsa = orisnitsa_mod.Orisnitsa;

/// The allocator `oris_new` uses to allocate the opaque handle itself — distinct
/// from any `Orisnitsa` instance's own bucket/tree allocation paths (which map OS
/// pages directly via `os.zig`, never through this). Matches `orisnik`'s own
/// `oris_new`, which uses `Box::new` — whatever the process's ambient global
/// allocator is; `std.heap.page_allocator` is the closest Zig equivalent needing
/// no configuration.
const handle_allocator = std.heap.page_allocator;

/// Creates a fresh allocator instance on the heap, returning an opaque owning
/// handle. Pair with `oris_destroy`. Never fails to return a live handle —
/// matches `orisnik`'s own `oris_new`, which aborts (via `Box::new`) on OS memory
/// exhaustion rather than returning null, a property of the handle's own storage
/// unrelated to the `Orisnitsa` instance's own allocation paths (which do return
/// null on failure). Zig expresses "never null" directly in the return type,
/// where Rust could only document it on an otherwise-nullable `*mut Orisnik`.
export fn oris_new() *Orisnitsa {
    const handle = handle_allocator.create(Orisnitsa) catch @panic("out of memory allocating an Orisnitsa handle");
    handle.* = .init();
    return handle;
}

/// Destroys an allocator instance created by `oris_new`.
///
/// `handle` must be a still-live result of `oris_new` (or `null`, in which case
/// this is a no-op), not yet destroyed, and not used again after this call — by
/// this function or any other `oris_*` call. Every allocation made through
/// `handle` should already be freed or intentionally leaked first: destroying the
/// instance does not return its outstanding OS pages/arenas (matching HPHA, which
/// never returns memory to the OS except via an explicit `purge()`) — call
/// `oris_purge` beforehand if reclaiming that memory matters.
export fn oris_destroy(handle: ?*Orisnitsa) void {
    const h = handle orelse return;
    handle_allocator.destroy(h);
}

/// Allocates `size` bytes at the allocator's default alignment. `size == 0`
/// returns `null`. Ports `allocator::alloc(size_t)`.
///
/// `handle` must be live (a still-live result of `oris_new`, not yet destroyed).
export fn oris_alloc(handle: *Orisnitsa, size: usize) ?[*]u8 {
    return handle.alloc(size);
}

/// Allocates `size` bytes aligned to `alignment`. `size == 0` returns `null`.
/// Ports `allocator::alloc(size_t, size_t)`.
///
/// `handle` must be live.
export fn oris_alloc_aligned(handle: *Orisnitsa, size: usize, alignment: usize) ?[*]u8 {
    return handle.allocAligned(size, alignment);
}

/// Allocates `count * size` bytes at the default alignment, zeroed. Ports
/// `allocator::calloc`.
///
/// `handle` must be live.
export fn oris_calloc(handle: *Orisnitsa, count: usize, size: usize) ?[*]u8 {
    return handle.calloc(count, size);
}

/// Grows, shrinks, or moves `ptr` to `size` bytes at the default alignment. `ptr
/// == null` acts as `oris_alloc`; `size == 0` acts as `oris_free` and returns
/// `null`. Ports `allocator::realloc(void*, size_t)`.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
export fn oris_realloc(handle: *Orisnitsa, ptr: ?[*]u8, size: usize) ?[*]u8 {
    return handle.realloc(ptr, size);
}

/// Grows, shrinks, or moves `ptr` to `size` bytes aligned to `alignment`. `ptr ==
/// null` acts as `oris_alloc_aligned`; `size == 0` acts as `oris_free` and
/// returns `null`. Ports `allocator::realloc(void*, size_t, size_t)`.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
export fn oris_realloc_aligned(handle: *Orisnitsa, ptr: ?[*]u8, size: usize, alignment: usize) ?[*]u8 {
    return handle.reallocAligned(ptr, size, alignment);
}

/// Grows or shrinks `ptr` in place to the extent possible, returning the
/// resulting size. `ptr == null` returns 0. Ports `allocator::resize`.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
export fn oris_resize(handle: *Orisnitsa, ptr: ?[*]u8, size: usize) usize {
    return handle.resize(ptr, size);
}

/// Queries the usable size of `ptr`'s allocation. `ptr == null` returns 0. Ports
/// `allocator::size`.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
export fn oris_size(handle: *Orisnitsa, ptr: ?[*]u8) usize {
    return handle.querySize(ptr);
}

/// Frees `ptr`. `ptr == null` is a no-op. Ports `allocator::free(void*)`.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
export fn oris_free(handle: *Orisnitsa, ptr: ?[*]u8) void {
    handle.free(ptr);
}

/// Frees `ptr`, given its original request size at the default alignment. `ptr
/// == null` is a no-op. Ports `allocator::free(void*, size_t)`.
///
/// `orig_size` must be `ptr`'s size **at the moment it was allocated**, not a
/// size from any later `oris_realloc`/`oris_resize` call — see
/// `Orisnitsa.freeWithSize`'s own doc for why. Prefer `oris_free` whenever
/// `ptr`'s allocation history isn't certain to be realloc-free.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced with `orig_size` at the default alignment.
export fn oris_free_with_size(handle: *Orisnitsa, ptr: ?[*]u8, orig_size: usize) void {
    handle.freeWithSize(ptr, orig_size);
}

/// Frees `ptr`, given its original request size and alignment. `ptr == null` is
/// a no-op. Ports `allocator::free(void*, size_t, size_t)`.
///
/// `orig_size`/`old_alignment` must be `ptr`'s size/alignment **at the moment it
/// was allocated** — see `oris_free_with_size`'s doc for why. Prefer
/// `oris_free` whenever `ptr`'s allocation history isn't certain to be
/// realloc-free.
///
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced with `orig_size`/`old_alignment`.
export fn oris_free_with_size_aligned(handle: *Orisnitsa, ptr: ?[*]u8, orig_size: usize, old_alignment: usize) void {
    handle.freeWithSizeAligned(ptr, orig_size, old_alignment);
}

/// Returns every fully-unused page/arena to the OS. Ports `allocator::purge`.
///
/// `handle` must be live.
export fn oris_purge(handle: *Orisnitsa) void {
    handle.purge();
}

/// Total bytes currently claimed from the OS across both allocation paths. Ports
/// `allocator::allocated`.
///
/// `handle` must be live.
export fn oris_allocated(handle: *Orisnitsa) usize {
    return handle.allocated();
}

const testing = std.testing;

// Every allocating call below reaches real `os.map` through a freshly
// `oris_new`-created handle (see `orisnitsa.zig`'s test module doc for why: no
// OS-free seeding seam exists at this layer), exercised by native
// `zig build test` on all three CI OSes (zig-ci.yml).

test "C-ABI round trip: alloc, realloc, free, purge" {
    const handle = oris_new();
    defer oris_destroy(handle);

    const ptr = oris_alloc(handle, 64) orelse return error.TestUnexpectedResult;
    @memset(ptr[0..64], 0xAB);

    try testing.expectEqual(@as(usize, 64), oris_size(handle, ptr));

    const grown = oris_realloc(handle, ptr, 512) orelse return error.TestUnexpectedResult;
    // The first 64 bytes must have been preserved across the realloc.
    try testing.expect(std.mem.allEqual(u8, grown[0..64], 0xAB));

    try testing.expect(oris_allocated(handle) > 0);

    oris_free(handle, grown);
    oris_purge(handle);
    try testing.expectEqual(@as(usize, 0), oris_allocated(handle));
}

test "C-ABI aligned alloc and free-with-size" {
    const handle = oris_new();
    defer oris_destroy(handle);

    const ptr = oris_alloc_aligned(handle, 48, 128) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % 128);
    oris_free_with_size_aligned(handle, ptr, 48, 128);

    const calloc_ptr = oris_calloc(handle, 4, 16) orelse return error.TestUnexpectedResult;
    // `calloc_ptr` is a live allocation of at least 64 bytes, zeroed by
    // `oris_calloc`.
    try testing.expect(std.mem.allEqual(u8, calloc_ptr[0..64], 0));
    oris_free_with_size(handle, calloc_ptr, 64);
}

test "oris_destroy on a null handle is a no-op" {
    oris_destroy(null);
}
