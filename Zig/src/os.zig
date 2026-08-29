// SPDX-License-Identifier: MIT OR Apache-2.0
//! Cross-platform virtual-memory layer.
//!
//! Ports `Cpp/hpha.h`'s `virtual_alloc`/`virtual_free` and `VIRTUAL_PAGE_SIZE`, mirroring
//! `orisnik`'s `os.rs`. HPHA is Win32-only (`VirtualAlloc`); this module abstracts the
//! same "get `PAGE_SIZE`-aligned pages from the OS, return them only on `purge`"
//! contract over Windows (`VirtualAlloc`/`VirtualFree`) and Unix (`mmap`/`munmap`).
//!
//! `PAGE_SIZE` is fixed at 64 KiB on **every** platform — not each OS's native page
//! size — because the bucket and tree allocators' page-count and split/coalesce math
//! must be identical across OSes for the cross-port invariant (`ROADMAP.md`) to hold
//! even within one language, and identical to `orisnik`'s own choice. On Windows this
//! matches the OS's own 64 KiB "allocation granularity" for free (`VirtualAlloc`
//! addresses are naturally aligned to it). On Unix, `mmap` only guarantees
//! native-page alignment (4 KiB, or 16 KiB on Apple Silicon) — `map`'s Unix
//! implementation over-allocates and trims to reach 64 KiB, the same technique
//! jemalloc/mimalloc use for chunk alignment on POSIX.
//!
//! Calls `std.c.mmap`/`std.c.munmap` directly rather than `std.posix.mmap`/`munmap`:
//! the latter's `munmap` deliberately forbids unmapping a sub-range of a larger
//! existing mapping (documented on `std.posix.munmap` itself), which is exactly the
//! partial-trim operation the alignment technique below needs. That restriction is a
//! Zig API-level design choice, not a POSIX `munmap(2)` syscall restriction, so
//! calling the raw `std.c` binding directly — matching `orisnik`'s own choice to use
//! the `libc` crate's `mmap`/`munmap` directly rather than a higher-level wrapper —
//! is the correct way to reach for it.

const std = @import("std");
const builtin = @import("builtin");
const align_helpers = @import("align.zig");

/// The page size every allocator subsystem grows by, in bytes. Fixed across all
/// platforms — see the module doc.
pub const PAGE_SIZE: usize = 1 << 16; // 64 KiB, matches HPHA's VIRTUAL_PAGE_SIZE_LOG2

const is_windows = builtin.os.tag == .windows;

/// Requests `size` bytes from the OS, aligned to `PAGE_SIZE`.
///
/// `size` must be a non-zero multiple of `PAGE_SIZE`. Returns `null` on OS failure
/// (out of address space / memory pressure) — allocation failure is a value, not a
/// panic, per `Zig/CONVENTIONS.md`'s "Allocation outcomes are values" rule.
pub fn map(size: usize) ?[*]u8 {
    std.debug.assert(size > 0 and size % PAGE_SIZE == 0);
    if (builtin.is_test and test_vm.shouldFail()) return null;
    return if (is_windows) mapWindows(size) else mapUnix(size);
}

/// Test-only out-of-memory injection over the OS boundary. Compiled out entirely
/// outside a test build (`builtin.is_test` is `comptime`-known, so the branch in `map`
/// above vanishes in a release artifact).
///
/// # Why this exists
/// Every `orelse return null` on a `systemAlloc`/`os.map` result in `Buckets` and
/// `Tree` was unexecuted by any test before v0.1.1: there was no way to make a mapping
/// fail, so the out-of-memory early-outs existed only on paper.
///
/// `Zig/CONVENTIONS.md` previously named `std.testing.checkAllAllocationFailures` as
/// the tool for this. It is not applicable here, and the reason is structural rather
/// than incidental: that helper wraps a `FailingAllocator` around a *backing*
/// `std.mem.Allocator` and passes it **to** the code under test, so it exercises
/// allocator *consumers*. `Orisnitsa` consumes no allocator — it calls `os.map`
/// directly — so the only place a failure can be injected is here.
///
/// # Parity with `orisnik`'s `os::test_vm`
/// The injection half is identical. `orisnik`'s seam carries a second half this one
/// deliberately does not: a heap-backed stand-in that replaces the real syscall
/// *under Miri*, because Miri cannot interpret `VirtualAlloc`/`mmap` and every
/// allocating test would otherwise be skipped there. Zig has no Miri, and its own
/// verification gate — `Debug`/`ReleaseSafe` runtime safety checks — works against
/// the real mappings, so there is nothing for a stand-in to unlock. The asymmetry is
/// in the *tooling*, not in what the two ports test.
pub const test_vm = struct {
    /// Successful `map` calls remaining before it starts returning `null`; `null`
    /// disables injection.
    var fail_after: ?usize = null;

    /// Makes the next `successes` calls to `map` succeed and every call after that
    /// fail, until `clearFailure`. Pair with `defer os.test_vm.clearFailure();` so a
    /// failing assertion cannot leak injection into the next test.
    pub fn failMapAfter(successes: usize) void {
        fail_after = successes;
    }

    /// Disables out-of-memory injection.
    pub fn clearFailure() void {
        fail_after = null;
    }

    /// Consumes one budgeted success, reporting whether this `map` call must fail.
    pub fn shouldFail() bool {
        const n = fail_after orelse return false;
        if (n == 0) return true;
        fail_after = n - 1;
        return false;
    }
};

/// Returns memory previously obtained from `map` back to the OS.
///
/// # Safety
/// - `ptr` must have been returned by a prior call to `map` on this platform and not
///   already unmapped.
/// - `size` must be the exact size passed to that `map` call.
pub fn unmap(ptr: [*]u8, size: usize) void {
    std.debug.assert(size > 0 and size % PAGE_SIZE == 0);
    if (is_windows) unmapWindows(ptr) else unmapUnix(ptr, size);
}

// ---- Windows: VirtualAlloc / VirtualFree ----
//
// Declared directly rather than pulled from `std.os.windows` — Zig 0.16's stdlib
// does not expose `VirtualAlloc`/`VirtualFree` itself (its own `PageAllocator` uses
// the lower-level `ntdll.NtAllocateVirtualMemory`/`NtFreeVirtualMemory` to support
// arbitrary caller-requested alignment, which `orisnitsa` does not need: `PAGE_SIZE`
// is fixed, and Windows' `VirtualAlloc` already returns addresses naturally aligned
// to 64 KiB, its own documented allocation granularity). Two `extern "kernel32"`
// declarations, matching `orisnik`'s equally direct `#[link(name = "kernel32")]`
// declarations in `os.rs`.

const MEM_COMMIT: u32 = 0x0000_1000;
const MEM_RELEASE: u32 = 0x0000_8000;
const PAGE_READWRITE: u32 = 0x04;

extern "kernel32" fn VirtualAlloc(
    lpAddress: ?*anyopaque,
    dwSize: usize,
    flAllocationType: u32,
    flProtect: u32,
) callconv(.winapi) ?*anyopaque;

extern "kernel32" fn VirtualFree(
    lpAddress: ?*anyopaque,
    dwSize: usize,
    dwFreeType: u32,
) callconv(.winapi) c_int;

fn mapWindows(size: usize) ?[*]u8 {
    // SAFETY: a null lpAddress lets the OS choose the base address; MEM_COMMIT |
    // PAGE_READWRITE requests a fresh, writable mapping of exactly `size` bytes.
    // VirtualAlloc returns null on failure and otherwise a pointer that aliases no
    // live allocation this program already made (it is fresh OS-backed memory).
    const raw = VirtualAlloc(null, size, MEM_COMMIT, PAGE_READWRITE) orelse return null;
    const bytes: [*]u8 = @ptrCast(raw);
    // Windows' allocation granularity is documented as 64 KiB, matching PAGE_SIZE;
    // this holds unconditionally (`std.debug.assert`, present in Debug/ReleaseSafe,
    // elided in ReleaseFast) because a misaligned page would silently corrupt every
    // downstream bucket/tree offset — see `Zig/CONVENTIONS.md`'s `assert` vs safety
    // checks section.
    std.debug.assert(@intFromPtr(bytes) % PAGE_SIZE == 0);
    return bytes;
}

/// # Safety
/// Same contract as `unmap` (this is its Windows implementation): `ptr` must be a
/// still-live result of `mapWindows` above.
fn unmapWindows(ptr: [*]u8) void {
    // SAFETY: caller guarantees `ptr` was returned by a prior VirtualAlloc call from
    // `mapWindows` above and not yet freed; VirtualFree with dwFreeType =
    // MEM_RELEASE requires dwSize == 0 and releases the entire original region,
    // matching HPHA's own `VirtualFree(addr, 0, MEM_RELEASE)` call.
    const ok = VirtualFree(@ptrCast(ptr), 0, MEM_RELEASE);
    std.debug.assert(ok != 0); // "VirtualFree failed"
}

// ---- Unix: mmap / munmap ----

fn mapUnix(size: usize) ?[*]u8 {
    // mmap only guarantees native-page alignment (4 KiB, or 16 KiB on Apple
    // Silicon); over-request by one PAGE_SIZE so there is always enough slack to
    // trim an aligned `size`-byte window out of the mapping.
    const request = size + PAGE_SIZE;
    // SAFETY: anonymous, private mapping; addr = null lets the kernel choose the
    // base address, fd = -1 and offset = 0 are the POSIX-required values for
    // MAP_ANON(YMOUS). Failure is reported as `std.c.MAP_FAILED` and checked below
    // before any use of `raw`, so no invalid pointer is ever read.
    const raw = std.c.mmap(
        null,
        request,
        .{ .READ = true, .WRITE = true },
        .{ .TYPE = .PRIVATE, .ANONYMOUS = true },
        -1,
        0,
    );
    if (raw == std.c.MAP_FAILED) return null;
    // mmap's result is a raw byte-addressable region; `@ptrCast` reinterprets the
    // pointee type without touching the address (no alignment change: `u8` has the
    // loosest possible alignment requirement).
    const base: [*]u8 = @ptrCast(raw);
    // ALIGN: round the mapping's base address up to PAGE_SIZE — mmap only
    // guarantees native-page alignment, not PAGE_SIZE (64 KiB) alignment.
    const aligned = align_helpers.alignUp(base, PAGE_SIZE);

    const head_len = @intFromPtr(aligned) - @intFromPtr(base);
    if (head_len > 0) {
        // ALIGN: `std.c.munmap` requires its pointer aligned to (at least) the
        // native page size; `base` is `std.c.mmap`'s own unmodified result, and
        // POSIX guarantees `mmap` returns memory aligned to the native page size —
        // `@alignCast` here recovers a guarantee `[*]u8`'s type (natural alignment
        // 1) already lost, not fabricates a new one.
        // SAFETY: `aligned` is within [base, base + request) since `request` has a
        // full PAGE_SIZE of slack over `size`, so `head_len` is in [0, PAGE_SIZE)
        // and [base, base + head_len) is a strict, still-mapped prefix of the
        // mmap'd region — trimming it does not touch [aligned, aligned + size).
        _ = std.c.munmap(@ptrCast(@alignCast(base)), head_len);
    }
    const tail_len = request - head_len - size;
    if (tail_len > 0) {
        // ALIGN: `aligned + size` is the end of the window being returned to the
        // caller; everything after it up to the mapping's end is unused slack.
        const tail = aligned + size;
        // ALIGN: `tail` is `aligned + size` — `aligned` is PAGE_SIZE-aligned (by
        // construction, via `alignUp` above) and `size` is a multiple of PAGE_SIZE
        // (`map`'s own caller contract, checked by its `std.debug.assert`), so
        // `tail` is PAGE_SIZE-aligned too, which is at least the native page size
        // `std.c.munmap` requires — same reasoning as the head trim's `@alignCast`.
        // SAFETY: aligned's address + size + tail_len == base's address + request
        // (the full mapped length), so [tail, tail + tail_len) is a strict,
        // still-mapped suffix of the mmap'd region, disjoint from
        // [aligned, aligned + size).
        _ = std.c.munmap(@ptrCast(@alignCast(tail)), tail_len);
    }
    return aligned;
}

/// # Safety
/// Same contract as `unmap` (this is its Unix implementation): `ptr`/`size` must
/// describe a still-live result of `mapUnix` above.
fn unmapUnix(ptr: [*]u8, size: usize) void {
    // ALIGN: `ptr` is a live result of `mapUnix` (this function's own contract),
    // whose own postcondition (asserted in `unmap`) is PAGE_SIZE alignment — at
    // least the native page size `std.c.munmap` requires.
    // SAFETY: caller guarantees `ptr`/`size` describe exactly the [aligned, aligned +
    // size) sub-range `mapUnix` returned above, which after trimming the head/tail
    // slivers is itself a single, still-mapped region.
    const ret = std.c.munmap(@ptrCast(@alignCast(ptr)), size);
    std.debug.assert(ret == 0); // "munmap failed"
}

// Every test below is skipped when cross-compiling for a target this machine
// cannot execute (Zig's test runner cannot run a foreign-architecture binary
// natively) — `zig build test` on each of the three CI OSes exercises the real
// syscalls for that platform natively; that native run is this module's actual
// verification, mirroring `orisnik`'s own `os.rs` test module (which is Miri-ignored
// for the equivalent reason: neither Miri nor a foreign-target test binary can
// exercise a real OS's virtual-memory syscalls).

test "map returns PAGE_SIZE-aligned memory" {
    const ptr = map(PAGE_SIZE) orelse return error.TestUnexpectedResult; // "OS map failed"
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % PAGE_SIZE);
    unmap(ptr, PAGE_SIZE);
}

test "a multi-page region is writable end to end" {
    const size = PAGE_SIZE * 3;
    const ptr = map(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % PAGE_SIZE);
    const slice = ptr[0..size];
    @memset(slice, 0xAB);
    try std.testing.expect(std.mem.allEqual(u8, slice, 0xAB));
    unmap(ptr, size);
}

test "repeated map/unmap cycles stay aligned" {
    for (0..8) |_| {
        const ptr = map(PAGE_SIZE) orelse return error.TestUnexpectedResult; // "OS map failed"
        try std.testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % PAGE_SIZE);
        unmap(ptr, PAGE_SIZE);
    }
}

test "concurrent live mappings do not alias" {
    const a = map(PAGE_SIZE) orelse return error.TestUnexpectedResult; // "OS map failed"
    const b = map(PAGE_SIZE) orelse return error.TestUnexpectedResult; // "OS map failed"
    try std.testing.expect(a != b);
    const a_start = @intFromPtr(a);
    const b_start = @intFromPtr(b);
    const ranges_overlap = a_start < b_start + PAGE_SIZE and b_start < a_start + PAGE_SIZE;
    try std.testing.expect(!ranges_overlap);
    unmap(a, PAGE_SIZE);
    unmap(b, PAGE_SIZE);
}
