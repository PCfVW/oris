// SPDX-License-Identifier: MIT OR Apache-2.0
//! Payload poisoning — filling a block's payload with a recognizable pattern on
//! allocation (catches reads of uninitialized memory) and on free (catches
//! use-after-free reads), so a bug reads *this*, not silently plausible-looking
//! leftover data.
//!
//! Ports `Cpp/hpha.cpp:762-767`'s `debug_record_map::initial_fill` exactly: a
//! repeating 4-byte pattern, `{0xFF, 0xC0, 0xC0, 0xFF}`, chosen (per HPHA's own
//! comment) because it reads as a quiet-NaN bit pattern in either endianness.
//! This is a **separate** mechanism from the guard ramp (`spomen_guard.zig`) —
//! guard bytes trail the payload to catch overflow, poisoning fills the payload
//! itself. Mirrors `orisnik`'s `Rust/src/spomen/poison.rs`.
//!
//! Wired into the tree/bucket `alloc`/`allocAligned` choke points (fill on
//! success, after the guard write — matching HPHA's
//! `write_guard()`-then-`initial_fill()` order inside `debug_record_map::add`)
//! and into `free`/`freeWithSize*` (fill before the underlying reclaim —
//! matching `debug_remove` running before `bucket_free`/`tree_free` in
//! `allocator::free`). Deliberately **not** wired into `realloc`/`resize`:
//! HPHA's own `update`/`replace` never poison, only `add`/`remove` do (see
//! `Cpp/hpha.cpp`'s `debug_record_map`, `update`/`replace` bodies).
//!
//! `calloc` composes with this for free: `orisnitsa.zig`'s `Orisnitsa.calloc`
//! calls `alloc` (which poisons), then unconditionally zero-fills the exact
//! same span — the poison is immediately overwritten, exactly as it would be in
//! HPHA (which poisons inside `alloc` unconditionally too, with no
//! `calloc`-specific bypass).

/// The repeating fill pattern. Ports `debug_record_map::initial_fill`'s
/// `unsigned char sFiller[] = {0xFF,0xC0,0xC0,0xFF}`.
const PATTERN = [4]u8{ 0xFF, 0xC0, 0xC0, 0xFF };

/// The pattern byte at position `i` of a `fill`ed span — the one place
/// `PATTERN` is actually indexed, so every caller (this module's own `fill`,
/// plus tests elsewhere that check a poisoned payload) shares one clearly
/// in-bounds site instead of repeating the same `% PATTERN.len` computation.
/// Zig has no clippy-equivalent indexing lint forcing this factoring (unlike
/// the Rust port's `#[allow(clippy::indexing_slicing)]`), but it is kept for
/// the same "one place indexes the pattern" clarity, and so test code that
/// wants to predict the poisoned pattern can call it too.
pub fn byteAt(i: usize) u8 {
    // INDEX: `PATTERN.len == 4`, and `i % PATTERN.len < 4` always.
    return PATTERN[i % PATTERN.len];
}

/// Fills `len` bytes starting at `ptr` with the repeating `PATTERN`.
///
/// `ptr` must be valid for `len` bytes, writable, and exclusively owned for
/// that span (no other live reference into it).
pub fn fill(ptr: [*]u8, len: usize) void {
    // EXPLICIT: a plain `for i in 0..len` loop over single-byte writes, not a
    // bulk-fill helper — `len` is not necessarily a multiple of `PATTERN.len`,
    // and this is a direct, one-to-one port of HPHA's own
    // `for (s = 0; s < size; s++) p[s] = sFiller[s % 4];` loop, not a
    // functionally-equivalent rewrite.
    for (0..len) |i| {
        // SAFETY: `ptr` is valid, writable and exclusively owned for `len` bytes
        // (this function's caller contract) and `i < len`, so the raw write stays
        // in bounds and races with no other live reference.
        // INDEX: `i < len`, so this stays within `ptr`'s valid span (caller's
        // contract: valid, writable and exclusively owned for `len` bytes).
        ptr[i] = byteAt(i);
    }
}

const testing = @import("std").testing;

test "fills shorter than the pattern" {
    var buf = [_]u8{ 0, 0, 0 };
    fill(&buf, 3);
    try testing.expectEqual([3]u8{ PATTERN[0], PATTERN[1], PATTERN[2] }, buf);
}

test "cycles the pattern past its own length" {
    var buf = [_]u8{0} ** 10;
    fill(&buf, 10);
    for (0..10) |i| {
        try testing.expectEqual(byteAt(i), buf[i]);
    }
}

test "zero-length fill touches nothing" {
    var buf = [_]u8{0xAB} ** 4;
    fill(&buf, 0);
    try testing.expectEqual([4]u8{ 0xAB, 0xAB, 0xAB, 0xAB }, buf);
}
