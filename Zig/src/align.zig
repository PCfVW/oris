// SPDX-License-Identifier: MIT OR Apache-2.0
//! Alignment and rounding helpers shared by every allocator subsystem.
//!
//! Ports `Cpp/hpha.h`'s `round_up`/`round_down`/`align_up`/`align_down`, mirroring
//! `orisnik`'s `align.rs`. Every `alignment` parameter here must be a power of two —
//! callers are responsible for validating that (the public API validates the
//! caller-supplied alignment before any of these are reached). `roundUp`/`roundDown`
//! delegate to `std.mem.alignForward`/`alignBackward`, which themselves assert
//! power-of-two-ness via `std.debug.assert` — elided in `ReleaseFast`/`ReleaseSmall`,
//! present in `Debug`/`ReleaseSafe`, exactly the tool `Zig/CONVENTIONS.md`'s `assert`
//! vs safety-checks section prescribes for a hot-path invariant.

const std = @import("std");

/// Rounds `value` down to the nearest multiple of `alignment` (`alignment` must be a
/// power of two). Thin wrapper over `std.mem.alignBackward` so every call site in this
/// module tree uses one name, per `Zig/CONVENTIONS.md`'s "single `align_up`/
/// `align_down` helper, never open-code the mask twice" rule.
pub fn roundDown(value: usize, alignment: usize) usize {
    return std.mem.alignBackward(usize, value, alignment);
}

/// Rounds `value` up to the nearest multiple of `alignment` (`alignment` must be a
/// power of two). Thin wrapper over `std.mem.alignForward`.
pub fn roundUp(value: usize, alignment: usize) usize {
    return std.mem.alignForward(usize, value, alignment);
}

/// Rounds a pointer's address down to the nearest multiple of `alignment`.
pub fn alignDown(ptr: [*]u8, alignment: usize) [*]u8 {
    // PROVENANCE: `addr` is read only for its bit pattern; the result is rebuilt at
    // the rounded address, so it derives from the same allocation `ptr` already
    // pointed into — only the address changes.
    // ALIGN: round the address down to `alignment`, matching HPHA's `align_down`.
    const addr = @intFromPtr(ptr);
    return @ptrFromInt(roundDown(addr, alignment));
}

/// Rounds a pointer's address up to the nearest multiple of `alignment`.
pub fn alignUp(ptr: [*]u8, alignment: usize) [*]u8 {
    // PROVENANCE: see `alignDown` — same reasoning, rounding the other direction.
    // ALIGN: round the address up to `alignment`, matching HPHA's `align_up`.
    const addr = @intFromPtr(ptr);
    return @ptrFromInt(roundUp(addr, alignment));
}

test "roundDown: a multiple of the alignment is its own identity" {
    try std.testing.expectEqual(@as(usize, 64), roundDown(64, 64));
    try std.testing.expectEqual(@as(usize, 128), roundDown(128, 64));
}

test "roundDown: clears the low bits" {
    try std.testing.expectEqual(@as(usize, 64), roundDown(65, 64));
    try std.testing.expectEqual(@as(usize, 0), roundDown(1, 64));
    try std.testing.expectEqual(@as(usize, 56), roundDown(63, 8));
}

test "roundUp: a multiple of the alignment is its own identity" {
    try std.testing.expectEqual(@as(usize, 64), roundUp(64, 64));
    try std.testing.expectEqual(@as(usize, 0), roundUp(0, 64));
}

test "roundUp: crosses to the next multiple" {
    try std.testing.expectEqual(@as(usize, 128), roundUp(65, 64));
    try std.testing.expectEqual(@as(usize, 8), roundUp(1, 8));
    try std.testing.expectEqual(@as(usize, 16), roundUp(9, 8));
}

test "alignDown/alignUp: pointer round-trip across a boundary" {
    // A comptime address probe: alignDown/alignUp never dereference, they only do
    // address arithmetic, so a literal @ptrFromInt is a sound way to exercise the
    // math in isolation without a real allocation behind it (the same technique
    // std.mem's own `alignPointer` test uses).
    const ptr: [*]u8 = @ptrFromInt(0x1_2345);
    const down = alignDown(ptr, 0x1000);
    const up = alignUp(ptr, 0x1000);
    try std.testing.expectEqual(@as(usize, 0x1_2000), @intFromPtr(down));
    try std.testing.expectEqual(@as(usize, 0x1_3000), @intFromPtr(up));
}

test "alignDown/alignUp: an already-aligned pointer is unchanged" {
    const ptr: [*]u8 = @ptrFromInt(0x1_0000);
    try std.testing.expectEqual(@as(usize, 0x1_0000), @intFromPtr(alignDown(ptr, 0x1000)));
    try std.testing.expectEqual(@as(usize, 0x1_0000), @intFromPtr(alignUp(ptr, 0x1000)));
}
