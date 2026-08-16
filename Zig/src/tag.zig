// SPDX-License-Identifier: MIT OR Apache-2.0
//! Tagged-pointer helper for the intrusive red-black tree's parent link.
//!
//! Ports `Cpp/hpha.h`'s `ptr_bits<node_base, 2>` — HPHA's mechanism for storing a
//! red-black tree node's colour and which side of its parent it hangs from inside the
//! low two bits of the parent pointer itself, so the tree's per-node overhead stays at
//! exactly `children[2] + neighbours[2] + parent`, with no separate colour/side fields.
//!
//! Simpler than `orisnik`'s `tag.rs`: Rust needs a `TaggedPtr<T>` wrapper type and
//! `map_addr` gymnastics purely to satisfy strict-provenance rules Zig has no
//! equivalent of (`Zig/CONVENTIONS.md`'s "Pointer and Address Conversion" section).
//! Here the tagged value is a plain `usize` — the tree node's `parent` field IS this
//! `usize` directly, never a separate wrapper type — with `@ptrFromInt`/`@intFromPtr`
//! used only at the point of dereference/construction, in `rbtree.zig`. The two bits
//! are only ever meaningful while the address is non-dangling: every red-black tree
//! node has `@alignOf >= @sizeOf(usize)` (it embeds a `usize`-sized field alongside
//! its pointers), which is at least 4 on every platform this project targets, so bits
//! 0 and 1 of a valid node address are always zero before tagging.
//!
//! **`0` (fully untagged) is a valid tagged value, not an error case**: a red-black
//! tree node chained onto an equal-key group but not the group's tree-attached
//! representative has a literal null parent link (mirroring HPHA's `mParent = NULL`),
//! which the tree tests directly via `untagLink(tagged) == 0`.

const std = @import("std");

const TAG_MASK: usize = 0b11;

/// Bit 0 of a tagged link: the node's red-black colour (see `rbtree.Colour`).
pub const BIT_COLOUR: u1 = 0;
/// Bit 1 of a tagged link: which of the parent's two children this node is (see
/// `rbtree.Side`).
pub const BIT_SIDE: u1 = 1;

/// Packs `bits` (at most the low two bits) into the low two bits of `addr`, which
/// must itself have those bits clear (a tag-bit-aligned address — see the module doc).
pub fn tagLink(addr: usize, bits: usize) usize {
    // TAG: bits [0..2) of `addr` carry (colour, parent-side).
    return addr | (bits & TAG_MASK);
}

/// Recovers the untagged address (possibly `0`) from `tagged`.
pub fn untagLink(tagged: usize) usize {
    // UNTAG: clear bits [0..2) to recover the aligned node address (or `0`).
    return tagged & ~TAG_MASK;
}

/// Reads one tag bit.
pub fn bit(tagged: usize, which: u1) bool {
    // CAST: u1 -> the shift-amount type `usize`'s `Log2Int` requires; `which` is
    // exactly 0 or 1, always in range for the shift.
    return (tagged & (@as(usize, 1) << @intCast(which))) != 0;
}

/// Sets one tag bit, leaving the address and the other bit untouched.
pub fn setBit(tagged: usize, which: u1) usize {
    // TAG: OR in one bit of the two-bit tag; the address is untouched.
    // CAST: see `bit`.
    return tagged | (@as(usize, 1) << @intCast(which));
}

/// Clears one tag bit, leaving the address and the other bit untouched.
pub fn clearBit(tagged: usize, which: u1) usize {
    // UNTAG: clear one bit of the two-bit tag; the address is untouched.
    // CAST: see `bit`.
    return tagged & ~(@as(usize, 1) << @intCast(which));
}

/// Replaces the address, preserving the current tag bits.
pub fn setLink(tagged: usize, new_addr: usize) usize {
    // TAG: reapply the preserved (colour, parent-side) bits onto the new address.
    return tagLink(new_addr, tagged & TAG_MASK);
}

test "tagLink/untagLink: round-trip with no bits set" {
    const addr: usize = 0x1000;
    const tagged = tagLink(addr, 0);
    try std.testing.expectEqual(addr, untagLink(tagged));
    try std.testing.expect(!bit(tagged, BIT_COLOUR));
    try std.testing.expect(!bit(tagged, BIT_SIDE));
}

test "tagLink: packs the initial bits" {
    const addr: usize = 0x2000;
    const tagged = tagLink(addr, 0b11);
    try std.testing.expectEqual(addr, untagLink(tagged));
    try std.testing.expect(bit(tagged, BIT_COLOUR));
    try std.testing.expect(bit(tagged, BIT_SIDE));
}

test "setBit/clearBit: the two bits are independent" {
    const addr: usize = 0x3000;
    var tagged = tagLink(addr, 0);
    tagged = setBit(tagged, BIT_COLOUR);
    try std.testing.expect(bit(tagged, BIT_COLOUR));
    try std.testing.expect(!bit(tagged, BIT_SIDE));
    tagged = setBit(tagged, BIT_SIDE);
    try std.testing.expect(bit(tagged, BIT_COLOUR));
    try std.testing.expect(bit(tagged, BIT_SIDE));
    tagged = clearBit(tagged, BIT_COLOUR);
    try std.testing.expect(!bit(tagged, BIT_COLOUR));
    try std.testing.expect(bit(tagged, BIT_SIDE));
    try std.testing.expectEqual(addr, untagLink(tagged));
}

test "setLink: preserves the current tag bits" {
    const addr1: usize = 0x4000;
    const addr2: usize = 0x5000;
    var tagged = tagLink(addr1, 1 << BIT_SIDE);
    tagged = setLink(tagged, addr2);
    try std.testing.expectEqual(addr2, untagLink(tagged));
    try std.testing.expect(!bit(tagged, BIT_COLOUR));
    try std.testing.expect(bit(tagged, BIT_SIDE));
}

test "untagLink: a null (0) address round-trips with bits" {
    // The whole reason this module deals in plain tagged `usize`s rather than a
    // pointer-typed wrapper — see the module doc: a red-black tree node's tagged
    // parent link is `0` when the node is chained but not its equal-key group's
    // tree-attached member.
    var tagged = tagLink(0, 0);
    try std.testing.expectEqual(@as(usize, 0), untagLink(tagged));
    tagged = setBit(tagged, BIT_COLOUR);
    try std.testing.expectEqual(@as(usize, 0), untagLink(tagged));
    try std.testing.expect(bit(tagged, BIT_COLOUR));
}
