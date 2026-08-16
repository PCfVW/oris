// SPDX-License-Identifier: MIT OR Apache-2.0
//! The large-allocation path's inline block header, and the two node types the tree
//! allocator embeds inside a free block's own payload.
//!
//! Ports `Cpp/hpha.h`'s `block_header`, `free_node`, and `small_free_node`, mirroring
//! `orisnik`'s `block.rs`. A `BlockHeader` physically precedes every large-path
//! payload (allocated or free); `size_and_flags` doubles as the size of the block
//! *and* the offset to the next physical block (`BlockHeader.next` is computed, not
//! stored — HPHA keeps no separate "next block" pointer). `FreeNode`/`SmallFreeNode`
//! are placed at a block's `mem()` only while it is free, reusing its own payload as
//! the red-black tree / list bookkeeping storage for that block — zero overhead over
//! the block simply being free. `tree.zig` (Phase 5) owns the multi-block operations
//! (`splitBlock`/`shiftBlock`/`coalesceBlock`, `tree*`); this module owns a single
//! block's own layout and physical-neighbour chain.
//!
//! # 64-bit only
//! Matches `orisnik`'s own stance (see `block.rs`'s module doc): HPHA's C++ pads
//! `block_header` to `DEFAULT_ALIGNMENT` bytes past `sizeof(block_header*) +
//! sizeof(size_t)`, which on a 32-bit build leaves the *size* right but not the
//! *alignment* — a latent 32-bit gap in the 2007 reference. Rather than port that
//! gap, this targets 64-bit only for v0.1.0 (matching every CI runner, all 64-bit),
//! enforced at `comptime` below.
//!
//! # Field/accessor naming
//! Rust's `block_header` has a private `prev`/`size_and_flags` field alongside a
//! same-named public accessor function (`BlockHeader::prev(this)`) — legal in Rust,
//! since associated-function calls (`Type::method(x)`) and field access (`x.field`)
//! are syntactically distinct. Zig has one namespace per struct for fields and
//! declarations, so same-named field+method pairs are a compile error. Rather than
//! invent an unrelated name, `prev` stays a plain, directly-accessed field here (it
//! needs no derived/masked semantics unlike `size_and_flags`, so the accessor layer
//! was pure ceremony in the Rust original); `size_and_flags` likewise stays a plain
//! field, always touched through `size`/`setSize`/`used`/`setUsed`/`setUnused` by
//! convention (Zig has no field-privacy to enforce this, unlike Rust's `pub(crate)`).

const std = @import("std");
const rbtree = @import("rbtree.zig");
const list = @import("list.zig");

comptime {
    std.debug.assert(@bitSizeOf(usize) == 64);
}

/// Default alignment for the allocator's public API, and the alignment
/// `BlockHeader`'s own layout guarantees. Ports `allocator::DEFAULT_ALIGNMENT`
/// (`sizeof(double)`).
pub const DEFAULT_ALIGNMENT: usize = 8;

const BL_USED: usize = 1;
/// The two low bits of `size_and_flags` are reserved for flags (only `BL_USED` is
/// defined; bit 1 is unused but still masked off by `BlockHeader.size`, matching
/// HPHA's `mSizeAndFlags & ~3` exactly rather than just `& ~1`).
const SIZE_MASK: usize = ~@as(usize, 0b11);

/// The inline header physically preceding every large-path payload. Ports
/// `block_header`.
///
/// # Invariants
/// - `size()` is always a multiple of 4 (in practice always a multiple of
///   `@sizeOf(BlockHeader)`, since every block boundary is block-header-aligned —
///   `tree.zig`, Phase 5, always rounds requested sizes up to a multiple of
///   `@sizeOf(BlockHeader)` before installing them, mirroring HPHA's own
///   `tree_alloc`'s `round_up(size, sizeof(block_header))`; every `// ALIGN:`
///   comment below on a `*BlockHeader` cast relies on this caller contract, not on
///   anything this module enforces itself).
/// - `next(this) == mem(this) + size(this)` always — there is no separate stored
///   "next" pointer; `next` is a computed position, and `setNext` works backwards
///   from a target position to a size.
/// - The physical chain (`prev`/`next`) always terminates at fence blocks with
///   `size() == 0` (installed by `tree.zig`'s `treeAddBlock`), so `next`/`prev`
///   walks never run off the end of a tree arena.
pub const BlockHeader = extern struct {
    /// The physically-previous block header, or a fence block if this is the first
    /// real block in its arena — `null` only for the arena's own opening fence
    /// (`tree.zig`'s `addBlock`), which has no physical predecessor at all. That
    /// `null` is not a "never read" placeholder: `tree.zig`'s `purgeBlock` reads a
    /// candidate block's `prev.prev` and checks it against `null` specifically to
    /// detect "this block's predecessor is the opening fence, i.e. this is the
    /// arena's very first block" — an optional, not a non-optional pointer,
    /// because that check is load-bearing. Byte offset 0, naturally 8-byte
    /// (`DEFAULT_ALIGNMENT`)-aligned there since every `BlockHeader` position is
    /// itself 8-aligned (the layout guards below) — `?*BlockHeader` and
    /// `*BlockHeader` have identical size/alignment (Zig's null-pointer
    /// optimization), so this costs nothing over the non-optional field this
    /// module used before `tree.zig` needed to read a real `null` here.
    prev: ?*BlockHeader,
    /// Low 2 bits: flags (`BL_USED`, bit 1 unused). Remaining bits: this block's
    /// size in bytes, header included, i.e. the byte distance from `mem()` to the
    /// next block header. Byte offset 8 (64-bit), 8-byte aligned for the same
    /// reason as `prev` above. Always go through `size`/`setSize`/`used`/
    /// `setUsed`/`setUnused` — see the module doc's "Field/accessor naming" note.
    size_and_flags: usize,

    /// This block's size in bytes (header included), with the flag bits masked off.
    pub fn size(this: *BlockHeader) usize {
        return this.size_and_flags & SIZE_MASK;
    }

    /// Sets this block's size, preserving the flag bits. `sz` must be a multiple of 4.
    pub fn setSize(this: *BlockHeader, sz: usize) void {
        std.debug.assert(sz & ~SIZE_MASK == 0); // "size must be a multiple of 4"
        const flags = this.size_and_flags & ~SIZE_MASK;
        this.size_and_flags = flags | sz;
    }

    /// The start of this block's payload — the address immediately after the
    /// header.
    ///
    /// `this` must be live, with at least `@sizeOf(BlockHeader)` bytes valid after
    /// it (true for any block header ever installed by `tree.zig`).
    pub fn mem(this: *BlockHeader) [*]u8 {
        const base: [*]u8 = @ptrCast(this);
        return base + @sizeOf(BlockHeader);
    }

    /// The next physical block — a computed position (`mem() + size()`), not a
    /// stored pointer.
    pub fn next(this: *BlockHeader) *BlockHeader {
        const m = this.mem();
        const sz = this.size();
        const nxt = m + sz;
        // ALIGN: `m` is 8-aligned (`this` is a `BlockHeader`, align 8;
        // `@sizeOf(BlockHeader)` is a multiple of 8) and `sz` is a multiple of 8
        // (caller-contract invariant documented on the struct above), so `nxt` is
        // 8-aligned too — exactly `@alignOf(BlockHeader)`.
        return @ptrCast(@alignCast(nxt));
    }

    /// Sets this block's size so that `next` would return `target`. Ports the
    /// setter overload of `block_header::next` — computes a size from a target
    /// position, it does not store a pointer.
    ///
    /// `target` must be at or after `this.mem()`.
    pub fn setNext(this: *BlockHeader, target: *BlockHeader) void {
        const m = this.mem();
        // PROVENANCE: both addresses are read only for the byte distance between
        // them, never reconstructed into a pointer here — `setSize` stores that
        // distance as a plain integer, and a later `next()` call is what re-derives
        // an actual pointer from it (via its own, separately-justified arithmetic).
        const target_addr = @intFromPtr(target);
        const mem_addr = @intFromPtr(m);
        std.debug.assert(target_addr >= mem_addr); // "target must be at or after this block's own payload start"
        this.setSize(target_addr - mem_addr);
    }

    /// Whether this block is currently the allocated (not free) half of the
    /// large-allocation path's own bookkeeping — distinct from whether a payload
    /// happens to be user-live; the tree allocator sets/clears this exactly when it
    /// installs/removes a block from its free index.
    pub fn used(this: *BlockHeader) bool {
        return (this.size_and_flags & BL_USED) != 0;
    }

    /// Marks this block used, preserving its size.
    pub fn setUsed(this: *BlockHeader) void {
        this.size_and_flags |= BL_USED;
    }

    /// Marks this block unused (free), preserving its size.
    pub fn setUnused(this: *BlockHeader) void {
        this.size_and_flags &= ~BL_USED;
    }

    /// Removes `this` from the physical chain by growing its predecessor to
    /// swallow its space — HPHA never moves memory to unlink a block, it resizes
    /// the previous block's computed span instead. Ports `block_header::unlink`.
    ///
    /// `this`, `this`'s physical predecessor, and `this`'s physical successor must
    /// all be live — in particular `this` must not be the arena's own opening
    /// fence (the only block whose `prev` is ever `null`; fences are never
    /// unlinked).
    pub fn unlink(this: *BlockHeader) void {
        const nxt = this.next();
        const prv = this.prev.?;
        nxt.prev = prv;
        prv.setNext(nxt);
    }

    /// Inserts `this` into the physical chain immediately after `link`, taking
    /// over the span `link` used to claim beyond the split point (shrinking `link`
    /// in the process). Ports `block_header::link_after`.
    ///
    /// `this` must be live, with valid memory for at least `@sizeOf(BlockHeader)`
    /// bytes after it. `link` and `link`'s physical successor must be live.
    pub fn linkAfter(this: *BlockHeader, link: *BlockHeader) void {
        this.prev = link;
        const link_next = link.next();
        this.setNext(link_next);
        const this_next = this.next();
        this_next.prev = this;
        // `this` was just given a real (non-null) `prev` above (`link`), so this
        // unwrap is sound regardless of what `this.prev` held before this call.
        const this_prev = this.prev.?;
        this_prev.setNext(this);
    }
};

comptime {
    // Layout lock — matches `orisnik`'s `#[repr(C)]` `BlockHeader` field-for-field,
    // per `Zig/CONVENTIONS.md`'s "extern and packed layout lock" rule.
    std.debug.assert(@sizeOf(BlockHeader) == 2 * @sizeOf(usize));
    std.debug.assert(@alignOf(BlockHeader) == DEFAULT_ALIGNMENT);
    std.debug.assert(@offsetOf(BlockHeader, "prev") == 0);
    std.debug.assert(@offsetOf(BlockHeader, "size_and_flags") == @sizeOf(usize));
}

/// Recovers the block header immediately preceding a payload pointer. Ports the
/// allocator's `ptr_get_block_header`.
///
/// `ptr` must be a payload pointer previously returned by the tree allocator (i.e.
/// `ptr == header.mem()` for some live `header`).
pub fn ptrGetBlockHeader(ptr: [*]u8) *BlockHeader {
    const header = ptr - @sizeOf(BlockHeader);
    // ALIGN: `ptr` is `header.mem()` for some live `header` (this function's
    // contract), which is 8-aligned (`mem` = `this + 16`, `this` already
    // 8-aligned); stepping back the same 16 bytes recovers that 8-aligned address.
    return @ptrCast(@alignCast(header));
}

/// The red-black tree node the tree allocator embeds at a free block's `mem()`,
/// keyed by the owning block's size. Ports `free_node`.
pub const FreeNode = extern struct {
    /// This node's tree linkage. Byte offset 0 (required by `IntrusiveMultiRbTree`).
    node: rbtree.NodeBase = .{},

    pub const Key = usize;

    /// The block header owning this free node — `this` is always exactly
    /// `block.mem()` while the block is free.
    ///
    /// `this` must currently be a live free block's embedded `FreeNode` (i.e.
    /// stepping back `@sizeOf(BlockHeader)` bytes from it is a live, unused
    /// `BlockHeader`).
    pub fn getBlock(this: *FreeNode) *BlockHeader {
        const base: [*]u8 = @ptrCast(this);
        const header = base - @sizeOf(BlockHeader);
        // ALIGN: `this` is `block.mem()` for some live `block` (this function's
        // contract), which is 8-aligned; stepping back the same 16 bytes recovers
        // that 8-aligned address.
        return @ptrCast(@alignCast(header));
    }

    /// Orders by the owning block's size. `IntrusiveMultiRbTree`'s required `cmp`.
    pub fn cmp(this: *FreeNode, other: *FreeNode) std.math.Order {
        return std.math.order(this.getBlock().size(), other.getBlock().size());
    }

    /// `IntrusiveMultiRbTree`'s required `cmpKey`.
    pub fn cmpKey(this: *FreeNode, key: usize) std.math.Order {
        return std.math.order(this.getBlock().size(), key);
    }
};

/// The plain list node the tree allocator embeds at a small free block's `mem()` —
/// an optimization over `FreeNode` for blocks too small to be worth indexing by
/// size in the tree (never queried, so a list suffices; see `tree.zig`). Ports
/// `small_free_node`.
pub const SmallFreeNode = extern struct {
    /// This node's list linkage. Byte offset 0 (required by `IntrusiveList`).
    link: list.ListLink = list.ListLink.UNLINKED,
};

const testing = std.testing;

/// A raw, heap-backed arena for placing block headers into during tests — a
/// stand-in for the real VM-mapped tree arena `tree.zig` will use. Backed by
/// `[]u64`, not `[]u8`, so the type system itself guarantees 8-byte
/// (`DEFAULT_ALIGNMENT`) alignment.
const Arena = struct {
    buf: []u64,

    fn init(allocator: std.mem.Allocator, size: usize) !Arena {
        const words = (size + @sizeOf(u64) - 1) / @sizeOf(u64);
        const buf = try allocator.alloc(u64, words);
        @memset(buf, 0);
        return .{ .buf = buf };
    }

    fn deinit(self: *Arena, allocator: std.mem.Allocator) void {
        allocator.free(self.buf);
    }

    /// `offset` (in bytes) must be a multiple of 8 — every call site below uses
    /// offsets that are, by construction, multiples of `@sizeOf(BlockHeader)` (16)
    /// or otherwise chosen to be 8-aligned.
    fn headerAt(self: *Arena, offset: usize) *BlockHeader {
        std.debug.assert(offset % @alignOf(BlockHeader) == 0);
        const base: [*]u8 = @ptrCast(self.buf.ptr);
        const byte_ptr = base + offset;
        // ALIGN: `self.buf` is `[]u64`-backed (8-aligned by the type system);
        // `offset` is a multiple of 8 (checked above), so `byte_ptr` is 8-aligned.
        return @ptrCast(@alignCast(byte_ptr));
    }
};

/// Installs a fresh, unused block header of `size` bytes (header included) at
/// `header`, with `prev` as its physical predecessor (`null` for a test's
/// synthetic first block, whose `prev` is never read — matching `orisnik`'s own
/// `null_mut()` placeholder in the same tests, directly representable now that
/// `BlockHeader.prev` is `?*BlockHeader`).
///
/// `header` must be valid for `@sizeOf(BlockHeader)` bytes; `prev`, if non-null,
/// must be live.
fn installBlock(header: *BlockHeader, prev: ?*BlockHeader, size: usize) void {
    header.prev = prev;
    header.setSize(size);
    header.setUnused();
}

test "size/used round-trip" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const h = arena.headerAt(0);
    installBlock(h, null, 64);
    try testing.expectEqual(@as(usize, 64), h.size());
    try testing.expect(!h.used());
    h.setUsed();
    try testing.expect(h.used());
    try testing.expectEqual(@as(usize, 64), h.size()); // flag bit must not corrupt size
    h.setUnused();
    try testing.expect(!h.used());
}

test "next is computed from mem plus size" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const h = arena.headerAt(0);
    installBlock(h, null, 64);
    const mem = h.mem();
    const nxt = h.next();
    const nxt_bytes: [*]u8 = @ptrCast(nxt);
    try testing.expectEqual(@intFromPtr(mem) + 64, @intFromPtr(nxt_bytes));
}

test "setNext computes size from target position" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const h = arena.headerAt(0);
    installBlock(h, null, 64);
    const target = arena.headerAt(80);
    h.setNext(target);
    try testing.expectEqual(target, h.next());
    try testing.expectEqual(@as(usize, 80 - @sizeOf(BlockHeader)), h.size());
}

test "unlink grows predecessor over removed block" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const a = arena.headerAt(0);
    const b = arena.headerAt(48);
    const c = arena.headerAt(96);
    installBlock(a, null, 48);
    installBlock(b, a, 48);
    installBlock(c, b, 0); // fence
    b.setNext(c);
    b.unlink();
    try testing.expectEqual(c, a.next());
    try testing.expectEqual(a, c.prev.?);
}

test "linkAfter splits predecessor span" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const a = arena.headerAt(0);
    const end = arena.headerAt(96);
    installBlock(a, null, 0);
    a.setNext(end); // `a` initially spans up to `end`
    const new_block = arena.headerAt(48);
    new_block.linkAfter(a);
    try testing.expectEqual(new_block, a.next()); // a shrank to end at the split point
    try testing.expectEqual(a, new_block.prev.?);
    try testing.expectEqual(end, new_block.next()); // new_block inherited a's old span boundary
    try testing.expectEqual(new_block, end.prev.?);
}

test "ptrGetBlockHeader round-trips with mem" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 256);
    defer arena.deinit(allocator);
    const h = arena.headerAt(0);
    installBlock(h, null, 64);
    const mem = h.mem();
    try testing.expectEqual(h, ptrGetBlockHeader(mem));
}

// A free node's block-size comparisons drive the tree allocator's whole
// size-keyed index; test it against a real `IntrusiveMultiRbTree`, not just in
// isolation, since that is the only way `FreeNode` is ever used.
test "free node orders by owning block size" {
    const allocator = testing.allocator;
    var arena = try Arena.init(allocator, 1024);
    defer arena.deinit(allocator);
    const sizes = [_]usize{ 64, 128, 32, 96 };
    var headers: [4]*BlockHeader = undefined;
    var offset: usize = 0;
    for (sizes, 0..) |sz, i| {
        const h = arena.headerAt(offset);
        installBlock(h, null, sz);
        headers[i] = h;
        offset += 200;
    }

    var tree: rbtree.IntrusiveMultiRbTree(FreeNode) = .init();
    for (headers) |h| {
        const node: *FreeNode = @ptrCast(@alignCast(h.mem()));
        tree.insert(node);
    }

    const smallest = tree.minimum().?;
    try testing.expectEqual(@as(usize, 32), smallest.getBlock().size());

    const found = tree.lowerBound(96).?;
    try testing.expectEqual(@as(usize, 96), found.getBlock().size());

    for (headers) |h| {
        const node: *FreeNode = @ptrCast(@alignCast(h.mem()));
        tree.erase(node);
    }
    try testing.expect(tree.isEmpty());
}
