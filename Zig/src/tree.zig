// SPDX-License-Identifier: MIT OR Apache-2.0
//! The large-allocation path: best-fit over a red-black tree of free blocks, with
//! physical-neighbour coalescing.
//!
//! Ports `Cpp/hpha.h`/`hpha.cpp`'s `allocator::{split_block, shift_block,
//! coalesce_block, tree_*}`, mirroring `orisnik`'s `tree.rs`. Every free block's
//! payload doubles as either a `FreeNode` (tree-indexed, for blocks bigger than
//! `MAX_SMALL_ALLOCATION`) or a `SmallFreeNode` (plain-listed — never queried by
//! size, so a list is cheaper) — see `block.zig`'s module doc. On top of that, the
//! single most-recently-freed block is cached outside both structures
//! (`mr_free_block`) as a fast path for the very common "free then immediately
//! realloc/alloc a similar size" pattern.
//!
//! # Fence blocks
//! Every OS-backed arena this module grows (`Tree.addBlock`) is bracketed by two
//! zero-sized, permanently-`used` fence block headers — one before the first real
//! block (`prev == null`), one after the last (`size() == 0`). Real blocks'
//! `prev`/`next()` walks (in `coalesceBlock`, `Tree.purgeBlock`) terminate at these
//! without needing a separate "is this the arena boundary" check: a fence is simply
//! always `used()`, so coalescing never merges across it, exactly like a real
//! allocated block. This is exactly why `block.zig`'s `BlockHeader.prev` had to
//! become `?*BlockHeader` rather than staying a non-optional field: the opening
//! fence's `null` prev is read here, in `purgeBlock`, to detect "this candidate
//! block is the arena's very first."
//!
//! # `&self` vs `*Self`
//! Same simplification as `bucket.zig`'s `Buckets`/`Bucket`: `orisnik`'s `Tree`
//! wraps `mr_free_block`/`allocated_bytes` in `Cell`s purely to satisfy Rust's
//! `&self`-only aliasing rule at the allocator trait boundary. Every method here
//! just takes `*Tree` directly, and both fields are plain.

const std = @import("std");
const align_helpers = @import("align.zig");
const block = @import("block.zig");
const bucket = @import("bucket.zig");
const list = @import("list.zig");
const os = @import("os.zig");
const rbtree = @import("rbtree.zig");

const BlockHeader = block.BlockHeader;
const FreeNode = block.FreeNode;
const SmallFreeNode = block.SmallFreeNode;

/// The minimum block size: large enough to hold a `FreeNode` in its payload once
/// free. Ports the `if (size < sizeof(free_node)) size = sizeof(free_node);` clamp
/// repeated at the top of every `tree_*` sizing path.
const MIN_BLOCK_SIZE: usize = @sizeOf(FreeNode);

/// The minimum leftover a split must produce to be worth splitting off as its own
/// free block — a header plus room for a `FreeNode`. Ports the
/// `sizeof(block_header) + sizeof(free_node)` threshold repeated throughout
/// `hpha.cpp`'s `tree_*` functions.
const SPLIT_REMAINDER_MIN: usize = @sizeOf(BlockHeader) + @sizeOf(FreeNode);

/// Rounds `size` up to a valid block payload size: at least `MIN_BLOCK_SIZE`, and a
/// multiple of `@sizeOf(BlockHeader)` (so every block boundary this produces stays
/// `BlockHeader`-aligned — see `block.zig`'s alignment note). Ports the
/// `if (size < sizeof(free_node)) size = sizeof(free_node); size = round_up(size,
/// sizeof(block_header));` pair opening every `tree_alloc*`/`tree_realloc*`/`tree_resize`.
fn normalizeSize(size: usize) usize {
    const clamped = if (size < MIN_BLOCK_SIZE) MIN_BLOCK_SIZE else size;
    return align_helpers.roundUp(clamped, @sizeOf(BlockHeader));
}

/// Splits `bl` at `size` bytes into its payload, turning the remainder (at least
/// `SPLIT_REMAINDER_MIN` bytes, header included) into a new, unused block linked
/// right after it. Ports `allocator::split_block`.
///
/// `bl` must be live, with `size + SPLIT_REMAINDER_MIN <= bl.size()`, and `size`
/// must be a multiple of `@sizeOf(BlockHeader)` (every call site in this module
/// upholds this — see `normalizeSize` and the alignment-offset splits in
/// `Tree.allocAligned`/`Tree.reallocAligned`, which rely on every block's `mem()`
/// being `@sizeOf(BlockHeader)`-aligned, itself a consequence of every block size
/// being a multiple of `@sizeOf(BlockHeader)`).
fn splitBlock(bl: *BlockHeader, size: usize) void {
    std.debug.assert(size % @sizeOf(BlockHeader) == 0);
    const bl_bytes: [*]u8 = @ptrCast(bl);
    const split_point = bl_bytes + (size + @sizeOf(BlockHeader));
    // ALIGN: `bl` is a live `BlockHeader`, hence 8-aligned; `size` is a multiple of
    // `@sizeOf(BlockHeader)` (16) per this function's contract, and so is
    // `@sizeOf(BlockHeader)` itself, so `split_point` stays 8-aligned.
    const new_bl: *BlockHeader = @ptrCast(@alignCast(split_point));
    new_bl.linkAfter(bl);
    new_bl.setUnused();
}

/// Moves `bl` forward by `offs` bytes in place, splicing it out of its old physical
/// position and into a new one immediately after its old predecessor. Used to align
/// a block's payload when the exact alignment offset is too small to be worth
/// leaving behind as its own free block. Ports `allocator::shift_block`.
///
/// `bl` must be live and attached to a live physical chain (live `prev`/`next()`).
/// `offs > 0`, and shifting `bl` by `offs` bytes must stay within `bl`'s own span
/// (i.e. `offs <= bl.size()`, though in practice always far smaller — see the
/// alignment-offset call sites).
fn shiftBlock(bl: *BlockHeader, offs: usize) *BlockHeader {
    std.debug.assert(offs > 0);
    const prv = bl.prev.?;
    bl.unlink();
    const bl_bytes: [*]u8 = @ptrCast(bl);
    const shifted = bl_bytes + offs;
    // ALIGN: `bl` is 8-aligned; every alignment-offset call site in this module
    // only ever shifts by a multiple of `@sizeOf(BlockHeader)` (see `splitBlock`'s
    // contract doc for why every block's `mem()` is always `BlockHeader`-aligned,
    // the same reasoning applies to shift offsets, which are alignment gaps
    // between two such positions).
    // Named `shifted_bl`, not reusing `bl` (which `orisnik`'s `shift_block`
    // reassigns via `let bl = shifted.cast(...)`) — Zig errors on identifier
    // shadowing between a parameter and a same-named local.
    const shifted_bl: *BlockHeader = @ptrCast(@alignCast(shifted));
    shifted_bl.linkAfter(prv);
    shifted_bl.setUnused();
    return shifted_bl;
}

/// The large-allocation path's state: the free-block index (a size-keyed tree for
/// blocks bigger than `MAX_SMALL_ALLOCATION`, a plain list for smaller ones), the
/// most-recently-freed-block fast-path cache, and the running allocated-byte total.
/// Ports the tree-related slice of `allocator` (`mMRFreeBlock`, `mFreeTree`,
/// `mSmallFreeList`, `mTotalAllocatedSizeTree`, and the free `tree_*` methods).
///
/// # Invariants
/// - Every currently-free block is indexed in exactly one place: `mr_free_block`,
///   or `free_tree` (size `>` `MAX_SMALL_ALLOCATION`), or `small_free_list` (size
///   `<=` `MAX_SMALL_ALLOCATION`) — never more than one, and never none while
///   unused. `attach`/`detach` are the only crossing points between these three.
/// - No two physically-adjacent blocks are ever both free: every path that frees
///   or splits a block runs it through `coalesceBlock` first, so a free block's
///   `prev`/`next()` are always themselves either used or a fence.
/// - `allocated_bytes` is exactly the sum of `size` arguments passed to
///   `systemAlloc` minus those passed to `systemFree` — the total bytes this
///   `Tree` currently has mapped from the OS.
pub const Tree = struct {
    /// The single most recently freed block, checked before searching the
    /// tree/list at all — HPHA's fast path for "free, then immediately
    /// reallocate a similar size." Never itself a member of
    /// `free_tree`/`small_free_list`.
    mr_free_block: ?*BlockHeader = null,
    /// Free blocks bigger than `MAX_SMALL_ALLOCATION`, keyed by size.
    free_tree: rbtree.IntrusiveMultiRbTree(FreeNode) = .init(),
    /// Free blocks at most `MAX_SMALL_ALLOCATION` — never queried by size, so a
    /// plain list is cheaper than tree bookkeeping for them.
    small_free_list: list.IntrusiveList(SmallFreeNode) = .init(),
    /// Total bytes currently mapped for the tree path (whole `PAGE_SIZE`-multiple
    /// arenas, fences included).
    allocated_bytes: usize = 0,

    /// Builds an empty tree allocator, with nothing yet mapped from the OS.
    pub fn init() Tree {
        return .{};
    }

    /// Total bytes currently claimed from the OS by the tree path. Ports the tree
    /// half of `allocator::allocated`.
    pub fn allocated(self: *Tree) usize {
        return self.allocated_bytes;
    }

    /// Coalesces `bl` (which must currently be unused) with either physical
    /// neighbour that is also free, detaching any neighbour absorbed this way
    /// from whichever index it was in. Returns the (possibly different) block
    /// header now representing the merged span. Ports `allocator::coalesce_block`.
    ///
    /// `bl` must be live, unused, and attached to a live physical chain.
    fn coalesceBlock(self: *Tree, bl: *BlockHeader) *BlockHeader {
        std.debug.assert(!bl.used());
        const nxt = bl.next();
        if (!nxt.used()) {
            // `nxt` is live and unused, hence currently indexed (in the tree, the
            // small list, or the MR cache) — a live free block always is.
            self.detach(nxt);
            nxt.unlink();
        }
        const prv = bl.prev.?;
        // Named `result`, not reusing `bl` (which `orisnik`'s `coalesce_block`
        // reassigns via `let mut bl = bl;`) — Zig errors on identifier shadowing
        // between a parameter and a same-named local.
        var result = bl;
        if (!prv.used()) {
            // `prv` is live and unused, hence currently indexed (same reasoning
            // as `nxt` above).
            self.detach(prv);
            result.unlink();
            result = prv;
        }
        return result;
    }

    /// Maps `size` bytes (a multiple of `os.PAGE_SIZE`) for the tree arena. Ports
    /// `allocator::tree_system_alloc`.
    fn systemAlloc(self: *Tree, size: usize) ?[*]u8 {
        std.debug.assert(size % os.PAGE_SIZE == 0);
        const ptr = os.map(size) orelse return null;
        self.allocated_bytes += size;
        return ptr;
    }

    /// Returns a tree arena mapping to the OS. Ports `allocator::tree_system_free`.
    ///
    /// `ptr`/`size` must be a still-live result of `systemAlloc` on `self`.
    fn systemFree(self: *Tree, ptr: [*]u8, size: usize) void {
        os.unmap(ptr, size);
        self.allocated_bytes -= size;
    }

    /// Lays out a freshly-mapped `size`-byte arena as two fence blocks bracketing
    /// one large free block, then coalesces (a no-op here, since both neighbours
    /// are fences and therefore `used`, but kept for fidelity — see the module
    /// doc). Ports `allocator::tree_add_block`.
    ///
    /// `mem` must be live, exclusively owned, for exactly `size` bytes, `size` a
    /// multiple of `@sizeOf(BlockHeader)` and at least `3 * @sizeOf(BlockHeader)`.
    fn addBlock(self: *Tree, mem: [*]u8, size: usize) *BlockHeader {
        std.debug.assert(size % @sizeOf(BlockHeader) == 0);
        std.debug.assert(size >= 3 * @sizeOf(BlockHeader));
        // ALIGN: `mem` is `os.map`'s result, PAGE_SIZE-aligned, hence 8-aligned.
        const fence0: *BlockHeader = @ptrCast(@alignCast(mem));
        fence0.prev = null;
        fence0.setSize(0);
        fence0.setUsed();

        const real_front_bytes = fence0.mem();
        // ALIGN: `fence0` is 8-aligned; `BlockHeader.mem` adds
        // `@sizeOf(BlockHeader)` (a multiple of 8), so `real_front_bytes` stays
        // 8-aligned.
        const real_front: *BlockHeader = @ptrCast(@alignCast(real_front_bytes));
        real_front.prev = fence0;
        real_front.setSize(0);
        real_front.setUsed();

        const end_fence_bytes = mem + (size - @sizeOf(BlockHeader));
        // ALIGN: `mem` is 8-aligned; `size` and `@sizeOf(BlockHeader)` are both
        // multiples of 8, so `end_fence_bytes` stays 8-aligned.
        const end_fence: *BlockHeader = @ptrCast(@alignCast(end_fence_bytes));
        end_fence.setSize(0);
        end_fence.setUsed();

        real_front.setUnused();
        real_front.setNext(end_fence);
        end_fence.prev = real_front;

        // `real_front` is live, unused (just set above), and attached to the live
        // chain just built (fence0 <-> real_front <-> end_fence).
        return self.coalesceBlock(real_front);
    }

    /// Maps a fresh arena sized to comfortably fit one `size`-byte block (`size`
    /// already the exact block payload size being requested, header excluded),
    /// lays it out via `addBlock`. Ports `allocator::tree_grow`.
    fn grow(self: *Tree, size: usize) ?*BlockHeader {
        const with_overhead = size + 3 * @sizeOf(BlockHeader); // two fences plus one fake
        const rounded = align_helpers.roundUp(with_overhead, os.PAGE_SIZE);
        const mem = self.systemAlloc(rounded) orelse return null;
        return self.addBlock(mem, rounded);
    }

    /// Extracts a free block of at least `size` bytes: the MR-cached block if it
    /// fits, otherwise the smallest fitting block in the tree (walking one step to
    /// an equal-key chain neighbour first when possible, since removing a plain
    /// chain link is cheaper than removing a tree-attached node). Ports
    /// `allocator::tree_extract`.
    fn extract(self: *Tree, size: usize) ?*BlockHeader {
        if (self.mr_free_block) |best| {
            if (best.size() >= size) {
                self.detach(best);
                return best;
            }
        }
        const best_node = self.free_tree.lowerBound(size) orelse return null;
        // Improves removal time: an equal-key chain link is O(1) to remove, while
        // the tree-attached representative needs a full erase_fixup.
        const chained = rbtree.next(best_node);
        const best_block = chained.getBlock();
        self.detach(best_block);
        return best_block;
    }

    /// Extracts a free block of at least `size` bytes whose `mem()` can be aligned
    /// to `alignment` without more than `size` bytes of slack. Same
    /// MR-cache-first, chain-neighbour-preferred strategy as `extract`, but must
    /// additionally walk candidates in `[size, size + alignment)` since a
    /// merely-big-enough block might not leave room for the alignment padding.
    /// Ports `allocator::tree_extract_aligned`.
    fn extractAligned(self: *Tree, size: usize, alignment: usize) ?*BlockHeader {
        if (self.mr_free_block) |best| {
            const m = best.mem();
            // PROVENANCE: both addresses are read only for the byte distance
            // between them, never reconstructed into a pointer here.
            const alignment_offs = @intFromPtr(align_helpers.alignUp(m, alignment)) - @intFromPtr(m);
            if (best.size() >= size + alignment_offs) {
                self.detach(best);
                return best;
            }
        }
        const size_upper = size + alignment;
        // `cur`/`last_node` are `?*FreeNode` throughout (rather than a single
        // pointer compared against a real sentinel `end()`, as HPHA's C++ has):
        // `null` here is exactly that sentinel. Every comparison and advance below
        // mirrors the C++ `while (bestNode != lastNode)` loop's *shape* precisely,
        // including which node's fit is (and is not) checked, which is why this
        // can't be simplified to higher-level constructs.
        var cur = self.free_tree.lowerBound(size);
        const last_node = self.free_tree.upperBound(size_upper);
        // EXPLICIT: walks the `[size, size_upper)` candidate sequence looking for
        // one with enough room for both the payload and the alignment padding;
        // `cur` is the state, not expressible as an iterator over a tree-order
        // walk. A `cur == null` exit (checked by the `while` below) means we
        // walked past the maximum node without reaching `last_node` — only
        // happens when `last_node` is itself `null` (nothing in the tree is as
        // large as `size_upper`), matching HPHA's `bestNode == end()`.
        while (cur) |node| {
            if (cur == last_node) {
                // Reached the upper bound without finding a fit; `last_node`
                // itself is never fit-checked (mirrors the C++ `while` condition
                // being checked *before* the loop body).
                break;
            }
            // PROVENANCE: `node`'s address is read only for its bit pattern (fed
            // into the same rounding arithmetic `align.roundUp` uses elsewhere),
            // never reconstructed into a pointer — `node` itself is what's used
            // as a pointer, unaffected by this read.
            const addr = @intFromPtr(node);
            const alignment_offs = align_helpers.roundUp(addr, alignment) - addr;
            const candidate = node.getBlock();
            if (candidate.size() >= size + alignment_offs) {
                break;
            }
            cur = self.free_tree.succ(node);
        }
        const found = cur orelse return null;
        // Improves removal time, same reasoning as `extract` — but only applies
        // when we stopped *at* `last_node` (no fit found in range); a genuine fit
        // found strictly before it is used as-is.
        const best_node = if (cur == last_node) rbtree.next(found) else found;
        const best_block = best_node.getBlock();
        self.detach(best_block);
        return best_block;
    }

    /// Indexes `bl` as free: the previous MR-cached block (if any) is pushed into
    /// the tree or small list first, then `bl` becomes the new MR-cached block.
    /// Ports `allocator::tree_attach`.
    ///
    /// `bl` must be live and unused, or `null` (used by `purge` to flush the MR
    /// cache without installing a new block).
    fn attach(self: *Tree, bl: ?*BlockHeader) void {
        if (self.mr_free_block) |last| {
            const size = last.size();
            // `last`'s `mem()` is exactly where it was indexed from on a prior
            // `attach` (this same invariant, inductively) or is fresh free space
            // at least `MIN_BLOCK_SIZE` bytes (every block this module creates is
            // normalized to at least that), so a `FreeNode`/`SmallFreeNode` fits.
            const mem = last.mem();
            if (size > bucket.MAX_SMALL_ALLOCATION) {
                // ALIGN: `mem` is `@sizeOf(BlockHeader)`-aligned (every block's
                // `mem()` is, per `splitBlock`'s contract doc), hence 8-aligned —
                // matches `FreeNode`'s alignment (its only field is `NodeBase`,
                // align 8).
                const node: *FreeNode = @ptrCast(@alignCast(mem));
                self.free_tree.insert(node);
            } else {
                // ALIGN: same reasoning as the `FreeNode` cast above;
                // `SmallFreeNode` is likewise align-8 (its only field is
                // `ListLink`, align 8).
                const node: *SmallFreeNode = @ptrCast(@alignCast(mem));
                self.small_free_list.pushBack(node);
            }
        }
        self.mr_free_block = bl;
    }

    /// Removes `bl` from wherever it is currently indexed (the MR cache, the
    /// tree, or the small list). Ports `allocator::tree_detach`.
    fn detach(self: *Tree, bl: *BlockHeader) void {
        if (self.mr_free_block == bl) {
            self.mr_free_block = null;
            return;
        }
        const size = bl.size();
        const mem = bl.mem();
        if (size > bucket.MAX_SMALL_ALLOCATION) {
            // ALIGN: see `attach`'s identical cast for why this is 8-aligned.
            const node: *FreeNode = @ptrCast(@alignCast(mem));
            self.free_tree.erase(node);
        } else {
            // ALIGN: see `attach`'s identical cast for why this is 8-aligned.
            const node: *SmallFreeNode = @ptrCast(@alignCast(mem));
            list.unlinkNode(node);
        }
    }

    /// Allocates `size` bytes on the tree path. Ports `allocator::tree_alloc`.
    pub fn alloc(self: *Tree, size: usize) ?[*]u8 {
        const sz = normalizeSize(size);
        const new_bl = self.extract(sz) orelse (self.grow(sz) orelse return null);
        const new_bl_size = new_bl.size();
        std.debug.assert(new_bl_size >= sz);
        if (new_bl_size >= sz + SPLIT_REMAINDER_MIN) {
            splitBlock(new_bl, sz);
            self.attach(new_bl.next());
        }
        new_bl.setUsed();
        return new_bl.mem();
    }

    /// Allocates `size` bytes on the tree path, aligned to `alignment`. Ports
    /// `allocator::tree_alloc_aligned`.
    pub fn allocAligned(self: *Tree, size: usize, alignment: usize) ?[*]u8 {
        const sz = normalizeSize(size);
        var new_bl = self.extractAligned(sz, alignment) orelse (self.grow(sz + alignment) orelse return null);
        const new_bl_size = new_bl.size();
        std.debug.assert(new_bl_size >= sz);
        const mem = new_bl.mem();
        // PROVENANCE: both addresses are read only for the byte distance between
        // them, never reconstructed into a pointer here.
        const alignment_offs = @intFromPtr(align_helpers.alignUp(mem, alignment)) - @intFromPtr(mem);
        std.debug.assert(new_bl_size >= sz + alignment_offs);
        if (alignment_offs >= SPLIT_REMAINDER_MIN) {
            // `alignment_offs - @sizeOf(BlockHeader)` is the padding block's
            // payload size, a multiple of `@sizeOf(BlockHeader)` (see
            // `splitBlock`'s contract doc: every block's `mem()`, hence every
            // alignment offset between two such positions, is a
            // `@sizeOf(BlockHeader)` multiple), and this branch's own
            // `>= SPLIT_REMAINDER_MIN` check is exactly `splitBlock`'s size
            // precondition applied to that padding block.
            splitBlock(new_bl, alignment_offs - @sizeOf(BlockHeader));
            // `new_bl` is live and unused (still its pre-extraction state;
            // `extractAligned` never marks it used).
            self.attach(new_bl);
            new_bl = new_bl.next();
        } else if (alignment_offs > 0) {
            // `new_bl` is live and attached to a live physical chain (from
            // `extractAligned`/`grow`, both return blocks freshly spliced into a
            // real chain); `alignment_offs` is a `@sizeOf(BlockHeader)` multiple
            // (same reasoning as above) and within `new_bl`'s own span (the
            // `>= size + alignment_offs` check above).
            new_bl = shiftBlock(new_bl, alignment_offs);
        }
        if (new_bl.size() >= sz + SPLIT_REMAINDER_MIN) {
            splitBlock(new_bl, sz);
            self.attach(new_bl.next());
        }
        new_bl.setUsed();
        const mem_out = new_bl.mem();
        std.debug.assert(@intFromPtr(mem_out) % alignment == 0);
        return mem_out;
    }

    /// Grows or shrinks `ptr` in place when a physical neighbour can absorb the
    /// difference, otherwise falls back to allocate/copy/free. Ports
    /// `allocator::tree_realloc`.
    ///
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    pub fn realloc(self: *Tree, ptr: [*]u8, size: usize) ?[*]u8 {
        const sz = normalizeSize(size);
        const bl = block.ptrGetBlockHeader(ptr);
        const bl_size = bl.size();
        if (bl_size >= sz) {
            if (bl_size >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                const coalesced = self.coalesceBlock(bl.next());
                self.attach(coalesced);
            }
            return ptr;
        }
        const next = bl.next();
        const next_used = next.used();
        const next_size: usize = if (next_used) 0 else next.size() + @sizeOf(BlockHeader);
        if (bl_size + next_size >= sz) {
            std.debug.assert(!next_used);
            self.detach(next);
            next.unlink();
            const bl_size_now = bl.size();
            std.debug.assert(bl_size_now >= sz);
            if (bl_size_now >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                self.attach(bl.next());
            }
            return ptr;
        }
        const prev = bl.prev.?;
        const prev_used = prev.used();
        const prev_size: usize = if (prev_used) 0 else prev.size() + @sizeOf(BlockHeader);
        if (bl_size + prev_size + next_size >= sz) {
            std.debug.assert(!prev_used);
            self.detach(prev);
            bl.unlink();
            if (!next_used) {
                self.detach(next);
                next.unlink();
            }
            // Named `merged`, not reusing `bl` (which `orisnik`'s `tree_realloc`
            // reassigns via `let bl = prev;`) — Zig errors on identifier
            // shadowing between an existing local and a same-named rebinding.
            const merged = prev;
            merged.setUsed();
            const merged_size_now = merged.size();
            std.debug.assert(merged_size_now >= sz);
            const new_ptr = merged.mem();
            // `ptr` is valid for `bl_size` bytes (its own pre-move size); `new_ptr`
            // is `merged`'s own fresh payload start, with room for at least
            // `bl_size` bytes (`merged`'s new size is `>= sz > bl_size`); the two
            // ranges may overlap (this is exactly a block growing backwards over
            // its own former self), hence `@memmove`'s overlap-safe copy, not
            // `@memcpy`.
            @memmove(new_ptr[0..bl_size], ptr[0..bl_size]);
            if (merged.size() >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(merged, sz);
                self.attach(merged.next());
            }
            return new_ptr;
        }
        // Fall back: no physical neighbour can absorb the growth; allocate fresh,
        // copy, free the old block.
        const new_ptr = self.alloc(sz) orelse return null;
        // `new_ptr` was just allocated with room for at least `sz > bl_size`
        // bytes; `ptr` is valid for `bl_size` bytes; the two allocations never
        // overlap (freshly, independently allocated).
        @memcpy(new_ptr[0..bl_size], ptr[0..bl_size]);
        self.free(ptr);
        return new_ptr;
    }

    /// Grows or shrinks `ptr` in place, aligned to `alignment`, otherwise falls
    /// back to allocate/copy/free. Ports `allocator::tree_realloc_aligned`.
    ///
    /// `ptr` must be a still-live tree-path allocation this instance produced,
    /// itself already aligned to `alignment`.
    pub fn reallocAligned(self: *Tree, ptr: [*]u8, size: usize, alignment: usize) ?[*]u8 {
        std.debug.assert(@intFromPtr(ptr) % alignment == 0);
        const sz = normalizeSize(size);
        const bl = block.ptrGetBlockHeader(ptr);
        const bl_size = bl.size();
        if (bl_size >= sz) {
            if (bl_size >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                const coalesced = self.coalesceBlock(bl.next());
                self.attach(coalesced);
            }
            return ptr;
        }
        const next = bl.next();
        const next_used = next.used();
        const next_size: usize = if (next_used) 0 else next.size() + @sizeOf(BlockHeader);
        if (bl_size + next_size >= sz) {
            std.debug.assert(!next_used);
            self.detach(next);
            next.unlink();
            const bl_size_now = bl.size();
            std.debug.assert(bl_size_now >= sz);
            if (bl_size_now >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                self.attach(bl.next());
            }
            return ptr;
        }
        const prev = bl.prev.?;
        const prev_used = prev.used();
        const prev_size: usize = if (prev_used) 0 else prev.size() + @sizeOf(BlockHeader);
        const alignment_offs: usize = if (prev_used) 0 else blk: {
            const prev_mem = prev.mem();
            // PROVENANCE: both addresses are read only for the byte distance
            // between them, never reconstructed into a pointer here.
            break :blk @intFromPtr(align_helpers.alignUp(prev_mem, alignment)) - @intFromPtr(prev_mem);
        };
        if (bl_size + prev_size + next_size >= sz + alignment_offs) {
            std.debug.assert(!prev_used);
            self.detach(prev);
            bl.unlink();
            if (!next_used) {
                self.detach(next);
                next.unlink();
            }
            // Named `shifted_prev`, not reusing `prev` (which `orisnik`'s
            // `tree_realloc_aligned` reassigns via `let mut prev = prev;`) — Zig
            // errors on identifier shadowing.
            var shifted_prev = prev;
            if (alignment_offs >= SPLIT_REMAINDER_MIN) {
                // Same reasoning as `allocAligned`'s identical branch.
                splitBlock(shifted_prev, alignment_offs - @sizeOf(BlockHeader));
                // `shifted_prev` is live and unused (unlinked from its index
                // above, not yet re-attached).
                self.attach(shifted_prev);
                shifted_prev = shifted_prev.next();
            } else if (alignment_offs > 0) {
                // `shifted_prev` is live, attached to a live chain (it was just
                // unlinked and is about to be relinked by the surrounding logic —
                // more precisely, at this point it is temporarily detached from
                // the physical chain along with `bl`/`next`; `shiftBlock` itself
                // only needs its *own* prev/next fields to still be live, which
                // they are, since only it itself was unlinked, not its
                // neighbours).
                shifted_prev = shiftBlock(shifted_prev, alignment_offs);
            }
            // Named `merged`, not `bl` (which `orisnik`'s counterpart reassigns
            // via `let bl = prev;`) — same identifier-shadowing reason as
            // `realloc`.
            const merged = shifted_prev;
            merged.setUsed();
            const merged_size_now = merged.size();
            std.debug.assert(merged_size_now >= sz);
            const new_ptr = merged.mem();
            std.debug.assert(@intFromPtr(new_ptr) % alignment == 0);
            // `ptr` is valid for `bl_size` bytes; `new_ptr` has room for at least
            // `bl_size` bytes; the ranges may overlap (growing in place).
            @memmove(new_ptr[0..bl_size], ptr[0..bl_size]);
            if (merged_size_now >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(merged, sz);
                self.attach(merged.next());
            }
            return new_ptr;
        }
        const new_ptr = self.allocAligned(sz, alignment) orelse return null;
        // `new_ptr` was just allocated with room for at least `bl_size` bytes;
        // `ptr` is valid for `bl_size` bytes; freshly, independently allocated,
        // so never overlapping.
        @memcpy(new_ptr[0..bl_size], ptr[0..bl_size]);
        self.free(ptr);
        return new_ptr;
    }

    /// Grows `ptr` in place if a following free block can absorb the difference,
    /// without moving it; returns the resulting size either way (the block's own
    /// size if it couldn't grow enough). Ports `allocator::tree_resize`.
    ///
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    pub fn resize(self: *Tree, ptr: [*]u8, size: usize) usize {
        const sz = normalizeSize(size);
        const bl = block.ptrGetBlockHeader(ptr);
        const bl_size = bl.size();
        if (bl_size >= sz) {
            if (bl_size >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                const coalesced = self.coalesceBlock(bl.next());
                self.attach(coalesced);
            }
            return bl.size();
        }
        const next = bl.next();
        const next_used = next.used();
        const next_size = next.size();
        if (!next_used and bl_size + next_size + @sizeOf(BlockHeader) >= sz) {
            self.detach(next);
            next.unlink();
            if (bl.size() >= sz + SPLIT_REMAINDER_MIN) {
                splitBlock(bl, sz);
                self.attach(bl.next());
            }
            const bl_size_now = bl.size();
            std.debug.assert(bl_size_now >= sz);
        }
        return bl.size();
    }

    /// Frees `ptr`, coalescing with either physical neighbour that is also free.
    /// Ports `allocator::tree_free`.
    ///
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    pub fn free(self: *Tree, ptr: [*]u8) void {
        const bl = block.ptrGetBlockHeader(ptr);
        bl.setUnused();
        // `bl` is live and unused (just set above), attached to a live chain
        // (this function's contract: `ptr` was a live allocation).
        const coalesced = self.coalesceBlock(bl);
        self.attach(coalesced);
    }

    /// Returns `bl`'s whole arena to the OS if `bl` is the arena's only content
    /// (its physical predecessor is the arena's opening fence, its successor the
    /// closing one). Ports `allocator::tree_purge_block`.
    ///
    /// `bl` must be live, unused, and attached to a live physical chain.
    fn purgeBlock(self: *Tree, bl: *BlockHeader) void {
        std.debug.assert(!bl.used());
        // `bl.prev` is never `null` here: `bl` is a real (non-fence) block, per
        // this function's own contract, and fences are the only blocks with a
        // `null` prev. `bl.next()` needs no analogous unwrap — it is computed,
        // never stored, so its type has no `null` to check in the first place
        // (unlike `orisnik`'s raw `*mut BlockHeader`, which carries a redundant
        // `debug_assert!(!next.is_null())` this port has no equivalent state for).
        const prev = bl.prev.?;
        std.debug.assert(prev.used());
        const next = bl.next();
        std.debug.assert(next.used());
        const prev_prev = prev.prev;
        const next_size = next.size();
        if (prev_prev == null and next_size == 0) {
            self.detach(bl);
            const mem_start: [*]u8 = @ptrCast(prev);
            const bl_mem = bl.mem();
            const bl_size = bl.size();
            // `bl_mem` is `bl`'s own payload start; `bl_size` bytes past it stays
            // within `bl`'s own span.
            const past_payload = bl_mem + bl_size;
            // `past_payload` is exactly `next` (`bl.mem() + bl.size()` is
            // `bl.next()` by definition), live (established above);
            // `@sizeOf(BlockHeader)` bytes past it stays within `next`'s own span.
            const mem_end = past_payload + @sizeOf(BlockHeader);
            // PROVENANCE: both addresses are read only for the byte distance
            // between them, never reconstructed into a pointer here.
            const size = @intFromPtr(mem_end) - @intFromPtr(mem_start);
            std.debug.assert(@intFromPtr(mem_start) % os.PAGE_SIZE == 0);
            std.debug.assert(size % os.PAGE_SIZE == 0);
            // `mem_start`/`size` describe exactly the arena `addBlock` originally
            // mapped (the opening fence through the closing one, established by
            // the `prev_prev`/`next_size` checks above), not referenced again
            // after this call (everything in it — `bl`, `prev`, `next` — is
            // either just detached or was never indexed at all, being a fence).
            self.systemFree(mem_start, size);
        }
    }

    /// Returns every fully-unused arena to the OS. Ports `allocator::tree_purge`.
    pub fn purge(self: *Tree) void {
        // Flush the MR cache so its block is visible to the scan below (a block
        // only the MR cache references can't be identified as purgeable by
        // walking the tree alone).
        self.attach(null);
        // Only an arena whose sole content is one free block spanning (almost)
        // the whole thing is purgeable — `addBlock` reserves two fences plus one
        // fake block of overhead, so the smallest possible whole-arena free block
        // is PAGE_SIZE minus that overhead.
        const min_purgeable = os.PAGE_SIZE - 3 * @sizeOf(BlockHeader) - @sizeOf(FreeNode);
        // EXPLICIT: walks every free-tree node at or above `min_purgeable`,
        // advancing to each one's successor *before* possibly purging it out from
        // under the walk (mirrors HPHA's own `node = node->succ()` before
        // `tree_purge_block`); `node` is the state, not expressible as an
        // iterator invalidated by removal.
        var node = self.free_tree.lowerBound(min_purgeable);
        while (node) |cur| {
            const blk = cur.getBlock();
            node = self.free_tree.succ(cur);
            // `blk` is live, unused (a `FreeNode` only ever sits at a free
            // block's `mem()`), attached to a live physical chain.
            self.purgeBlock(blk);
        }
        self.attach(null);
    }
};

const testing = std.testing;

// A heap-backed, `@sizeOf(BlockHeader)`-aligned (in practice far more — `[]u64`
// guarantees 8-byte alignment, the same as `os.map`'s real 64 KiB pages provide)
// stand-in for a real OS-mapped tree arena. Lets `Tree.addBlock` (the actual
// arena-layout logic) run under `std.testing.allocator` leak detection without
// touching real `os.map`. Every test using this must never call `Tree.purge`:
// purging tries to `os.unmap` whatever arena it reclaims, which is unsound for
// memory that didn't come from `os.map` in the first place.
const FakeArena = struct {
    buf: []u64,

    fn init(allocator: std.mem.Allocator, size: usize) !FakeArena {
        const words = (size + @sizeOf(u64) - 1) / @sizeOf(u64);
        const buf = try allocator.alloc(u64, words);
        @memset(buf, 0);
        return .{ .buf = buf };
    }

    fn deinit(self: *FakeArena, allocator: std.mem.Allocator) void {
        allocator.free(self.buf);
    }

    fn ptr(self: *FakeArena) [*]u8 {
        return @ptrCast(self.buf.ptr);
    }
};

// Lays `size` bytes of `arena` out as one big free block and attaches it, exactly
// like `Tree.grow` does for real OS memory — but skipping `systemAlloc`, so no real
// OS call happens (see `FakeArena`'s doc).
fn seed(tree: *Tree, arena: *FakeArena, size: usize) void {
    const front = tree.addBlock(arena.ptr(), size);
    tree.attach(front);
}

test "seeded alloc serves without touching the OS" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const ptr = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    @memset(ptr[0..64], 0xAB);
}

test "alloc splits a remainder which stays available" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    // The remainder (far bigger than SPLIT_REMAINDER_MIN) was split off and
    // attached; a second, disjoint allocation must still succeed from it without
    // any OS growth.
    const b = tree.alloc(64) orelse return error.TestUnexpectedResult; // "split remainder must be available"
    try testing.expect(a != b);
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
}

test "free then alloc same size reuses the MR-cached block" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    tree.free(a);
    const b = tree.alloc(64) orelse return error.TestUnexpectedResult; // "freed block must be reusable"
    // The most-recently-freed block is checked first and fits exactly: the fast
    // path must return the very same address, not a different free region.
    try testing.expectEqual(a, b);
}

test "free coalesces adjacent blocks, enabling a larger alloc" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    // Three sequential allocations carve up the same seeded region in order (the
    // MR-cache-first extract path always prefers the just-split remainder).
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    const b = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    const c = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    tree.free(b);
    tree.free(a);
    // `a` and `b`'s space must now be one merged free block: an allocation
    // bigger than either alone (but within their combined span) must succeed
    // without touching the OS.
    const combined = tree.alloc(64 + 64 + 32) orelse return error.TestUnexpectedResult; // "coalesced span must fit this"
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    tree.free(c);
    tree.free(combined);
}

test "small and large free blocks are both retrievable past the MR cache" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 8192);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 8192);
    const small = tree.alloc(64) orelse return error.TestUnexpectedResult; // <= MAX_SMALL_ALLOCATION once freed
    const large = tree.alloc(bucket.MAX_SMALL_ALLOCATION + 64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    const spacer = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    tree.free(small);
    tree.free(large);
    // `large`'s free happened after `small`'s, so `small` was pushed out of the
    // MR cache into `small_free_list` (its size is `<= MAX_SMALL_ALLOCATION`) —
    // and is still retrievable via a fresh small allocation.
    const small_again = tree.alloc(64) orelse return error.TestUnexpectedResult; // "small_free_list entry must be reusable"
    // `large` itself is the current MR block; freeing `spacer` (unrelated, since
    // it's not physically adjacent to `large` after the two frees above) pushes
    // `large` into `free_tree` (its size is `> MAX_SMALL_ALLOCATION`).
    tree.free(spacer);
    const large_again = tree.alloc(bucket.MAX_SMALL_ALLOCATION + 64) orelse return error.TestUnexpectedResult; // "free_tree entry must be reusable"
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    tree.free(small_again);
    tree.free(large_again);
}

test "allocAligned respects every requested alignment" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 8192);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 8192);
    for ([_]usize{ 16, 32, 64, 128, 256 }) |alignment| {
        const ptr = tree.allocAligned(48, alignment) orelse return error.TestUnexpectedResult; // "seeded arena has room"
        try testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % alignment); // "misaligned for requested alignment"
        tree.free(ptr);
    }
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
}

test "realloc shrink splits off a reusable remainder" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(512) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    @memset(a[0..512], 0xCD);
    const shrunk = tree.realloc(a, 64) orelse return error.TestUnexpectedResult; // "shrinking never fails"
    try testing.expectEqual(a, shrunk); // shrinking must not move the block
    // The remainder split off by the shrink must be available for reuse.
    const reused = tree.alloc(128) orelse return error.TestUnexpectedResult; // "split remainder must be available"
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    tree.free(shrunk);
    tree.free(reused);
}

test "realloc grows in place over a following free block" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    @memset(a[0..64], 0xEF);
    // The remainder after `a` is free (split off and attached by `alloc` above);
    // growing into it must succeed in place.
    const grown = tree.realloc(a, 512) orelse return error.TestUnexpectedResult; // "must grow into the free remainder"
    try testing.expectEqual(a, grown); // growing into a following free block must not move it
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    // The first 64 bytes must have been preserved across the in-place grow.
    try testing.expect(std.mem.allEqual(u8, grown[0..64], 0xEF));
    tree.free(grown);
}

test "realloc falls back to alloc/copy/free when boxed in" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    @memset(a[0..64], 0x11);
    // `b` immediately follows `a`, leaving no free neighbour for `a` to grow into.
    const b = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    const moved = tree.realloc(a, 512) orelse return error.TestUnexpectedResult; // "falls back to a fresh allocation"
    try testing.expect(moved != a); // boxed-in growth must relocate
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    // The first 64 bytes must have been preserved across the copy.
    try testing.expect(std.mem.allEqual(u8, moved[0..64], 0x11));
    tree.free(moved);
    tree.free(b);
}

test "resize reports the grown size without moving" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    const new_size = tree.resize(a, 512);
    try testing.expect(new_size >= 512);
    // `resize` never moves the block — verify it's still usable as a 512-byte
    // region at its original address.
    @memset(a[0..512], 0x22);
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // must not have called os.map
    tree.free(a);
}

test "resize reports the unchanged size when it cannot grow" {
    const allocator = testing.allocator;
    var tree: Tree = .init();
    var arena = try FakeArena.init(allocator, 4096);
    defer arena.deinit(allocator);
    seed(&tree, &arena, 4096);
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "seeded arena has room"
    // Querying with `a`'s own current size must be a no-op that reports that same
    // size.
    const original_size = tree.resize(a, 64);
    _ = tree.alloc(64) orelse return error.TestUnexpectedResult; // boxes `a` in
    const after = tree.resize(a, 4096);
    try testing.expectEqual(original_size, after); // "boxed-in resize must report the unchanged size, never fail or move"
    tree.free(a);
}

// "Tree.alloc/free/purge returns memory to the OS" is the one test in this module
// that calls real `Tree.alloc`/`grow`/`purge` against actual OS memory (it must:
// `purge` returning memory to the OS is exactly the behaviour under test, and
// `os.unmap` is unsound to call on anything but real `os.map` memory — see
// `FakeArena`'s doc). Exercised by native `zig build test` on all three CI OSes,
// just like `os.zig`'s own tests.
test "Tree.alloc/free/purge returns memory to the OS" {
    var tree: Tree = .init();
    const a = tree.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(tree.allocated() > 0);
    tree.free(a);
    tree.purge();
    try testing.expectEqual(@as(usize, 0), tree.allocated()); // "a freshly-grown, now fully-free arena must be fully reclaimed"
}
