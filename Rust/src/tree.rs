// SPDX-License-Identifier: MIT OR Apache-2.0
//! The large-allocation path: best-fit over a red-black tree of free blocks, with
//! physical-neighbour coalescing.
//!
//! Ports `Cpp/hpha.h`/`hpha.cpp`'s `allocator::{split_block, shift_block,
//! coalesce_block, tree_*}`. Every free block's payload doubles as either a
//! [`FreeNode`] (tree-indexed, for blocks bigger than [`MAX_SMALL_ALLOCATION`]) or a
//! [`SmallFreeNode`] (plain-listed — never queried by size, so a list is cheaper) —
//! see `block.rs`'s module doc. On top of that, the single most-recently-freed block
//! is cached outside both structures (`mr_free_block`) as a fast path for the very
//! common "free then immediately realloc/alloc a similar size" pattern.
//!
//! # Fence blocks
//! Every OS-backed arena this module grows ([`Tree::add_block`]) is bracketed by two
//! zero-sized, permanently-`used` fence block headers — one before the first real
//! block (`prev() == null`), one after the last (`size() == 0`). Real blocks'
//! `prev()`/`next()` walks (in [`coalesce_block`], [`Tree::purge_block`]) terminate at
//! these without needing a separate "is this the arena boundary" check: a fence is
//! simply always `used()`, so coalescing never merges across it, exactly like a real
//! allocated block.

use crate::align::round_up;
use crate::block::{self, BlockHeader, FreeNode, SmallFreeNode};
use crate::bucket::MAX_SMALL_ALLOCATION;
use crate::list::{self, IntrusiveList};
use crate::os;
use crate::rbtree::{self, IntrusiveMultiRbTree};
use core::cell::Cell;
use core::ptr::NonNull;

/// The minimum block size: large enough to hold a [`FreeNode`] in its payload once
/// free. Ports the `if (size < sizeof(free_node)) size = sizeof(free_node);` clamp
/// repeated at the top of every `tree_*` sizing path.
const MIN_BLOCK_SIZE: usize = size_of::<FreeNode>();

/// The minimum leftover a split must produce to be worth splitting off as its own
/// free block — a header plus room for a [`FreeNode`]. Ports the
/// `sizeof(block_header) + sizeof(free_node)` threshold repeated throughout
/// `hpha.cpp`'s `tree_*` functions.
const SPLIT_REMAINDER_MIN: usize = size_of::<BlockHeader>() + size_of::<FreeNode>();

/// The largest request this module's own size arithmetic can carry without an
/// intermediate step wrapping `usize`.
///
/// Every term is one rounding step on the path from a caller's `size` to a mapped
/// arena, subtracted so that step's headroom is guaranteed:
///
/// - `os::PAGE_SIZE` — [`Tree::grow`]'s `round_up(_, PAGE_SIZE)`
/// - `3 * size_of::<BlockHeader>()` — [`Tree::grow`]'s two fences plus one fake block
/// - `size_of::<BlockHeader>()` — [`normalize_size`]'s own `round_up(_, 16)`
///
/// # Deviation from HPHA, and why it is not one
/// HPHA performs this arithmetic unchecked, so a sufficiently large request wraps and
/// yields a block far smaller than asked for (`tree_alloc(SIZE_MAX)` normalizes to
/// zero). That is not behaviour this port preserves: **no request at or below this
/// bound changes behaviour**, and every request above it was already unsatisfiable —
/// HPHA merely corrupted the heap instead of saying so. The bound is roughly
/// `usize::MAX - 64 KiB`, so no allocation any real machine could serve is affected.
/// Rejecting is therefore a strict refinement of undefined behaviour, not a change of
/// contract, and it touches no state transition the cross-port invariant counts.
pub(crate) const MAX_ALLOCATION: usize =
    usize::MAX - os::PAGE_SIZE - 3 * size_of::<BlockHeader>() - size_of::<BlockHeader>();

/// Rounds `size` up to a valid block payload size: at least [`MIN_BLOCK_SIZE`], and a
/// multiple of `size_of::<BlockHeader>()` (so every block boundary this produces stays
/// `BlockHeader`-aligned — see `block.rs`'s alignment note). Ports the
/// `if (size < sizeof(free_node)) size = sizeof(free_node); size = round_up(size,
/// sizeof(block_header));` pair opening every `tree_alloc*`/`tree_realloc*`/`tree_resize`.
///
/// Returns `None` when `size` exceeds [`MAX_ALLOCATION`] — the one place this port
/// declines to reproduce HPHA's unchecked arithmetic; see that constant's own doc.
#[must_use]
const fn normalize_size(size: usize) -> Option<usize> {
    if size > MAX_ALLOCATION {
        return None;
    }
    let size = if size < MIN_BLOCK_SIZE {
        MIN_BLOCK_SIZE
    } else {
        size
    };
    Some(round_up(size, size_of::<BlockHeader>()))
}

/// Splits `bl` at `size` bytes into its payload, turning the remainder (at least
/// [`SPLIT_REMAINDER_MIN`] bytes, header included) into a new, unused block linked
/// right after it. Ports `allocator::split_block`.
///
/// # Safety
/// `bl` must be live, with `size + SPLIT_REMAINDER_MIN <= BlockHeader::size(bl)`, and
/// `size` must be a multiple of `size_of::<BlockHeader>()` (every call site in this
/// module upholds this — see `normalize_size` and the alignment-offset splits in
/// [`Tree::alloc_aligned`]/[`Tree::realloc_aligned`], which rely on every block's
/// `mem()` being `size_of::<BlockHeader>()`-aligned, itself a consequence of every
/// block size being a multiple of `size_of::<BlockHeader>()`).
unsafe fn split_block(bl: *mut BlockHeader, size: usize) {
    debug_assert_eq!(size % size_of::<BlockHeader>(), 0);
    // SAFETY: `bl` is live (this function's contract); the split point is within
    // `bl`'s own span (this function's size precondition).
    let split_point = unsafe { bl.cast::<u8>().byte_add(size + size_of::<BlockHeader>()) };
    // ALIGN: `bl` is a live `BlockHeader`, hence 8-aligned; `size` is a multiple of
    // `size_of::<BlockHeader>()` (16) per this function's contract, and so is
    // `size_of::<BlockHeader>()` itself, so `split_point` stays 8-aligned.
    #[allow(clippy::cast_ptr_alignment)]
    let new_bl = split_point.cast::<BlockHeader>();
    // SAFETY: `new_bl` is within `bl`'s own valid span (this function's contract);
    // `bl` is live.
    unsafe { BlockHeader::link_after(new_bl, bl) };
    // SAFETY: `new_bl` is live (just linked above).
    unsafe { BlockHeader::set_unused(new_bl) };
}

/// Moves `bl` forward by `offs` bytes in place, splicing it out of its old physical
/// position and into a new one immediately after its old predecessor. Used to align a
/// block's payload when the exact alignment offset is too small to be worth leaving
/// behind as its own free block. Ports `allocator::shift_block`.
///
/// # Safety
/// `bl` must be live and attached to a live physical chain (live `prev()`/`next()`).
/// `offs > 0`, and `bl.byte_add(offs)` must stay within `bl`'s own span (i.e.
/// `offs <= BlockHeader::size(bl)`, though in practice always far smaller — see the
/// alignment-offset call sites).
#[must_use]
unsafe fn shift_block(bl: *mut BlockHeader, offs: usize) -> *mut BlockHeader {
    debug_assert!(offs > 0);
    // SAFETY: `bl` is live (this function's contract).
    let prev = unsafe { BlockHeader::prev(bl) };
    // SAFETY: `bl` is live, attached to a live chain (this function's contract).
    unsafe { BlockHeader::unlink(bl) };
    // SAFETY: `bl` is live; `offs` stays within its own span (this function's
    // contract), so the shifted position is still valid memory this call owns.
    let shifted = unsafe { bl.cast::<u8>().byte_add(offs) };
    // ALIGN: `bl` is 8-aligned; every alignment-offset call site in this module only
    // ever shifts by a multiple of `size_of::<BlockHeader>()` (see `split_block`'s
    // contract doc for why every block's `mem()` is always `BlockHeader`-aligned, the
    // same reasoning applies to shift offsets, which are alignment gaps between two
    // such positions).
    #[allow(clippy::cast_ptr_alignment)]
    let bl = shifted.cast::<BlockHeader>();
    // SAFETY: `bl` (the shifted position) is live (this function's contract); `prev`
    // is live (was `bl`'s own predecessor before the unlink above, unaffected by it).
    unsafe { BlockHeader::link_after(bl, prev) };
    // SAFETY: `bl` is live.
    unsafe { BlockHeader::set_unused(bl) };
    bl
}

/// The large-allocation path's state: the free-block index (a size-keyed tree for
/// blocks bigger than [`MAX_SMALL_ALLOCATION`], a plain list for smaller ones), the
/// most-recently-freed-block fast-path cache, and the running allocated-byte total.
/// Ports the tree-related slice of `allocator` (`mMRFreeBlock`, `mFreeTree`,
/// `mSmallFreeList`, `mTotalAllocatedSizeTree`, and the free `tree_*` methods).
///
/// # Invariants
/// - Every currently-free block is indexed in exactly one place: `mr_free_block`, or
///   `free_tree` (size `>` [`MAX_SMALL_ALLOCATION`]), or `small_free_list` (size `<=`
///   [`MAX_SMALL_ALLOCATION`]) — never more than one, and never none while unused.
///   [`Tree::attach`]/[`Tree::detach`] are the only crossing points between these three.
/// - No two physically-adjacent blocks are ever both free: every path that frees or
///   splits a block runs it through [`coalesce_block`] first, so a free block's
///   `prev()`/`next()` are always themselves either used or a fence.
/// - `allocated_bytes` is exactly the sum of `size` arguments passed to
///   [`Tree::system_alloc`] minus those passed to [`Tree::system_free`] — the total
///   bytes this `Tree` currently has mapped from the OS.
#[allow(clippy::struct_field_names)]
// `free_tree` ending in the struct's own name ("Tree") is the clearest name
// available for "the tree of free blocks" specifically (as opposed to
// `small_free_list`, `mr_free_block` — the other two free-block stores this type
// owns); renaming it to satisfy the lint would make the three less parallel, not more
// readable.
pub(crate) struct Tree {
    /// The single most recently freed block, checked before searching the tree/list
    /// at all — HPHA's fast path for "free, then immediately reallocate a similar
    /// size." Never itself a member of `free_tree`/`small_free_list`; a plain
    /// pointer, not part of any self-referential structure, so (unlike the
    /// list/tree sentinels) a bare `Cell` needs no `UnsafeCell`-lazy-init treatment
    /// — see `list.rs`'s `IntrusiveList` doc for that contrast.
    mr_free_block: Cell<Option<NonNull<BlockHeader>>>,
    /// Free blocks bigger than [`MAX_SMALL_ALLOCATION`], keyed by size.
    free_tree: IntrusiveMultiRbTree<FreeNode>,
    /// Free blocks at most [`MAX_SMALL_ALLOCATION`] — never queried by size, so a
    /// plain list is cheaper than tree bookkeeping for them.
    small_free_list: IntrusiveList<SmallFreeNode>,
    /// Total bytes currently mapped for the tree path (whole `PAGE_SIZE`-multiple
    /// arenas, fences included).
    allocated_bytes: Cell<usize>,
}

impl Tree {
    #[must_use]
    pub(crate) const fn new() -> Self {
        Self {
            mr_free_block: Cell::new(None),
            free_tree: IntrusiveMultiRbTree::new(),
            small_free_list: IntrusiveList::new(),
            allocated_bytes: Cell::new(0),
        }
    }

    /// Total bytes currently claimed from the OS by the tree path. Ports the tree
    /// half of `allocator::allocated`.
    #[must_use]
    pub(crate) fn allocated(&self) -> usize {
        self.allocated_bytes.get()
    }

    /// Coalesces `bl` (which must currently be unused) with either physical neighbour
    /// that is also free, detaching any neighbour absorbed this way from whichever
    /// index it was in. Returns the (possibly different) block header now
    /// representing the merged span. Ports `allocator::coalesce_block`.
    ///
    /// # Safety
    /// `bl` must be live, unused, and attached to a live physical chain.
    #[must_use]
    unsafe fn coalesce_block(&self, bl: *mut BlockHeader) -> *mut BlockHeader {
        // SAFETY: `bl` is live (this function's contract).
        debug_assert!(!unsafe { BlockHeader::used(bl) });
        // SAFETY: `bl` is live.
        let next = unsafe { BlockHeader::next(bl) };
        // SAFETY: `next` is live (this function's contract: `bl` attached to a live chain).
        if !unsafe { BlockHeader::used(next) } {
            // SAFETY: `next` is live and unused, hence currently indexed (in the
            // tree, the small list, or the MR cache) — a live free block always is.
            let next = unsafe { NonNull::new_unchecked(next) };
            self.detach(next);
            // SAFETY: `next` is live.
            unsafe { BlockHeader::unlink(next.as_ptr()) };
        }
        // SAFETY: `bl` is live.
        let prev = unsafe { BlockHeader::prev(bl) };
        let mut bl = bl;
        // SAFETY: `prev` is live (this function's contract).
        if !unsafe { BlockHeader::used(prev) } {
            // SAFETY: `prev` is live and unused, hence currently indexed (same
            // reasoning as `next` above).
            let prev_nn = unsafe { NonNull::new_unchecked(prev) };
            self.detach(prev_nn);
            // SAFETY: `bl` is live.
            unsafe { BlockHeader::unlink(bl) };
            bl = prev;
        }
        bl
    }

    /// Maps `size` bytes (a multiple of `os::PAGE_SIZE`) for the tree arena. Ports
    /// `allocator::tree_system_alloc`.
    #[must_use]
    fn system_alloc(&self, size: usize) -> Option<NonNull<u8>> {
        debug_assert_eq!(size % os::PAGE_SIZE, 0);
        let ptr = os::map(size)?;
        self.allocated_bytes.set(self.allocated_bytes.get() + size);
        Some(ptr)
    }

    /// Returns a tree arena mapping to the OS. Ports `allocator::tree_system_free`.
    ///
    /// # Safety
    /// `ptr`/`size` must be a still-live result of [`Tree::system_alloc`] on `self`.
    unsafe fn system_free(&self, ptr: NonNull<u8>, size: usize) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { os::unmap(ptr, size) };
        self.allocated_bytes.set(self.allocated_bytes.get() - size);
    }

    /// Lays out a freshly-mapped `size`-byte arena as two fence blocks bracketing one
    /// large free block, then coalesces (a no-op here, since both neighbours are
    /// fences and therefore `used`, but kept for fidelity — see the module doc).
    /// Ports `allocator::tree_add_block`.
    ///
    /// # Safety
    /// `mem` must be live, exclusively owned, for exactly `size` bytes, `size` a
    /// multiple of `size_of::<BlockHeader>()` and at least `3 * size_of::<BlockHeader>()`.
    #[must_use]
    unsafe fn add_block(&self, mem: NonNull<u8>, size: usize) -> *mut BlockHeader {
        debug_assert_eq!(size % size_of::<BlockHeader>(), 0);
        debug_assert!(size >= 3 * size_of::<BlockHeader>());
        // ALIGN: `mem` is `os::map`'s result, PAGE_SIZE-aligned, hence 8-aligned.
        #[allow(clippy::cast_ptr_alignment)]
        let fence0 = mem.as_ptr().cast::<BlockHeader>();
        // SAFETY: `fence0` is live (this function's contract: `mem` valid for `size`
        // bytes, at least one `BlockHeader` of which this is); writes one field via
        // each of the three calls below.
        unsafe { BlockHeader::set_prev(fence0, core::ptr::null_mut()) };
        // SAFETY: `fence0` is live.
        unsafe { BlockHeader::set_size(fence0, 0) };
        // SAFETY: `fence0` is live.
        unsafe { BlockHeader::set_used(fence0) };

        // SAFETY: `fence0` is live.
        let real_front = unsafe { BlockHeader::mem(fence0) };
        // ALIGN: `fence0` is 8-aligned; `BlockHeader::mem` adds `size_of::<BlockHeader>()`
        // (a multiple of 8), so `real_front` stays 8-aligned.
        #[allow(clippy::cast_ptr_alignment)]
        let real_front = real_front.cast::<BlockHeader>();
        // SAFETY: `real_front` is within `mem`'s own span (this function's
        // size-precondition guarantees at least `3 * size_of::<BlockHeader>()` bytes,
        // and `real_front` is only `size_of::<BlockHeader>()` in).
        unsafe { BlockHeader::set_prev(real_front, fence0) };
        // SAFETY: `real_front` is live.
        unsafe { BlockHeader::set_size(real_front, 0) };
        // SAFETY: `real_front` is live.
        unsafe { BlockHeader::set_used(real_front) };

        // SAFETY: `mem` is valid for `size` bytes (this function's contract);
        // `size - size_of::<BlockHeader>()` stays within that range (`size` is at
        // least `3 * size_of::<BlockHeader>()`, this function's contract).
        let end_fence = unsafe { mem.as_ptr().byte_add(size - size_of::<BlockHeader>()) };
        // ALIGN: `mem` is 8-aligned; `size` and `size_of::<BlockHeader>()` are both
        // multiples of 8, so `end_fence` stays 8-aligned.
        #[allow(clippy::cast_ptr_alignment)]
        let end_fence = end_fence.cast::<BlockHeader>();
        // SAFETY: `end_fence` is within `mem`'s own span (established above).
        unsafe { BlockHeader::set_size(end_fence, 0) };
        // SAFETY: `end_fence` is live.
        unsafe { BlockHeader::set_used(end_fence) };

        // SAFETY: `real_front` is live.
        unsafe { BlockHeader::set_unused(real_front) };
        // SAFETY: `real_front` is live; `end_fence` is at/after `real_front.mem()`
        // (`real_front` is the second `BlockHeader`-sized slot in `mem`, `end_fence`
        // the last, and `size >= 3 * size_of::<BlockHeader>()`).
        unsafe { BlockHeader::set_next(real_front, end_fence) };
        // SAFETY: `end_fence` is live.
        unsafe { BlockHeader::set_prev(end_fence, real_front) };

        // SAFETY: `real_front` is live, unused (just set above), and attached to the
        // live chain just built (fence0 <-> real_front <-> end_fence).
        unsafe { self.coalesce_block(real_front) }
    }

    /// Maps a fresh arena sized to comfortably fit one `size`-byte block (`size`
    /// already the exact block payload size being requested, header excluded), lays
    /// it out via [`Tree::add_block`]. Ports `allocator::tree_grow`.
    #[must_use]
    fn grow(&self, size: usize) -> Option<*mut BlockHeader> {
        let size = size + 3 * size_of::<BlockHeader>(); // two fences plus one fake
        let size = round_up(size, os::PAGE_SIZE);
        let mem = self.system_alloc(size)?;
        // SAFETY: `mem` is live, exclusively owned, for exactly `size` bytes
        // (`system_alloc`'s own guarantee); `size` is a multiple of `os::PAGE_SIZE`
        // (just rounded up to it), hence of `size_of::<BlockHeader>()` (`PAGE_SIZE`
        // is 65536, a multiple of 16), and at least `3 * size_of::<BlockHeader>()`
        // (rounded up from a value that already included that much).
        Some(unsafe { self.add_block(mem, size) })
    }

    /// Extracts a free block of at least `size` bytes: the MR-cached block if it
    /// fits, otherwise the smallest fitting block in the tree (walking one step to an
    /// equal-key chain neighbour first when possible, since removing a plain chain
    /// link is cheaper than removing a tree-attached node). Ports
    /// `allocator::tree_extract`.
    #[must_use]
    fn extract(&self, size: usize) -> Option<*mut BlockHeader> {
        if let Some(best) = self.mr_free_block.get() {
            // SAFETY: `best` is live (the MR cache only ever holds a live free block).
            if unsafe { BlockHeader::size(best.as_ptr()) } >= size {
                self.detach(best);
                return Some(best.as_ptr());
            }
        }
        let best_node = self.free_tree.lower_bound(&size)?;
        // Improves removal time: an equal-key chain link is O(1) to remove, while the
        // tree-attached representative needs a full erase_fixup.
        let best_node = rbtree::next(best_node);
        // SAFETY: `best_node` is live (just returned by the tree above).
        let best_block = unsafe { FreeNode::get_block(best_node.as_ptr()) };
        // SAFETY: `best_block` is live.
        let best_block = unsafe { NonNull::new_unchecked(best_block) };
        self.detach(best_block);
        Some(best_block.as_ptr())
    }

    /// Extracts a free block of at least `size` bytes whose `mem()` can be aligned to
    /// `alignment` without more than `size` bytes of slack. Same MR-cache-first,
    /// chain-neighbour-preferred strategy as [`Tree::extract`], but must additionally
    /// walk candidates in `[size, size + alignment)` since a merely-big-enough block
    /// might not leave room for the alignment padding. Ports
    /// `allocator::tree_extract_aligned`.
    #[must_use]
    fn extract_aligned(&self, size: usize, alignment: usize) -> Option<*mut BlockHeader> {
        if let Some(best) = self.mr_free_block.get() {
            // SAFETY: `best` is live.
            let mem = unsafe { BlockHeader::mem(best.as_ptr()) };
            let alignment_offs = crate::align::align_up(mem, alignment).addr() - mem.addr();
            // SAFETY: `best` is live.
            if unsafe { BlockHeader::size(best.as_ptr()) } >= size + alignment_offs {
                self.detach(best);
                return Some(best.as_ptr());
            }
        }
        let size_upper = size + alignment;
        // `cur`/`last_node` are `Option`-typed throughout (rather than `best_node`
        // alone as in HPHA's C++, which has a real sentinel `end()` sentinel value to
        // compare pointers against): `None` here is exactly that sentinel. Every
        // comparison and advance below mirrors the C++ `while (bestNode != lastNode)`
        // loop's *shape* precisely, including which node's fit is (and is not)
        // checked, which is why this can't be simplified to iterator adapters.
        let mut cur = self.free_tree.lower_bound(&size);
        let last_node = self.free_tree.upper_bound(&size_upper);
        // EXPLICIT: walks the `[size, size_upper)` candidate sequence looking for one
        // with enough room for both the payload and the alignment padding; `cur` is
        // the state, not expressible as an iterator over a tree-order walk.
        // A `cur == None` exit (checked by `while let` below) means we walked past
        // the maximum node without reaching `last_node` — only happens when
        // `last_node` is itself `None` (nothing in the tree is as large as
        // `size_upper`), matching HPHA's `bestNode == end()`.
        while let Some(node) = cur {
            if cur == last_node {
                // Reached the upper bound without finding a fit; `last_node` itself
                // is never fit-checked (mirrors the C++ `while` condition being
                // checked *before* the loop body).
                break;
            }
            let addr = node.addr().get();
            let alignment_offs = round_up(addr, alignment) - addr;
            // SAFETY: `node` is live (a tree-order walk between two live bounds).
            let block = unsafe { FreeNode::get_block(node.as_ptr()) };
            // SAFETY: `block` is live.
            if unsafe { BlockHeader::size(block) } >= size + alignment_offs {
                break;
            }
            cur = self.free_tree.succ(node);
        }
        let best_node = cur?;
        // Improves removal time, same reasoning as `extract` — but only applies when
        // we stopped *at* `last_node` (no fit found in range); a genuine fit found
        // strictly before it is used as-is.
        let best_node = if cur == last_node {
            rbtree::next(best_node)
        } else {
            best_node
        };
        // SAFETY: `best_node` is live.
        let best_block = unsafe { FreeNode::get_block(best_node.as_ptr()) };
        // SAFETY: `best_block` is live.
        let best_block = unsafe { NonNull::new_unchecked(best_block) };
        self.detach(best_block);
        Some(best_block.as_ptr())
    }

    /// Indexes `bl` as free: the previous MR-cached block (if any) is pushed into the
    /// tree or small list first, then `bl` becomes the new MR-cached block. Ports
    /// `allocator::tree_attach`.
    ///
    /// # Safety
    /// `bl` must be live and unused, or `None` (used by [`Tree::purge`] to flush the
    /// MR cache without installing a new block).
    unsafe fn attach(&self, bl: Option<NonNull<BlockHeader>>) {
        if let Some(last) = self.mr_free_block.get() {
            // SAFETY: `last` is live (the MR cache only ever holds a live free block).
            let size = unsafe { BlockHeader::size(last.as_ptr()) };
            // SAFETY: `last` is live; its `mem()` is exactly where it was indexed
            // from on a prior `attach` (this same invariant, inductively) or is
            // fresh free space at least `MIN_BLOCK_SIZE` bytes (every block this
            // module creates is normalized to at least that), so a `FreeNode`/
            // `SmallFreeNode` fits.
            let mem = unsafe { BlockHeader::mem(last.as_ptr()) };
            if size > MAX_SMALL_ALLOCATION {
                // ALIGN: `mem` is `size_of::<BlockHeader>()`-aligned (every block's
                // `mem()` is, per `split_block`'s contract doc), hence 8-aligned —
                // matches `FreeNode`'s alignment (its only field is `NodeBase`, align 8).
                #[allow(clippy::cast_ptr_alignment)]
                let node = mem.cast::<FreeNode>();
                // SAFETY: `node` derives from `last`'s own address (a live,
                // non-null `NonNull<BlockHeader>`) by a small positive offset
                // (`size_of::<BlockHeader>()`), which cannot wrap around to null.
                let node = unsafe { NonNull::new_unchecked(node) };
                self.free_tree.insert(node);
            } else {
                // ALIGN: same reasoning as the `FreeNode` cast above; `SmallFreeNode`
                // is likewise align-8 (its only field is `ListLink`, align 8).
                #[allow(clippy::cast_ptr_alignment)]
                let node = mem.cast::<SmallFreeNode>();
                // SAFETY: same non-null reasoning as the `FreeNode` case above.
                let node = unsafe { NonNull::new_unchecked(node) };
                self.small_free_list.push_back(node);
            }
        }
        self.mr_free_block.set(bl);
    }

    /// Removes `bl` from wherever it is currently indexed (the MR cache, the tree, or
    /// the small list). Ports `allocator::tree_detach`.
    fn detach(&self, bl: NonNull<BlockHeader>) {
        if self.mr_free_block.get() == Some(bl) {
            self.mr_free_block.set(None);
            return;
        }
        // SAFETY: `bl` is live (caller-supplied, currently indexed by this function's
        // own contract); reads one field's worth of state via `size`/`mem`.
        let size = unsafe { BlockHeader::size(bl.as_ptr()) };
        // SAFETY: `bl` is live.
        let mem = unsafe { BlockHeader::mem(bl.as_ptr()) };
        if size > MAX_SMALL_ALLOCATION {
            // ALIGN: see `attach`'s identical cast for why this is 8-aligned.
            #[allow(clippy::cast_ptr_alignment)]
            let node = mem.cast::<FreeNode>();
            // SAFETY: `node` derives from `bl`'s own address (a live, non-null
            // `NonNull<BlockHeader>`) by a small positive offset, which cannot wrap
            // around to null.
            let node = unsafe { NonNull::new_unchecked(node) };
            self.free_tree.erase(node);
        } else {
            // ALIGN: see `attach`'s identical cast for why this is 8-aligned.
            #[allow(clippy::cast_ptr_alignment)]
            let node = mem.cast::<SmallFreeNode>();
            // SAFETY: same non-null reasoning as the `FreeNode` case above.
            let node = unsafe { NonNull::new_unchecked(node) };
            list::unlink_node(node);
        }
    }

    /// Allocates `size` bytes on the tree path. Ports `allocator::tree_alloc`.
    #[must_use]
    pub(crate) fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
        let size = normalize_size(size)?;
        let new_bl = match self.extract(size) {
            Some(bl) => bl,
            None => self.grow(size)?,
        };
        // SAFETY: `new_bl` is live (from `extract`/`grow`, both return live blocks).
        let new_bl_size = unsafe { BlockHeader::size(new_bl) };
        debug_assert!(new_bl_size >= size);
        if new_bl_size >= size + SPLIT_REMAINDER_MIN {
            // SAFETY: `new_bl` is live; the size check above establishes this
            // function's own precondition.
            unsafe { split_block(new_bl, size) };
            // SAFETY: `new_bl` is live.
            let remainder = unsafe { BlockHeader::next(new_bl) };
            // SAFETY: `remainder` is live (just split off above), unused (`split_block`
            // marks it so).
            let remainder = unsafe { NonNull::new_unchecked(remainder) };
            // SAFETY: forwarded — `remainder` is live and unused.
            unsafe { self.attach(Some(remainder)) };
        }
        // SAFETY: `new_bl` is live.
        unsafe { BlockHeader::set_used(new_bl) };
        // SAFETY: `new_bl` is live.
        let mem = unsafe { BlockHeader::mem(new_bl) };
        // SAFETY: `mem` derives from `new_bl` (a live, non-null pointer) by a small
        // positive offset, which cannot wrap around to null.
        Some(unsafe { NonNull::new_unchecked(mem) })
    }

    /// Allocates `size` bytes on the tree path, aligned to `alignment`. Ports
    /// `allocator::tree_alloc_aligned`.
    #[must_use]
    pub(crate) fn alloc_aligned(&self, size: usize, alignment: usize) -> Option<NonNull<u8>> {
        let size = normalize_size(size)?;
        // The aligned path adds `alignment` on top of the normalized size — in
        // `extract_aligned`'s `size + alignment` upper bound and in `grow`'s own
        // `size + alignment` below — so it needs that much more headroom than
        // `normalize_size` alone guarantees. Checked here rather than at each `+`,
        // for the same reason and with the same rationale as `MAX_ALLOCATION` itself.
        if alignment > MAX_ALLOCATION || size > MAX_ALLOCATION - alignment {
            return None;
        }
        let mut new_bl = match self.extract_aligned(size, alignment) {
            Some(bl) => bl,
            None => self.grow(size + alignment)?,
        };
        // SAFETY: `new_bl` is live.
        let new_bl_size = unsafe { BlockHeader::size(new_bl) };
        debug_assert!(new_bl_size >= size);
        // SAFETY: `new_bl` is live.
        let mem = unsafe { BlockHeader::mem(new_bl) };
        let alignment_offs = crate::align::align_up(mem, alignment).addr() - mem.addr();
        debug_assert!(new_bl_size >= size + alignment_offs);
        if alignment_offs >= SPLIT_REMAINDER_MIN {
            // SAFETY: `new_bl` is live; `alignment_offs - size_of::<BlockHeader>()`
            // is the padding block's payload size, a multiple of
            // `size_of::<BlockHeader>()` (see `split_block`'s contract doc: every
            // block's `mem()`, hence every alignment offset between two such
            // positions, is a `size_of::<BlockHeader>()` multiple), and this branch's
            // own `>= SPLIT_REMAINDER_MIN` check is exactly `split_block`'s size
            // precondition applied to that padding block.
            unsafe { split_block(new_bl, alignment_offs - size_of::<BlockHeader>()) };
            // SAFETY: `new_bl` is live and unused (still its pre-extraction state;
            // `extract_aligned` never marks it used).
            let new_bl_nn = unsafe { NonNull::new_unchecked(new_bl) };
            // SAFETY: forwarded — `new_bl` is live and unused.
            unsafe { self.attach(Some(new_bl_nn)) };
            // SAFETY: `new_bl` is live.
            new_bl = unsafe { BlockHeader::next(new_bl) };
        } else if alignment_offs > 0 {
            // SAFETY: `new_bl` is live and attached to a live physical chain (from
            // `extract_aligned`/`grow`, both return blocks freshly spliced into a
            // real chain); `alignment_offs` is a `size_of::<BlockHeader>()` multiple
            // (same reasoning as above) and within `new_bl`'s own span (the
            // `>= size + alignment_offs` check above).
            new_bl = unsafe { shift_block(new_bl, alignment_offs) };
        }
        // SAFETY: `new_bl` is live.
        if unsafe { BlockHeader::size(new_bl) } >= size + SPLIT_REMAINDER_MIN {
            // SAFETY: `new_bl` is live; the size check above establishes
            // `split_block`'s precondition.
            unsafe { split_block(new_bl, size) };
            // SAFETY: `new_bl` is live.
            let remainder = unsafe { BlockHeader::next(new_bl) };
            // SAFETY: `remainder` is live and unused (just split off).
            let remainder = unsafe { NonNull::new_unchecked(remainder) };
            // SAFETY: forwarded.
            unsafe { self.attach(Some(remainder)) };
        }
        // SAFETY: `new_bl` is live.
        unsafe { BlockHeader::set_used(new_bl) };
        // SAFETY: `new_bl` is live.
        let mem = unsafe { BlockHeader::mem(new_bl) };
        debug_assert_eq!(mem.addr() % alignment, 0);
        // SAFETY: `mem` derives from `new_bl` (a live, non-null pointer) by a small
        // positive offset, which cannot wrap around to null.
        Some(unsafe { NonNull::new_unchecked(mem) })
    }

    /// Grows or shrinks `ptr` in place when a physical neighbour can absorb the
    /// difference, otherwise falls back to allocate/copy/free. Ports
    /// `allocator::tree_realloc`.
    ///
    /// # Safety
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    #[must_use]
    pub(crate) unsafe fn realloc(&self, ptr: NonNull<u8>, size: usize) -> Option<NonNull<u8>> {
        let size = normalize_size(size)?;
        // SAFETY: forwarded from this function's own contract.
        let bl = unsafe { block::ptr_get_block_header(ptr.as_ptr()) };
        // SAFETY: `bl` is live.
        let bl_size = unsafe { BlockHeader::size(bl) };
        if bl_size >= size {
            if bl_size >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; the size check above establishes
                // `split_block`'s precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let next = unsafe { BlockHeader::next(bl) };
                // SAFETY: `next` is live (just split off above) and unused
                // (`split_block` marks it so), attached to a live chain.
                let next = unsafe { self.coalesce_block(next) };
                // SAFETY: `next` is live and unused (either the just-split block, or
                // that merged with a free neighbour by `coalesce_block`, still unused
                // either way).
                let next = unsafe { NonNull::new_unchecked(next) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(next)) };
            }
            return Some(ptr);
        }
        // SAFETY: `bl` is live.
        let next = unsafe { BlockHeader::next(bl) };
        // SAFETY: `next` is live (`bl` attached to a live chain, this function's contract).
        let next_used = unsafe { BlockHeader::used(next) };
        let next_size = if next_used {
            0
        } else {
            // SAFETY: `next` is live.
            unsafe { BlockHeader::size(next) + size_of::<BlockHeader>() }
        };
        if bl_size + next_size >= size {
            debug_assert!(!next_used);
            // SAFETY: `next` is live and unused (currently indexed, per this
            // branch's `!next_used` invariant).
            let next_nn = unsafe { NonNull::new_unchecked(next) };
            self.detach(next_nn);
            // SAFETY: `next` is live.
            unsafe { BlockHeader::unlink(next) };
            // SAFETY: `bl` is live.
            let bl_size_now = unsafe { BlockHeader::size(bl) };
            debug_assert!(bl_size_now >= size);
            if bl_size_now >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let remainder = unsafe { BlockHeader::next(bl) };
                // SAFETY: `remainder` is live and unused (just split off).
                let remainder = unsafe { NonNull::new_unchecked(remainder) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(remainder)) };
            }
            return Some(ptr);
        }
        // SAFETY: `bl` is live.
        let prev = unsafe { BlockHeader::prev(bl) };
        // SAFETY: `prev` is live (`bl` attached to a live chain).
        let prev_used = unsafe { BlockHeader::used(prev) };
        let prev_size = if prev_used {
            0
        } else {
            // SAFETY: `prev` is live.
            unsafe { BlockHeader::size(prev) + size_of::<BlockHeader>() }
        };
        if bl_size + prev_size + next_size >= size {
            debug_assert!(!prev_used);
            // SAFETY: `prev` is live and unused (this branch's `!prev_used` invariant).
            let prev_nn = unsafe { NonNull::new_unchecked(prev) };
            self.detach(prev_nn);
            // SAFETY: `bl` is live.
            unsafe { BlockHeader::unlink(bl) };
            if !next_used {
                // SAFETY: `next` is live and unused.
                let next_nn = unsafe { NonNull::new_unchecked(next) };
                self.detach(next_nn);
                // SAFETY: `next` is live.
                unsafe { BlockHeader::unlink(next) };
            }
            let bl = prev;
            // SAFETY: `bl` is live.
            unsafe { BlockHeader::set_used(bl) };
            // SAFETY: `bl` is live.
            let bl_size_now = unsafe { BlockHeader::size(bl) };
            debug_assert!(bl_size_now >= size);
            // SAFETY: `bl` is live.
            let new_ptr = unsafe { BlockHeader::mem(bl) };
            // SAFETY: `ptr` is valid for `bl_size` bytes (its own pre-move size,
            // this function's own contract that it was a live allocation); `new_ptr`
            // is `bl`'s own fresh payload start, with room for at least `bl_size`
            // bytes (`bl`'s new size is `>= size > bl_size`); the two ranges may
            // overlap (this is exactly a block growing backwards over its own
            // former self), hence `memmove`-style overlap-safe copying.
            unsafe { new_ptr.copy_from(ptr.as_ptr(), bl_size) };
            // SAFETY: `bl` is live.
            if unsafe { BlockHeader::size(bl) } >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let remainder = unsafe { BlockHeader::next(bl) };
                // SAFETY: `remainder` is live and unused.
                let remainder = unsafe { NonNull::new_unchecked(remainder) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(remainder)) };
            }
            // SAFETY: `new_ptr` derives from `bl` (a live, non-null pointer) by a
            // small positive offset, which cannot wrap around to null.
            return Some(unsafe { NonNull::new_unchecked(new_ptr) });
        }
        // Fall back: no physical neighbour can absorb the growth; allocate fresh,
        // copy, free the old block.
        let new_ptr = self.alloc(size)?;
        // SAFETY: `new_ptr` was just allocated with room for at least `size > bl_size`
        // bytes; `ptr` is valid for `bl_size` bytes (this function's own contract);
        // the two allocations never overlap (freshly, independently allocated).
        unsafe {
            new_ptr
                .as_ptr()
                .copy_from_nonoverlapping(ptr.as_ptr(), bl_size);
        };
        // SAFETY: `ptr` is a live tree-path allocation this instance produced (this
        // function's contract), not used again after this call.
        unsafe { self.free(ptr) };
        Some(new_ptr)
    }

    /// Grows or shrinks `ptr` in place, aligned to `alignment`, otherwise falls back
    /// to allocate/copy/free. Ports `allocator::tree_realloc_aligned`.
    ///
    /// # Safety
    /// `ptr` must be a still-live tree-path allocation this instance produced, itself
    /// already aligned to `alignment`.
    #[must_use]
    pub(crate) unsafe fn realloc_aligned(
        &self,
        ptr: NonNull<u8>,
        size: usize,
        alignment: usize,
    ) -> Option<NonNull<u8>> {
        debug_assert_eq!(ptr.addr().get() % alignment, 0);
        let size = normalize_size(size)?;
        // Same headroom requirement as `alloc_aligned`, which this falls back to.
        if alignment > MAX_ALLOCATION || size > MAX_ALLOCATION - alignment {
            return None;
        }
        // SAFETY: forwarded from this function's own contract.
        let bl = unsafe { block::ptr_get_block_header(ptr.as_ptr()) };
        // SAFETY: `bl` is live.
        let bl_size = unsafe { BlockHeader::size(bl) };
        if bl_size >= size {
            if bl_size >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let next = unsafe { BlockHeader::next(bl) };
                // SAFETY: `next` is live and unused, attached to a live chain.
                let next = unsafe { self.coalesce_block(next) };
                // SAFETY: `next` is live and unused.
                let next = unsafe { NonNull::new_unchecked(next) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(next)) };
            }
            return Some(ptr);
        }
        // SAFETY: `bl` is live.
        let next = unsafe { BlockHeader::next(bl) };
        // SAFETY: `next` is live.
        let next_used = unsafe { BlockHeader::used(next) };
        let next_size = if next_used {
            0
        } else {
            // SAFETY: `next` is live.
            unsafe { BlockHeader::size(next) + size_of::<BlockHeader>() }
        };
        if bl_size + next_size >= size {
            debug_assert!(!next_used);
            // SAFETY: `next` is live and unused.
            let next_nn = unsafe { NonNull::new_unchecked(next) };
            self.detach(next_nn);
            // SAFETY: `next` is live.
            unsafe { BlockHeader::unlink(next) };
            // SAFETY: `bl` is live.
            let bl_size_now = unsafe { BlockHeader::size(bl) };
            debug_assert!(bl_size_now >= size);
            if bl_size_now >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let remainder = unsafe { BlockHeader::next(bl) };
                // SAFETY: `remainder` is live and unused.
                let remainder = unsafe { NonNull::new_unchecked(remainder) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(remainder)) };
            }
            return Some(ptr);
        }
        // SAFETY: `bl` is live.
        let prev = unsafe { BlockHeader::prev(bl) };
        // SAFETY: `prev` is live.
        let prev_used = unsafe { BlockHeader::used(prev) };
        let prev_size = if prev_used {
            0
        } else {
            // SAFETY: `prev` is live.
            unsafe { BlockHeader::size(prev) + size_of::<BlockHeader>() }
        };
        let alignment_offs = if prev_used {
            0
        } else {
            // SAFETY: `prev` is live.
            let prev_mem = unsafe { BlockHeader::mem(prev) };
            crate::align::align_up(prev_mem, alignment).addr() - prev_mem.addr()
        };
        if bl_size + prev_size + next_size >= size + alignment_offs {
            debug_assert!(!prev_used);
            // SAFETY: `prev` is live and unused.
            let prev_nn = unsafe { NonNull::new_unchecked(prev) };
            self.detach(prev_nn);
            // SAFETY: `bl` is live.
            unsafe { BlockHeader::unlink(bl) };
            if !next_used {
                // SAFETY: `next` is live and unused.
                let next_nn = unsafe { NonNull::new_unchecked(next) };
                self.detach(next_nn);
                // SAFETY: `next` is live.
                unsafe { BlockHeader::unlink(next) };
            }
            let mut prev = prev;
            if alignment_offs >= SPLIT_REMAINDER_MIN {
                // SAFETY: `prev` is live; `alignment_offs - size_of::<BlockHeader>()`
                // is a `size_of::<BlockHeader>()` multiple (same reasoning as
                // `alloc_aligned`), and this branch's own check establishes
                // `split_block`'s size precondition.
                unsafe { split_block(prev, alignment_offs - size_of::<BlockHeader>()) };
                // SAFETY: `prev` is live and unused (unlinked from its index above,
                // not yet re-attached).
                let prev_nn = unsafe { NonNull::new_unchecked(prev) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(prev_nn)) };
                // SAFETY: `prev` is live.
                prev = unsafe { BlockHeader::next(prev) };
            } else if alignment_offs > 0 {
                // SAFETY: `prev` is live, attached to a live chain (it was just
                // unlinked and is about to be relinked by the surrounding logic —
                // more precisely, at this point `prev` is temporarily detached from
                // the physical chain along with `bl`/`next`; `shift_block` itself
                // only needs `prev`'s *own* prev/next fields to still be live, which
                // they are, since only `prev` itself was unlinked, not its neighbours).
                prev = unsafe { shift_block(prev, alignment_offs) };
            }
            let bl = prev;
            // SAFETY: `bl` is live.
            unsafe { BlockHeader::set_used(bl) };
            // SAFETY: `bl` is live.
            let bl_size_now = unsafe { BlockHeader::size(bl) };
            debug_assert!(bl_size_now >= size);
            // SAFETY: `bl` is live.
            let new_ptr = unsafe { BlockHeader::mem(bl) };
            debug_assert_eq!(new_ptr.addr() % alignment, 0);
            // SAFETY: `ptr` is valid for `bl_size` bytes; `new_ptr` has room for at
            // least `bl_size` bytes; the ranges may overlap (growing in place).
            unsafe { new_ptr.copy_from(ptr.as_ptr(), bl_size) };
            if bl_size_now >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let remainder = unsafe { BlockHeader::next(bl) };
                // SAFETY: `remainder` is live and unused.
                let remainder = unsafe { NonNull::new_unchecked(remainder) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(remainder)) };
            }
            // SAFETY: `new_ptr` derives from `bl` (a live, non-null pointer) by a
            // small positive offset, which cannot wrap around to null.
            return Some(unsafe { NonNull::new_unchecked(new_ptr) });
        }
        let new_ptr = self.alloc_aligned(size, alignment)?;
        // SAFETY: `new_ptr` was just allocated with room for at least `bl_size`
        // bytes; `ptr` is valid for `bl_size` bytes; freshly, independently
        // allocated, so never overlapping.
        unsafe {
            new_ptr
                .as_ptr()
                .copy_from_nonoverlapping(ptr.as_ptr(), bl_size);
        };
        // SAFETY: `ptr` is a live tree-path allocation this instance produced (this
        // function's contract), not used again after this call.
        unsafe { self.free(ptr) };
        Some(new_ptr)
    }

    /// Grows `ptr` in place if a following free block can absorb the difference,
    /// without moving it; returns the resulting size either way (the block's own
    /// size if it couldn't grow enough). Ports `allocator::tree_resize`.
    ///
    /// # Safety
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    #[must_use]
    pub(crate) unsafe fn resize(&self, ptr: NonNull<u8>, size: usize) -> usize {
        // SAFETY: forwarded from this function's own contract.
        let bl = unsafe { block::ptr_get_block_header(ptr.as_ptr()) };
        let Some(size) = normalize_size(size) else {
            // Past `MAX_ALLOCATION` (see its doc): no growth is possible, which is
            // exactly what this function already reports for any request it cannot
            // satisfy in place — the block keeps its current size, unmoved.
            // SAFETY: `bl` is live.
            return unsafe { BlockHeader::size(bl) };
        };
        // SAFETY: `bl` is live.
        let bl_size = unsafe { BlockHeader::size(bl) };
        if bl_size >= size {
            if bl_size >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; size check above establishes the precondition.
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let next = unsafe { BlockHeader::next(bl) };
                // SAFETY: `next` is live and unused, attached to a live chain.
                let next = unsafe { self.coalesce_block(next) };
                // SAFETY: `next` is live and unused.
                let next = unsafe { NonNull::new_unchecked(next) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(next)) };
            }
            // SAFETY: `bl` is live.
            return unsafe { BlockHeader::size(bl) };
        }
        // SAFETY: `bl` is live.
        let next = unsafe { BlockHeader::next(bl) };
        // SAFETY: `next` is live.
        let next_used = unsafe { BlockHeader::used(next) };
        // SAFETY: `next` is live.
        let next_size = unsafe { BlockHeader::size(next) };
        if !next_used && bl_size + next_size + size_of::<BlockHeader>() >= size {
            // SAFETY: `next` is live and unused (this branch's own `!next_used` check).
            let next_nn = unsafe { NonNull::new_unchecked(next) };
            self.detach(next_nn);
            // SAFETY: `next` is live.
            unsafe { BlockHeader::unlink(next) };
            // SAFETY: `bl` is live.
            if unsafe { BlockHeader::size(bl) } >= size + SPLIT_REMAINDER_MIN {
                // SAFETY: `bl` is live; the merged size, at least `size`, establishes
                // `split_block`'s precondition when it's also `>= size +
                // SPLIT_REMAINDER_MIN` (checked here).
                unsafe { split_block(bl, size) };
                // SAFETY: `bl` is live.
                let remainder = unsafe { BlockHeader::next(bl) };
                // SAFETY: `remainder` is live and unused.
                let remainder = unsafe { NonNull::new_unchecked(remainder) };
                // SAFETY: forwarded.
                unsafe { self.attach(Some(remainder)) };
            }
            // SAFETY: `bl` is live.
            let bl_size_now = unsafe { BlockHeader::size(bl) };
            debug_assert!(bl_size_now >= size);
        }
        // SAFETY: `bl` is live.
        unsafe { BlockHeader::size(bl) }
    }

    /// Frees `ptr`, coalescing with either physical neighbour that is also free.
    /// Ports `allocator::tree_free`.
    ///
    /// # Safety
    /// `ptr` must be a still-live tree-path allocation this instance produced.
    pub(crate) unsafe fn free(&self, ptr: NonNull<u8>) {
        // SAFETY: forwarded from this function's own contract.
        let bl = unsafe { block::ptr_get_block_header(ptr.as_ptr()) };
        // SAFETY: `bl` is live.
        unsafe { BlockHeader::set_unused(bl) };
        // SAFETY: `bl` is live and unused (just set above), attached to a live chain
        // (this function's contract: `ptr` was a live allocation).
        let bl = unsafe { self.coalesce_block(bl) };
        // SAFETY: `bl` is live and unused (either the original block, or that merged
        // with a free neighbour, still unused either way).
        let bl = unsafe { NonNull::new_unchecked(bl) };
        // SAFETY: forwarded.
        unsafe { self.attach(Some(bl)) };
    }

    /// Returns `bl`'s whole arena to the OS if `bl` is the arena's only content (its
    /// physical predecessor is the arena's opening fence, its successor the closing
    /// one). Ports `allocator::tree_purge_block`.
    ///
    /// # Safety
    /// `bl` must be live, unused, and attached to a live physical chain.
    unsafe fn purge_block(&self, bl: *mut BlockHeader) {
        // SAFETY: `bl` is live (this function's contract).
        debug_assert!(!unsafe { BlockHeader::used(bl) });
        // SAFETY: `bl` is live.
        let prev = unsafe { BlockHeader::prev(bl) };
        debug_assert!(!prev.is_null());
        // SAFETY: `prev` is live (this function's contract: `bl` attached to a live chain).
        debug_assert!(unsafe { BlockHeader::used(prev) });
        // SAFETY: `bl` is live.
        let next = unsafe { BlockHeader::next(bl) };
        debug_assert!(!next.is_null());
        // SAFETY: `next` is live.
        debug_assert!(unsafe { BlockHeader::used(next) });
        // SAFETY: `prev` is live.
        let prev_prev = unsafe { BlockHeader::prev(prev) };
        // SAFETY: `next` is live.
        let next_size = unsafe { BlockHeader::size(next) };
        if prev_prev.is_null() && next_size == 0 {
            // SAFETY: `bl` is live and currently indexed (unused, this function's contract).
            let bl_nn = unsafe { NonNull::new_unchecked(bl) };
            self.detach(bl_nn);
            let mem_start = prev.cast::<u8>();
            // SAFETY: `bl` is live; reads its own payload start.
            let bl_mem = unsafe { BlockHeader::mem(bl) };
            // SAFETY: `bl` is live; reads its own size.
            let bl_size = unsafe { BlockHeader::size(bl) };
            // SAFETY: `bl_mem` is live (`bl`'s own payload start, established above);
            // `bl_size` bytes past it stays within `bl`'s own span.
            let past_payload = unsafe { bl_mem.byte_add(bl_size) };
            // SAFETY: `past_payload` is exactly `next` (`bl.mem() + bl.size()` is
            // `BlockHeader::next(bl)` by definition), live (established above);
            // `size_of::<BlockHeader>()` bytes past it stays within `next`'s own span.
            let mem_end = unsafe { past_payload.byte_add(size_of::<BlockHeader>()) };
            let size = mem_end.addr() - mem_start.addr();
            debug_assert_eq!(mem_start.addr() % os::PAGE_SIZE, 0);
            debug_assert_eq!(size % os::PAGE_SIZE, 0);
            // SAFETY: `mem_start` is `prev` (the arena's opening fence, live and,
            // per this function's `prev_prev.is_null()` check, the very first block
            // of its arena — i.e. the arena's own base address), non-null.
            let mem_start = unsafe { NonNull::new_unchecked(mem_start) };
            // SAFETY: `mem_start`/`size` describe exactly the arena `add_block`
            // originally mapped (the opening fence through the closing one,
            // established by the `prev_prev`/`next_size` checks above), not
            // referenced again after this call (everything in it — `bl`, `prev`,
            // `next` — is either just detached or was never indexed at all, being a
            // fence).
            unsafe { self.system_free(mem_start, size) };
        }
    }

    /// Returns every fully-unused arena to the OS. Ports `allocator::tree_purge`.
    pub(crate) fn purge(&self) {
        // Flush the MR cache so its block is visible to the scan below (a block only
        // the MR cache references can't be identified as purgeable by walking the
        // tree alone).
        // SAFETY: `None` unconditionally satisfies `attach`'s contract (this is
        // exactly the "flush without installing a new block" case its doc describes).
        unsafe { self.attach(None) };
        // Only an arena whose sole content is one free block spanning (almost) the
        // whole thing is purgeable — `add_block` reserves two fences plus one fake
        // block of overhead, so the smallest possible whole-arena free block is
        // PAGE_SIZE minus that overhead.
        let min_purgeable = os::PAGE_SIZE - 3 * size_of::<BlockHeader>() - size_of::<FreeNode>();
        // EXPLICIT: walks every free-tree node at or above `min_purgeable`, advancing
        // to each one's successor *before* possibly purging it out from under the
        // walk (mirrors HPHA's own `node = node->succ()` before `tree_purge_block`);
        // `node` is the state, not expressible as an iterator invalidated by removal.
        let mut node = self.free_tree.lower_bound(&min_purgeable);
        while let Some(cur) = node {
            // SAFETY: `cur` is live (returned by the tree above).
            let block = unsafe { FreeNode::get_block(cur.as_ptr()) };
            node = self.free_tree.succ(cur);
            // SAFETY: `block` is live, unused (a `FreeNode` only ever sits at a free
            // block's `mem()`), attached to a live physical chain.
            unsafe { self.purge_block(block) };
        }
        // SAFETY: same as the flush above.
        unsafe { self.attach(None) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A heap-backed, `size_of::<BlockHeader>()`-aligned (in practice far more —
    /// `Vec<u64>` guarantees 8-byte alignment, the same as `os::map`'s real 64 KiB
    /// pages provide) stand-in for a real OS-mapped tree arena. Lets [`Tree::add_block`]
    /// (the actual arena-layout logic) run under Miri directly, without needing
    /// `os::map`, which — like `bucket.rs`'s equivalent tests — Miri cannot interpret
    /// (see `os.rs`'s module doc). Every test using this must never call
    /// [`Tree::purge`]: purging tries to `os::unmap` whatever arena it reclaims,
    /// which is unsound for memory that didn't come from `os::map` in the first place.
    struct FakeArena {
        buf: Vec<u64>,
    }

    impl FakeArena {
        fn new(size: usize) -> Self {
            Self {
                buf: vec![0_u64; size.div_ceil(size_of::<u64>())],
            }
        }

        fn ptr(&mut self) -> NonNull<u8> {
            NonNull::new(self.buf.as_mut_ptr().cast::<u8>()).expect("Vec's pointer is never null")
        }
    }

    /// Lays `size` bytes of `arena` out as one big free block and attaches it,
    /// exactly like [`Tree::grow`] does for real OS memory — but skipping
    /// `system_alloc`, so no real OS call happens (see [`FakeArena`]'s doc).
    fn seed(tree: &Tree, arena: &mut FakeArena, size: usize) {
        // SAFETY: `arena`'s buffer is exclusively owned by this call, live for
        // exactly `size` bytes (caller supplies a `size` within `FakeArena::new`'s
        // own allocation), a multiple of `size_of::<BlockHeader>()` and at least
        // `3 * size_of::<BlockHeader>()` (every call site below upholds this).
        let front = unsafe { tree.add_block(arena.ptr(), size) };
        // SAFETY: `front` is live and unused (`add_block`'s own postcondition: it
        // always returns a block freshly marked unused by `coalesce_block`).
        let front = unsafe { NonNull::new_unchecked(front) };
        // SAFETY: forwarded — `front` is live and unused.
        unsafe { tree.attach(Some(front)) };
    }

    #[test]
    fn seeded_alloc_serves_without_touching_the_os() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let ptr = tree.alloc(64).expect("seeded arena has room");
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.as_ptr().write_bytes(0xAB, 64) };
    }

    #[test]
    fn alloc_splits_remainder_which_stays_available() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        // The remainder (far bigger than SPLIT_REMAINDER_MIN) was split off and
        // attached; a second, disjoint allocation must still succeed from it without
        // any OS growth.
        let b = tree.alloc(64).expect("split remainder must be available");
        assert_ne!(a, b);
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
    }

    #[test]
    fn free_then_alloc_same_size_reuses_mr_cached_block() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { tree.free(a) };
        let b = tree.alloc(64).expect("freed block must be reusable");
        // The most-recently-freed block is checked first and fits exactly: the
        // fast path must return the very same address, not a different free region.
        assert_eq!(a, b);
    }

    #[test]
    fn free_coalesces_adjacent_blocks_enabling_a_larger_alloc() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        // Three sequential allocations carve up the same seeded region in order (the
        // MR-cache-first extract path always prefers the just-split remainder).
        let a = tree.alloc(64).expect("seeded arena has room");
        let b = tree.alloc(64).expect("seeded arena has room");
        let c = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `b` is a live allocation this `tree` produced.
        unsafe { tree.free(b) };
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { tree.free(a) };
        // `a` and `b`'s space must now be one merged free block: an allocation
        // bigger than either alone (but within their combined span) must succeed
        // without touching the OS.
        let combined = tree
            .alloc(64 + 64 + 32)
            .expect("coalesced span must fit this");
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: `c` is a live allocation this `tree` produced.
        unsafe { tree.free(c) };
        // SAFETY: `combined` is a live allocation this `tree` produced.
        unsafe { tree.free(combined) };
    }

    #[test]
    fn small_and_large_free_blocks_are_both_retrievable_past_the_mr_cache() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(8192);
        seed(&tree, &mut arena, 8192);
        let small = tree.alloc(64).expect("seeded arena has room"); // <= MAX_SMALL_ALLOCATION once freed
        let large = tree
            .alloc(MAX_SMALL_ALLOCATION + 64)
            .expect("seeded arena has room");
        let spacer = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `small` is a live allocation this `tree` produced.
        unsafe { tree.free(small) };
        // SAFETY: `large` is a live allocation this `tree` produced.
        unsafe { tree.free(large) };
        // `large`'s free happened after `small`'s, so `small` was pushed out of the
        // MR cache into `small_free_list` (its size is `<= MAX_SMALL_ALLOCATION`) —
        // and is still retrievable via a fresh small allocation.
        let small_again = tree
            .alloc(64)
            .expect("small_free_list entry must be reusable");
        // `large` itself is the current MR block; freeing `spacer` (unrelated, since
        // it's not physically adjacent to `large` after the two frees above) pushes
        // `large` into `free_tree` (its size is `> MAX_SMALL_ALLOCATION`).
        // SAFETY: `spacer` is a live allocation this `tree` produced.
        unsafe { tree.free(spacer) };
        let large_again = tree
            .alloc(MAX_SMALL_ALLOCATION + 64)
            .expect("free_tree entry must be reusable");
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: `small_again` is a live allocation this `tree` produced.
        unsafe { tree.free(small_again) };
        // SAFETY: `large_again` is a live allocation this `tree` produced.
        unsafe { tree.free(large_again) };
    }

    #[test]
    fn alloc_aligned_respects_every_requested_alignment() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(8192);
        seed(&tree, &mut arena, 8192);
        for &alignment in &[16usize, 32, 64, 128, 256] {
            let ptr = tree
                .alloc_aligned(48, alignment)
                .expect("seeded arena has room");
            assert_eq!(
                ptr.addr().get() % alignment,
                0,
                "misaligned for requested alignment {alignment}"
            );
            // SAFETY: `ptr` is a live allocation this `tree` produced.
            unsafe { tree.free(ptr) };
        }
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
    }

    #[test]
    fn realloc_shrink_splits_off_a_reusable_remainder() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(512).expect("seeded arena has room");
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { a.as_ptr().write_bytes(0xCD, 512) };
        // SAFETY: `a` is a live allocation this `tree` produced.
        let shrunk = unsafe { tree.realloc(a, 64) }.expect("shrinking never fails");
        assert_eq!(shrunk, a, "shrinking must not move the block");
        // The remainder split off by the shrink must be available for reuse.
        let reused = tree.alloc(128).expect("split remainder must be available");
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: `shrunk` is a live allocation this `tree` produced.
        unsafe { tree.free(shrunk) };
        // SAFETY: `reused` is a live allocation this `tree` produced.
        unsafe { tree.free(reused) };
    }

    #[test]
    fn realloc_grows_in_place_over_a_following_free_block() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `a` is valid for at least 64 bytes.
        unsafe { a.as_ptr().write_bytes(0xEF, 64) };
        // The remainder after `a` is free (split off and attached by `alloc` above);
        // growing into it must succeed in place.
        // SAFETY: `a` is a live allocation this `tree` produced.
        let grown = unsafe { tree.realloc(a, 512) }.expect("must grow into the free remainder");
        assert_eq!(
            grown, a,
            "growing into a following free block must not move it"
        );
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: the first 64 bytes must have been preserved across the in-place grow.
        let preserved = unsafe { core::slice::from_raw_parts(grown.as_ptr(), 64) };
        assert!(preserved.iter().all(|&b| b == 0xEF));
        // SAFETY: `grown` is a live allocation this `tree` produced.
        unsafe { tree.free(grown) };
    }

    #[test]
    fn realloc_falls_back_to_alloc_copy_free_when_boxed_in() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `a` is valid for at least 64 bytes.
        unsafe { a.as_ptr().write_bytes(0x11, 64) };
        // `b` immediately follows `a`, leaving no free neighbour for `a` to grow into.
        let b = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `a` is a live allocation this `tree` produced.
        let moved = unsafe { tree.realloc(a, 512) }.expect("falls back to a fresh allocation");
        assert_ne!(moved, a, "boxed-in growth must relocate");
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: the first 64 bytes must have been preserved across the copy.
        let preserved = unsafe { core::slice::from_raw_parts(moved.as_ptr(), 64) };
        assert!(preserved.iter().all(|&byte| byte == 0x11));
        // SAFETY: `moved` is a live allocation this `tree` produced.
        unsafe { tree.free(moved) };
        // SAFETY: `b` is a live allocation this `tree` produced.
        unsafe { tree.free(b) };
    }

    #[test]
    fn resize_reports_grown_size_without_moving() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        // SAFETY: `a` is a live allocation this `tree` produced.
        let new_size = unsafe { tree.resize(a, 512) };
        assert!(new_size >= 512);
        // `resize` never moves the block — verify it's still usable as a 512-byte
        // region at its original address.
        // SAFETY: `resize` grew `a` in place to at least 512 bytes.
        unsafe { a.as_ptr().write_bytes(0x22, 512) };
        assert_eq!(tree.allocated(), 0, "must not have called os::map");
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { tree.free(a) };
    }

    #[test]
    fn resize_reports_unchanged_size_when_it_cannot_grow() {
        let tree = Tree::new();
        let mut arena = FakeArena::new(4096);
        seed(&tree, &mut arena, 4096);
        let a = tree.alloc(64).expect("seeded arena has room");
        let original_size = {
            // SAFETY: `a` is a live allocation this `tree` produced; querying with
            // its own current size must be a no-op that reports that same size.
            unsafe { tree.resize(a, 64) }
        };
        let _b = tree.alloc(64).expect("seeded arena has room"); // boxes `a` in
        // SAFETY: `a` is a live allocation this `tree` produced.
        let after = unsafe { tree.resize(a, 4096) };
        assert_eq!(
            after, original_size,
            "boxed-in resize must report the unchanged size, never fail or move"
        );
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { tree.free(a) };
    }

    // `tree_alloc_free_purge_returns_memory_to_os` is the one test in this module
    // that calls real `Tree::alloc`/`grow`/`purge` against actual OS memory (it must:
    // `purge` returning memory to the OS is exactly the behaviour under test, and
    // `os::unmap` is unsound to call on anything but real `os::map` memory — see
    // `FakeArena`'s doc). Under Miri both sides of that pair are `os::test_vm`'s
    // heap-backed stand-in, so the test runs there too.
    #[test]
    fn tree_alloc_free_purge_returns_memory_to_os() {
        let tree = Tree::new();
        let a = tree.alloc(64).expect("OS map failed");
        assert!(tree.allocated() > 0);
        // SAFETY: `a` is a live allocation this `tree` produced.
        unsafe { tree.free(a) };
        tree.purge();
        assert_eq!(
            tree.allocated(),
            0,
            "a freshly-grown, now fully-free arena must be fully reclaimed"
        );
    }
}
