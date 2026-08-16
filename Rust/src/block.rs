// SPDX-License-Identifier: MIT OR Apache-2.0
//! The large-allocation path's inline block header, and the two node types the tree
//! allocator embeds inside a free block's own payload.
//!
//! Ports `Cpp/hpha.h`'s `block_header`, `free_node`, and `small_free_node`. A
//! `BlockHeader` physically precedes every large-path payload (allocated or free);
//! `size_and_flags` doubles as the size of the block *and* the offset to the next
//! physical block (`BlockHeader::next` is computed, not stored — HPHA keeps no
//! separate "next block" pointer). `FreeNode`/`SmallFreeNode` are placed at
//! `BlockHeader::mem()` only while a block is free, reusing its own payload as the
//! red-black tree / list bookkeeping storage for that block — zero overhead over the
//! block being free at all. `tree.rs` (Phase 5) owns the multi-block operations
//! (`split_block`/`shift_block`/`coalesce_block`, `tree_*`); this module owns a single
//! block's own layout and physical-neighbour chain.
//!
//! # 64-bit only
//! HPHA's C++ pads `block_header` to `DEFAULT_ALIGNMENT` (`sizeof(double)`, 8 bytes)
//! bytes past `sizeof(block_header*) + sizeof(size_t)` — which on a 32-bit build
//! leaves the *size* right but not the *alignment* (both fields are 4-byte aligned
//! there, not 8), a latent 32-bit gap in the 2007 reference itself. Rather than port
//! that gap, this crate targets 64-bit only for v0.1.0 (matching the GitHub-hosted
//! CI runners, which are all 64-bit) and enforces it at compile time below.

use crate::list::ListLink;
use crate::list::ListNode;
use crate::rbtree::NodeBase;
use crate::rbtree::RbNode;
use core::cmp::Ordering;
use core::ptr::NonNull;

const _: () = assert!(
    usize::BITS == 64,
    "orisnik v0.1.0 targets 64-bit platforms only — see block.rs's module doc"
);

/// Default alignment for the allocator's public API, and the alignment
/// `BlockHeader`'s own layout guarantees. Ports `allocator::DEFAULT_ALIGNMENT`
/// (`sizeof(double)`).
pub(crate) const DEFAULT_ALIGNMENT: usize = 8;

const BL_USED: usize = 1;
/// The two low bits of `size_and_flags` are reserved for flags (only `BL_USED` is
/// defined; bit 1 is unused but still masked off by [`BlockHeader::size`], matching
/// HPHA's `mSizeAndFlags & ~3` exactly rather than just `& ~1`).
const SIZE_MASK: usize = !0b11;

// [`BlockHeader::set_size`]'s `debug_assert!` only checks "multiple of 4" — mirroring
// HPHA's own local `assert((size & 3) == 0)` verbatim — but every `*mut BlockHeader`
// cast in this module (`next`, `ptr_get_block_header`, `FreeNode::get_block`) needs
// the *stronger* guarantee that block boundaries are 8-byte (`DEFAULT_ALIGNMENT`)
// aligned. That stronger guarantee is a caller contract, not something this module
// enforces itself: `tree.rs` (Phase 5) always rounds requested sizes up to a multiple
// of `size_of::<BlockHeader>()` (16 bytes) before installing them — mirroring HPHA's
// own `tree_alloc`'s `round_up(size, sizeof(block_header))` — so every block's `size`
// is in practice always a multiple of 16, hence of `DEFAULT_ALIGNMENT` (8). Every
// `// ALIGN:` comment below on a `*mut BlockHeader` cast relies on this.

/// The inline header physically preceding every large-path payload. Ports
/// `block_header`.
///
/// # Invariants
/// - `size` is always a multiple of 4 (in practice always a multiple of
///   `size_of::<BlockHeader>()`, since every block boundary is block-header-aligned).
/// - `BlockHeader::next(this) == this.mem() + BlockHeader::size(this)` always — there
///   is no separate stored "next" pointer; `next` is a computed position, and
///   [`BlockHeader::set_next`] works backwards from a target position to a size.
/// - The physical chain (`prev`/`next`) always terminates at fence blocks with
///   `size() == 0` (installed by `tree.rs`'s `tree_add_block`), so `next`/`prev`
///   walks never run off the end of a tree arena.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct BlockHeader {
    /// The physically-previous block header, or a fence block if this is the first
    /// real block in its arena. Byte offset 0, naturally 8-byte
    /// (`DEFAULT_ALIGNMENT`)-aligned there since every `BlockHeader` position is
    /// itself 8-aligned (the layout guards below).
    prev: *mut BlockHeader,
    /// Low 2 bits: flags (`BL_USED`, bit 1 unused). Remaining bits: this block's size
    /// in bytes, header included, i.e. the byte distance from `mem()` to the next
    /// block header. Byte offset 8 (64-bit), 8-byte aligned for the same reason as
    /// `prev` above.
    size_and_flags: usize,
}

const _: () = assert!(size_of::<BlockHeader>() == 2 * size_of::<usize>());
const _: () = assert!(align_of::<BlockHeader>() == DEFAULT_ALIGNMENT);

impl BlockHeader {
    // ---- primitive field accessors (one raw dereference each) ----

    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn raw_prev(this: *mut BlockHeader) -> *mut BlockHeader {
        // SAFETY: caller guarantees `this` is live; reads one field.
        unsafe { (*this).prev }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn raw_set_prev(this: *mut BlockHeader, val: *mut BlockHeader) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).prev = val };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn raw_size_and_flags(this: *mut BlockHeader) -> usize {
        // SAFETY: caller guarantees `this` is live; reads one field.
        unsafe { (*this).size_and_flags }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn raw_set_size_and_flags(this: *mut BlockHeader, val: usize) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).size_and_flags = val };
    }

    // ---- derived accessors ----

    /// This block's size in bytes (header included), with the flag bits masked off.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn size(this: *mut BlockHeader) -> usize {
        // SAFETY: forwarded from this function's own contract.
        unsafe { BlockHeader::raw_size_and_flags(this) & SIZE_MASK }
    }

    /// Sets this block's size, preserving the flag bits. `size` must be a multiple of 4.
    ///
    /// # Safety
    /// `this` must be live.
    pub(crate) unsafe fn set_size(this: *mut BlockHeader, size: usize) {
        debug_assert_eq!(size & !SIZE_MASK, 0, "size must be a multiple of 4");
        // SAFETY: forwarded from this function's own contract.
        let flags = unsafe { BlockHeader::raw_size_and_flags(this) } & !SIZE_MASK;
        // SAFETY: forwarded from this function's own contract.
        unsafe { BlockHeader::raw_set_size_and_flags(this, flags | size) };
    }

    /// The start of this block's payload — the address immediately after the header.
    ///
    /// # Safety
    /// `this` must be live, with at least `size_of::<BlockHeader>()` bytes valid
    /// after it (true for any block header ever installed by `tree.rs`).
    #[must_use]
    pub(crate) unsafe fn mem(this: *mut BlockHeader) -> *mut u8 {
        // SAFETY: forwarded from this function's own contract; stays within the
        // same arena allocation (the payload immediately follows the header).
        unsafe { this.cast::<u8>().byte_add(size_of::<BlockHeader>()) }
    }

    /// The next physical block — a computed position (`mem() + size()`), not a
    /// stored pointer.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn next(this: *mut BlockHeader) -> *mut BlockHeader {
        // SAFETY: `this` is live (this function's contract).
        let mem = unsafe { BlockHeader::mem(this) };
        // SAFETY: `this` is live.
        let size = unsafe { BlockHeader::size(this) };
        // SAFETY: `mem` is `this`'s own payload start (just computed above); `size`
        // bytes past it stays within the same arena allocation (the invariant that
        // every block chain terminates at a zero-sized fence, documented on the type).
        let next = unsafe { mem.byte_add(size) };
        // ALIGN: `mem` is 8-aligned (`this` is a `BlockHeader`, align 8;
        // `size_of::<BlockHeader>()` is a multiple of 8) and `size` is a multiple of
        // 8 (caller-contract invariant documented above `SIZE_MASK`), so `next` is
        // 8-aligned too — exactly `align_of::<BlockHeader>()`.
        #[allow(clippy::cast_ptr_alignment)]
        next.cast::<BlockHeader>()
    }

    /// Sets this block's size so that [`BlockHeader::next`] would return `next`.
    /// Ports the setter overload of `block_header::next` — computes a size from a
    /// target position, it does not store a pointer.
    ///
    /// # Safety
    /// `this` must be live. `next` must be at or after `this.mem()`.
    pub(crate) unsafe fn set_next(this: *mut BlockHeader, next: *mut BlockHeader) {
        // SAFETY: `this` is live (this function's contract).
        let mem = unsafe { BlockHeader::mem(this) };
        debug_assert!(
            next.addr() >= mem.addr(),
            "next must be at or after this block's own payload start"
        );
        let size = next.addr() - mem.addr();
        // SAFETY: `this` is live.
        unsafe { BlockHeader::set_size(this, size) };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn prev(this: *mut BlockHeader) -> *mut BlockHeader {
        // SAFETY: forwarded from this function's own contract.
        unsafe { BlockHeader::raw_prev(this) }
    }

    /// # Safety
    /// `this` must be live.
    pub(crate) unsafe fn set_prev(this: *mut BlockHeader, prev: *mut BlockHeader) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { BlockHeader::raw_set_prev(this, prev) };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn used(this: *mut BlockHeader) -> bool {
        // SAFETY: forwarded from this function's own contract.
        (unsafe { BlockHeader::raw_size_and_flags(this) } & BL_USED) != 0
    }

    /// # Safety
    /// `this` must be live.
    pub(crate) unsafe fn set_used(this: *mut BlockHeader) {
        // SAFETY: `this` is live (this function's contract).
        let val = unsafe { BlockHeader::raw_size_and_flags(this) } | BL_USED;
        // SAFETY: `this` is live.
        unsafe { BlockHeader::raw_set_size_and_flags(this, val) };
    }

    /// # Safety
    /// `this` must be live.
    pub(crate) unsafe fn set_unused(this: *mut BlockHeader) {
        // SAFETY: `this` is live (this function's contract).
        let val = unsafe { BlockHeader::raw_size_and_flags(this) } & !BL_USED;
        // SAFETY: `this` is live.
        unsafe { BlockHeader::raw_set_size_and_flags(this, val) };
    }

    /// Removes `this` from the physical chain by growing its predecessor to swallow
    /// its space — HPHA never moves memory to unlink a block, it resizes the
    /// previous block's computed span instead. Ports `block_header::unlink`.
    ///
    /// # Safety
    /// `this`, `this`'s physical predecessor, and `this`'s physical successor must
    /// all be live.
    pub(crate) unsafe fn unlink(this: *mut BlockHeader) {
        // SAFETY: `this` is live (this function's contract).
        let next = unsafe { BlockHeader::next(this) };
        // SAFETY: `this` is live.
        let prev = unsafe { BlockHeader::prev(this) };
        // SAFETY: `next` is live (this function's contract).
        unsafe { BlockHeader::set_prev(next, prev) };
        // SAFETY: `prev` is live (this function's contract).
        unsafe { BlockHeader::set_next(prev, next) };
    }

    /// Inserts `this` into the physical chain immediately after `link`, taking over
    /// the span `link` used to claim beyond the split point (shrinking `link` in the
    /// process). Ports `block_header::link_after`.
    ///
    /// # Safety
    /// `this` must be live, with valid memory for at least `size_of::<BlockHeader>()`
    /// bytes after it. `link` and `link`'s physical successor must be live.
    pub(crate) unsafe fn link_after(this: *mut BlockHeader, link: *mut BlockHeader) {
        // SAFETY: `this` is live (this function's contract).
        unsafe { BlockHeader::set_prev(this, link) };
        // SAFETY: `link` is live (this function's contract).
        let link_next = unsafe { BlockHeader::next(link) };
        // SAFETY: `this` is live.
        unsafe { BlockHeader::set_next(this, link_next) };
        // SAFETY: `this` is live.
        let this_next = unsafe { BlockHeader::next(this) };
        // SAFETY: `this_next` is live (`link`'s old successor, live per this
        // function's contract).
        unsafe { BlockHeader::set_prev(this_next, this) };
        // SAFETY: `this` is live.
        let this_prev = unsafe { BlockHeader::prev(this) };
        // SAFETY: `this_prev` is live (`== link`, live per this function's contract).
        unsafe { BlockHeader::set_next(this_prev, this) };
    }
}

/// Recovers the block header immediately preceding a payload pointer. Ports the
/// allocator's `ptr_get_block_header`.
///
/// # Safety
/// `ptr` must be a payload pointer previously returned by the tree allocator (i.e.
/// `ptr == BlockHeader::mem(header)` for some live `header`).
#[must_use]
pub(crate) unsafe fn ptr_get_block_header(ptr: *mut u8) -> *mut BlockHeader {
    // SAFETY: forwarded from this function's own contract; stays within the same
    // arena allocation (the header immediately precedes the payload it owns).
    let header = unsafe { ptr.byte_sub(size_of::<BlockHeader>()) };
    // ALIGN: `ptr` is `BlockHeader::mem(header)` for some live `header` (this
    // function's contract), which is 8-aligned (`mem` = `this + 16`, `this` already
    // 8-aligned); stepping back the same 16 bytes recovers that 8-aligned address.
    #[allow(clippy::cast_ptr_alignment)]
    header.cast::<BlockHeader>()
}

/// The red-black tree node the tree allocator embeds at a free block's `mem()`,
/// keyed by the owning block's size. Ports `free_node`.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct FreeNode {
    /// This node's tree linkage. Byte offset 0 (required by [`RbNode`]).
    node: NodeBase,
}

impl FreeNode {
    /// The block header owning this free node — `this` is always exactly
    /// `BlockHeader::mem(block)` while the block is free.
    ///
    /// # Safety
    /// `this` must currently be a live free block's embedded `FreeNode` (i.e.
    /// `this.byte_sub(size_of::<BlockHeader>())` is a live, unused `BlockHeader`).
    #[must_use]
    pub(crate) unsafe fn get_block(this: *mut FreeNode) -> *mut BlockHeader {
        // SAFETY: forwarded from this function's own contract; stays within the
        // same arena allocation (the header immediately precedes this node).
        let header = unsafe { this.cast::<u8>().byte_sub(size_of::<BlockHeader>()) };
        // ALIGN: `this` is `BlockHeader::mem(block)` for some live `block` (this
        // function's contract), which is 8-aligned; stepping back the same 16 bytes
        // recovers that 8-aligned address.
        #[allow(clippy::cast_ptr_alignment)]
        header.cast::<BlockHeader>()
    }
}

// SAFETY: `node` is FreeNode's first field (repr(C) guarantees offset 0).
unsafe impl RbNode for FreeNode {
    type Key = usize;

    unsafe fn cmp(this: NonNull<Self>, other: NonNull<Self>) -> Ordering {
        // SAFETY: caller guarantees `this` is live.
        let this_block = unsafe { FreeNode::get_block(this.as_ptr()) };
        // SAFETY: `this_block` is live (`this`'s owning block, established above).
        let this_size = unsafe { BlockHeader::size(this_block) };
        // SAFETY: caller guarantees `other` is live.
        let other_block = unsafe { FreeNode::get_block(other.as_ptr()) };
        // SAFETY: `other_block` is live (`other`'s owning block, established above).
        let other_size = unsafe { BlockHeader::size(other_block) };
        this_size.cmp(&other_size)
    }

    unsafe fn cmp_key(this: NonNull<Self>, key: &usize) -> Ordering {
        // SAFETY: caller guarantees `this` is live.
        let this_block = unsafe { FreeNode::get_block(this.as_ptr()) };
        // SAFETY: `this_block` is live (`this`'s owning block, established above).
        let this_size = unsafe { BlockHeader::size(this_block) };
        this_size.cmp(key)
    }
}

/// The plain list node the tree allocator embeds at a small free block's `mem()` —
/// an optimization over [`FreeNode`] for blocks too small to be worth indexing by
/// size in the tree (never queried, so a list suffices; see `tree.rs`). Ports
/// `small_free_node`.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct SmallFreeNode {
    /// This node's list linkage. Byte offset 0 (required by [`ListNode`]).
    link: ListLink,
}

// SAFETY: `link` is SmallFreeNode's first field (repr(C) guarantees offset 0).
unsafe impl ListNode for SmallFreeNode {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rbtree::IntrusiveMultiRbTree;

    /// A raw, heap-backed arena for placing block headers into during tests — a
    /// stand-in for the real VM-mapped tree arena `tree.rs` will use. Backed by
    /// `Vec<u64>`, not `Vec<u8>`, so the type system itself guarantees 8-byte
    /// (`DEFAULT_ALIGNMENT`) alignment — `Vec<u8>`'s `align_of::<u8>() == 1` would
    /// only be 8-aligned by allocator happenstance, not by any language guarantee.
    struct Arena {
        // Kept alive for the struct's lifetime; blocks are placed inside `buf`.
        buf: Vec<u64>,
    }

    impl Arena {
        fn new(size: usize) -> Self {
            Self {
                buf: vec![0_u64; size.div_ceil(size_of::<u64>())],
            }
        }

        /// `offset` (in bytes) must be a multiple of 8 — every call site below uses
        /// offsets that are, by construction, multiples of `size_of::<BlockHeader>()`
        /// (16) or otherwise chosen to be 8-aligned.
        fn header_at(&mut self, offset: usize) -> *mut BlockHeader {
            debug_assert_eq!(offset % align_of::<BlockHeader>(), 0);
            // SAFETY: `offset` is caller-chosen within `self.buf`'s allocated length
            // (test-only helper; every call site below stays in bounds by
            // construction), and `self.buf` outlives every use of the returned
            // pointer within a test.
            let byte_ptr = unsafe { self.buf.as_mut_ptr().cast::<u8>().add(offset) };
            // ALIGN: `self.buf` is `Vec<u64>`-backed (8-aligned by the type system);
            // `offset` is a multiple of 8 (checked above), so `byte_ptr` is 8-aligned.
            #[allow(clippy::cast_ptr_alignment)]
            byte_ptr.cast::<BlockHeader>()
        }
    }

    /// Installs a fresh, unused block header of `size` bytes (header included) at
    /// `header`, with `prev` as its physical predecessor.
    ///
    /// # Safety
    /// `header` must be valid for `size_of::<BlockHeader>()` bytes; `prev` must be
    /// live (or dangling-but-never-dereferenced, as in a test's synthetic first block).
    unsafe fn install_block(header: *mut BlockHeader, prev: *mut BlockHeader, size: usize) {
        // SAFETY: `header` is valid for a BlockHeader per this function's contract.
        unsafe { BlockHeader::set_prev(header, prev) };
        // SAFETY: `header` is valid.
        unsafe { BlockHeader::set_size(header, size) };
        // SAFETY: `header` is valid.
        unsafe { BlockHeader::set_unused(header) };
    }

    #[test]
    fn size_used_roundtrip() {
        let mut arena = Arena::new(256);
        let h = arena.header_at(0);
        // SAFETY: `h` is valid for a BlockHeader (within `arena.buf`'s 256 bytes).
        unsafe { install_block(h, core::ptr::null_mut(), 64) };
        // SAFETY: `h` is live.
        assert_eq!(unsafe { BlockHeader::size(h) }, 64);
        // SAFETY: `h` is live.
        assert!(!unsafe { BlockHeader::used(h) });
        // SAFETY: `h` is live.
        unsafe { BlockHeader::set_used(h) };
        // SAFETY: `h` is live.
        assert!(unsafe { BlockHeader::used(h) });
        // SAFETY: `h` is live.
        let size = unsafe { BlockHeader::size(h) };
        assert_eq!(size, 64, "flag bit must not corrupt size");
        // SAFETY: `h` is live.
        unsafe { BlockHeader::set_unused(h) };
        // SAFETY: `h` is live.
        assert!(!unsafe { BlockHeader::used(h) });
    }

    #[test]
    fn next_is_computed_from_mem_plus_size() {
        let mut arena = Arena::new(256);
        let h = arena.header_at(0);
        // SAFETY: `h` is valid for a BlockHeader.
        unsafe { install_block(h, core::ptr::null_mut(), 64) };
        // SAFETY: `h` is live.
        let mem = unsafe { BlockHeader::mem(h) };
        // SAFETY: `h` is live.
        let next = unsafe { BlockHeader::next(h) };
        assert_eq!(next.cast::<u8>().addr(), mem.addr() + 64);
    }

    #[test]
    fn set_next_computes_size_from_target_position() {
        let mut arena = Arena::new(256);
        let h = arena.header_at(0);
        // SAFETY: `h` is valid for a BlockHeader.
        unsafe { install_block(h, core::ptr::null_mut(), 64) };
        // SAFETY: `h` is live; `target` (80 bytes into the arena) is within bounds.
        let target = arena.header_at(80);
        // SAFETY: `h` is live; `target` is at/after `h.mem()`.
        unsafe { BlockHeader::set_next(h, target) };
        // SAFETY: `h` is live.
        assert_eq!(unsafe { BlockHeader::next(h) }, target);
        // SAFETY: `h` is live.
        let size = unsafe { BlockHeader::size(h) };
        assert_eq!(size, 80 - size_of::<BlockHeader>());
    }

    #[test]
    fn unlink_grows_predecessor_over_removed_block() {
        let mut arena = Arena::new(256);
        let a = arena.header_at(0);
        let b = arena.header_at(48);
        let c = arena.header_at(96);
        // SAFETY: `a` is valid for a BlockHeader within `arena.buf`.
        unsafe { install_block(a, core::ptr::null_mut(), 48) };
        // SAFETY: `b` is valid for a BlockHeader within `arena.buf`; `a` is live.
        unsafe { install_block(b, a, 48) };
        // SAFETY: `c` is valid for a BlockHeader within `arena.buf`; `b` is live.
        unsafe { install_block(c, b, 0) }; // fence
        // SAFETY: `b` is live; `c` is live.
        unsafe { BlockHeader::set_next(b, c) };
        // SAFETY: a/b/c form a live physical chain (just installed above).
        unsafe { BlockHeader::unlink(b) };
        // SAFETY: `a` is live.
        assert_eq!(unsafe { BlockHeader::next(a) }, c);
        // SAFETY: `c` is live.
        assert_eq!(unsafe { BlockHeader::prev(c) }, a);
    }

    #[test]
    fn link_after_splits_predecessor_span() {
        let mut arena = Arena::new(256);
        let a = arena.header_at(0);
        let end = arena.header_at(96);
        // SAFETY: `a` is valid for a BlockHeader within `arena.buf`.
        unsafe { install_block(a, core::ptr::null_mut(), 0) };
        // SAFETY: `a` is live. `a` initially spans up to `end`.
        unsafe { BlockHeader::set_next(a, end) };
        let new_block = arena.header_at(48);
        // SAFETY: `new_block` is valid for a BlockHeader; `a` is live with a live
        // successor (`end`, just established above).
        unsafe { BlockHeader::link_after(new_block, a) };
        // SAFETY: `a` is live.
        let a_next = unsafe { BlockHeader::next(a) };
        assert_eq!(a_next, new_block, "a shrank to end at the split point");
        // SAFETY: `new_block` is live.
        assert_eq!(unsafe { BlockHeader::prev(new_block) }, a);
        // SAFETY: `new_block` is live.
        let new_block_next = unsafe { BlockHeader::next(new_block) };
        assert_eq!(
            new_block_next, end,
            "new_block inherited a's old span boundary"
        );
        // SAFETY: `end` is live (a fence header, installed as `a`'s target above).
        assert_eq!(unsafe { BlockHeader::prev(end) }, new_block);
    }

    #[test]
    fn ptr_get_block_header_roundtrips_with_mem() {
        let mut arena = Arena::new(256);
        let h = arena.header_at(0);
        // SAFETY: `h` is valid for a BlockHeader.
        unsafe { install_block(h, core::ptr::null_mut(), 64) };
        // SAFETY: `h` is live.
        let mem = unsafe { BlockHeader::mem(h) };
        // SAFETY: `mem` is `h`'s own payload start, so stepping back recovers `h`.
        assert_eq!(unsafe { ptr_get_block_header(mem) }, h);
    }

    /// A free node's block-size comparisons drive the tree allocator's whole
    /// size-keyed index; test it against a real `IntrusiveMultiRbTree`, not just in
    /// isolation, since that is the only way `FreeNode`/`RbNode` are ever used.
    #[test]
    fn free_node_orders_by_owning_block_size() {
        let mut arena = Arena::new(1024);
        let sizes = [64usize, 128, 32, 96];
        let mut headers = Vec::new();
        let mut offset = 0;
        for &size in &sizes {
            let h = arena.header_at(offset);
            // SAFETY: `h` is valid for a BlockHeader within `arena.buf` (offsets
            // chosen with generous spacing relative to the small test sizes).
            unsafe { install_block(h, core::ptr::null_mut(), size) };
            headers.push(h);
            offset += 200;
        }

        let tree: IntrusiveMultiRbTree<FreeNode> = IntrusiveMultiRbTree::new();
        for &h in &headers {
            // SAFETY: `h` is live; its `mem()` is within the block's own span
            // (`size` bytes, each `>= size_of::<FreeNode>()` for these test sizes),
            // so writing a `FreeNode` there is in-bounds.
            let mem = unsafe { BlockHeader::mem(h) };
            // ALIGN: `mem` is 8-aligned (`BlockHeader::mem`'s own guarantee), and
            // `FreeNode`'s only field is `NodeBase` (align 8) — matches.
            #[allow(clippy::cast_ptr_alignment)]
            let node = mem.cast::<FreeNode>();
            let node = NonNull::new(node).expect("arena pointer is never null");
            tree.insert(node);
        }

        let smallest = tree.minimum().expect("tree is non-empty");
        // SAFETY: `smallest` is live (just returned by the tree above).
        let smallest_block = unsafe { FreeNode::get_block(smallest.as_ptr()) };
        // SAFETY: `smallest_block` is live.
        assert_eq!(unsafe { BlockHeader::size(smallest_block) }, 32);

        let found = tree.lower_bound(&96).expect("a block of size >= 96 exists");
        // SAFETY: `found` is live.
        let found_block = unsafe { FreeNode::get_block(found.as_ptr()) };
        // SAFETY: `found_block` is live.
        assert_eq!(unsafe { BlockHeader::size(found_block) }, 96);

        for &h in &headers {
            // SAFETY: `h` is live; its `mem()` was written as a `FreeNode` above.
            let mem = unsafe { BlockHeader::mem(h) };
            // ALIGN: same as the insertion loop above.
            #[allow(clippy::cast_ptr_alignment)]
            let node = mem.cast::<FreeNode>();
            let node = NonNull::new(node).expect("arena pointer is never null");
            tree.erase(node);
        }
        assert!(tree.is_empty());
    }
}
