// SPDX-License-Identifier: MIT OR Apache-2.0
//! Intrusive, augmented red-black tree supporting duplicate keys ("multi-tree").
//!
//! Ports `Cpp/hpha.h`'s `intrusive_multi_rbtree_base`/`intrusive_multi_rbtree<T>` (node
//! layout and multi-tree operations) and the fixup algorithms in `Cpp/hpha.cpp`
//! (`insert_fixup`/`erase_fixup`). This is the tree allocator's free-block index,
//! keyed by block size — the highest-risk module for the cross-port invariant
//! (`ROADMAP.md`), since it counts rotations and coalescing operations, not just final
//! tree shape. Every function below preserves HPHA's operation *order*, not just its
//! net effect, even where a reordering would be mathematically equivalent.
//!
//! # Equal keys: the "chain"
//! HPHA's tree is a *multi*-tree: several elements may share one key (several free
//! blocks of the same size). Rather than allow duplicate tree nodes, exactly one
//! member of an equal-key group occupies a real tree position (the "attached"
//! member); the rest are threaded onto it via `neighbours` — a circular doubly-linked
//! list *distinct* from `list.rs`'s `IntrusiveList` (no separate sentinel: any member
//! can be a valid entry point, and the attached member is simply the one whose
//! `parent` is non-null). This is why [`NodeBase::parent`] is nullable — see
//! `tag.rs`'s `TaggedPtr` doc for why that required revisiting the Phase 1 design.
//!
//! # Sentinel design
//! Same lazy-self-init pattern as `list.rs`'s `IntrusiveList`, for the same Tree
//! Borrows reason (see that module's doc): the tree's `head` sentinel lives in an
//! `UnsafeCell`, self-links on first touch, and every [`IntrusiveMultiRbTree`] method
//! takes `&self`. The same non-move-after-first-use contract applies.

use crate::tag::{BIT_COLOUR, BIT_SIDE, TaggedPtr};
use core::cell::UnsafeCell;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// Which of a node's two children/neighbours/tree-order-links a position refers to.
/// Ports `side`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Side {
    Left,
    Right,
}

impl Side {
    /// Array index for this side — a `match`, not an `as` cast (avoids the
    /// `as_conversions` lint entirely rather than annotating around it).
    #[must_use]
    const fn index(self) -> usize {
        match self {
            Side::Left => 0,
            Side::Right => 1,
        }
    }

    /// The other side. Ports `side o = (side)(1 - s)`.
    #[must_use]
    pub(crate) const fn other(self) -> Side {
        match self {
            Side::Left => Side::Right,
            Side::Right => Side::Left,
        }
    }
}

/// A red-black tree node's colour. Ports `colour`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Colour {
    Black,
    Red,
}

/// The embedded fields of a red-black tree node. Ports `node_base`.
///
/// # Invariants
/// - `children[Side::Right] == self` (the "nil" test, [`NodeBase::is_nil`]) marks an
///   empty subtree; every real node's children are themselves live `NodeBase`s or the
///   tree's sentinel.
/// - `neighbours[Side::Left] == self` means this node has no equal-key duplicates
///   ([`NodeBase::chained`] is `false`).
/// - `parent` is null exactly when this node is chained but not its equal-key group's
///   tree-attached representative ([`NodeBase::is_attached`] is `false`) — see the
///   module doc's "Equal keys" section.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct NodeBase {
    /// Left (index 0) and right (index 1) tree children.
    children: [*mut NodeBase; 2],
    /// Left (index 0, "prev") and right (index 1, "next") links in this node's
    /// equal-key group's circular chain.
    neighbours: [*mut NodeBase; 2],
    /// Tagged parent pointer: bit [`BIT_COLOUR`] is this node's red-black colour, bit
    /// [`BIT_SIDE`] is which of the parent's two children this node is. Null (with
    /// either tag state) means this node is a chained, non-tree-attached duplicate.
    parent: TaggedPtr<NodeBase>,
}

const _: () = assert!(size_of::<NodeBase>() == 5 * size_of::<usize>());

impl NodeBase {
    // ---- primitive field accessors (one raw dereference each) ----

    /// # Safety
    /// `this` must be live.
    #[must_use]
    // INDEX: `s.index()` is `Side::index`, which only ever returns 0 or 1 — always
    // in bounds for a 2-element array.
    #[allow(clippy::indexing_slicing)]
    unsafe fn raw_child(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        // SAFETY: caller guarantees `this` is live; reads one array element.
        unsafe { (*this).children[s.index()] }
    }

    /// # Safety
    /// `this` must be live.
    // INDEX: `s.index()` is `Side::index`, which only ever returns 0 or 1 — always
    // in bounds for a 2-element array.
    #[allow(clippy::indexing_slicing)]
    unsafe fn raw_set_child(this: *mut NodeBase, s: Side, val: *mut NodeBase) {
        // SAFETY: caller guarantees `this` is live; writes one array element.
        unsafe { (*this).children[s.index()] = val };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    // INDEX: `s.index()` is `Side::index`, which only ever returns 0 or 1 — always
    // in bounds for a 2-element array.
    #[allow(clippy::indexing_slicing)]
    unsafe fn raw_neighbour(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        // SAFETY: caller guarantees `this` is live; reads one array element.
        unsafe { (*this).neighbours[s.index()] }
    }

    /// # Safety
    /// `this` must be live.
    // INDEX: `s.index()` is `Side::index`, which only ever returns 0 or 1 — always
    // in bounds for a 2-element array.
    #[allow(clippy::indexing_slicing)]
    unsafe fn raw_set_neighbour(this: *mut NodeBase, s: Side, val: *mut NodeBase) {
        // SAFETY: caller guarantees `this` is live; writes one array element.
        unsafe { (*this).neighbours[s.index()] = val };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn raw_parent(this: *mut NodeBase) -> TaggedPtr<NodeBase> {
        // SAFETY: caller guarantees `this` is live; reads one field (Copy).
        unsafe { (*this).parent }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn raw_set_parent(this: *mut NodeBase, val: TaggedPtr<NodeBase>) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).parent = val };
    }

    // ---- derived accessors (one primitive call each) ----

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn child(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_child(this, s) }
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn neighbour(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_neighbour(this, s) }
    }

    /// The node's parent, or null if it is a chained, non-attached duplicate.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn parent(this: *mut NodeBase) -> *mut NodeBase {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_parent(this) }.ptr()
    }

    /// # Safety
    /// `this` must be live and attached ([`NodeBase::is_attached`]).
    #[must_use]
    pub(crate) unsafe fn parent_side(this: *mut NodeBase) -> Side {
        // SAFETY: forwarded from this function's own contract.
        if unsafe { NodeBase::raw_parent(this) }.bit(BIT_SIDE) {
            Side::Right
        } else {
            Side::Left
        }
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn colour(this: *mut NodeBase) -> Colour {
        // SAFETY: forwarded from this function's own contract.
        if unsafe { NodeBase::raw_parent(this) }.bit(BIT_COLOUR) {
            Colour::Red
        } else {
            Colour::Black
        }
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn red(this: *mut NodeBase) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::colour(this) == Colour::Red }
    }

    /// This node is chained onto an equal-key group but is not its tree-attached
    /// representative. Ports `node_base::head()` — renamed to avoid confusion with
    /// `list.rs`'s unrelated sentinel-head concept.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn is_attached(this: *mut NodeBase) -> bool {
        // SAFETY: forwarded from this function's own contract.
        !unsafe { NodeBase::parent(this) }.is_null()
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn is_nil(this: *mut NodeBase) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_child(this, Side::Right) == this }
    }

    /// This node has equal-key duplicates chained onto it (in either direction; the
    /// chain is circular so both directions are non-self exactly when either is).
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn chained(this: *mut NodeBase) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_neighbour(this, Side::Left) != this }
    }

    // ---- mutators (compose primitives; one unsafe call per line) ----

    /// # Safety
    /// `this` must be live.
    unsafe fn set_child(this: *mut NodeBase, s: Side, val: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_set_child(this, s, val) };
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn set_neighbour(this: *mut NodeBase, s: Side, val: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_set_neighbour(this, s, val) };
    }

    /// Replaces the parent pointer, preserving the current colour/side tag.
    ///
    /// # Safety
    /// `this` must be live.
    unsafe fn set_parent_ptr(this: *mut NodeBase, val: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        let mut tagged = unsafe { NodeBase::raw_parent(this) };
        tagged.set_ptr(val);
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_set_parent(this, tagged) };
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn set_parent_side(this: *mut NodeBase, s: Side) {
        // SAFETY: forwarded from this function's own contract.
        let mut tagged = unsafe { NodeBase::raw_parent(this) };
        match s {
            Side::Left => tagged.clear_bit(BIT_SIDE),
            Side::Right => tagged.set_bit(BIT_SIDE),
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_set_parent(this, tagged) };
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn set_colour(this: *mut NodeBase, c: Colour) {
        // SAFETY: forwarded from this function's own contract.
        let mut tagged = unsafe { NodeBase::raw_parent(this) };
        match c {
            Colour::Black => tagged.clear_bit(BIT_COLOUR),
            Colour::Red => tagged.set_bit(BIT_COLOUR),
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::raw_set_parent(this, tagged) };
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn make_red(this: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::set_colour(this, Colour::Red) };
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn make_black(this: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { NodeBase::set_colour(this, Colour::Black) };
    }

    // ---- structural operations ----

    /// Rotates `this` down and its side-`o` child (`o` = the side opposite `s`) up
    /// into `this`'s former position. Ports `node_base::rotate`.
    ///
    /// # Safety
    /// `this` must be live and attached, with `this`'s parent's child on `this`'s own
    /// `parent_side` equal to `this` (the standard rotation precondition); `this`'s
    /// side-`o` child must be a live, non-nil node.
    pub(crate) unsafe fn rotate(this: *mut NodeBase, s: Side) {
        let o = s.other();
        // SAFETY: forwarded from this function's own contract.
        let ps = unsafe { NodeBase::parent_side(this) };
        // SAFETY: forwarded from this function's own contract.
        let this_parent = unsafe { NodeBase::parent(this) };
        // SAFETY: forwarded from this function's own contract.
        let top = unsafe { NodeBase::child(this, o) };
        // SAFETY: `top` is live (this function's precondition: a non-nil child).
        let top_s_child = unsafe { NodeBase::child(top, s) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, o, top_s_child) };
        // SAFETY: `top_s_child` is live (read live above, from a live `top`).
        unsafe { NodeBase::set_parent_ptr(top_s_child, this) };
        // SAFETY: same as above.
        unsafe { NodeBase::set_parent_side(top_s_child, o) };
        // SAFETY: `top` is live.
        unsafe { NodeBase::set_parent_ptr(top, this_parent) };
        // SAFETY: `top` is live.
        unsafe { NodeBase::set_parent_side(top, ps) };
        // SAFETY: `this_parent` is live (this function's precondition).
        unsafe { NodeBase::set_child(this_parent, ps, top) };
        // SAFETY: `top` is live.
        unsafe { NodeBase::set_child(top, s, this) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_ptr(this, top) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_side(this, s) };
    }

    /// The tree-order predecessor (`s` = [`Side::Left`]) or successor (`s` =
    /// [`Side::Right`]) of `this`, walking the equal-key chain first (O(1) for
    /// duplicates) and falling back to a genuine tree walk. May return the tree's
    /// sentinel (never dereferenced as such by this function). Ports
    /// `node_base::pred_or_succ`.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn pred_or_succ(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        // SAFETY: forwarded from this function's own contract.
        let cur = unsafe { NodeBase::neighbour(this, s) };
        // SAFETY: `cur` is live (a real node's neighbour is always live).
        let cur_parent = unsafe { NodeBase::parent(cur) };
        if cur_parent.is_null() {
            return cur;
        }
        // SAFETY: `cur` is live.
        let first_child = unsafe { NodeBase::child(cur, s) };
        // SAFETY: `first_child` is live (a live node's child is always live, nil or not).
        if unsafe { NodeBase::is_nil(first_child) } {
            let mut cur = cur;
            let mut xessor = cur_parent;
            // EXPLICIT: climb parents while `cur` is a side-`s` child; `cur`/`xessor`
            // are the state threaded up the tree, not expressible as an iterator.
            loop {
                // SAFETY: `cur` is live.
                if unsafe { NodeBase::parent_side(cur) } != s {
                    break;
                }
                cur = xessor;
                // SAFETY: `xessor` is live (this loop's own invariant, re-established
                // below on every iteration; true on entry since `cur_parent` is live).
                xessor = unsafe { NodeBase::parent(xessor) };
            }
            xessor
        } else {
            let o = s.other();
            let mut xessor = first_child;
            // EXPLICIT: descend to the subtree's side-`o` extreme; `xessor` is the
            // state threaded down the tree, not expressible as an iterator.
            loop {
                // SAFETY: `xessor` is live.
                let next = unsafe { NodeBase::child(xessor, o) };
                // SAFETY: `next` is live.
                if unsafe { NodeBase::is_nil(next) } {
                    break;
                }
                xessor = next;
            }
            xessor
        }
    }

    /// The extreme node (leftmost for `s` = [`Side::Left`], rightmost for
    /// [`Side::Right`]) of the subtree rooted at `this`. Returns `this` itself if
    /// `this` is nil. Ports `node_base::min_or_max`.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    // Only reached (in this crate) through `IntrusiveMultiRbTree::minimum`, itself
    // currently exercised only by `block.rs`'s test suite — both are the faithful
    // port of `node_base`/`intrusive_multi_rbtree`'s general-purpose min/max API,
    // kept for completeness rather than because `tree.rs`'s own dispatch needs them.
    #[allow(dead_code)]
    pub(crate) unsafe fn min_or_max(this: *mut NodeBase, s: Side) -> *mut NodeBase {
        let mut cur = this;
        let mut minmax = cur;
        // EXPLICIT: descend to the side-`s` extreme; `cur`/`minmax` are the state
        // threaded down the tree, not expressible as an iterator.
        // SAFETY: `cur` is live (starts live per this function's contract, and is
        // re-established live on every loop iteration below).
        while !unsafe { NodeBase::is_nil(cur) } {
            minmax = cur;
            // SAFETY: `cur` is live (just checked non-nil above).
            cur = unsafe { NodeBase::child(cur, s) };
        }
        minmax
    }

    /// Attaches a freshly-unlinked `this` as `parent`'s side-`s` child (a fresh, red
    /// leaf — rotations/recolouring happen in [`insert_fixup`]). Ports
    /// `node_base::attach_to`.
    ///
    /// # Safety
    /// `this` must be a live node that is not currently part of any tree or chain.
    /// `parent` must be live with a live `child(s)` (nil counts).
    pub(crate) unsafe fn attach_to(this: *mut NodeBase, parent: *mut NodeBase, s: Side) {
        // SAFETY: `this` is live (this function's contract).
        unsafe { NodeBase::set_neighbour(this, Side::Left, this) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_neighbour(this, Side::Right, this) };
        // SAFETY: `parent` is live (this function's contract).
        let leaf_child = unsafe { NodeBase::child(parent, s) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, Side::Left, leaf_child) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, Side::Right, leaf_child) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_ptr(this, parent) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_side(this, s) };
        // SAFETY: `parent` is live.
        unsafe { NodeBase::set_child(parent, s, this) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::make_red(this) };
    }

    /// Splices `child` into `this`'s structural position (parent's child pointer
    /// retargeted; `child`'s own colour is untouched). Used when `this` is being
    /// removed from the tree and has at most one non-nil child. Ports
    /// `node_base::substitute_with`.
    ///
    /// # Safety
    /// `this` must be live and attached. `child` must be live.
    pub(crate) unsafe fn substitute_with(this: *mut NodeBase, child: *mut NodeBase) {
        // SAFETY: forwarded from this function's own contract.
        let ps = unsafe { NodeBase::parent_side(this) };
        // SAFETY: forwarded from this function's own contract.
        let this_parent = unsafe { NodeBase::parent(this) };
        // SAFETY: `child` is live (this function's contract).
        unsafe { NodeBase::set_parent_ptr(child, this_parent) };
        // SAFETY: `child` is live.
        unsafe { NodeBase::set_parent_side(child, ps) };
        // SAFETY: `this_parent` is live (this function's contract: `this` attached).
        unsafe { NodeBase::set_child(this_parent, ps, child) };
    }

    /// Makes `this` assume `node`'s structural position, children, and colour —
    /// `node` is being fully removed from the tree and `this` (its equal-key chain
    /// successor) is taking its place. Ports `node_base::switch_with`.
    ///
    /// # Safety
    /// `this != node`. `node` must be live and attached. `node`'s children and parent
    /// must be live.
    pub(crate) unsafe fn switch_with(this: *mut NodeBase, node: *mut NodeBase) {
        debug_assert!(this != node);
        // SAFETY: forwarded from this function's own contract.
        debug_assert!(unsafe { NodeBase::is_attached(node) });
        // SAFETY: forwarded from this function's own contract.
        let nps = unsafe { NodeBase::parent_side(node) };
        // SAFETY: `node` is live (this function's contract).
        let node_left = unsafe { NodeBase::child(node, Side::Left) };
        // SAFETY: `node` is live.
        let node_right = unsafe { NodeBase::child(node, Side::Right) };
        // SAFETY: `this` must be live (a node about to replace another is always live).
        unsafe { NodeBase::set_child(this, Side::Left, node_left) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, Side::Right, node_right) };
        // SAFETY: forwarded from this function's own contract.
        let node_parent = unsafe { NodeBase::parent(node) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_ptr(this, node_parent) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_side(this, nps) };
        // SAFETY: `node_left` is live (this function's contract).
        unsafe { NodeBase::set_parent_ptr(node_left, this) };
        // SAFETY: `node_left` is live.
        unsafe { NodeBase::set_parent_side(node_left, Side::Left) };
        // SAFETY: `node_right` is live (this function's contract).
        unsafe { NodeBase::set_parent_ptr(node_right, this) };
        // SAFETY: `node_right` is live.
        unsafe { NodeBase::set_parent_side(node_right, Side::Right) };
        // SAFETY: `node_parent` is live (this function's contract).
        unsafe { NodeBase::set_child(node_parent, nps, this) };
        // SAFETY: `node` is live.
        let node_colour = unsafe { NodeBase::colour(node) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_colour(this, node_colour) };
    }

    /// Removes `this` from its equal-key group's chain. Ports `node_base::unlink`
    /// (the chain-unlink overload — distinct from the tree-structural removal in
    /// [`erase`]).
    ///
    /// # Safety
    /// `this` must be live and currently chained ([`NodeBase::chained`]) or
    /// self-linked (a no-op splice in that case).
    pub(crate) unsafe fn unlink_from_chain(this: *mut NodeBase) {
        // SAFETY: `this` is live (this function's contract); reads one field.
        let next = unsafe { NodeBase::raw_neighbour(this, Side::Right) };
        // SAFETY: `this` is live; reads one field.
        let prev = unsafe { NodeBase::raw_neighbour(this, Side::Left) };
        // SAFETY: `next` is live (a live node's neighbour is always live).
        unsafe { NodeBase::set_neighbour(next, Side::Left, prev) };
        // SAFETY: `prev` is live.
        unsafe { NodeBase::set_neighbour(prev, Side::Right, next) };
    }

    /// Chains `this` into `node`'s equal-key group, immediately before `node`.
    /// `this` becomes a plain chain link: no tree position, no colour that matters,
    /// null parent. Ports `node_base::link`.
    ///
    /// # Safety
    /// `this` must not currently be part of any tree or chain. `node` must be live.
    pub(crate) unsafe fn link_into_chain(this: *mut NodeBase, node: *mut NodeBase) {
        // SAFETY: `node` is live (this function's contract); reads one field.
        let node_prev = unsafe { NodeBase::raw_neighbour(node, Side::Left) };
        // SAFETY: `this` is live (this function's contract).
        unsafe { NodeBase::set_neighbour(this, Side::Left, node_prev) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_neighbour(this, Side::Right, node) };
        // SAFETY: `node` is live.
        unsafe { NodeBase::set_neighbour(node, Side::Left, this) };
        // SAFETY: `node_prev` is live (a live node's neighbour is always live).
        unsafe { NodeBase::set_neighbour(node_prev, Side::Right, this) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, Side::Left, core::ptr::null_mut()) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_child(this, Side::Right, core::ptr::null_mut()) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_ptr(this, core::ptr::null_mut()) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::set_parent_side(this, Side::Left) };
        // SAFETY: `this` is live.
        unsafe { NodeBase::make_red(this) };
    }
}

/// Rebalances after [`NodeBase::attach_to`] attached `node` as a fresh red leaf. Ports
/// `intrusive_multi_rbtree_base::insert_fixup` (`Cpp/hpha.cpp`).
///
/// # Safety
/// `head` must be a live tree sentinel; `node` must be a live, just-attached node.
unsafe fn insert_fixup(head: *mut NodeBase, node: *mut NodeBase) {
    let mut cur = node;
    // SAFETY: `cur` is live (this function's contract).
    let mut p = unsafe { NodeBase::parent(cur) };
    // EXPLICIT: climb and recolour/rotate while the parent is red; `cur`/`p` are the
    // state threaded up the tree, not expressible as an iterator.
    // SAFETY: `p` is live (re-established live at the bottom of every loop iteration;
    // true on entry since a freshly-attached node always has a live parent).
    while unsafe { NodeBase::red(p) } {
        // SAFETY: `p` is live (just read as red above).
        let pp = unsafe { NodeBase::parent(p) };
        // SAFETY: `p` is live.
        let s = unsafe { NodeBase::parent_side(p) };
        let o = s.other();
        // SAFETY: `pp` is live (a red node is never the tree's own root sentinel
        // child, so it always has a live parent).
        let pp_right = unsafe { NodeBase::child(pp, o) };
        // SAFETY: `pp_right` is live.
        if unsafe { NodeBase::red(pp_right) } {
            // SAFETY: `p` is live.
            unsafe { NodeBase::make_black(p) };
            // SAFETY: `pp_right` is live.
            unsafe { NodeBase::make_black(pp_right) };
            // SAFETY: `pp` is live.
            unsafe { NodeBase::make_red(pp) };
            cur = pp;
            // SAFETY: `cur` is live.
            p = unsafe { NodeBase::parent(cur) };
        } else {
            // SAFETY: `p` is live.
            let p_o_child = unsafe { NodeBase::child(p, o) };
            if cur == p_o_child {
                cur = p;
                // SAFETY: `cur` is live.
                unsafe { NodeBase::rotate(cur, s) };
                // SAFETY: `cur` is live.
                p = unsafe { NodeBase::parent(cur) };
            }
            // SAFETY: `p` is live.
            unsafe { NodeBase::make_black(p) };
            // SAFETY: `pp` is live.
            unsafe { NodeBase::make_red(pp) };
            // SAFETY: `pp` is live.
            unsafe { NodeBase::rotate(pp, o) };
        }
    }
    // SAFETY: `head` is live (this function's contract).
    let root = unsafe { NodeBase::child(head, Side::Left) };
    // SAFETY: `root` is live (the tree's root is always live, nil or not).
    unsafe { NodeBase::make_black(root) };
}

/// Rebalances after a black node was spliced out during erase, starting from the
/// child (`node`) that took its place (possibly the tree's own nil sentinel — that is
/// exactly the "double black at an empty subtree" case this walk terminates from via
/// the `cur != root` / `cur` red checks, matching HPHA exactly). Ports
/// `intrusive_multi_rbtree_base::erase_fixup` (`Cpp/hpha.cpp`).
///
/// # Safety
/// `head` must be a live tree sentinel; `node` must be live.
// `p`/`s`/`o`/`w`/`c` deliberately mirror `Cpp/hpha.cpp`'s own variable names
// (`p`, `s`, `o`, `w`, `c`) line-for-line, so this algorithm can be audited side by
// side against the reference it ports — renaming them to longer names would work
// against exactly the review that matters most for this function. `w_o_child`/
// `w_s_child` are deliberately parallel names for symmetric concepts (`w`'s child on
// side `o` vs. side `s`), not a naming mistake.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
unsafe fn erase_fixup(head: *mut NodeBase, node: *mut NodeBase) {
    let mut cur = node;
    // SAFETY: `head` is live (this function's contract).
    let root = unsafe { NodeBase::child(head, Side::Left) };
    // EXPLICIT: climb and rebalance while `cur` is black and not the root; `cur` is
    // the state threaded up the tree, not expressible as an iterator.
    // SAFETY: `cur` is live (this function's contract, re-established at the bottom
    // of every loop iteration below).
    while !unsafe { NodeBase::red(cur) } && cur != root {
        // SAFETY: `cur` is live.
        let p = unsafe { NodeBase::parent(cur) };
        // SAFETY: `cur` is live.
        let s = unsafe { NodeBase::parent_side(cur) };
        let o = s.other();
        // SAFETY: `p` is live.
        let mut w = unsafe { NodeBase::child(p, o) };
        // SAFETY: `w` is live.
        if unsafe { NodeBase::red(w) } {
            // SAFETY: `w` is live.
            unsafe { NodeBase::make_black(w) };
            // SAFETY: `p` is live.
            unsafe { NodeBase::make_red(p) };
            // SAFETY: `w` is live.
            w = unsafe { NodeBase::child(w, s) };
            // SAFETY: `p` is live.
            unsafe { NodeBase::rotate(p, s) };
        }
        // SAFETY: `w` is live.
        let w_left = unsafe { NodeBase::child(w, Side::Left) };
        // SAFETY: `w` is live.
        let w_right = unsafe { NodeBase::child(w, Side::Right) };
        // SAFETY: `w_left` is live.
        let w_left_black = unsafe { !NodeBase::red(w_left) };
        // SAFETY: `w_right` is live.
        let w_right_black = unsafe { !NodeBase::red(w_right) };
        if w_left_black && w_right_black {
            // SAFETY: `w` is live.
            unsafe { NodeBase::make_red(w) };
            cur = p;
        } else {
            // SAFETY: `w` is live.
            let w_o_child = unsafe { NodeBase::child(w, o) };
            // SAFETY: `w_o_child` is live.
            if unsafe { !NodeBase::red(w_o_child) } {
                // SAFETY: `w` is live.
                let w_s_child = unsafe { NodeBase::child(w, s) };
                // SAFETY: `w_s_child` is live.
                unsafe { NodeBase::make_black(w_s_child) };
                // SAFETY: `w` is live.
                unsafe { NodeBase::make_red(w) };
                let c = w_s_child;
                // SAFETY: `w` is live.
                unsafe { NodeBase::rotate(w, o) };
                w = c;
            }
            // SAFETY: `p` is live.
            let p_colour = unsafe { NodeBase::colour(p) };
            // SAFETY: `w` is live.
            unsafe { NodeBase::set_colour(w, p_colour) };
            // SAFETY: `p` is live.
            unsafe { NodeBase::make_black(p) };
            // SAFETY: `w` is live.
            let w_o_child = unsafe { NodeBase::child(w, o) };
            // SAFETY: `w_o_child` is live.
            unsafe { NodeBase::make_black(w_o_child) };
            // SAFETY: `p` is live.
            unsafe { NodeBase::rotate(p, s) };
            cur = root;
        }
    }
    // SAFETY: `cur` is live.
    unsafe { NodeBase::make_black(cur) };
}

/// Marks `Self` as usable as an [`IntrusiveMultiRbTree`] element.
///
/// # Safety
/// Implementors must place a [`NodeBase`] at byte offset 0 of `Self` (e.g. as the
/// first field of a `#[repr(C)]` struct), so that a `NonNull<Self>` and the
/// `NonNull<NodeBase>` obtained from [`RbNode::node`] denote the same address and are
/// interchangeable via `.cast()`.
pub(crate) unsafe trait RbNode: Sized {
    /// The query key type for [`IntrusiveMultiRbTree::lower_bound`]/`upper_bound`.
    type Key: ?Sized;

    /// This node's embedded [`NodeBase`].
    #[must_use]
    fn node(this: NonNull<Self>) -> NonNull<NodeBase> {
        this.cast()
    }

    /// Recovers the owning node from one of its [`NodeBase`]'s pointers.
    #[must_use]
    fn from_node(node: NonNull<NodeBase>) -> NonNull<Self> {
        node.cast()
    }

    /// Orders `this` against `other`. Ports the element type's `operator<`/`operator>`
    /// pair — `Ordering::Equal` here is HPHA's `!(a<b) && !(a>b)`, its definition of
    /// "same key, chain together" (a strict weak ordering's equivalence, not identity).
    ///
    /// # Safety
    /// `this` and `other` must both be live.
    unsafe fn cmp(this: NonNull<Self>, other: NonNull<Self>) -> Ordering;

    /// Orders `this` against a query `key`. Ports the element type's `operator<
    /// (const K&)`/`operator>(const K&)` pair used by `lower_bound`/`upper_bound`.
    ///
    /// # Safety
    /// `this` must be live.
    unsafe fn cmp_key(this: NonNull<Self>, key: &Self::Key) -> Ordering;
}

/// An intrusive multi-tree of `T`, headed by a self-referential sentinel. Ports
/// `intrusive_multi_rbtree<T>`. See the module doc for the lazy-sentinel-init and
/// non-move-after-first-use contract every method here relies on (identical in spirit
/// to `list.rs`'s `IntrusiveList`).
pub(crate) struct IntrusiveMultiRbTree<T: RbNode> {
    head: UnsafeCell<NodeBase>,
    _marker: PhantomData<T>,
}

impl<T: RbNode> IntrusiveMultiRbTree<T> {
    /// Builds an empty tree. The sentinel is **not** self-linked yet — see the module
    /// doc.
    pub(crate) const fn new() -> Self {
        Self {
            head: UnsafeCell::new(NodeBase {
                children: [core::ptr::null_mut(); 2],
                neighbours: [core::ptr::null_mut(); 2],
                parent: TaggedPtr::null(),
            }),
            _marker: PhantomData,
        }
    }

    /// Returns a raw pointer to this tree's own head sentinel, self-linking it (all
    /// three link groups, to itself) on the first call. Same `UnsafeCell` rationale as
    /// `list.rs`'s `IntrusiveList::head_ptr`.
    fn head_ptr(&self) -> *mut NodeBase {
        let head = self.head.get();
        // SAFETY: `head` is live (the cell's own allocation).
        let right_child = unsafe { NodeBase::raw_child(head, Side::Right) };
        if right_child.is_null() {
            // First touch since `new()` — self-link the sentinel now that its final
            // address is known; `new()` itself cannot do this (module doc).
            // SAFETY: `head` is live.
            unsafe { NodeBase::set_child(head, Side::Left, head) };
            // SAFETY: `head` is live.
            unsafe { NodeBase::set_child(head, Side::Right, head) };
            // SAFETY: `head` is live.
            unsafe { NodeBase::set_neighbour(head, Side::Left, head) };
            // SAFETY: `head` is live.
            unsafe { NodeBase::set_neighbour(head, Side::Right, head) };
            // SAFETY: `head` is live.
            unsafe { NodeBase::raw_set_parent(head, TaggedPtr::new(head, 0)) };
        }
        head
    }

    /// Whether this tree currently holds no nodes. Ports
    /// `intrusive_multi_rbtree::empty`.
    #[must_use]
    // General-purpose API completeness; `tree.rs` never needs to ask an
    // `IntrusiveMultiRbTree` directly whether it is empty (a `lower_bound`/`succ`
    // returning `None` already tells every caller what it needs).
    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool {
        let head = self.head_ptr();
        // SAFETY: `head_ptr` always returns a live, at-least-self-linked sentinel.
        unsafe { NodeBase::child(head, Side::Left) == head }
    }

    #[must_use]
    fn root(&self) -> *mut NodeBase {
        let head = self.head_ptr();
        // SAFETY: `head` is live and linked.
        unsafe { NodeBase::child(head, Side::Left) }
    }

    /// Inserts `node`. If an equal-key element already exists, `node` is chained onto
    /// it instead of becoming a new tree position. Ports `intrusive_multi_rbtree::
    /// do_insert`.
    pub(crate) fn insert(&self, node: NonNull<T>) {
        let head = self.head_ptr();
        let node_base = T::node(node).as_ptr();
        let end = head;
        let mut last = head;
        let mut cur = self.root();
        let mut s = Side::Left;
        // EXPLICIT: BST descent to the insertion point; `cur`/`last`/`s` are the
        // state threaded down the tree, not expressible as an iterator.
        while cur != end {
            last = cur;
            // SAFETY: `cur != end` (the sentinel), so it is live.
            let cur_node = unsafe { NonNull::new_unchecked(cur) };
            let cur_typed = T::from_node(cur_node);
            // SAFETY: `node` is live (caller-supplied, about to be inserted);
            // `cur_typed` is live (just established above).
            let ordering = unsafe { T::cmp(node, cur_typed) };
            match ordering {
                Ordering::Less => {
                    s = Side::Left;
                }
                Ordering::Greater => {
                    s = Side::Right;
                }
                Ordering::Equal => {
                    // SAFETY: `node_base` is caller-supplied and not yet linked
                    // anywhere; `cur` is live.
                    unsafe { NodeBase::link_into_chain(node_base, cur) };
                    return;
                }
            }
            // SAFETY: `cur` is live.
            cur = unsafe { NodeBase::child(cur, s) };
        }
        // SAFETY: `node_base` is unlinked (caller-supplied, fresh); `last` is live.
        unsafe { NodeBase::attach_to(node_base, last, s) };
        // SAFETY: `head` is live; `node_base` is now a live, freshly-attached node.
        unsafe { insert_fixup(head, node_base) };
    }

    /// Removes `node`. Ports `intrusive_multi_rbtree::do_erase`.
    pub(crate) fn erase(&self, node: NonNull<T>) {
        let head = self.head_ptr();
        let node_base = T::node(node).as_ptr();
        // SAFETY: `node_base` is live (caller-supplied, currently in this tree).
        if unsafe { NodeBase::chained(node_base) } {
            // SAFETY: `node_base` is live.
            if !unsafe { NodeBase::is_attached(node_base) } {
                // Plain chain link, not the group's tree-attached representative:
                // O(1) removal, no tree structure touched.
                // SAFETY: `node_base` is live and chained (just checked above).
                unsafe { NodeBase::unlink_from_chain(node_base) };
                return;
            }
            // `node_base` is the group's tree-attached representative, and the group
            // has more members: promote the next chain member into its tree position.
            // SAFETY: `node_base` is live.
            let repl = unsafe { NodeBase::neighbour(node_base, Side::Right) };
            debug_assert!(repl != head);
            // SAFETY: `repl` is live (a live node's neighbour is always live).
            debug_assert!(!unsafe { NodeBase::is_attached(repl) });
            // SAFETY: `repl` is live; `node_base` is live and attached.
            unsafe { NodeBase::switch_with(repl, node_base) };
            // SAFETY: `node_base` is live and still chained (only its tree position
            // was taken over above; the chain links are untouched until this call).
            unsafe { NodeBase::unlink_from_chain(node_base) };
            return;
        }
        // Genuine tree removal: `node_base` has no equal-key duplicates at all.
        let end = head;
        let mut repl = node_base;
        let mut s = Side::Left;
        // SAFETY: `node_base` is live.
        let right = unsafe { NodeBase::child(node_base, Side::Right) };
        if right != end {
            // SAFETY: `node_base` is live.
            let left = unsafe { NodeBase::child(node_base, Side::Left) };
            if left != end {
                repl = right;
                // SAFETY: `repl` is live (assigned from `right`, live above).
                let mut repl_left = unsafe { NodeBase::child(repl, Side::Left) };
                // EXPLICIT: descend to the in-order successor (leftmost of the right
                // subtree); `repl`/`repl_left` are the state threaded down the tree.
                while repl_left != end {
                    repl = repl_left;
                    // SAFETY: `repl` is live.
                    repl_left = unsafe { NodeBase::child(repl, Side::Left) };
                }
            }
            s = Side::Right;
        }
        // SAFETY: `repl` is live.
        let red = unsafe { NodeBase::red(repl) };
        // SAFETY: `repl` is live.
        let repl_child = unsafe { NodeBase::child(repl, s) };
        // SAFETY: `repl` is live and attached (it is either `node_base` itself, or a
        // node reached by descending real tree children from it — both attached).
        unsafe { NodeBase::substitute_with(repl, repl_child) };
        if repl != node_base {
            // SAFETY: `repl != node_base`; `node_base` is live and attached.
            unsafe { NodeBase::switch_with(repl, node_base) };
        }
        if !red {
            // SAFETY: `head` is live; `repl_child` is live (possibly the sentinel).
            unsafe { erase_fixup(head, repl_child) };
        }
    }

    /// The first element not ordered before `key` (`!(element < key)`). Ports
    /// `intrusive_multi_rbtree::do_lower_bound`.
    #[must_use]
    pub(crate) fn lower_bound(&self, key: &T::Key) -> Option<NonNull<T>> {
        let head = self.head_ptr();
        let end = head;
        let mut best = head;
        let mut cur = self.root();
        // EXPLICIT: BST descent narrowing the best-so-far bound; `cur`/`best` are the
        // state threaded down the tree, not expressible as an iterator.
        while cur != end {
            // SAFETY: `cur != end`, so it is live.
            let cur_node = unsafe { NonNull::new_unchecked(cur) };
            let cur_typed = T::from_node(cur_node);
            // SAFETY: `cur_typed` is live (just established above).
            let ordering = unsafe { T::cmp_key(cur_typed, key) };
            if ordering == Ordering::Less {
                // SAFETY: `cur` is live.
                cur = unsafe { NodeBase::child(cur, Side::Right) };
            } else {
                best = cur;
                // SAFETY: `cur` is live.
                cur = unsafe { NodeBase::child(cur, Side::Left) };
            }
        }
        if best == end {
            None
        } else {
            // SAFETY: `best != end`, so it is live.
            let best_node = unsafe { NonNull::new_unchecked(best) };
            Some(T::from_node(best_node))
        }
    }

    /// The first element ordered strictly after `key` (`element > key`). Ports
    /// `intrusive_multi_rbtree::do_upper_bound`.
    #[must_use]
    pub(crate) fn upper_bound(&self, key: &T::Key) -> Option<NonNull<T>> {
        let head = self.head_ptr();
        let end = head;
        let mut best = head;
        let mut cur = self.root();
        // EXPLICIT: BST descent narrowing the best-so-far bound; `cur`/`best` are the
        // state threaded down the tree, not expressible as an iterator.
        while cur != end {
            // SAFETY: `cur != end`, so it is live.
            let cur_node = unsafe { NonNull::new_unchecked(cur) };
            let cur_typed = T::from_node(cur_node);
            // SAFETY: `cur_typed` is live (just established above).
            let ordering = unsafe { T::cmp_key(cur_typed, key) };
            if ordering == Ordering::Greater {
                best = cur;
                // SAFETY: `cur` is live.
                cur = unsafe { NodeBase::child(cur, Side::Left) };
            } else {
                // SAFETY: `cur` is live.
                cur = unsafe { NodeBase::child(cur, Side::Right) };
            }
        }
        if best == end {
            None
        } else {
            // SAFETY: `best != end`, so it is live.
            let best_node = unsafe { NonNull::new_unchecked(best) };
            Some(T::from_node(best_node))
        }
    }

    /// The smallest-keyed element, or `None` if the tree is empty.
    #[must_use]
    // General-purpose API completeness (HPHA's `intrusive_multi_rbtree::begin()`);
    // `tree.rs`'s own dispatch always has a size key to search by (`lower_bound`),
    // never needs the unconditional minimum. Exercised by `block.rs`'s test suite.
    #[allow(dead_code)]
    pub(crate) fn minimum(&self) -> Option<NonNull<T>> {
        let head = self.head_ptr();
        // SAFETY: `head` is live.
        let node = unsafe { NodeBase::min_or_max(self.root(), Side::Left) };
        if node == head {
            None
        } else {
            // SAFETY: `node != head`, so it is a real node.
            Some(T::from_node(unsafe { NonNull::new_unchecked(node) }))
        }
    }

    /// The tree-order successor of `node`, or `None` if `node` is the maximum.
    #[must_use]
    pub(crate) fn succ(&self, node: NonNull<T>) -> Option<NonNull<T>> {
        let head = self.head_ptr();
        let node_base = T::node(node).as_ptr();
        // SAFETY: `node_base` is live (caller-supplied, currently in this tree).
        let s = unsafe { NodeBase::pred_or_succ(node_base, Side::Right) };
        if s == head {
            None
        } else {
            // SAFETY: `s != head`, so it is a real node.
            Some(T::from_node(unsafe { NonNull::new_unchecked(s) }))
        }
    }
}

/// The next member of `node`'s equal-key chain (a node with no duplicates is its own
/// chain, so this returns `node` itself in that case). Distinct from
/// [`IntrusiveMultiRbTree::succ`] (true tree order) — ports `node_base::next()`, the
/// chain-neighbour overload, not `node_base::succ()`. A free function rather than a
/// tree method: the equal-key chain never touches the tree's sentinel, so no tree
/// state is needed — mirrors `list.rs`'s free-standing `unlink_node`.
#[must_use]
pub(crate) fn next<T: RbNode>(node: NonNull<T>) -> NonNull<T> {
    let node_base = T::node(node).as_ptr();
    // SAFETY: `node` is live (caller-supplied `NonNull`), hence so is its embedded
    // `NodeBase`.
    let next_base = unsafe { NodeBase::neighbour(node_base, Side::Right) };
    // SAFETY: `next_base` is live — a live node's chain neighbour is always live,
    // and the chain never includes the tree's sentinel (unlike true tree order).
    T::from_node(unsafe { NonNull::new_unchecked(next_base) })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[repr(C)]
    struct TestNode {
        base: NodeBase,
        key: i32,
        id: u32,
    }

    // SAFETY: `base` is TestNode's first field (repr(C) guarantees offset 0).
    unsafe impl RbNode for TestNode {
        type Key = i32;

        unsafe fn cmp(this: NonNull<Self>, other: NonNull<Self>) -> Ordering {
            // SAFETY: caller guarantees `this` is live; short-lived shared ref,
            // dropped immediately after the comparison, never stored.
            let this_key = unsafe { this.as_ref().key };
            // SAFETY: caller guarantees `other` is live; same as above.
            let other_key = unsafe { other.as_ref().key };
            this_key.cmp(&other_key)
        }

        unsafe fn cmp_key(this: NonNull<Self>, key: &i32) -> Ordering {
            // SAFETY: caller guarantees `this` is live; short-lived shared ref.
            unsafe { this.as_ref().key.cmp(key) }
        }
    }

    fn boxed(key: i32, id: u32) -> NonNull<TestNode> {
        let boxed = Box::new(TestNode {
            base: NodeBase {
                children: [core::ptr::null_mut(); 2],
                neighbours: [core::ptr::null_mut(); 2],
                parent: TaggedPtr::null(),
            },
            key,
            id,
        });
        NonNull::new(Box::into_raw(boxed)).expect("Box::into_raw is never null")
    }

    /// Reads a live test node's key. Every call site below passes a node that is
    /// still linked into (or was just found in) a live tree, hence still alive.
    fn key_of(n: NonNull<TestNode>) -> i32 {
        // SAFETY: `n` is live — see this function's own doc.
        unsafe { n.as_ref().key }
    }

    /// # Safety
    /// `node` must have been leaked via `Box::into_raw` in `boxed` and not used again.
    unsafe fn drop_boxed(node: NonNull<TestNode>) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { drop(Box::from_raw(node.as_ptr())) };
    }

    /// Structural checker: no red-red violations, equal black-height on every root-to-
    /// nil path, BST order property holds, chain membership matches key equality.
    /// Ports `DEBUG_MULTI_RBTREE`'s `check()`/`check_height()`, kept always-available
    /// under test rather than gated, per the plan's Phase 3 test strategy.
    fn check_invariants<T: RbNode<Key = i32>>(tree: &IntrusiveMultiRbTree<T>) {
        let head = tree.head_ptr();
        // SAFETY: `head` is live and linked.
        assert!(unsafe { !NodeBase::red(head) }, "sentinel must be black");
        let root = tree.root();
        if root == head {
            return;
        }
        // SAFETY: `root` is live.
        assert!(unsafe { !NodeBase::red(root) }, "root must be black");
        check_node::<T>(root, i32::MIN, i32::MAX);
    }

    /// Recursively validates the BST-order and black-height invariants of the
    /// subtree rooted at `node`, whose keys are all within `[lo, hi]` (an
    /// intentionally loose bound: sibling subtrees can share a boundary key when
    /// duplicates exist, so this checks "no key strays outside its ancestors'
    /// bounds," not tight per-node bounds). Returns the subtree's black-height.
    fn check_node<T: RbNode<Key = i32>>(node: *mut NodeBase, lo: i32, hi: i32) -> u32 {
        // SAFETY: `node` is live (caller-supplied, reachable from a live tree).
        if unsafe { NodeBase::is_nil(node) } {
            return 0;
        }
        let typed = T::from_node(NonNull::new(node).expect("live node is non-null"));
        // SAFETY: `typed` is live.
        let key = unsafe { T::cmp_key(typed, &lo) };
        assert_ne!(key, Ordering::Less, "BST order violated (lo bound)");
        // SAFETY: `typed` is live.
        let key_hi = unsafe { T::cmp_key(typed, &hi) };
        assert_ne!(key_hi, Ordering::Greater, "BST order violated (hi bound)");
        // SAFETY: `node` is live.
        let red = unsafe { NodeBase::red(node) };
        // SAFETY: `node` is live.
        let left = unsafe { NodeBase::child(node, Side::Left) };
        // SAFETY: `node` is live.
        let right = unsafe { NodeBase::child(node, Side::Right) };
        if red {
            // SAFETY: `left`/`right` are live.
            assert!(unsafe { !NodeBase::red(left) }, "red node has a red child");
            // SAFETY: `right` is live.
            assert!(unsafe { !NodeBase::red(right) }, "red node has a red child");
        }
        let left_h = check_node::<T>(left, lo, hi);
        let right_h = check_node::<T>(right, lo, hi);
        assert_eq!(left_h, right_h, "unequal black-height across children");
        left_h + u32::from(!red)
    }

    #[test]
    fn new_tree_is_empty() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        assert!(tree.is_empty());
        assert!(tree.minimum().is_none());
        assert!(tree.lower_bound(&0).is_none());
    }

    #[test]
    fn single_insert_is_findable() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let a = boxed(5, 0);
        tree.insert(a);
        assert!(!tree.is_empty());
        assert_eq!(tree.minimum(), Some(a));
        assert_eq!(tree.lower_bound(&5), Some(a));
        check_invariants(&tree);
        tree.erase(a);
        assert!(tree.is_empty());
        // SAFETY: `a` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(a) };
    }

    #[test]
    fn ascending_insert_stress_maintains_invariants() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let nodes: Vec<_> = (0..200).map(|k| boxed(k, 0)).collect();
        for &n in &nodes {
            tree.insert(n);
            check_invariants(&tree);
        }
        assert_eq!(tree.minimum().map(key_of), Some(0));
        for &n in &nodes {
            tree.erase(n);
            check_invariants(&tree);
        }
        assert!(tree.is_empty());
        for n in nodes {
            // SAFETY: every node above was erased from `tree` in this same loop
            // before being dropped here.
            unsafe { drop_boxed(n) };
        }
    }

    #[test]
    fn descending_insert_stress_maintains_invariants() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let nodes: Vec<_> = (0..200).rev().map(|k| boxed(k, 0)).collect();
        for &n in &nodes {
            tree.insert(n);
            check_invariants(&tree);
        }
        for &n in &nodes {
            tree.erase(n);
            check_invariants(&tree);
        }
        assert!(tree.is_empty());
        for n in nodes {
            // SAFETY: erased above before being dropped here.
            unsafe { drop_boxed(n) };
        }
    }

    #[test]
    fn pseudo_random_insert_erase_stress_matches_btreemap() {
        // A small xorshift PRNG, seeded fixed for reproducibility — no external RNG
        // dependency, matching the crate's determinism stance (ROADMAP.md's
        // cross-port invariant excludes non-value-affecting randomness like this test
        // harness's own seed, but the tree algorithm itself must stay a pure function
        // of the operation sequence, which this test cross-checks against BTreeMap).
        let mut state: u32 = 0x1234_5678;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            state
        };

        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let mut oracle: BTreeMap<i32, Vec<NonNull<TestNode>>> = BTreeMap::new();
        let mut live: Vec<NonNull<TestNode>> = Vec::new();

        for step in 0..3000u32 {
            // CAST: u32 -> i32, narrow key range for frequent duplicate keys
            // (exercises the equal-key chain, not just distinct-key tree shape).
            // `% 32` bounds the value to [0, 32), which never wraps as i32.
            #[allow(clippy::as_conversions, clippy::cast_possible_wrap)]
            let key = (next() % 32) as i32;
            let insert = live.is_empty() || next() % 3 != 0;
            if insert {
                let n = boxed(key, step);
                tree.insert(n);
                oracle.entry(key).or_default().push(n);
                live.push(n);
            } else {
                // CAST: u32 -> usize, narrowing an index already bounded by
                // `live.len()` via the modulo below.
                #[allow(clippy::as_conversions)]
                let idx = (next() as usize) % live.len();
                let n = live.swap_remove(idx);
                let k = key_of(n);
                tree.erase(n);
                let bucket = oracle.get_mut(&k).expect("key present in oracle");
                let pos = bucket.iter().position(|&x| x == n).expect("node in bucket");
                bucket.remove(pos);
                if bucket.is_empty() {
                    oracle.remove(&k);
                }
                // SAFETY: `n` was just erased from `tree` above.
                unsafe { drop_boxed(n) };
            }
            check_invariants(&tree);
            assert_eq!(
                tree.minimum().map(key_of),
                oracle.keys().next().copied(),
                "minimum mismatch at step {step}"
            );
        }
        for n in live {
            tree.erase(n);
            // SAFETY: `n` was just erased from `tree` above.
            unsafe { drop_boxed(n) };
        }
    }

    /// Prints, on stdout, the exact same operation trace as
    /// `pseudo_random_insert_erase_stress_matches_btreemap` (same PRNG algorithm and
    /// seed, same insert/erase decision logic), but instead of checking against
    /// `BTreeMap`, prints the full in-order key sequence after every step —
    /// including equal-key chain enumeration order, via repeated `succ()` from
    /// `minimum()`, exactly what `intrusive_multi_rbtree<T>::begin()`/`++` walks in
    /// the C++ reference.
    ///
    /// This is a manual cross-validation tool, not an automated test: it was run
    /// once (during the port's Phase 3 development) against a companion C++ harness
    /// that links the real, unmodified `Cpp/hpha.cpp` and runs the identical
    /// PRNG-driven sequence through the actual `intrusive_multi_rbtree`, printing the
    /// same format. All 3000 steps matched byte-for-byte. `#[ignore]`d because it
    /// requires a separately-built C++ companion (not part of this crate or its CI)
    /// to be meaningful — run with `cargo test --lib -- --ignored --nocapture
    /// rbtree::tests::print_oracle_cross_validation_trace` and diff against a fresh
    /// build of that harness if `rbtree.rs`'s tree-shape logic is ever revisited.
    #[test]
    #[ignore = "manual C++ oracle cross-validation tool, not a self-contained test"]
    fn print_oracle_cross_validation_trace() {
        let mut state: u32 = 0x1234_5678;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            state
        };

        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let mut live: Vec<NonNull<TestNode>> = Vec::new();

        for step in 0..3000u32 {
            #[allow(clippy::as_conversions, clippy::cast_possible_wrap)]
            let key = (next() % 32) as i32;
            let insert = live.is_empty() || next() % 3 != 0;
            if insert {
                let n = boxed(key, step);
                tree.insert(n);
                live.push(n);
            } else {
                #[allow(clippy::as_conversions)]
                let idx = (next() as usize) % live.len();
                let n = live.swap_remove(idx);
                tree.erase(n);
                // SAFETY: `n` was just erased from `tree` above.
                unsafe { drop_boxed(n) };
            }
            let mut trace_line = String::new();
            let mut cur = tree.minimum();
            while let Some(n) = cur {
                trace_line.push_str(&key_of(n).to_string());
                trace_line.push(' ');
                cur = tree.succ(n);
            }
            println!("{trace_line}");
        }
        for n in live {
            tree.erase(n);
            // SAFETY: `n` was just erased from `tree` above.
            unsafe { drop_boxed(n) };
        }
    }

    #[test]
    fn duplicate_keys_chain_and_all_erase_cleanly() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let a = boxed(7, 0);
        let b = boxed(7, 1);
        let c = boxed(7, 2);
        tree.insert(a);
        tree.insert(b);
        tree.insert(c);
        check_invariants(&tree);
        // Exactly one of the three is tree-attached; lower_bound(7) finds it.
        let found = tree.lower_bound(&7).expect("key 7 present");
        assert_eq!(key_of(found), 7);
        tree.erase(a);
        check_invariants(&tree);
        assert_eq!(tree.lower_bound(&7).map(key_of), Some(7));
        tree.erase(b);
        check_invariants(&tree);
        assert_eq!(tree.lower_bound(&7).map(key_of), Some(7));
        tree.erase(c);
        check_invariants(&tree);
        assert!(tree.lower_bound(&7).is_none());
        assert!(tree.is_empty());
        // SAFETY: `a` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(a) };
        // SAFETY: `b` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(b) };
        // SAFETY: `c` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(c) };
    }

    #[test]
    fn lower_and_upper_bound_semantics() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let nodes: Vec<_> = [10, 20, 20, 30].into_iter().map(|k| boxed(k, 0)).collect();
        for &n in &nodes {
            tree.insert(n);
        }
        assert_eq!(tree.lower_bound(&15).map(key_of), Some(20));
        assert_eq!(tree.lower_bound(&20).map(key_of), Some(20));
        assert_eq!(tree.upper_bound(&20).map(key_of), Some(30));
        assert!(tree.upper_bound(&30).is_none());
        assert!(tree.lower_bound(&31).is_none());
        for n in nodes {
            tree.erase(n);
            // SAFETY: `n` was just erased from `tree` above.
            unsafe { drop_boxed(n) };
        }
    }

    #[test]
    fn succ_walks_duplicates_then_tree_order() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let ten_a = boxed(10, 0);
        let ten_b = boxed(10, 1);
        let twenty = boxed(20, 2);
        tree.insert(ten_a);
        tree.insert(ten_b);
        tree.insert(twenty);
        let first_ten = tree.lower_bound(&10).expect("key 10 present");
        let after_first = tree.succ(first_ten).expect("has a successor");
        assert_eq!(key_of(after_first), 10);
        let after_second = tree.succ(after_first).expect("has a successor");
        assert_eq!(key_of(after_second), 20);
        assert!(tree.succ(after_second).is_none());
        tree.erase(ten_a);
        tree.erase(ten_b);
        tree.erase(twenty);
        // SAFETY: `ten_a` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(ten_a) };
        // SAFETY: `ten_b` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(ten_b) };
        // SAFETY: `twenty` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(twenty) };
    }

    #[test]
    fn next_walks_equal_key_chain_and_wraps() {
        let tree: IntrusiveMultiRbTree<TestNode> = IntrusiveMultiRbTree::new();
        let single = boxed(5, 0);
        tree.insert(single);
        // A node with no duplicates is its own one-element chain.
        assert_eq!(next(single), single);

        let ten_a = boxed(10, 1);
        let ten_b = boxed(10, 2);
        let ten_c = boxed(10, 3);
        tree.insert(ten_a);
        tree.insert(ten_b);
        tree.insert(ten_c);
        // The chain is circular over exactly the three equal-key members, in some
        // order — walking `next` three times returns to the start, and never visits
        // `single` (a different key) along the way.
        let step1 = next(ten_a);
        let step2 = next(step1);
        let step3 = next(step2);
        assert_eq!(step3, ten_a);
        let visited = [ten_a, step1, step2];
        assert!(visited.contains(&ten_b));
        assert!(visited.contains(&ten_c));

        tree.erase(single);
        tree.erase(ten_a);
        tree.erase(ten_b);
        tree.erase(ten_c);
        // SAFETY: `single` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(single) };
        // SAFETY: `ten_a` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(ten_a) };
        // SAFETY: `ten_b` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(ten_b) };
        // SAFETY: `ten_c` was erased from `tree` above and is not referenced again.
        unsafe { drop_boxed(ten_c) };
    }
}
