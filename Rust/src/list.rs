// SPDX-License-Identifier: MIT OR Apache-2.0
//! Intrusive, circular, doubly-linked list with a self-referential sentinel head.
//!
//! Ports `Cpp/hpha.h`'s `intrusive_list_base`/`intrusive_list<T>` — used for the
//! bucket allocator's per-bucket page list and the tree allocator's small-free-block
//! list. A node's link fields live inside the node itself (no separate allocation per
//! list membership); `T` embeds a [`ListLink`] as its first field so a `ListLink`
//! pointer and a `T` pointer are the same address (see [`ListNode`]).
//!
//! # Lazy sentinel initialization
//! [`IntrusiveList::new`] cannot self-link its `head` sentinel the way HPHA's C++
//! constructor does: computing `&self.head` before `self` is at its final resting
//! place is not expressible in Rust (a `const fn` returning `Self` by value has no
//! stable address to take yet, and even a non-`const fn` returning `Self` by value
//! would compute the wrong address if the caller's binding later moves the returned
//! value). Every method instead calls [`IntrusiveList::head_ptr`], which self-links
//! `head` on its *first* call — by then the list is already wherever the caller
//! placed it, since the caller had to form a reference to call the method at all.
//! **Callers must not move an `IntrusiveList` after the first call to any of its
//! methods** — the same implicit constraint HPHA's C++ objects already have (C++
//! never defines a move constructor for this type either); this just makes the
//! constraint explicit instead of leaving it a silent, undocumented assumption.
//!
//! # Why `head` is an `UnsafeCell`
//! A self-linked sentinel's whole point is that the pointer value written into
//! `head.prev`/`head.next` on the *first* call stays validly dereferenceable on every
//! *later*, separate call. A bare field pointer obtained via `&mut self` does not have
//! that property under Tree Borrows: each new `&mut self` at the top of a later method
//! call is a fresh reborrow, and Miri (`-Zmiri-tree-borrows`) catches the earlier
//! call's persisted pointer as a real "write through a since-frozen tag" violation —
//! confirmed empirically while building this module, not a theoretical concern.
//! Wrapping `head` in `UnsafeCell<ListLink>` and reaching it only through
//! `UnsafeCell::get` (a raw pointer rooted in the cell's own allocation, not in any
//! particular `&self`/`&mut self` borrow) is the standard fix, and is why every method
//! here takes `&self` rather than `&mut self` — `Rust/CONVENTIONS.md`'s "Layout,
//! `MaybeUninit`, `UnsafeCell`" section anticipates exactly this pattern.

use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ptr::NonNull;

/// The embedded link fields of an intrusive list node. Ports `node_base`.
///
/// # Invariants
/// - [`ListLink::UNLINKED`] (both fields null) means "never touched" — distinct from
///   "linked to itself," which is what an empty list's self-linked head looks like
///   (both fields equal to the node's own address). That distinction is what makes
///   lazy self-init possible: a null `prev` is the "self-link me now" signal.
/// - Once linked (to itself, or into a real chain), both fields are always non-null.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI shared with orisnitsa's `extern struct` equivalent; frozen.
pub(crate) struct ListLink {
    /// The previous node in the circular chain (or `self`, if this is a self-linked
    /// sentinel/singleton). Byte offset 0 in every [`ListNode`] implementor.
    prev: *mut ListLink,
    /// The next node in the circular chain (or `self`, if this is a self-linked
    /// sentinel/singleton). Byte offset 8 in every [`ListNode`] implementor (64-bit).
    next: *mut ListLink,
}

impl ListLink {
    /// A node that has never been linked into any list.
    pub(crate) const UNLINKED: Self = Self {
        prev: core::ptr::null_mut(),
        next: core::ptr::null_mut(),
    };

    /// Reads `this`'s `next` link.
    ///
    /// # Safety
    /// `this` must point to a live, linked `ListLink`.
    #[must_use]
    pub(crate) unsafe fn next(this: *mut ListLink) -> *mut ListLink {
        // SAFETY: caller guarantees `this` is live; reads one field through a raw
        // pointer, forming no reference.
        unsafe { (*this).next }
    }

    /// Reads `this`'s `prev` link.
    ///
    /// # Safety
    /// `this` must point to a live, linked `ListLink`.
    #[must_use]
    // `next`'s symmetric counterpart, part of the faithful `intrusive_list_base`
    // port; no current caller in this crate needs a backward single-node step, but
    // it is legitimate general-purpose API, not scaffolding.
    #[allow(dead_code)]
    pub(crate) unsafe fn prev(this: *mut ListLink) -> *mut ListLink {
        // SAFETY: caller guarantees `this` is live; reads one field through a raw
        // pointer, forming no reference.
        unsafe { (*this).prev }
    }

    /// Removes `this` from whatever chain it is currently linked into.
    ///
    /// # Safety
    /// `this` must currently be linked (self-linked counts) — i.e. not
    /// [`ListLink::UNLINKED`] — and `this`'s `next`/`prev` must be live.
    pub(crate) unsafe fn unlink(this: *mut ListLink) {
        // Ports HPHA's `node_base::unlink`; for a self-linked singleton this
        // degenerates to `this.next = this.prev = this`, a harmless no-op splice.
        // SAFETY: caller guarantees `this` is linked; reads one field.
        let next = unsafe { (*this).next };
        // SAFETY: caller guarantees `this` is linked; reads one field.
        let prev = unsafe { (*this).prev };
        // SAFETY: `next` is `this`'s own `next` field, read live above; writes one field.
        unsafe { (*next).prev = prev };
        // SAFETY: `prev` is `this`'s own `prev` field, read live above; writes one field.
        unsafe { (*prev).next = next };
    }

    /// Links `this` into the chain immediately before `before`.
    ///
    /// # Safety
    /// `this` must not currently be part of any chain (freshly [`ListLink::UNLINKED`]
    /// or just [`ListLink::unlink`]ed). `before` must be live and linked (self-linked
    /// counts), and `before`'s `prev` must be live.
    pub(crate) unsafe fn link_before(this: *mut ListLink, before: *mut ListLink) {
        // SAFETY: caller guarantees `before` is live and linked; reads one field.
        let prev = unsafe { (*before).prev };
        // SAFETY: `this` is caller-guaranteed unlinked, so this write cannot corrupt a
        // chain it used to belong to; writes one field.
        unsafe { (*this).prev = prev };
        // SAFETY: same as above; writes one field.
        unsafe { (*this).next = before };
        // SAFETY: `before` is live and linked (caller guarantee); writes one field.
        unsafe { (*before).prev = this };
        // SAFETY: `prev` is live (`before`'s own `prev` field, read live above); writes
        // one field.
        unsafe { (*prev).next = this };
    }
}

const _: () = assert!(size_of::<ListLink>() == 2 * size_of::<usize>());

/// Marks `Self` as usable as an [`IntrusiveList`] element.
///
/// # Safety
/// Implementors must place a [`ListLink`] at byte offset 0 of `Self` (e.g. as the
/// first field of a `#[repr(C)]` struct), so that a `NonNull<Self>` and the
/// `NonNull<ListLink>` obtained from [`ListNode::link`] denote the same address and
/// are interchangeable via `.cast()`.
pub(crate) unsafe trait ListNode: Sized {
    /// This node's embedded link, as a `ListLink` pointer.
    #[must_use]
    fn link(this: NonNull<Self>) -> NonNull<ListLink> {
        this.cast()
    }

    /// Recovers the owning node from one of its link's pointers.
    #[must_use]
    fn from_link(link: NonNull<ListLink>) -> NonNull<Self> {
        link.cast()
    }
}

/// An intrusive circular doubly-linked list of `T`, headed by a self-referential
/// sentinel. Ports `intrusive_list<T>`. See the module doc for the lazy-sentinel-init
/// and non-move-after-first-use contract every method here relies on.
pub(crate) struct IntrusiveList<T: ListNode> {
    /// The sentinel node. Not part of any node's on-heap payload — this is the list
    /// container's own state, not frozen ABI — so it needs no `#[repr(C)]` offset
    /// contract, only the `UnsafeCell` wrapping described in the module doc.
    head: UnsafeCell<ListLink>,
    /// Zero-sized; ties this container to element type `T` without storing one.
    _marker: PhantomData<T>,
}

impl<T: ListNode> IntrusiveList<T> {
    /// Builds an empty list. The sentinel is **not** self-linked yet — see the module
    /// doc's "Lazy sentinel initialization" section.
    pub(crate) const fn new() -> Self {
        Self {
            head: UnsafeCell::new(ListLink::UNLINKED),
            _marker: PhantomData,
        }
    }

    /// Returns a raw pointer to this list's own head sentinel, self-linking it on the
    /// first call. See the module doc's "Why `head` is an `UnsafeCell`" section for
    /// why this takes `&self`, not `&mut self`.
    fn head_ptr(&self) -> *mut ListLink {
        // `UnsafeCell::get` roots `head`'s provenance in the cell's own allocation
        // rather than in this call's `&self` borrow, so the pointer stays valid to
        // dereference from arbitrarily many later, separate calls — unlike a plain
        // `&raw mut self.head` derived from `&mut self` (see the module doc).
        let head = self.head.get();
        // SAFETY: `head` is live (the cell's own allocation); reads one field.
        let prev = unsafe { (*head).prev };
        if prev.is_null() {
            // First touch since `new()` — self-link the sentinel now that its final
            // address is known; `new()` itself cannot do this (see module doc).
            // SAFETY: `head` is live; writes one field.
            unsafe { (*head).prev = head };
            // SAFETY: `head` is live; writes one field.
            unsafe { (*head).next = head };
        }
        head
    }

    /// A raw pointer to this list's sentinel — never a real node, only ever a
    /// traversal boundary. For manual traversal loops that mirror HPHA's own
    /// hand-rolled walks (e.g. [`IntrusiveList::contains`]).
    #[must_use]
    pub(crate) fn sentinel(&self) -> *mut ListLink {
        self.head_ptr()
    }

    /// Whether `target` (a candidate node's own link pointer) is currently linked
    /// into this list — an `O(n)` exhaustive scan, never on any hot path. Exists
    /// for [`crate::bucket::Buckets::ptr_in_bucket`]'s debug-only verification of
    /// its own fast-path marker check, mirroring HPHA's `ptr_in_bucket`'s own
    /// `#ifndef NDEBUG` exhaustive-search assertion.
    #[must_use]
    pub(crate) fn contains(&self, target: *mut ListLink) -> bool {
        let sentinel = self.sentinel();
        let mut cur = sentinel;
        // EXPLICIT: raw-pointer chase instead of an iterator — same reasoning as
        // `manual_traversal_visits_all_nodes_in_order`'s test-only walk; `cur` is
        // the state, not expressible as an iterator over an intrusive list's raw
        // links.
        loop {
            // SAFETY: `cur` starts at the sentinel (live, linked per `head_ptr`'s
            // guarantee) and is advanced only to further live links reachable from
            // it — every node in a well-formed list is live for as long as the
            // list itself is not concurrently mutated, true here since this method
            // takes `&self`, not `&mut self`.
            cur = unsafe { ListLink::next(cur) };
            if cur == sentinel {
                return false;
            }
            if cur == target {
                return true;
            }
        }
    }

    /// Whether this list currently holds no real nodes. Ports
    /// `intrusive_list::empty`.
    #[must_use]
    // General-purpose API completeness (HPHA's `intrusive_list::empty`); no current
    // caller needs it — `Bucket`/`Buckets` check emptiness via `Page::is_empty`
    // (slot use-count), not list emptiness.
    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool {
        let head = self.head_ptr();
        // SAFETY: `head_ptr` always returns a live, at-least-self-linked sentinel.
        unsafe { ListLink::next(head) == head }
    }

    /// Inserts `node` at the front of the list. `node` must not currently be linked
    /// into any list.
    pub(crate) fn push_front(&self, node: NonNull<T>) {
        let head = self.head_ptr();
        let node_link = T::link(node).as_ptr();
        // SAFETY: `head_ptr` guarantees `head` is live and linked, so `head`'s `next`
        // is live; caller guarantees `node` is not currently linked anywhere.
        let first = unsafe { ListLink::next(head) };
        // SAFETY: `first` (live, linked per the above) is a valid `link_before` target;
        // `node_link` is unlinked per this method's own contract.
        unsafe { ListLink::link_before(node_link, first) };
    }

    /// Inserts `node` at the back of the list. `node` must not currently be linked
    /// into any list.
    pub(crate) fn push_back(&self, node: NonNull<T>) {
        let head = self.head_ptr();
        let node_link = T::link(node).as_ptr();
        // SAFETY: `head` is live and linked (`head_ptr`'s guarantee); `node_link` is
        // unlinked per this method's own contract.
        unsafe { ListLink::link_before(node_link, head) };
    }

    /// The first node, or `None` if the list is empty.
    #[must_use]
    pub(crate) fn front(&self) -> Option<NonNull<T>> {
        let head = self.head_ptr();
        // SAFETY: `head_ptr` guarantees `head` is live and linked.
        let first = unsafe { ListLink::next(head) };
        if first == head {
            return None;
        }
        // SAFETY: `first != head`, so it is a real node's link (not the sentinel);
        // every linked node's address is non-null.
        let first = unsafe { NonNull::new_unchecked(first) };
        Some(T::from_link(first))
    }
}

/// Removes `node` from whatever list it is currently linked into.
///
/// A free function rather than an `IntrusiveList` method, matching HPHA's own
/// `node_base::unlink`: removal is local pointer surgery on `node`'s own links and
/// its immediate neighbours, and never touches the owning list's `head` — so, exactly
/// as in HPHA, no reference to the list is needed to remove one of its nodes (only the
/// node itself, e.g. from `bucket_purge`'s manual page-list walk in `bucket.rs`).
///
/// `node` must currently be linked into a list (see [`ListLink::unlink`]'s contract).
pub(crate) fn unlink_node<T: ListNode>(node: NonNull<T>) {
    let node_link = T::link(node).as_ptr();
    // SAFETY: caller guarantees `node` is currently linked into a list.
    unsafe { ListLink::unlink(node_link) };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C)]
    struct TestNode {
        link: ListLink,
        value: u32,
    }

    // SAFETY: `link` is TestNode's first field (repr(C) guarantees offset 0).
    unsafe impl ListNode for TestNode {}

    fn boxed(value: u32) -> NonNull<TestNode> {
        let boxed = Box::new(TestNode {
            link: ListLink::UNLINKED,
            value,
        });
        NonNull::new(Box::into_raw(boxed)).expect("Box::into_raw is never null")
    }

    // SAFETY: `node` was leaked via `Box::into_raw` in `boxed` above and is not used
    // again after this call.
    unsafe fn drop_boxed(node: NonNull<TestNode>) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { drop(Box::from_raw(node.as_ptr())) };
    }

    #[test]
    fn new_list_is_empty() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        assert!(list.is_empty());
        assert!(list.front().is_none());
    }

    #[test]
    fn push_front_single_node_becomes_front() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let a = boxed(1);
        list.push_front(a);
        assert!(!list.is_empty());
        assert_eq!(list.front(), Some(a));
        unlink_node(a);
        // SAFETY: `a` was unlinked above and is not referenced again.
        unsafe { drop_boxed(a) };
    }

    #[test]
    fn push_back_orders_after_existing_front() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let a = boxed(1);
        let b = boxed(2);
        list.push_back(a);
        list.push_back(b);
        // front is still `a`; `b` was appended after it, not before.
        assert_eq!(list.front(), Some(a));
        unlink_node(a);
        unlink_node(b);
        // SAFETY: `a` was unlinked above and is not referenced again.
        unsafe { drop_boxed(a) };
        // SAFETY: `b` was unlinked above and is not referenced again.
        unsafe { drop_boxed(b) };
    }

    #[test]
    fn push_front_orders_before_existing_front() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let a = boxed(1);
        let b = boxed(2);
        list.push_back(a);
        list.push_front(b);
        // `b` was pushed to the front, ahead of `a`.
        assert_eq!(list.front(), Some(b));
        unlink_node(a);
        unlink_node(b);
        // SAFETY: `a` was unlinked above and is not referenced again.
        unsafe { drop_boxed(a) };
        // SAFETY: `b` was unlinked above and is not referenced again.
        unsafe { drop_boxed(b) };
    }

    #[test]
    fn remove_makes_list_empty_again() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let a = boxed(1);
        list.push_front(a);
        unlink_node(a);
        assert!(list.is_empty());
        assert!(list.front().is_none());
        // SAFETY: `a` was unlinked above and is not referenced again.
        unsafe { drop_boxed(a) };
    }

    #[test]
    fn manual_traversal_visits_all_nodes_in_order() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let nodes: Vec<NonNull<TestNode>> = (0..5).map(boxed).collect();
        for &n in &nodes {
            list.push_back(n);
        }
        let sentinel = list.sentinel();
        let mut seen = Vec::new();
        // EXPLICIT: raw-pointer chase instead of an iterator — mirrors the manual
        // traversal `bucket_purge` will do in `bucket.rs`; there is no safe iterator
        // over an intrusive list's raw links to build one over.
        // SAFETY: `sentinel` and every node reachable from it via `ListLink::next` are
        // live for the duration of this loop (the list is not mutated while walking).
        let mut cur = unsafe { ListLink::next(sentinel) };
        while cur != sentinel {
            // SAFETY: `cur != sentinel`, so it is a real node's link.
            let node = TestNode::from_link(unsafe { NonNull::new_unchecked(cur) });
            // SAFETY: `node` is live (owned by this test's `nodes` vec).
            seen.push(unsafe { node.as_ref().value });
            // SAFETY: `cur` is live, per the loop's own guarantee above.
            cur = unsafe { ListLink::next(cur) };
        }
        assert_eq!(seen, vec![0, 1, 2, 3, 4]);
        for n in nodes {
            unlink_node(n);
            // SAFETY: `n` was just unlinked above.
            unsafe { drop_boxed(n) };
        }
    }

    #[test]
    fn interleaved_push_and_remove_matches_expected_front() {
        let list: IntrusiveList<TestNode> = IntrusiveList::new();
        let a = boxed(1);
        let b = boxed(2);
        let c = boxed(3);
        list.push_back(a);
        list.push_back(b);
        unlink_node(a);
        assert_eq!(list.front(), Some(b));
        list.push_front(c);
        assert_eq!(list.front(), Some(c));
        unlink_node(b);
        unlink_node(c);
        assert!(list.is_empty());
        // SAFETY: `a` was unlinked above and is not referenced again.
        unsafe { drop_boxed(a) };
        // SAFETY: `b` was unlinked above and is not referenced again.
        unsafe { drop_boxed(b) };
        // SAFETY: `c` was unlinked above and is not referenced again.
        unsafe { drop_boxed(c) };
    }
}
