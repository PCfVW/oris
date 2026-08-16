// SPDX-License-Identifier: MIT OR Apache-2.0
//! Intrusive, circular, doubly-linked list with a self-referential sentinel head.
//!
//! Ports `Cpp/hpha.h`'s `intrusive_list_base`/`intrusive_list<T>`, mirroring `orisnik`'s
//! `list.rs` — used for the bucket allocator's per-bucket page list and the tree
//! allocator's small-free-block list. A node's link fields live inside the node itself
//! (no separate allocation per list membership); every element type embeds a `ListLink`
//! field named `link`, recovered from a link pointer via `@fieldParentPtr("link", ...)`
//! — Zig's standard intrusive-container idiom (see `std.DoublyLinkedList`'s own doc
//! comment). Simpler than `orisnik`'s `ListNode` trait: `@fieldParentPtr` computes the
//! right offset regardless of where `link` sits in the struct, not just at byte offset 0.
//!
//! Deliberately keeps HPHA's own sentinel-based, circular design rather than adopting
//! `std.DoublyLinkedList`'s `?*Node`-terminated one: the cross-port invariant
//! (`ROADMAP.md`) requires identical operation order to `orisnik`'s `list.rs`, itself a
//! faithful port of `intrusive_list_base` rather than an idiomatic rewrite.
//!
//! # Lazy sentinel initialization
//! An `IntrusiveList` must be usable as a plain, `comptime`-constructible zero value
//! (`IntrusiveList(T).init()`) so a container embedding one (`Bucket`, `Tree`) can
//! itself stay `comptime`-constructible — but a self-referential sentinel's `prev`/
//! `next` cannot point at `&self.head` until `self` is at its *final* address, which a
//! function returning `Self` by value does not yet have (the same reasoning `orisnik`'s
//! `list.rs` documents at length, and which applies in Zig too, even without Rust's
//! borrow checker — this is about the sentinel's *address*, not aliasing). Every method
//! therefore calls `headPtr`, which self-links `head` on its *first* call, once the
//! list is wherever the caller placed it. **Callers must not move an `IntrusiveList`
//! after the first call to any of its methods** — the same implicit constraint HPHA's
//! C++ objects already have (C++ never defines a move constructor for this type either).

const std = @import("std");

/// The embedded link fields of an intrusive list node. Ports `node_base`.
///
/// # Invariants
/// - `.UNLINKED` (both fields `null`) means "never touched" — distinct from "linked to
///   itself," which is what an empty list's self-linked head looks like (both fields
///   point at the node's own address). That distinction is what makes lazy self-init
///   possible: a `null` `prev` is the "self-link me now" signal.
/// - Once linked (to itself, or into a real chain), both fields are always non-`null`.
pub const ListLink = extern struct {
    /// The previous node in the circular chain (or `&self`, if this is a self-linked
    /// sentinel/singleton), or `null` if never linked. Byte offset 0.
    prev: ?*ListLink = null,
    /// The next node in the circular chain (or `&self`, if this is a self-linked
    /// sentinel/singleton), or `null` if never linked. Byte offset 8 (64-bit).
    next: ?*ListLink = null,

    /// A node that has never been linked into any list.
    pub const UNLINKED: ListLink = .{ .prev = null, .next = null };

    /// Removes `this` from whatever chain it is currently linked into.
    ///
    /// `this` must currently be linked (self-linked counts) — i.e. not `.UNLINKED` —
    /// and `this`'s `next`/`prev` must be live.
    pub fn unlink(this: *ListLink) void {
        // Ports HPHA's `node_base::unlink`; for a self-linked singleton this
        // degenerates to `this.next = this.prev = this`, a harmless no-op splice.
        const next = this.next.?;
        const prev = this.prev.?;
        next.prev = prev;
        prev.next = next;
    }

    /// Links `this` into the chain immediately before `before`.
    ///
    /// `this` must not currently be part of any chain (freshly `.UNLINKED` or just
    /// `unlink`ed). `before` must be live and linked (self-linked counts).
    pub fn linkBefore(this: *ListLink, before: *ListLink) void {
        const prev = before.prev.?;
        this.prev = prev;
        this.next = before;
        before.prev = this;
        prev.next = this;
    }
};

comptime {
    // Layout lock — matches `orisnik`'s `#[repr(C)]` `ListLink` field-for-field, per
    // `Zig/CONVENTIONS.md`'s "extern and packed layout lock" rule.
    std.debug.assert(@sizeOf(ListLink) == 2 * @sizeOf(usize));
    std.debug.assert(@offsetOf(ListLink, "prev") == 0);
    std.debug.assert(@offsetOf(ListLink, "next") == @sizeOf(usize));
}

/// An intrusive circular doubly-linked list of `T`, headed by a self-referential
/// sentinel. Ports `intrusive_list<T>`. `T` must have a field named `link: ListLink`.
/// See the module doc for the lazy-sentinel-init and non-move-after-first-use contract
/// every method here relies on.
pub fn IntrusiveList(comptime T: type) type {
    return struct {
        /// The sentinel node. Not part of any node's on-heap payload — this is the
        /// list container's own state, not frozen ABI — so it needs no `extern`
        /// layout-lock contract, only the lazy self-link the module doc describes.
        head: ListLink = ListLink.UNLINKED,

        const Self = @This();

        /// Builds an empty list. The sentinel is **not** self-linked yet — see the
        /// module doc's "Lazy sentinel initialization" section.
        pub fn init() Self {
            return .{ .head = ListLink.UNLINKED };
        }

        /// Returns a pointer to this list's own head sentinel, self-linking it on the
        /// first call.
        fn headPtr(self: *Self) *ListLink {
            if (self.head.prev == null) {
                // First touch since `init()` — self-link the sentinel now that its
                // final address is known; `init()` itself cannot do this (see the
                // module doc).
                self.head.prev = &self.head;
                self.head.next = &self.head;
            }
            return &self.head;
        }

        /// A pointer to this list's sentinel — never a real node, only ever a
        /// traversal boundary. For manual traversal loops that mirror HPHA's own
        /// hand-rolled walks (e.g. `contains`).
        pub fn sentinel(self: *Self) *ListLink {
            return self.headPtr();
        }

        /// Whether `target` (a candidate node's own link pointer) is currently linked
        /// into this list — an `O(n)` exhaustive scan, never on any hot path. Exists
        /// for the bucket allocator's debug-only verification of its own fast-path
        /// page-marker check, mirroring HPHA's `ptr_in_bucket`'s own `#ifndef NDEBUG`
        /// exhaustive-search assertion (see `bucket.zig`, once written).
        pub fn contains(self: *Self, target: *ListLink) bool {
            const s = self.headPtr();
            var cur: *ListLink = s;
            // EXPLICIT: raw-pointer chase instead of an iterator — `cur` is the
            // state, not expressible as an iterator over an intrusive list's raw
            // links.
            while (true) {
                cur = cur.next.?;
                if (cur == s) return false;
                if (cur == target) return true;
            }
        }

        /// Whether this list currently holds no real nodes. Ports
        /// `intrusive_list::empty`.
        pub fn isEmpty(self: *Self) bool {
            const head = self.headPtr();
            return head.next.? == head;
        }

        /// Inserts `node` at the front of the list. `node` must not currently be
        /// linked into any list.
        pub fn pushFront(self: *Self, node: *T) void {
            const head = self.headPtr();
            // SAFETY: `head` is live and linked (`headPtr`'s guarantee), so `head`'s
            // `next` is live; caller guarantees `node` is not currently linked
            // anywhere, satisfying `linkBefore`'s precondition.
            const first = head.next.?;
            node.link.linkBefore(first);
        }

        /// Inserts `node` at the back of the list. `node` must not currently be
        /// linked into any list.
        pub fn pushBack(self: *Self, node: *T) void {
            const head = self.headPtr();
            // SAFETY: `head` is live and linked (`headPtr`'s guarantee); caller
            // guarantees `node` is not currently linked anywhere.
            node.link.linkBefore(head);
        }

        /// The first node, or `null` if the list is empty.
        pub fn front(self: *Self) ?*T {
            const head = self.headPtr();
            const first = head.next.?;
            if (first == head) return null;
            // `first != head`, so it is a real node's link, not the sentinel.
            return @fieldParentPtr("link", first);
        }
    };
}

/// Removes `node` from whatever list it is currently linked into.
///
/// A free function rather than an `IntrusiveList` method, matching HPHA's own
/// `node_base::unlink`: removal is local pointer surgery on `node`'s own links and its
/// immediate neighbours, and never touches the owning list's head — so, exactly as in
/// HPHA, no reference to the list is needed to remove one of its nodes (only the node
/// itself, e.g. from the bucket allocator's manual page-list walk during `purge`).
///
/// `node` must currently be linked into a list (see `ListLink.unlink`'s contract).
/// `node` must have a field named `link: ListLink`.
pub fn unlinkNode(node: anytype) void {
    node.link.unlink();
}

const testing = std.testing;

const TestNode = struct {
    link: ListLink = ListLink.UNLINKED,
    value: u32,
};

fn boxed(allocator: std.mem.Allocator, value: u32) !*TestNode {
    const node = try allocator.create(TestNode);
    node.* = .{ .link = ListLink.UNLINKED, .value = value };
    return node;
}

test "a new list is empty" {
    var list: IntrusiveList(TestNode) = .init();
    try testing.expect(list.isEmpty());
    try testing.expect(list.front() == null);
}

test "pushFront: a single node becomes the front" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    const a = try boxed(allocator, 1);
    defer allocator.destroy(a);

    list.pushFront(a);
    try testing.expect(!list.isEmpty());
    try testing.expectEqual(a, list.front());
    unlinkNode(a);
}

test "pushBack: orders after the existing front" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    const a = try boxed(allocator, 1);
    defer allocator.destroy(a);
    const b = try boxed(allocator, 2);
    defer allocator.destroy(b);

    list.pushBack(a);
    list.pushBack(b);
    // front is still `a`; `b` was appended after it, not before.
    try testing.expectEqual(a, list.front());
    unlinkNode(a);
    unlinkNode(b);
}

test "pushFront: orders before the existing front" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    const a = try boxed(allocator, 1);
    defer allocator.destroy(a);
    const b = try boxed(allocator, 2);
    defer allocator.destroy(b);

    list.pushBack(a);
    list.pushFront(b);
    // `b` was pushed to the front, ahead of `a`.
    try testing.expectEqual(b, list.front());
    unlinkNode(a);
    unlinkNode(b);
}

test "unlinkNode: removing the only node makes the list empty again" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    const a = try boxed(allocator, 1);
    defer allocator.destroy(a);

    list.pushFront(a);
    unlinkNode(a);
    try testing.expect(list.isEmpty());
    try testing.expect(list.front() == null);
}

test "manual traversal visits every node in order" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    var nodes: [5]*TestNode = undefined;
    for (0..5) |i| {
        nodes[i] = try boxed(allocator, @intCast(i));
        list.pushBack(nodes[i]);
    }
    defer for (nodes) |n| allocator.destroy(n);

    const s = list.sentinel();
    var seen: [5]u32 = undefined;
    var count: usize = 0;
    // EXPLICIT: raw-pointer chase instead of an iterator — mirrors the manual
    // traversal the bucket allocator's `purge` will do; there is no safe iterator
    // over an intrusive list's raw links to build one over.
    var cur = s.next.?;
    while (cur != s) : (cur = cur.next.?) {
        const node: *TestNode = @fieldParentPtr("link", cur);
        seen[count] = node.value;
        count += 1;
    }
    try testing.expectEqual(5, count);
    try testing.expectEqualSlices(u32, &.{ 0, 1, 2, 3, 4 }, &seen);

    for (nodes) |n| unlinkNode(n);
}

test "interleaved push and remove match the expected front" {
    const allocator = testing.allocator;
    var list: IntrusiveList(TestNode) = .init();
    const a = try boxed(allocator, 1);
    defer allocator.destroy(a);
    const b = try boxed(allocator, 2);
    defer allocator.destroy(b);
    const c = try boxed(allocator, 3);
    defer allocator.destroy(c);

    list.pushBack(a);
    list.pushBack(b);
    unlinkNode(a);
    try testing.expectEqual(b, list.front());
    list.pushFront(c);
    try testing.expectEqual(c, list.front());
    unlinkNode(b);
    unlinkNode(c);
    try testing.expect(list.isEmpty());
}
