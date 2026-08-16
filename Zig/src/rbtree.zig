// SPDX-License-Identifier: MIT OR Apache-2.0
//! Intrusive, augmented red-black tree supporting duplicate keys ("multi-tree").
//!
//! Ports `Cpp/hpha.h`'s `intrusive_multi_rbtree_base`/`intrusive_multi_rbtree<T>` (node
//! layout and multi-tree operations) and the fixup algorithms in `Cpp/hpha.cpp`
//! (`insert_fixup`/`erase_fixup`), mirroring `orisnik`'s `rbtree.rs`. This is the tree
//! allocator's free-block index, keyed by block size — the highest-risk module for the
//! cross-port invariant (`ROADMAP.md`), since it counts rotations and coalescing
//! operations, not just final tree shape. Every function below preserves HPHA's
//! operation *order*, not just its net effect, even where a reordering would be
//! mathematically equivalent.
//!
//! # Equal keys: the "chain"
//! HPHA's tree is a *multi*-tree: several elements may share one key (several free
//! blocks of the same size). Rather than allow duplicate tree nodes, exactly one member
//! of an equal-key group occupies a real tree position (the "attached" member); the
//! rest are threaded onto it via `neighbours` — a circular doubly-linked list *distinct*
//! from `list.zig`'s `IntrusiveList` (no separate sentinel: any member can be a valid
//! entry point, and the attached member is simply the one whose `parent` is non-null).
//! This is why `NodeBase.parent` is nullable, unlike `children`/`neighbours`.
//!
//! # Tagged parent link
//! `parent` packs the node's colour and parent-side bits into the same `usize` as the
//! parent address, via `tag.zig` — simpler than `orisnik`'s `TaggedPtr<T>` wrapper (see
//! `tag.zig`'s module doc), but the *nullable-ness* is identical: a `0` `parent` means
//! this node is chained but not its equal-key group's tree-attached representative.
//!
//! # Sentinel design
//! Same lazy-self-init pattern as `list.zig`'s `IntrusiveList`: `headPtr` self-links the
//! tree's sentinel on first touch, signalled by `parent == 0` (the same value a fresh,
//! unattached real node also starts with — the two cases are distinguished by *which*
//! check a caller performs, exactly as in `orisnik`). Every method calls `headPtr` first.
//! **Callers must not move an `IntrusiveMultiRbTree` after the first call to any of its
//! methods.**
//!
//! `children`/`neighbours` are plain (non-optional) `*NodeBase`, so — unlike
//! `orisnik`'s raw `*mut NodeBase`, which can hold a literal null — they cannot
//! represent "no value" at all; every node's `children`/`neighbours` are given a
//! real, deterministic value (never left at the struct's `undefined` default) by
//! whichever of `headPtr`'s self-link, `attachTo`, or `linkIntoChain` first touches
//! it. Where `orisnik` writes a literal null into a chained node's `children`
//! (`link_into_chain`), this file writes a self-reference — the same sentinel value
//! `isNil` already treats as "no real child", and, like `orisnik`'s null, never read
//! as a real child by any operation here (`isNil` is only ever called on a *child of
//! an attached node*, and a chained node is never anyone's child). Not a tracked
//! deviation from the cross-port invariant (which is about state *transitions*, not
//! the bit-pattern of fields no operation ever reads) — but deterministic rather than
//! `undefined` on principle, not merely as a style preference.

const std = @import("std");
const tag = @import("tag.zig");

/// Which of a node's two children/neighbours/tree-order-links a position refers to.
/// Ports `side`. Backed by `u1` so `@intFromEnum` is directly the array index — no
/// separate index-computing helper needed (unlike `orisnik`'s `Side::index`, added
/// there purely to avoid an `as` cast Zig has no equivalent lint for).
pub const Side = enum(u1) {
    left = 0,
    right = 1,

    /// The other side. Ports `side o = (side)(1 - s)`.
    pub fn other(self: Side) Side {
        return switch (self) {
            .left => .right,
            .right => .left,
        };
    }
};

/// A red-black tree node's colour. Ports `colour`. Backed by `u1` matching
/// `tag.BIT_COLOUR`'s bit meaning (set = red).
pub const Colour = enum(u1) {
    black = 0,
    red = 1,
};

/// The embedded fields of a red-black tree node. Ports `node_base`.
///
/// # Invariants
/// - `children[.right] == this` (the "nil" test, `isNil`) marks an empty subtree;
///   every real node's children are themselves live `NodeBase`s or the tree's sentinel.
/// - `neighbours[.left] == this` means this node has no equal-key duplicates
///   (`chained` is `false`).
/// - `parent` is `0` exactly when this node is chained but not its equal-key group's
///   tree-attached representative (`isAttached` is `false`) — see the module doc's
///   "Equal keys" section.
pub const NodeBase = extern struct {
    /// Left (index 0) and right (index 1) tree children. Only meaningful once this
    /// node is attached to a tree, chained, or is the sentinel past its first touch
    /// (`= undefined` is this field's pre-that-point placeholder, never its steady
    /// state) — see the module doc.
    children: [2]*NodeBase = undefined,
    /// Left (index 0, "prev") and right (index 1, "next") links in this node's
    /// equal-key group's circular chain. Only meaningful once this node is attached,
    /// chained, or is the sentinel past its first touch.
    neighbours: [2]*NodeBase = undefined,
    /// Tagged parent link: bit `tag.BIT_COLOUR` is this node's red-black colour, bit
    /// `tag.BIT_SIDE` is which of the parent's two children this node is. `0` (with
    /// either tag state) means this node is a chained, non-tree-attached duplicate,
    /// or (for the tree's own sentinel) not yet self-linked.
    parent: usize = 0,

    // ---- derived accessors ----

    /// `this`'s side-`s` tree child (the tree's sentinel, or `this` itself, if nil —
    /// see `isNil`).
    pub fn child(this: *NodeBase, s: Side) *NodeBase {
        return this.children[@intFromEnum(s)];
    }

    fn setChild(this: *NodeBase, s: Side, val: *NodeBase) void {
        this.children[@intFromEnum(s)] = val;
    }

    /// `this`'s side-`s` equal-key chain link (see the module doc's "Equal keys"
    /// section). `this` itself if `this` has no duplicates (`!chained`).
    pub fn neighbour(this: *NodeBase, s: Side) *NodeBase {
        return this.neighbours[@intFromEnum(s)];
    }

    fn setNeighbour(this: *NodeBase, s: Side, val: *NodeBase) void {
        this.neighbours[@intFromEnum(s)] = val;
    }

    /// The node's parent, or `null` if it is a chained, non-attached duplicate.
    pub fn parentPtr(this: *NodeBase) ?*NodeBase {
        // PROVENANCE: `addr` is either `0` (see `isAttached`) or was produced by
        // `@intFromPtr` on a live `*NodeBase` in `setParentPtr` — the only writer of
        // this field — so reconstructing it here is always sound.
        const addr = tag.untagLink(this.parent);
        return if (addr == 0) null else @ptrFromInt(addr);
    }

    /// `this` must be attached (`isAttached`).
    pub fn parentSide(this: *NodeBase) Side {
        return if (tag.bit(this.parent, tag.BIT_SIDE)) .right else .left;
    }

    /// `this` must be attached (`isAttached`) — an unattached, chained node's colour
    /// bit is meaningless (`linkIntoChain` sets it but nothing ever reads it there).
    pub fn colour(this: *NodeBase) Colour {
        return if (tag.bit(this.parent, tag.BIT_COLOUR)) .red else .black;
    }

    /// `this` must be attached (`isAttached`) — see `colour`.
    pub fn red(this: *NodeBase) bool {
        return this.colour() == .red;
    }

    /// This node is chained onto an equal-key group but is not its tree-attached
    /// representative. Ports `node_base::head()` — renamed to avoid confusion with
    /// `list.zig`'s unrelated sentinel-head concept.
    pub fn isAttached(this: *NodeBase) bool {
        return this.parentPtr() != null;
    }

    /// `this` marks an empty subtree — true only for the tree's own self-linked
    /// sentinel (see the struct's `# Invariants`), never for a real, attached node.
    pub fn isNil(this: *NodeBase) bool {
        return this.child(.right) == this;
    }

    /// This node has equal-key duplicates chained onto it (in either direction; the
    /// chain is circular so both directions are non-self exactly when either is).
    pub fn chained(this: *NodeBase) bool {
        return this.neighbour(.left) != this;
    }

    // ---- mutators ----

    /// Replaces the parent pointer (possibly `null`), preserving the current
    /// colour/side tag.
    fn setParentPtr(this: *NodeBase, val: ?*NodeBase) void {
        // PROVENANCE: `v` is a live `*NodeBase` (the new parent, or the tree's own
        // sentinel); its address is read only to store in the tagged `parent` field,
        // reconstructed later via `parentPtr`'s `@ptrFromInt`.
        const addr: usize = if (val) |v| @intFromPtr(v) else 0;
        this.parent = tag.setLink(this.parent, addr);
    }

    fn setParentSide(this: *NodeBase, s: Side) void {
        this.parent = switch (s) {
            .left => tag.clearBit(this.parent, tag.BIT_SIDE),
            .right => tag.setBit(this.parent, tag.BIT_SIDE),
        };
    }

    fn setColour(this: *NodeBase, c: Colour) void {
        this.parent = switch (c) {
            .black => tag.clearBit(this.parent, tag.BIT_COLOUR),
            .red => tag.setBit(this.parent, tag.BIT_COLOUR),
        };
    }

    fn makeRed(this: *NodeBase) void {
        this.setColour(.red);
    }

    fn makeBlack(this: *NodeBase) void {
        this.setColour(.black);
    }

    // ---- structural operations ----

    /// Rotates `this` down and its side-`o` child (`o` = the side opposite `s`) up
    /// into `this`'s former position. Ports `node_base::rotate`.
    ///
    /// `this` must be live and attached, with `this`'s parent's child on `this`'s own
    /// `parentSide` equal to `this` (the standard rotation precondition); `this`'s
    /// side-`o` child must be non-nil.
    pub fn rotate(this: *NodeBase, s: Side) void {
        const o = s.other();
        const ps = this.parentSide();
        const this_parent = this.parentPtr().?;
        const top = this.child(o);
        const top_s_child = top.child(s);
        this.setChild(o, top_s_child);
        top_s_child.setParentPtr(this);
        top_s_child.setParentSide(o);
        top.setParentPtr(this_parent);
        top.setParentSide(ps);
        this_parent.setChild(ps, top);
        top.setChild(s, this);
        this.setParentPtr(top);
        this.setParentSide(s);
    }

    /// The tree-order predecessor (`s` = `.left`) or successor (`s` = `.right`) of
    /// `this`, walking the equal-key chain first (O(1) for duplicates) and falling
    /// back to a genuine tree walk. May return the tree's sentinel (never dereferenced
    /// as such by this function). Ports `node_base::pred_or_succ`.
    pub fn predOrSucc(this: *NodeBase, s: Side) *NodeBase {
        const cur = this.neighbour(s);
        const cur_parent = cur.parentPtr() orelse return cur;
        const first_child = cur.child(s);
        if (first_child.isNil()) {
            var c = cur;
            var xessor = cur_parent;
            // EXPLICIT: climb parents while `c` is a side-`s` child; `c`/`xessor` are
            // the state threaded up the tree, not expressible as an iterator.
            while (c.parentSide() == s) {
                c = xessor;
                xessor = xessor.parentPtr().?;
            }
            return xessor;
        } else {
            const o = s.other();
            var xessor = first_child;
            // EXPLICIT: descend to the subtree's side-`o` extreme; `xessor` is the
            // state threaded down the tree, not expressible as an iterator.
            while (true) {
                // Shadowing note: named `descended`, not `next`, only to avoid
                // colliding with this file's own top-level `next` free function
                // (Zig errors on identifier shadowing) — `orisnik`'s `rbtree.rs`
                // names this same local `next`.
                const descended = xessor.child(o);
                if (descended.isNil()) break;
                xessor = descended;
            }
            return xessor;
        }
    }

    /// The extreme node (leftmost for `s` = `.left`, rightmost for `.right`) of the
    /// subtree rooted at `this`. Returns `this` itself if `this` is nil. Ports
    /// `node_base::min_or_max`.
    ///
    /// General-purpose API completeness (HPHA's `node_base::min_or_max`); reached in
    /// this port only through `IntrusiveMultiRbTree.minimum`.
    pub fn minOrMax(this: *NodeBase, s: Side) *NodeBase {
        var cur = this;
        var minmax = cur;
        // EXPLICIT: descend to the side-`s` extreme; `cur`/`minmax` are the state
        // threaded down the tree, not expressible as an iterator.
        while (!cur.isNil()) {
            minmax = cur;
            cur = cur.child(s);
        }
        return minmax;
    }

    /// Attaches a freshly-unlinked `this` as `parent_node`'s side-`s` child (a fresh,
    /// red leaf — rotations/recolouring happen in `insertFixup`). Ports
    /// `node_base::attach_to`.
    ///
    /// `this` must not currently be part of any tree or chain. `parent_node` must be
    /// live with a live `child(s)` (nil counts).
    fn attachTo(this: *NodeBase, parent_node: *NodeBase, s: Side) void {
        this.setNeighbour(.left, this);
        this.setNeighbour(.right, this);
        const leaf_child = parent_node.child(s);
        this.setChild(.left, leaf_child);
        this.setChild(.right, leaf_child);
        this.setParentPtr(parent_node);
        this.setParentSide(s);
        parent_node.setChild(s, this);
        this.makeRed();
    }

    /// Splices `child_node` into `this`'s structural position (parent's child pointer
    /// retargeted; `child_node`'s own colour is untouched). Used when `this` is being
    /// removed from the tree and has at most one non-nil child. Ports
    /// `node_base::substitute_with`.
    ///
    /// `this` must be live and attached. `child_node` must be live.
    fn substituteWith(this: *NodeBase, child_node: *NodeBase) void {
        const ps = this.parentSide();
        const this_parent = this.parentPtr().?;
        child_node.setParentPtr(this_parent);
        child_node.setParentSide(ps);
        this_parent.setChild(ps, child_node);
    }

    /// Makes `this` assume `node`'s structural position, children, and colour —
    /// `node` is being fully removed from the tree and `this` (its equal-key chain
    /// successor) is taking its place. Ports `node_base::switch_with`.
    ///
    /// `this != node`. `node` must be live and attached. `node`'s children and parent
    /// must be live.
    fn switchWith(this: *NodeBase, node: *NodeBase) void {
        std.debug.assert(this != node);
        std.debug.assert(node.isAttached());
        const nps = node.parentSide();
        const node_left = node.child(.left);
        const node_right = node.child(.right);
        this.setChild(.left, node_left);
        this.setChild(.right, node_right);
        const node_parent = node.parentPtr().?;
        this.setParentPtr(node_parent);
        this.setParentSide(nps);
        node_left.setParentPtr(this);
        node_left.setParentSide(.left);
        node_right.setParentPtr(this);
        node_right.setParentSide(.right);
        node_parent.setChild(nps, this);
        this.setColour(node.colour());
    }

    /// Removes `this` from its equal-key group's chain. Ports `node_base::unlink`
    /// (the chain-unlink overload — distinct from the tree-structural removal in
    /// `IntrusiveMultiRbTree.erase`).
    ///
    /// `this` must be live and currently chained (`chained`) or self-linked (a no-op
    /// splice in that case).
    fn unlinkFromChain(this: *NodeBase) void {
        // Named `chain_next`, not `next` (which `orisnik`'s `list.rs` counterpart
        // uses) — this file has its own top-level `next` free function in scope,
        // and Zig errors on identifier shadowing.
        const chain_next = this.neighbour(.right);
        const prev = this.neighbour(.left);
        chain_next.setNeighbour(.left, prev);
        prev.setNeighbour(.right, chain_next);
    }

    /// Chains `this` into `node`'s equal-key group, immediately before `node`. `this`
    /// becomes a plain chain link: no tree position, no colour that matters, null
    /// parent. Ports `node_base::link`.
    ///
    /// `this` must not currently be part of any tree or chain. `node` must be live.
    fn linkIntoChain(this: *NodeBase, node: *NodeBase) void {
        const node_prev = node.neighbour(.left);
        this.setNeighbour(.left, node_prev);
        this.setNeighbour(.right, node);
        node.setNeighbour(.left, this);
        node_prev.setNeighbour(.right, this);
        // `orisnik`'s `link_into_chain` nulls `this`'s children here (Rust's raw
        // `*mut NodeBase` can represent null); Zig's `children` field is a
        // non-optional `*NodeBase` and cannot. Self-reference instead — the same
        // sentinel value `isNil` already treats as "no real child" — rather than
        // leaving these `undefined`. `children` on a chained node is provably never
        // read by any operation in this file (see the module doc), so this is a
        // hygiene improvement (no `undefined` reads, full parity with `orisnik`'s
        // explicit initialization), not a fix for an observed bug: the one RB-tree
        // trace divergence found during this port's oracle cross-validation (step 322
        // of the 3000-step run) traced to the *test's* trace buffer being too small
        // (256 bytes, truncating lines once `live.len` grew past ~90), not to this.
        this.setChild(.left, this);
        this.setChild(.right, this);
        this.setParentPtr(null);
        this.setParentSide(.left);
        this.makeRed();
    }
};

comptime {
    // Layout lock — matches `orisnik`'s `#[repr(C)]` `NodeBase` field-for-field, per
    // `Zig/CONVENTIONS.md`'s "extern and packed layout lock" rule.
    std.debug.assert(@sizeOf(NodeBase) == 5 * @sizeOf(usize));
    std.debug.assert(@offsetOf(NodeBase, "children") == 0);
    std.debug.assert(@offsetOf(NodeBase, "neighbours") == 2 * @sizeOf(usize));
    std.debug.assert(@offsetOf(NodeBase, "parent") == 4 * @sizeOf(usize));
}

/// Rebalances after `NodeBase.attachTo` attached `node` as a fresh red leaf. Ports
/// `intrusive_multi_rbtree_base::insert_fixup` (`Cpp/hpha.cpp`).
///
/// `head` must be a live tree sentinel; `node` must be a live, just-attached node.
fn insertFixup(head: *NodeBase, node: *NodeBase) void {
    var cur = node;
    var p = cur.parentPtr().?;
    // EXPLICIT: climb and recolour/rotate while the parent is red; `cur`/`p` are the
    // state threaded up the tree, not expressible as an iterator.
    while (p.red()) {
        const pp = p.parentPtr().?;
        const s = p.parentSide();
        const o = s.other();
        const pp_right = pp.child(o);
        if (pp_right.red()) {
            p.makeBlack();
            pp_right.makeBlack();
            pp.makeRed();
            cur = pp;
            p = cur.parentPtr().?;
        } else {
            const p_o_child = p.child(o);
            if (cur == p_o_child) {
                cur = p;
                cur.rotate(s);
                p = cur.parentPtr().?;
            }
            p.makeBlack();
            pp.makeRed();
            pp.rotate(o);
        }
    }
    const root = head.child(.left);
    root.makeBlack();
}

/// Rebalances after a black node was spliced out during erase, starting from the
/// child (`node`) that took its place (possibly the tree's own nil sentinel — that is
/// exactly the "double black at an empty subtree" case this walk terminates from via
/// the `cur != root` / `cur` red checks, matching HPHA exactly). Ports
/// `intrusive_multi_rbtree_base::erase_fixup` (`Cpp/hpha.cpp`).
///
/// `head` must be a live tree sentinel; `node` must be live.
///
/// `p`/`s`/`o`/`w`/`c` deliberately mirror `Cpp/hpha.cpp`'s own variable names (`p`,
/// `s`, `o`, `w`, `c`) line-for-line, so this algorithm can be audited side by side
/// against the reference it ports — renaming them to longer names would work against
/// exactly the review that matters most for this function.
fn eraseFixup(head: *NodeBase, node: *NodeBase) void {
    var cur = node;
    const root = head.child(.left);
    // EXPLICIT: climb and rebalance while `cur` is black and not the root; `cur` is
    // the state threaded up the tree, not expressible as an iterator.
    while (!cur.red() and cur != root) {
        const p = cur.parentPtr().?;
        const s = cur.parentSide();
        const o = s.other();
        var w = p.child(o);
        if (w.red()) {
            w.makeBlack();
            p.makeRed();
            w = w.child(s);
            p.rotate(s);
        }
        const w_left = w.child(.left);
        const w_right = w.child(.right);
        const w_left_black = !w_left.red();
        const w_right_black = !w_right.red();
        if (w_left_black and w_right_black) {
            w.makeRed();
            cur = p;
        } else {
            const w_o_child = w.child(o);
            if (!w_o_child.red()) {
                const w_s_child = w.child(s);
                w_s_child.makeBlack();
                w.makeRed();
                const c = w_s_child;
                w.rotate(o);
                w = c;
            }
            w.setColour(p.colour());
            p.makeBlack();
            // Named `w_o_child2`, not `w_o_child` — `orisnik`'s `erase_fixup` reuses
            // that name here via Rust's `let`-shadowing (a legitimately new read of
            // `w.child(o)`, taken *after* `w` was reassigned above); Zig errors on
            // identifier shadowing, so this second read needs its own name.
            const w_o_child2 = w.child(o);
            w_o_child2.makeBlack();
            p.rotate(s);
            cur = root;
        }
    }
    cur.makeBlack();
}

/// An intrusive multi-tree of `T`, headed by a self-referential sentinel. Ports
/// `intrusive_multi_rbtree<T>`. `T` must have a field named `node: NodeBase`, a
/// `pub const Key` type, and `pub fn cmp(this: *const T, other: *const T)
/// std.math.Order` / `pub fn cmpKey(this: *const T, key: T.Key) std.math.Order`
/// methods (`std.math.Order` is this port's `Ordering` — `Ordering::Equal` is HPHA's
/// `!(a<b) && !(a>b)`, its definition of "same key, chain together"). See the module
/// doc for the lazy-sentinel-init and non-move-after-first-use contract every method
/// here relies on (identical in spirit to `list.zig`'s `IntrusiveList`).
pub fn IntrusiveMultiRbTree(comptime T: type) type {
    return struct {
        /// The sentinel node. Not part of any node's on-heap payload — this is the
        /// tree container's own state, not frozen ABI — so it needs no `extern`
        /// layout-lock contract, only the lazy self-link the module doc describes.
        head: NodeBase = .{},

        const Self = @This();

        /// Builds an empty tree. The sentinel is **not** self-linked yet — see the
        /// module doc.
        pub fn init() Self {
            return .{};
        }

        /// Returns a pointer to this tree's own head sentinel, self-linking it (all
        /// three link groups, to itself) on the first call.
        fn headPtr(self: *Self) *NodeBase {
            if (self.head.parent == 0) {
                // First touch since `init()` — self-link the sentinel now that its
                // final address is known; `init()` itself cannot do this (module doc).
                self.head.children[0] = &self.head;
                self.head.children[1] = &self.head;
                self.head.neighbours[0] = &self.head;
                self.head.neighbours[1] = &self.head;
                // PROVENANCE: `&self.head` is the tree's own sentinel field, live for
                // as long as `self` is; self-referential address, reconstructed via
                // `parentPtr`'s `@ptrFromInt` like any other node's parent link.
                self.head.parent = tag.tagLink(@intFromPtr(&self.head), 0);
            }
            return &self.head;
        }

        /// Whether this tree currently holds no nodes. Ports
        /// `intrusive_multi_rbtree::empty`.
        ///
        /// General-purpose API completeness; nothing in this port's own dispatch
        /// needs it directly (a `lowerBound`/`succ` returning `null` already tells
        /// every caller what it needs).
        pub fn isEmpty(self: *Self) bool {
            const head = self.headPtr();
            return head.child(.left) == head;
        }

        fn root(self: *Self) *NodeBase {
            const head = self.headPtr();
            return head.child(.left);
        }

        /// Inserts `node`. If an equal-key element already exists, `node` is chained
        /// onto it instead of becoming a new tree position. Ports
        /// `intrusive_multi_rbtree::do_insert`.
        pub fn insert(self: *Self, node: *T) void {
            const head = self.headPtr();
            const node_base = &node.node;
            const end = head;
            var last = head;
            var cur = self.root();
            var s: Side = .left;
            // EXPLICIT: BST descent to the insertion point; `cur`/`last`/`s` are the
            // state threaded down the tree, not expressible as an iterator.
            while (cur != end) {
                last = cur;
                const cur_typed: *T = @fieldParentPtr("node", cur);
                switch (node.cmp(cur_typed)) {
                    .lt => s = .left,
                    .gt => s = .right,
                    .eq => {
                        node_base.linkIntoChain(cur);
                        return;
                    },
                }
                cur = cur.child(s);
            }
            node_base.attachTo(last, s);
            insertFixup(head, node_base);
        }

        /// Removes `node`. Ports `intrusive_multi_rbtree::do_erase`.
        pub fn erase(self: *Self, node: *T) void {
            const head = self.headPtr();
            const node_base = &node.node;
            if (node_base.chained()) {
                if (!node_base.isAttached()) {
                    // Plain chain link, not the group's tree-attached representative:
                    // O(1) removal, no tree structure touched.
                    node_base.unlinkFromChain();
                    return;
                }
                // `node_base` is the group's tree-attached representative, and the
                // group has more members: promote the next chain member into its
                // tree position.
                const repl = node_base.neighbour(.right);
                std.debug.assert(repl != head);
                std.debug.assert(!repl.isAttached());
                repl.switchWith(node_base);
                // `node_base` is live and still chained (only its tree position was
                // taken over above; the chain links are untouched until this call).
                node_base.unlinkFromChain();
                return;
            }
            // Genuine tree removal: `node_base` has no equal-key duplicates at all.
            const end = head;
            var repl = node_base;
            var s: Side = .left;
            const right = node_base.child(.right);
            if (right != end) {
                const left = node_base.child(.left);
                if (left != end) {
                    repl = right;
                    var repl_left = repl.child(.left);
                    // EXPLICIT: descend to the in-order successor (leftmost of the
                    // right subtree); `repl`/`repl_left` are the state threaded down
                    // the tree.
                    while (repl_left != end) {
                        repl = repl_left;
                        repl_left = repl.child(.left);
                    }
                }
                s = .right;
            }
            const red = repl.red();
            const repl_child = repl.child(s);
            // `repl` is live and attached (it is either `node_base` itself, or a
            // node reached by descending real tree children from it — both attached).
            repl.substituteWith(repl_child);
            if (repl != node_base) {
                repl.switchWith(node_base);
            }
            if (!red) {
                eraseFixup(head, repl_child);
            }
        }

        /// The first element not ordered before `key` (`!(element < key)`). Ports
        /// `intrusive_multi_rbtree::do_lower_bound`.
        pub fn lowerBound(self: *Self, key: T.Key) ?*T {
            const head = self.headPtr();
            const end = head;
            var best = head;
            var cur = self.root();
            // EXPLICIT: BST descent narrowing the best-so-far bound; `cur`/`best` are
            // the state threaded down the tree, not expressible as an iterator.
            while (cur != end) {
                const cur_typed: *T = @fieldParentPtr("node", cur);
                if (cur_typed.cmpKey(key) == .lt) {
                    cur = cur.child(.right);
                } else {
                    best = cur;
                    cur = cur.child(.left);
                }
            }
            if (best == end) return null;
            return @fieldParentPtr("node", best);
        }

        /// The first element ordered strictly after `key` (`element > key`). Ports
        /// `intrusive_multi_rbtree::do_upper_bound`.
        pub fn upperBound(self: *Self, key: T.Key) ?*T {
            const head = self.headPtr();
            const end = head;
            var best = head;
            var cur = self.root();
            // EXPLICIT: BST descent narrowing the best-so-far bound; `cur`/`best` are
            // the state threaded down the tree, not expressible as an iterator.
            while (cur != end) {
                const cur_typed: *T = @fieldParentPtr("node", cur);
                if (cur_typed.cmpKey(key) == .gt) {
                    best = cur;
                    cur = cur.child(.left);
                } else {
                    cur = cur.child(.right);
                }
            }
            if (best == end) return null;
            return @fieldParentPtr("node", best);
        }

        /// The smallest-keyed element, or `null` if the tree is empty.
        ///
        /// General-purpose API completeness (HPHA's `intrusive_multi_rbtree::begin()`);
        /// this port's own dispatch always has a size key to search by (`lowerBound`),
        /// never needs the unconditional minimum.
        pub fn minimum(self: *Self) ?*T {
            const head = self.headPtr();
            const node = self.root().minOrMax(.left);
            if (node == head) return null;
            return @fieldParentPtr("node", node);
        }

        /// The tree-order successor of `node`, or `null` if `node` is the maximum.
        pub fn succ(self: *Self, node: *T) ?*T {
            const head = self.headPtr();
            const s = node.node.predOrSucc(.right);
            if (s == head) return null;
            return @fieldParentPtr("node", s);
        }
    };
}

/// The next member of `node`'s equal-key chain (a node with no duplicates is its own
/// chain, so this returns `node` itself in that case). Distinct from
/// `IntrusiveMultiRbTree.succ` (true tree order) — ports `node_base::next()`, the
/// chain-neighbour overload, not `node_base::succ()`. A free function rather than a
/// tree method: the equal-key chain never touches the tree's sentinel, so no tree
/// state is needed — mirrors `list.zig`'s free-standing `unlinkNode`.
pub fn next(node: anytype) @TypeOf(node) {
    const T = @typeInfo(@TypeOf(node)).pointer.child;
    const next_base = node.node.neighbour(.right);
    return @as(*T, @fieldParentPtr("node", next_base));
}

const testing = std.testing;

const TestNode = struct {
    node: NodeBase = .{},
    key: i32,
    id: u32,

    pub const Key = i32;

    pub fn cmp(this: *const TestNode, other: *const TestNode) std.math.Order {
        return std.math.order(this.key, other.key);
    }

    pub fn cmpKey(this: *const TestNode, key: i32) std.math.Order {
        return std.math.order(this.key, key);
    }
};

fn boxed(allocator: std.mem.Allocator, key: i32, id: u32) !*TestNode {
    const node = try allocator.create(TestNode);
    node.* = .{ .node = .{}, .key = key, .id = id };
    return node;
}

/// Structural checker: no red-red violations, equal black-height on every root-to-nil
/// path, BST order property holds. Ports `DEBUG_MULTI_RBTREE`'s
/// `check()`/`check_height()`, kept always-available under test rather than gated,
/// per the plan's Phase 3 test strategy.
fn checkInvariants(tree: *IntrusiveMultiRbTree(TestNode)) void {
    const head = tree.headPtr();
    testing.expect(!head.red()) catch @panic("sentinel must be black");
    const root = tree.root();
    if (root == head) return;
    testing.expect(!root.red()) catch @panic("root must be black");
    _ = checkNode(root, std.math.minInt(i32), std.math.maxInt(i32));
}

/// Recursively validates the BST-order and black-height invariants of the subtree
/// rooted at `node`, whose keys are all within `[lo, hi]` (an intentionally loose
/// bound: sibling subtrees can share a boundary key when duplicates exist, so this
/// checks "no key strays outside its ancestors' bounds," not tight per-node bounds).
/// Returns the subtree's black-height.
fn checkNode(node: *NodeBase, lo: i32, hi: i32) u32 {
    if (node.isNil()) return 0;
    const typed: *TestNode = @fieldParentPtr("node", node);
    if (typed.cmpKey(lo) == .lt) @panic("BST order violated (lo bound)");
    if (typed.cmpKey(hi) == .gt) @panic("BST order violated (hi bound)");
    const red = node.red();
    const left = node.child(.left);
    const right = node.child(.right);
    if (red) {
        if (left.red()) @panic("red node has a red child");
        if (right.red()) @panic("red node has a red child");
    }
    const left_h = checkNode(left, lo, hi);
    const right_h = checkNode(right, lo, hi);
    if (left_h != right_h) @panic("unequal black-height across children");
    return left_h + @intFromBool(!red);
}

test "a new tree is empty" {
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    try testing.expect(tree.isEmpty());
    try testing.expect(tree.minimum() == null);
    try testing.expect(tree.lowerBound(0) == null);
}

test "a single insert is findable" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    const a = try boxed(allocator, 5, 0);
    defer allocator.destroy(a);

    tree.insert(a);
    try testing.expect(!tree.isEmpty());
    try testing.expectEqual(a, tree.minimum());
    try testing.expectEqual(a, tree.lowerBound(5));
    checkInvariants(&tree);
    tree.erase(a);
    try testing.expect(tree.isEmpty());
}

test "ascending insert stress maintains invariants" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    var nodes: [200]*TestNode = undefined;
    for (0..200) |k| nodes[k] = try boxed(allocator, @intCast(k), 0);
    defer for (nodes) |n| allocator.destroy(n);

    for (nodes) |n| {
        tree.insert(n);
        checkInvariants(&tree);
    }
    try testing.expectEqual(@as(i32, 0), tree.minimum().?.key);
    for (nodes) |n| {
        tree.erase(n);
        checkInvariants(&tree);
    }
    try testing.expect(tree.isEmpty());
}

test "descending insert stress maintains invariants" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    var nodes: [200]*TestNode = undefined;
    for (0..200) |k| nodes[199 - k] = try boxed(allocator, @intCast(k), 0);
    defer for (nodes) |n| allocator.destroy(n);

    for (nodes) |n| {
        tree.insert(n);
        checkInvariants(&tree);
    }
    for (nodes) |n| {
        tree.erase(n);
        checkInvariants(&tree);
    }
    try testing.expect(tree.isEmpty());
}

test "pseudo-random insert/erase stress matches a reference ordered map" {
    // A small xorshift PRNG, seeded fixed for reproducibility — no external RNG
    // dependency, matching the project's determinism stance (ROADMAP.md's
    // cross-port invariant excludes non-value-affecting randomness like this test
    // harness's own seed, but the tree algorithm itself must stay a pure function of
    // the operation sequence, which this test cross-checks).
    const allocator = testing.allocator;
    const State = struct {
        state: u32 = 0x1234_5678,
        fn next(self: *@This()) u32 {
            self.state ^= self.state << 13;
            self.state ^= self.state >> 17;
            self.state ^= self.state << 5;
            return self.state;
        }
    };
    var rng: State = .{};

    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    // Reference oracle: sorted map from key to the list of live nodes holding it, kept
    // sorted so `oracle_min` is O(log n) via `AutoArrayHashMap`'s own iteration — a
    // small fixed-size table (32 keys) makes a plain sorted array simplest here.
    var oracle: [32]std.ArrayList(*TestNode) = undefined;
    for (&oracle) |*bucket| bucket.* = .empty;
    defer for (&oracle) |*bucket| bucket.deinit(allocator);
    var live: std.ArrayList(*TestNode) = .empty;
    defer live.deinit(allocator);

    var step: u32 = 0;
    while (step < 3000) : (step += 1) {
        const key: i32 = @intCast(rng.next() % 32);
        const do_insert = live.items.len == 0 or rng.next() % 3 != 0;
        if (do_insert) {
            const n = try boxed(allocator, key, step);
            tree.insert(n);
            try oracle[@intCast(key)].append(allocator, n);
            try live.append(allocator, n);
        } else {
            const idx: usize = @intCast(rng.next() % @as(u32, @intCast(live.items.len)));
            const n = live.swapRemove(idx);
            const k = n.key;
            tree.erase(n);
            var bucket = &oracle[@intCast(k)];
            const pos = std.mem.indexOfScalar(*TestNode, bucket.items, n).?;
            _ = bucket.swapRemove(pos);
            allocator.destroy(n);
        }
        checkInvariants(&tree);

        var oracle_min: ?i32 = null;
        for (oracle, 0..) |bucket, k| {
            if (bucket.items.len > 0) {
                oracle_min = @intCast(k);
                break;
            }
        }
        const tree_min: ?i32 = if (tree.minimum()) |m| m.key else null;
        try testing.expectEqual(oracle_min, tree_min);
    }
    for (live.items) |n| {
        tree.erase(n);
        allocator.destroy(n);
    }
}

test "duplicate keys chain and all erase cleanly" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    const a = try boxed(allocator, 7, 0);
    defer allocator.destroy(a);
    const b = try boxed(allocator, 7, 1);
    defer allocator.destroy(b);
    const c = try boxed(allocator, 7, 2);
    defer allocator.destroy(c);

    tree.insert(a);
    tree.insert(b);
    tree.insert(c);
    checkInvariants(&tree);
    // Exactly one of the three is tree-attached; lowerBound(7) finds it.
    const found = tree.lowerBound(7).?;
    try testing.expectEqual(@as(i32, 7), found.key);
    tree.erase(a);
    checkInvariants(&tree);
    try testing.expectEqual(@as(i32, 7), tree.lowerBound(7).?.key);
    tree.erase(b);
    checkInvariants(&tree);
    try testing.expectEqual(@as(i32, 7), tree.lowerBound(7).?.key);
    tree.erase(c);
    checkInvariants(&tree);
    try testing.expect(tree.lowerBound(7) == null);
    try testing.expect(tree.isEmpty());
}

test "lower/upper bound semantics" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    const keys = [_]i32{ 10, 20, 20, 30 };
    var nodes: [4]*TestNode = undefined;
    for (keys, 0..) |k, i| nodes[i] = try boxed(allocator, k, 0);
    defer for (nodes) |n| allocator.destroy(n);
    for (nodes) |n| tree.insert(n);

    try testing.expectEqual(@as(i32, 20), tree.lowerBound(15).?.key);
    try testing.expectEqual(@as(i32, 20), tree.lowerBound(20).?.key);
    try testing.expectEqual(@as(i32, 30), tree.upperBound(20).?.key);
    try testing.expect(tree.upperBound(30) == null);
    try testing.expect(tree.lowerBound(31) == null);
    for (nodes) |n| tree.erase(n);
}

test "succ walks duplicates then tree order" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    const ten_a = try boxed(allocator, 10, 0);
    defer allocator.destroy(ten_a);
    const ten_b = try boxed(allocator, 10, 1);
    defer allocator.destroy(ten_b);
    const twenty = try boxed(allocator, 20, 2);
    defer allocator.destroy(twenty);

    tree.insert(ten_a);
    tree.insert(ten_b);
    tree.insert(twenty);
    const first_ten = tree.lowerBound(10).?;
    const after_first = tree.succ(first_ten).?;
    try testing.expectEqual(@as(i32, 10), after_first.key);
    const after_second = tree.succ(after_first).?;
    try testing.expectEqual(@as(i32, 20), after_second.key);
    try testing.expect(tree.succ(after_second) == null);
    tree.erase(ten_a);
    tree.erase(ten_b);
    tree.erase(twenty);
}

test "next walks the equal-key chain and wraps" {
    const allocator = testing.allocator;
    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    const single = try boxed(allocator, 5, 0);
    defer allocator.destroy(single);
    tree.insert(single);
    // A node with no duplicates is its own one-element chain.
    try testing.expectEqual(single, next(single));

    const ten_a = try boxed(allocator, 10, 1);
    defer allocator.destroy(ten_a);
    const ten_b = try boxed(allocator, 10, 2);
    defer allocator.destroy(ten_b);
    const ten_c = try boxed(allocator, 10, 3);
    defer allocator.destroy(ten_c);
    tree.insert(ten_a);
    tree.insert(ten_b);
    tree.insert(ten_c);
    // The chain is circular over exactly the three equal-key members, in some order —
    // walking `next` three times returns to the start, and never visits `single` (a
    // different key) along the way.
    const step1 = next(ten_a);
    const step2 = next(step1);
    const step3 = next(step2);
    try testing.expectEqual(ten_a, step3);
    try testing.expect(step1 == ten_b or step1 == ten_c);
    try testing.expect(step2 == ten_b or step2 == ten_c);
    try testing.expect(step1 != step2);

    tree.erase(single);
    tree.erase(ten_a);
    tree.erase(ten_b);
    tree.erase(ten_c);
}

// Prints, on stdout, the exact same operation trace as `orisnik`'s
// `rbtree::tests::print_oracle_cross_validation_trace` (same PRNG algorithm and
// seed, same insert/erase decision logic), after every step printing the full
// in-order key sequence — including equal-key chain enumeration order, via repeated
// `succ()` from `minimum()`, exactly what `intrusive_multi_rbtree<T>::begin()`/`++`
// walks in the C++ reference.
//
// A manual cross-validation tool, not a correctness assertion: it was run once
// (during this port's Phase 3 development) and diffed byte-for-byte against a fresh
// run of `orisnik`'s own already-C++-oracle-validated trace (same PRNG, same
// decision logic, same print format on both sides) — transitively validating this
// port against the C++ reference through Rust's own prior validation, without
// rebuilding the C++ harness.
//
// Hard-skipped by default (Rust's equivalent uses `#[ignore]`; Zig 0.16 has no
// per-test attribute for this, and its env-var API moved to an `Io`-backed
// `std.process.Environ` for this release with no simple free-function equivalent to
// the old `std.posix.getenv`/`std.process.getEnvVarOwned` — not worth taking on that
// complexity, and unstable besides, for a one-off manual tool). Skipping is not just
// an output-noise nicety: empirically, `zig build test` runs the suite behind a
// `--listen=-` IPC pipe to the build runner, and this test's ~600 KiB of
// `std.debug.print` output corrupts that protocol — the build step fails with
// "unable to read results of configure phase" / "failed command" even though every
// test, including this one, actually passes (confirmed by running the *same* binary
// via plain `zig test src/root.zig`, bypassing `build.zig`, which reports a clean
// "All N tests passed."). Since CI's `zig-ci.yml` runs `zig build test`, this test
// must stay opted-out of the default run, not merely filtered out by convention.
//
// To run it: flip `run_oracle_trace` to `true` below, then run
// `zig test src/root.zig --test-filter "oracle cross"` (plain `zig test`, NOT
// `zig build test`) — add `2>&1 | tee trace.txt` to capture output — and diff against
// a fresh `cargo test --lib -- --ignored --nocapture
// rbtree::tests::print_oracle_cross_validation_trace` if `rbtree.zig`'s tree-shape
// logic is ever revisited. Flip it back to `false` before committing.
test "oracle cross-validation trace (manual tool, not an assertion)" {
    const run_oracle_trace = false;
    if (!run_oracle_trace) return error.SkipZigTest;

    const State = struct {
        state: u32 = 0x1234_5678,
        fn next(self: *@This()) u32 {
            self.state ^= self.state << 13;
            self.state ^= self.state >> 17;
            self.state ^= self.state << 5;
            return self.state;
        }
    };
    var rng: State = .{};
    const allocator = testing.allocator;

    var tree: IntrusiveMultiRbTree(TestNode) = .init();
    var live: std.ArrayList(*TestNode) = .empty;
    defer live.deinit(allocator);

    // 8 KiB: comfortably above the ~2.8 KiB longest line this 3000-step run actually
    // produces (verified empirically). A too-small buffer here is not hypothetical —
    // an earlier 256-byte version of this buffer silently truncated long lines via
    // `bufPrint`'s `catch break` once `live.len` grew past ~90, which briefly looked
    // like a genuine tree-corruption bug (a chain member "disappearing" from the
    // printed walk) until the actual line lengths were measured.
    var buf: [8192]u8 = undefined;
    var step: u32 = 0;
    while (step < 3000) : (step += 1) {
        const key: i32 = @intCast(rng.next() % 32);
        const do_insert = live.items.len == 0 or rng.next() % 3 != 0;
        if (do_insert) {
            const n = try boxed(allocator, key, step);
            tree.insert(n);
            try live.append(allocator, n);
        } else {
            const idx: usize = @intCast(rng.next() % @as(u32, @intCast(live.items.len)));
            const n = live.swapRemove(idx);
            tree.erase(n);
            allocator.destroy(n);
        }
        var w: usize = 0;
        var cur = tree.minimum();
        while (cur) |n| : (cur = tree.succ(n)) {
            const printed = std.fmt.bufPrint(buf[w..], "{d} ", .{n.key}) catch break;
            w += printed.len;
        }
        std.debug.print("{s}\n", .{buf[0..w]});
    }
    for (live.items) |n| {
        tree.erase(n);
        allocator.destroy(n);
    }
}
