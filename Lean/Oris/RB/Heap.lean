-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Fixup

/-!
# `rbtree.rs`'s pointer code, on a model heap

Steps 1, 2, 3a and 3b of the heap layer, as numbered in the plan of `Lean/docs/heap-layer.md`
(§5, whose steps 3a–3d prove §4's theorems 2–5; theorem 1 is `rotateAt_refines`, in step 2).

- **Step 1, the definitions.** Every function below transcribes one function of
  `Rust/src/rbtree.rs`, **one heap update per Rust write, in the Rust's order**, with every read
  where the Rust reads it.
- **Step 2, the abstraction relation and the first refinement theorem.** `Rep`, `RepPath`,
  `Located` and `Tree` say when a heap represents a zipper state of `Oris/RB/Fixup.lean`, and
  `rotateAt_refines_left` and `rotateAt_refines_right` prove that `rotateAt` (`NodeBase::rotate`)
  performs the zipper's rotation.
- **Step 3a, the structural operations.** `attachTo_refines`, `substituteWith_refines_left` and
  `_right`, and `switchWith_refines` prove that `attach_to`, `substitute_with` and `switch_with`
  perform the zipper steps `insert` and `eraseAt` take: fill an empty hole with a red leaf,
  splice out a node with at most one child, put another address at a node's position. Each
  operation, `rotateAt` included, also has a per-address description of its result (`_apply`)
  and the list of records it changes (`_frame`).
- **Step 3b, `insert_fixup`.** `insertFixupLoop_refines` and `insertFixup_refines` prove that
  `insert_fixup` performs `insFix`: the same tree and the same rotation count, from any located
  node in a tree with a black root, given enough fuel. `insertFixup_refines_depth` is the first
  fuel theorem: fuel at least the tree's depth is enough.

Steps 3c (`erase_fixup`), 3d (the cached root) and 4 (the counted operations, the chains and the
transfer theorems) remain.

## The model (the note's §2)

- An address is a `Nat`, and `0` is the null pointer (`null`).
- A node is a `NodeRec`, one field per field of the Rust's `NodeBase`. The tagged `parent` word
  is split into its three parts, as `TaggedPtr`'s accessors split it: `parent` (the pointer),
  `red` (bit `BIT_COLOUR`, set for red) and `side` (bit `BIT_SIDE`, set for right).
- The heap is a total function `Addr → NodeRec`. A write updates one field of one node
  (`Heap.modify`). The Rust's `NodeBase` primitives that write the `parent` word
  (`set_parent_ptr`, `set_parent_side`, `set_colour`) are each one read-modify-write of that
  word, so each is one `Heap.modify` here.
- Two of `NodeBase`'s functions share their names with `Fixup.lean`'s zipper models of the same
  Rust: here they are `childAt` and `rotateAt` (an address in a heap, where the zipper's `child`
  and `rotate` take a subtree), so that both levels can be named in one statement.
- Rust's `Colour` enum is modelled as a `Bool` (`true` for red), the colour bit itself.
- Keys: the descent of `insert_counted` compares nodes with the Rust's `T::cmp`; here, with
  `cmp (key a) (key b)` for a fixed `key : Addr → α`.
- The loops (`insert_fixup`, `erase_fixup` and the two descents) take explicit fuel and return
  `none` when it runs out. That is this file's one departure from the Rust's behaviour: the Rust
  loops until the tree's structure stops them. Each loop spends one unit of fuel on its final,
  failing test, so fuel at least the tree's height **plus one** (its size plus one, for the
  descents) suffices. For `insert_fixup` this is proven (`insertFixup_refines_depth`: fuel at
  least `RBNode.depth`, the number of nodes on the longest branch, which is the height in edges
  plus one); for `erase_fixup` and the descents it is the plan's steps 3c and 4. Each loop's doc
  repeats this.
- `erase_fixup`'s root comes in two readings: `eraseFixup` reads it once on entry, as the Rust
  does, and `eraseFixupHpha` re-reads it, as `Cpp/hpha.cpp` does (reading it before testing
  `cur`'s colour, where HPHA's `&&` short-circuits: a read, so no field changes). The note's §6
  plans the theorem that they agree on a tree with a black root (on a red root they need not).

## Not modelled

Reads and effects of the Rust that change no field of any node, each also named in the doc of
the definition it concerns:
- The lazy sentinel (`head_ptr`): its first-touch self-linking, and the test of
  `head.children[Right]` it makes on every call (twice in `insert_counted`, through `head_ptr`
  and `root`). The operations here take an initialized `head`; `initHead` performs that first
  touch's writes, for tools that start from an empty tree.
- The Rust's `debug_assert!`s and their reads (`switch_with`'s `is_attached(node)` and
  `this != node`, `erase_counted`'s `repl != head` and `is_attached(repl)`).
- The rotation witness `tests::count_rotation`, which `rotate` calls in test builds.
-/

namespace Oris.RB

/-- `rbtree.rs` `Side::other`: the other side. -/
def Side.other : Side → Side
  | .left => .right
  | .right => .left

namespace Heap

/-- A node's address. `0` is the null pointer. -/
abbrev Addr := Nat

/-- The null pointer. -/
def null : Addr := 0

/-- `rbtree.rs` `NodeBase`: `children[0]`/`children[1]` are `left`/`right`,
`neighbours[0]`/`neighbours[1]` are `prev`/`next` (the equal-key chain), and the tagged `parent`
word is `parent`, `red` and `side`. The defaults are `NodeBase::UNLINKED` (every link null, both
tag bits clear). -/
structure NodeRec where
  left : Addr := null
  right : Addr := null
  prev : Addr := null
  next : Addr := null
  parent : Addr := null
  red : Bool := false
  side : Side := .left
  deriving DecidableEq, Repr

instance : Inhabited NodeRec := ⟨{}⟩

/-- The model heap: every address holds a node record. -/
abbrev Heap := Addr → NodeRec

/-- One write: `f` applied to the record at `a`, every other address unchanged. -/
def Heap.modify (h : Heap) (a : Addr) (f : NodeRec → NodeRec) : Heap :=
  fun b => if b = a then f (h a) else h b

/-! ## `NodeBase`'s accessors (reads) -/

/-- `NodeBase::child`: `children[s]`. Named `childAt`, not `child`, to keep it apart from the
zipper's `Oris.RB.child` (`Fixup.lean`), which this file also uses. -/
def childAt (h : Heap) (a : Addr) : Side → Addr
  | .left => (h a).left
  | .right => (h a).right

/-- `NodeBase::neighbour`: `neighbours[s]`. -/
def neighbour (h : Heap) (a : Addr) : Side → Addr
  | .left => (h a).prev
  | .right => (h a).next

/-- `NodeBase::parent`: the `parent` word's pointer. -/
def parent (h : Heap) (a : Addr) : Addr := (h a).parent

/-- `NodeBase::parent_side`: the `parent` word's side bit. -/
def parentSide (h : Heap) (a : Addr) : Side := (h a).side

/-- `NodeBase::colour` and `NodeBase::red`: the `parent` word's colour bit. -/
def red (h : Heap) (a : Addr) : Bool := (h a).red

/-- `NodeBase::is_attached`: a non-null `parent`. -/
def isAttached (h : Heap) (a : Addr) : Bool := parent h a != null

/-- `NodeBase::chained`: `neighbours[Left]` is not the node itself. -/
def chained (h : Heap) (a : Addr) : Bool := (h a).prev != a

/-! ## `NodeBase`'s mutators (one write each) -/

/-- `NodeBase::set_child`. -/
def setChild (h : Heap) (a : Addr) (s : Side) (v : Addr) : Heap :=
  h.modify a fun n => match s with
    | .left => { n with left := v }
    | .right => { n with right := v }

/-- `NodeBase::set_neighbour`. -/
def setNeighbour (h : Heap) (a : Addr) (s : Side) (v : Addr) : Heap :=
  h.modify a fun n => match s with
    | .left => { n with prev := v }
    | .right => { n with next := v }

/-- `NodeBase::set_parent_ptr`: replaces the pointer, keeping both tag bits. -/
def setParentPtr (h : Heap) (a : Addr) (v : Addr) : Heap :=
  h.modify a fun n => { n with parent := v }

/-- `NodeBase::set_parent_side`: replaces the side bit. -/
def setParentSide (h : Heap) (a : Addr) (s : Side) : Heap :=
  h.modify a fun n => { n with side := s }

/-- `NodeBase::set_colour`: replaces the colour bit (`true` for red). -/
def setColour (h : Heap) (a : Addr) (c : Bool) : Heap :=
  h.modify a fun n => { n with red := c }

/-- `NodeBase::make_red`. -/
def makeRed (h : Heap) (a : Addr) : Heap := setColour h a true

/-- `NodeBase::make_black`. -/
def makeBlack (h : Heap) (a : Addr) : Heap := setColour h a false

/-- `IntrusiveMultiRbTree::head_ptr`'s first-touch writes: the sentinel self-linked in all three
link groups, its `parent` word `TaggedPtr::new(head, 0)` (pointer `head`, black, left side),
written whole by `raw_set_parent`. -/
def initHead (h : Heap) (head : Addr) : Heap :=
  let h := setChild h head .left head
  let h := setChild h head .right head
  let h := setNeighbour h head .left head
  let h := setNeighbour h head .right head
  h.modify head fun n => { n with parent := head, red := false, side := .left }

/-! ## Structural operations -/

/-- `NodeBase::rotate`: rotates `this` down and its side-`o` child (`o = s.other`) up into
`this`'s former position. Four reads (`this`'s side and parent, its side-`o` child `top`, and
`top`'s side-`s` child), then nine writes, in the Rust's order. When `top`'s side-`s` child is
the sentinel, the second and third writes land on the sentinel's `parent` word (its scratch
fields; `docs/heap-layer.md`, §1). Not modelled: the test builds' call to
`tests::count_rotation`. Named `rotateAt`, not `rotate`, to keep it apart from the zipper's
`Oris.RB.rotate` (`Fixup.lean`), which the refinement theorems below state their results with. -/
def rotateAt (h : Heap) (this : Addr) (s : Side) : Heap :=
  let o := s.other
  let ps := parentSide h this
  let thisParent := parent h this
  let top := childAt h this o
  let topSChild := childAt h top s
  let h := setChild h this o topSChild
  let h := setParentPtr h topSChild this
  let h := setParentSide h topSChild o
  let h := setParentPtr h top thisParent
  let h := setParentSide h top ps
  let h := setChild h thisParent ps top
  let h := setChild h top s this
  let h := setParentPtr h this top
  setParentSide h this s

/-- `NodeBase::attach_to`: `this` becomes `parent`'s side-`s` child, a red leaf with no
equal-key duplicates. Its two children are `parent`'s old side-`s` child, read after the two
neighbour writes, as in the Rust (the sentinel, when the caller's descent ended there). -/
def attachTo (h : Heap) (this parent : Addr) (s : Side) : Heap :=
  let h := setNeighbour h this .left this
  let h := setNeighbour h this .right this
  let leafChild := childAt h parent s
  let h := setChild h this .left leafChild
  let h := setChild h this .right leafChild
  let h := setParentPtr h this parent
  let h := setParentSide h this s
  let h := setChild h parent s this
  makeRed h this

/-- `NodeBase::substitute_with`: `child` takes `this`'s place under `this`'s parent, its own
colour untouched. When `child` is the sentinel, this writes the sentinel's scratch `parent` and
side: how `erase_fixup` later finds an empty hole's parent, unless `switch_with` overwrites them
first (see `switchWith`). -/
def substituteWith (h : Heap) (this child : Addr) : Heap :=
  let ps := parentSide h this
  let thisParent := parent h this
  let h := setParentPtr h child thisParent
  let h := setParentSide h child ps
  setChild h thisParent ps child

/-- `NodeBase::switch_with`: `this` takes `node`'s tree position, children and colour. The
reads of `node`'s parent and colour come after the writes before them, as in the Rust.

When one of `node`'s children is the sentinel at the time of the call, the writes to that
child's `parent` word land on the sentinel's scratch fields. This happens in a two-child erase
whose successor `repl` was `node`'s right child with no right child of its own: `substitute_with`
has just written the sentinel's scratch `parent` as `node`, and this overwrites it as `this`
(`repl`), side right, which is where the hole now is; `erase_fixup` reads this second value. Not
modelled: the `debug_assert!`s on `is_attached(node)` and `this != node`. -/
def switchWith (h : Heap) (this node : Addr) : Heap :=
  let nps := parentSide h node
  let nodeLeft := childAt h node .left
  let nodeRight := childAt h node .right
  let h := setChild h this .left nodeLeft
  let h := setChild h this .right nodeRight
  let nodeParent := parent h node
  let h := setParentPtr h this nodeParent
  let h := setParentSide h this nps
  let h := setParentPtr h nodeLeft this
  let h := setParentSide h nodeLeft .left
  let h := setParentPtr h nodeRight this
  let h := setParentSide h nodeRight .right
  let h := setChild h nodeParent nps this
  let nodeColour := red h node
  setColour h this nodeColour

/-- `NodeBase::unlink_from_chain`: removes `this` from its equal-key chain. -/
def unlinkFromChain (h : Heap) (this : Addr) : Heap :=
  let next := (h this).next
  let prev := (h this).prev
  let h := setNeighbour h next .left prev
  setNeighbour h prev .right next

/-- `NodeBase::link_into_chain`: chains `this` into `node`'s equal-key group, just before
`node`, as a plain chain link (null children and parent, left side, red). -/
def linkIntoChain (h : Heap) (this node : Addr) : Heap :=
  let nodePrev := (h node).prev
  let h := setNeighbour h this .left nodePrev
  let h := setNeighbour h this .right node
  let h := setNeighbour h node .left this
  let h := setNeighbour h nodePrev .right this
  let h := setChild h this .left null
  let h := setChild h this .right null
  let h := setParentPtr h this null
  let h := setParentSide h this .left
  makeRed h this

/-! ## The fix-ups -/

/-- The loop of `rbtree.rs` `insert_fixup`, from its test `while red(p)`, with the rotations counted
so far. The first branch is the red uncle (recolour and climb); the second rotates once or twice and
leaves `p` black, so the next test ends the loop. On exit: `make_black(head.child(Left))`, the root
as it is then. The fuel is this file's one departure from the Rust (see the module doc): `none` when
it runs out, which fuel at least the tree's depth rules out (`insertFixup_refines_depth`). -/
def insertFixupLoop (head : Addr) : Nat → Heap → Addr → Addr → Nat → Option (Heap × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, h, cur, p, rotations =>
    if red h p then
      let pp := parent h p
      let s := parentSide h p
      let o := s.other
      let ppRight := childAt h pp o
      if red h ppRight then
        -- Red uncle: `make_black(p); make_black(pp_right); make_red(pp); cur = pp`.
        let h := makeBlack h p
        let h := makeBlack h ppRight
        let h := makeRed h pp
        let cur := pp
        insertFixupLoop head fuel h cur (parent h cur) rotations
      else
        -- Black uncle: if `cur == p_o_child`, `cur = p; rotate(cur, s)` first (inner case),
        -- then `make_black(p); make_red(pp); rotate(pp, o)`.
        let pOChild := childAt h p o
        let (h, cur, p, rotations) :=
          if cur = pOChild then
            let cur := p
            let h := rotateAt h cur s
            (h, cur, parent h cur, rotations + 1)
          else (h, cur, p, rotations)
        let h := makeBlack h p
        let h := makeRed h pp
        let h := rotateAt h pp o
        insertFixupLoop head fuel h cur p (rotations + 1)
    else
      let root := childAt h head .left
      some (makeBlack h root, rotations)

/-- `rbtree.rs` `insert_fixup`: rebalances after `attach_to` attached `node` as a red leaf, and
returns the rotations performed. The fuel is this file's one departure from the Rust (see the module
doc): `none` when it runs out, which fuel at least the tree's depth rules out
(`insertFixup_refines_depth`). -/
def insertFixup (fuel : Nat) (h : Heap) (head node : Addr) : Option (Heap × Nat) :=
  insertFixupLoop head fuel h node (parent h node) 0

/-- The loop of `rbtree.rs` `erase_fixup`, from its test `while !red(cur) && cur != root`, with the
rotations counted so far. `reread` chooses how `root` is read: `false` is the Rust's (the value
`root₀` read once on entry, used in the loop test and for the fourth case's `cur = root`), `true` is
`Cpp/hpha.cpp`'s (`mHead.child(LEFT)`, read afresh at each of those uses). The first case (`w` red)
runs first if it applies, then the second (`w`'s children both black: `make_red(w); cur = p`), or
the third if it applies and the fourth (which ends the loop). On exit: `make_black(cur)`. With
`reread`, the root is read before the test's `&&`, where HPHA reads it only when `cur` is black: a
read, so no field changes. The fuel is this file's one departure from the Rust (see the module doc):
`none` when it runs out. -/
def eraseFixupLoop (head : Addr) (reread : Bool) (root₀ : Addr) :
    Nat → Heap → Addr → Nat → Option (Heap × Nat)
  | 0, _, _, _ => none
  | fuel + 1, h, cur, rotations =>
    let root := if reread then childAt h head .left else root₀
    if !red h cur && cur != root then
      let p := parent h cur
      let s := parentSide h cur
      let o := s.other
      let w := childAt h p o
      -- First case: `w` red.
      let (h, w, rotations) :=
        if red h w then
          let h := makeBlack h w
          let h := makeRed h p
          let w := childAt h w s
          let h := rotateAt h p s
          (h, w, rotations + 1)
        else (h, w, rotations)
      let wLeft := childAt h w .left
      let wRight := childAt h w .right
      let wLeftBlack := !red h wLeft
      let wRightBlack := !red h wRight
      if wLeftBlack && wRightBlack then
        -- Second case.
        let h := makeRed h w
        eraseFixupLoop head reread root₀ fuel h p rotations
      else
        -- Third case, if `w`'s side-`o` child is black.
        let wOChild := childAt h w o
        let (h, w, rotations) :=
          if !red h wOChild then
            let wSChild := childAt h w s
            let h := makeBlack h wSChild
            let h := makeRed h w
            let c := wSChild
            let h := rotateAt h w o
            (h, c, rotations + 1)
          else (h, w, rotations)
        -- Fourth case.
        let pColour := red h p
        let h := setColour h w pColour
        let h := makeBlack h p
        let wOChild := childAt h w o
        let h := makeBlack h wOChild
        let h := rotateAt h p s
        let cur := if reread then childAt h head .left else root₀
        eraseFixupLoop head reread root₀ fuel h cur (rotations + 1)
    else
      some (makeBlack h cur, rotations)

/-- `erase_fixup` with its root read as `reread` chooses (see `eraseFixupLoop`): rebalances after a
black node was spliced out, starting from the child that took its place (possibly the sentinel), and
returns the rotations performed. `root₀` is read on entry, as the Rust reads `root`. The fuel is
this file's one departure from the Rust (see the module doc): `none` when it runs out. -/
def eraseFixupWith (reread : Bool) (fuel : Nat) (h : Heap) (head node : Addr) :
    Option (Heap × Nat) :=
  eraseFixupLoop head reread (childAt h head .left) fuel h node 0

/-- `rbtree.rs` `erase_fixup`: the root read once, on entry, as the Rust does. -/
def eraseFixup (fuel : Nat) (h : Heap) (head node : Addr) : Option (Heap × Nat) :=
  eraseFixupWith false fuel h head node

/-- `Cpp/hpha.cpp` `erase_fixup`: the root (`mHead.child(LEFT)`) re-read at each use. -/
def eraseFixupHpha (fuel : Nat) (h : Heap) (head node : Addr) : Option (Heap × Nat) :=
  eraseFixupWith true fuel h head node

/-! ## The tree operations -/

/-- The descent of `rbtree.rs` `insert_counted`, from its test `while cur != end`: `inl cur` if it
meets a node with an equal key, `inr (last, s)` if it reaches the sentinel below `last` on side `s`.
The fuel is this file's one departure from the Rust (see the module doc): `none` when it runs out.
-/
def insertDescent {α : Type _} (cmp : α → α → Ordering) (key : Addr → α) (h : Heap)
    (head node : Addr) : Nat → Addr → Addr → Side → Option (Addr ⊕ (Addr × Side))
  | 0, _, _, _ => none
  | fuel + 1, last, cur, s =>
    if cur != head then
      let last := cur
      match cmp (key node) (key cur) with
      | .lt => insertDescent cmp key h head node fuel last (childAt h cur .left) .left
      | .gt => insertDescent cmp key h head node fuel last (childAt h cur .right) .right
      | .eq => some (.inl cur)
    else some (.inr (last, s))

/-- `rbtree.rs` `IntrusiveMultiRbTree::insert_counted`: inserts `node`, chaining it onto an existing
element with an equal key (`Chain`, no rotation) or attaching it as a red leaf and rebalancing
(`Node`). The fuel is this file's one departure from the Rust (see the module doc): `none` when it
runs out. Not modelled: `head_ptr`'s lazy-initialization test (the `head` here is initialized). -/
def insertCounted {α : Type _} (cmp : α → α → Ordering) (key : Addr → α) (fuel : Nat)
    (h : Heap) (head node : Addr) : Option (Heap × InsertKind × Nat) :=
  match insertDescent cmp key h head node fuel head (childAt h head .left) .left with
  | none => none
  | some (.inl cur) => some (linkIntoChain h node cur, .chain, 0)
  | some (.inr (last, s)) =>
    let h := attachTo h node last s
    (insertFixup fuel h head node).map fun (h, rotations) => (h, .node, rotations)

/-- The descent of `rbtree.rs` `erase_counted` to the in-order successor, from its test `while
repl_left != end`: the leftmost node below `repl`. The fuel is this file's one departure from the
Rust (see the module doc): `none` when it runs out. -/
def successorDescent (h : Heap) (head : Addr) : Nat → Addr → Addr → Option Addr
  | 0, _, _ => none
  | fuel + 1, repl, replLeft =>
    if replLeft != head then successorDescent h head fuel replLeft (childAt h replLeft .left)
    else some repl

/-- `rbtree.rs` `IntrusiveMultiRbTree::erase_counted`, with `erase_fixup`'s root read as `reread`
chooses (see `eraseFixupLoop`). A chained, non-attached node is unlinked (`Link`); a chained,
attached one hands its tree position to its chain successor (`Promote`); otherwise the node, or its
in-order successor if it has two children, is spliced out, the successor takes the node's place, and
the tree is rebalanced if the spliced node was black (`Node`). The fuel is this file's one departure
from the Rust (see the module doc): `none` when it runs out. Not modelled: `head_ptr`'s
lazy-initialization test, and the `debug_assert!`s on `repl != head` and `is_attached(repl)`. -/
def eraseCountedWith (reread : Bool) (fuel : Nat) (h : Heap) (head node : Addr) :
    Option (Heap × EraseKind × Nat) :=
  if chained h node then
    if !isAttached h node then some (unlinkFromChain h node, .link, 0)
    else
      let repl := neighbour h node .right
      let h := switchWith h repl node
      some (unlinkFromChain h node, .promote, 0)
  else
    let right := childAt h node .right
    let found : Option (Addr × Side) :=
      if right != head then
        let left := childAt h node .left
        if left != head then
          (successorDescent h head fuel right (childAt h right .left)).map fun repl =>
            (repl, .right)
        else some (node, .right)
      else some (node, .left)
    found.bind fun (repl, s) =>
      let replRed := red h repl
      let replChild := childAt h repl s
      let h := substituteWith h repl replChild
      let h := if repl != node then switchWith h repl node else h
      if replRed then some (h, .node, 0)
      else
        (eraseFixupWith reread fuel h head replChild).map fun (h, rotations) =>
          (h, .node, rotations)

/-- `rbtree.rs` `IntrusiveMultiRbTree::erase_counted`, reading `erase_fixup`'s root once, as the
Rust does. -/
def eraseCounted (fuel : Nat) (h : Heap) (head node : Addr) : Option (Heap × EraseKind × Nat) :=
  eraseCountedWith false fuel h head node

/-- `erase_counted` with `Cpp/hpha.cpp`'s reading of `erase_fixup`'s root. -/
def eraseCountedHpha (fuel : Nat) (h : Heap) (head node : Addr) :
    Option (Heap × EraseKind × Nat) :=
  eraseCountedWith true fuel h head node

/-! ## The abstraction relation (step 2 of the note)

When a heap *is* a zipper state: `Rep` for a subtree, `RepPath` for its ancestors, `Located` for
the pair. Their basic lemmas: no address occurs twice in a represented tree (`Rep.nodup`), writes
outside a tree preserve it (`Rep.frame`, `RepPath.frame`), and a slot can change occupant
(`RepPath.retarget`). Then the first refinement theorem: `rotateAt` performs the zipper's
`rotate` (`rotateAt_refines_left`, `rotateAt_refines_right`). -/

open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- The colour bit `NodeBase` stores for a colour (`TaggedPtr`'s bit `BIT_COLOUR`): set for
red. It links `RBColor`, the zipper level's colours, to `NodeRec.red`. -/
def colourBit : RBColor → Bool
  | .red => true
  | .black => false

/-- Distinct colours have distinct bits. -/
theorem colourBit_inj {c c' : RBColor} (h : colourBit c = colourBit c') : c = c' := by
  cases c <;> cases c' <;> first | rfl | cases h

/-- The abstraction relation (the note's §3). `Rep h head a p s t`: in heap `h`, with sentinel
`head`, the subtree starting at address `a` *is* the tree of addresses `t`, and its first node's
tagged `parent` word names the slot `(p, s)`: side `s` of `p`. That `p`'s link points back to `a`
is `RepPath`'s part.

* An empty subtree is the sentinel itself (`nil`), and constrains nothing. `Rep` never reads the
  sentinel's record, so no write to the sentinel (its scratch `parent` and side included) can
  break it (`Rep.frame`, with `Rep.mem_ne`).
* A node (`node`) is a real address (neither the sentinel nor null) whose tagged `parent` word
  names `p` and `s` and holds `c`'s colour bit, and whose two children represent `l` and `r`.

The represented tree is a tree of *distinct* addresses (`Rep.nodup`), which is what makes frame
reasoning sound (`Rep.frame`). The tree stores addresses, not keys, so node identity survives
(the note's §2). -/
inductive Rep (h : Heap) (head : Addr) : Addr → Addr → Side → RBNode Addr → Prop
  | nil {p : Addr} {s : Side} : Rep h head head p s .nil
  | node {a p : Addr} {s : Side} {c : RBColor} {l r : RBNode Addr} :
      a ≠ head → a ≠ null → (h a).parent = p → (h a).side = s → (h a).red = colourBit c →
      Rep h head (h a).left a .left l → Rep h head (h a).right a .right r →
      Rep h head a p s (.node c l a r)

/-- `x`'s ancestor `n` levels up, read along `parent` pointers. Used by `Rep.nodup`'s proof. -/
def ancestor (h : Heap) (x : Addr) : Nat → Addr
  | 0 => x
  | n + 1 => (h (ancestor h x n)).parent

namespace Rep

variable {h h' : Heap} {head a p : Addr} {s : Side} {t : RBNode Addr}

/-- An empty subtree starts at the sentinel. -/
theorem nil_inv (hr : Rep h head a p s .nil) : a = head := by
  cases hr; rfl

/-- What a node's `Rep` says, read back: the inversion of `Rep.node`. -/
theorem node_inv {c : RBColor} {l r : RBNode Addr} {v : Addr}
    (hr : Rep h head a p s (.node c l v r)) :
    a = v ∧ v ≠ head ∧ v ≠ null ∧ (h v).parent = p ∧ (h v).side = s ∧
      (h v).red = colourBit c ∧
      Rep h head (h v).left v .left l ∧ Rep h head (h v).right v .right r := by
  cases hr with
  | node ha hn hp hs hc hl hr => exact ⟨rfl, ha, hn, hp, hs, hc, hl, hr⟩

/-- No address of a represented tree is the sentinel or null. -/
theorem mem_ne (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    x ≠ head ∧ x ≠ null := by
  induction hr with
  | nil => simp at hx
  | node ha hn _ _ _ _ _ ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact ihl hx
    · exact ⟨ha, hn⟩
    · exact ihr hx

/-- A subtree that does not start at the sentinel contains its starting address. -/
theorem root_mem (hr : Rep h head a p s t) (ha : a ≠ head) : a ∈ t.toList := by
  cases hr with
  | nil => exact absurd rfl ha
  | node => simp

/-- A non-empty subtree's first node points back to the slot it hangs in. -/
theorem root_fields (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    (h a).parent = p ∧ (h a).side = s := by
  cases hr with
  | nil => simp at hx
  | node _ _ hp hs => exact ⟨hp, hs⟩

/-- From any address of a subtree, following `parent` pointers reaches the subtree's first node,
staying inside the subtree on the way. -/
theorem climb (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    ∃ n, ancestor h x n = a ∧ ∀ k ≤ n, ancestor h x k ∈ t.toList := by
  induction hr with
  | nil => simp at hx
  | @node a p s c l r _ _ _ _ _ hl hr ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | rfl | hx
    · obtain ⟨n, hn, hk⟩ := ihl hx
      have hup : ancestor h x (n + 1) = a := by
        show (h (ancestor h x n)).parent = _
        rw [hn]; exact (hl.root_fields hx).1
      refine ⟨n + 1, hup, fun k hk' => ?_⟩
      by_cases hkn : k ≤ n
      · exact .inl (hk k hkn)
      · obtain rfl : k = n + 1 := by omega
        exact .inr (.inl hup)
    · refine ⟨0, rfl, fun k hk => ?_⟩
      obtain rfl : k = 0 := by omega
      exact .inr (.inl rfl)
    · obtain ⟨n, hn, hk⟩ := ihr hx
      have hup : ancestor h x (n + 1) = a := by
        show (h (ancestor h x n)).parent = _
        rw [hn]; exact (hr.root_fields hx).1
      refine ⟨n + 1, hup, fun k hk' => ?_⟩
      by_cases hkn : k ≤ n
      · exact .inr (.inr (hk k hkn))
      · obtain rfl : k = n + 1 := by omega
        exact .inr (.inl hup)

/-- Every address of a subtree starts a subtree of its own, no larger. -/
theorem sub (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    ∃ q σ u, Rep h head x q σ u ∧ u.size ≤ t.size := by
  induction hr with
  | nil => simp at hx
  | node ha hn hp hs hc hl hr ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · obtain ⟨q, σ, u, hu, hsz⟩ := ihl hx
      exact ⟨q, σ, u, hu, by simp only [RBNode.size]; omega⟩
    · exact ⟨_, _, _, .node ha hn hp hs hc hl hr, Nat.le_refl _⟩
    · obtain ⟨q, σ, u, hu, hsz⟩ := ihr hx
      exact ⟨q, σ, u, hu, by simp only [RBNode.size]; omega⟩

/-- The heap determines the tree: two `Rep`s from the same address represent the same tree,
whatever slot each claims. -/
theorem unique {p' : Addr} {s' : Side} {t' : RBNode Addr}
    (h₁ : Rep h head a p s t) (h₂ : Rep h head a p' s' t') : t = t' := by
  induction h₁ generalizing p' s' t' with
  | nil =>
    cases h₂ with
    | nil => rfl
    | node ha => exact absurd rfl ha
  | node ha _ _ _ hc _ _ ihl ihr =>
    cases h₂ with
    | nil => exact absurd rfl ha
    | node _ _ _ _ hc' hl' hr' => rw [ihl hl', ihr hr', colourBit_inj (hc.symm.trans hc')]

/-- **No address occurs twice in a represented tree** (the note's `Repr.nodup`), from `Rep` alone,
with no separate distinctness hypothesis. A node cannot occur below itself: by `unique` (the heap
determines the tree) it would start a tree as large as the one containing it. Its two subtrees are
disjoint thanks to the back-pointers: climbing `parent` pointers from a shared address would reach
the node's left and right children at the same height (whose side bits differ), or reach the node
inside one of them. -/
theorem nodup (hr : Rep h head a p s t) : t.toList.Nodup := by
  induction hr with
  | nil => simp
  | @node a p s c l r ha hn hp hs hc hl hr ihl ihr =>
    have hself : Rep h head a p s (.node c l a r) := .node ha hn hp hs hc hl hr
    have hal : a ∉ l.toList := fun hx => by
      obtain ⟨q, σ, u, hu, hsz⟩ := hl.sub hx
      obtain rfl := hself.unique hu
      simp only [RBNode.size] at hsz; omega
    have har : a ∉ r.toList := fun hx => by
      obtain ⟨q, σ, u, hu, hsz⟩ := hr.sub hx
      obtain rfl := hself.unique hu
      simp only [RBNode.size] at hsz; omega
    have hdis : ∀ x ∈ l.toList, x ∉ r.toList := fun x hxl hxr => by
      obtain ⟨n₁, h₁, hk₁⟩ := hl.climb hxl
      obtain ⟨n₂, h₂, hk₂⟩ := hr.climb hxr
      have sl := hl.root_fields hxl
      have sr := hr.root_fields hxr
      rcases Nat.lt_trichotomy n₁ n₂ with hlt | rfl | hgt
      · apply har
        have := hk₂ (n₁ + 1) hlt
        have e : ancestor h x (n₁ + 1) = a := by
          show (h (ancestor h x n₁)).parent = a
          rw [h₁]; exact sl.1
        rwa [e] at this
      · have e : (h a).left = (h a).right := h₁.symm.trans h₂
        rw [e] at sl
        cases sl.2.symm.trans sr.2
      · apply hal
        have := hk₁ (n₂ + 1) hgt
        have e : ancestor h x (n₂ + 1) = a := by
          show (h (ancestor h x n₂)).parent = a
          rw [h₂]; exact sr.1
        rwa [e] at this
    simp only [RBNode.toList_node, List.nodup_append, List.nodup_cons, List.mem_cons]
    refine ⟨ihl, ⟨har, ihr⟩, fun x hx y hy => ?_⟩
    rcases hy with rfl | hy
    · rintro rfl; exact hal hx
    · rintro rfl; exact hdis x hx hy

/-- **The frame lemma.** A heap that agrees with `h` on every address of `t` represents `t` at
the same slot. Writes elsewhere, to any field of the sentinel included, preserve `Rep`. -/
theorem frame (hr : Rep h head a p s t) (hf : ∀ x ∈ t.toList, h' x = h x) :
    Rep h' head a p s t := by
  induction hr with
  | nil => exact .nil
  | @node a p s c l r ha hn hp hs hc _ _ ihl ihr =>
    have haa : h' a = h a := hf a (by simp)
    refine .node ha hn (by rw [haa]; exact hp) (by rw [haa]; exact hs) (by rw [haa]; exact hc)
      ?_ ?_
    · rw [haa]; exact ihl fun x hx => hf x (by simp [hx])
    · rw [haa]; exact ihr fun x hx => hf x (by simp [hx])

/-- The frame lemma for a subtree that moves to a new slot: when the first node keeps its
children and colour but takes a new `parent` and side (as the subtree `rotateAt` moves across does),
and every other address of `t` keeps its record, the subtree is represented at the new slot. -/
theorem reroot {p' : Addr} {s' : Side} (hr : Rep h head a p s t)
    (hroot : a ≠ head → (h' a).left = (h a).left ∧ (h' a).right = (h a).right ∧
      (h' a).red = (h a).red ∧ (h' a).parent = p' ∧ (h' a).side = s')
    (hrest : ∀ x ∈ t.toList, x ≠ a → h' x = h x) : Rep h' head a p' s' t := by
  have hnd := hr.nodup
  cases hr with
  | nil => exact .nil
  | node ha hn _ _ hc hl hr =>
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := hroot ha
    simp only [RBNode.toList_node, List.nodup_append, List.nodup_cons] at hnd
    refine .node ha hn e₄ e₅ (e₃.trans hc) ?_ ?_
    · rw [e₁]
      exact hl.frame fun x hx => hrest x (by simp [hx])
        (by rintro rfl; exact hnd.2.2 x hx x (by simp) rfl)
    · rw [e₂]
      exact hr.frame fun x hx => hrest x (by simp [hx]) (by rintro rfl; exact hnd.2.1.1 hx)

end Rep

/-- The ancestors' half of the abstraction relation (the note's `ReprPath`). `RepPath h head a p s
path`: the slot `(p, s)`, the side-`s` child link of `p`, holds `a` and lies at `path` in the
tree. At the top (`root`), the slot is the sentinel's left link, the sentinel's right link points
to itself and the sentinel is black. Below a node `y` (`left`, `right`), `y` is a real address
holding `a` in that child link, with the path's colour for `y`, its other child representing the
path's sibling subtree, and `y`'s own slot, read from its tagged `parent` word, lying at the rest
of the path.

The slot's occupant `a` is an index, not read from `a` itself, so the relation holds equally of an
empty hole (`a` the sentinel, whose own `parent` field is scratch). -/
inductive RepPath (h : Heap) (head : Addr) : Addr → Addr → Side → Path Addr → Prop
  | root {a : Addr} : (h head).left = a → (h head).right = head → (h head).red = false →
      RepPath h head a head .left .root
  | left {a y : Addr} {c : RBColor} {pp : Path Addr} {b : RBNode Addr} :
      y ≠ head → y ≠ null → (h y).left = a → (h y).red = colourBit c →
      Rep h head (h y).right y .right b → RepPath h head y (h y).parent (h y).side pp →
      RepPath h head a y .left (.left c pp y b)
  | right {a y : Addr} {c : RBColor} {pp : Path Addr} {b : RBNode Addr} :
      y ≠ head → y ≠ null → (h y).right = a → (h y).red = colourBit c →
      Rep h head (h y).left y .left b → RepPath h head y (h y).parent (h y).side pp →
      RepPath h head a y .right (.right c b y pp)

/-- A located subtree, the heap counterpart of a zipper pair `(t, path)`: the subtree `t` hangs at
the slot `(p, s)`, which holds `a` and lies at `path`. -/
def Located (h : Heap) (head a p : Addr) (s : Side) (t : RBNode Addr) (path : Path Addr) :
    Prop :=
  Rep h head a p s t ∧ RepPath h head a p s path

/-- A whole tree: the sentinel's left link represents `t` (as the root slot), its right link
points to itself (what `is_nil` tests), and it is black. -/
def Tree (h : Heap) (head : Addr) (t : RBNode Addr) : Prop :=
  Rep h head (h head).left head .left t ∧ (h head).right = head ∧ (h head).red = false

/-- A whole tree is a tree located at the root. -/
theorem tree_iff_located {h : Heap} {head : Addr} {t : RBNode Addr} :
    Tree h head t ↔ Located h head (h head).left head .left t .root := by
  constructor
  · rintro ⟨hr, e₂, e₃⟩; exact ⟨hr, .root rfl e₂ e₃⟩
  · rintro ⟨hr, hp⟩
    cases hp with
    | root _ e₂ e₃ => exact ⟨hr, e₂, e₃⟩

namespace RepPath

variable {h h' : Heap} {head a p : Addr} {s : Side} {path : Path Addr} {t : RBNode Addr}

/-- Filling the path: a located subtree is part of a whole tree, `path.fill t`. -/
theorem fill (hp : RepPath h head a p s path) (hr : Rep h head a p s t) :
    Tree h head (path.fill t) := by
  induction hp generalizing t with
  | root e₁ e₂ e₃ => exact ⟨e₁ ▸ hr, e₂, e₃⟩
  | left hy hn ha hc hb _ ih => exact ih (.node hy hn rfl rfl hc (ha ▸ hr) hb)
  | right hy hn ha hc hb _ ih => exact ih (.node hy hn rfl rfl hc hb (ha ▸ hr))

/-- The slot's node is the sentinel (at the root) or one of the path's addresses. -/
theorem slot (hp : RepPath h head a p s path) : p = head ∨ p ∈ path.listL ++ path.listR := by
  cases hp with
  | root => exact .inl rfl
  | left => exact .inr (by simp)
  | right => exact .inr (by simp)

/-- The frame lemma for paths: a heap that agrees with `h` on every address of the path and on
the sentinel's links and colour keeps the path. -/
theorem frame (hp : RepPath h head a p s path)
    (hf : ∀ x ∈ path.listL ++ path.listR, h' x = h x)
    (e₁ : (h' head).left = (h head).left) (e₂ : (h' head).right = (h head).right)
    (e₃ : (h' head).red = (h head).red) : RepPath h' head a p s path := by
  induction hp with
  | root f₁ f₂ f₃ => exact .root (e₁.trans f₁) (e₂.trans f₂) (e₃.trans f₃)
  | @left a y c pp b hy hn ha hc hb _ ih =>
    have hyy : h' y = h y := hf y (by simp)
    refine .left hy hn (by rw [hyy]; exact ha) (by rw [hyy]; exact hc) ?_ ?_
    · rw [hyy]; exact hb.frame fun x hx => hf x (by simp [hx])
    · rw [hyy]
      exact ih fun x hx => hf x (by
        simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> simp [hx])
  | @right a y c pp b hy hn ha hc hb _ ih =>
    have hyy : h' y = h y := hf y (by simp)
    refine .right hy hn (by rw [hyy]; exact ha) (by rw [hyy]; exact hc) ?_ ?_
    · rw [hyy]; exact hb.frame fun x hx => hf x (by simp [hx])
    · rw [hyy]
      exact ih fun x hx => hf x (by
        simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> simp [hx])

end RepPath

/-- What `Nodup` says of a node's addresses. -/
theorem nodup_node {c : RBColor} {l r : RBNode Addr} {v : Addr}
    (hnd : (RBNode.node c l v r).toList.Nodup) :
    l.toList.Nodup ∧ r.toList.Nodup ∧ v ∉ l.toList ∧ v ∉ r.toList ∧
      ∀ x ∈ l.toList, x ∉ r.toList := by
  simp only [RBNode.toList_node, List.nodup_append, List.nodup_cons, List.mem_cons] at hnd
  obtain ⟨hl, ⟨hvr, hr⟩, hlr⟩ := hnd
  exact ⟨hl, hr, fun hv => hlr v hv v (.inl rfl) rfl, hvr,
    fun x hx hxr => hlr x hx x (.inr hxr) rfl⟩

namespace Located

variable {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr} {t : RBNode Addr}

/-- The path's addresses are outside the located subtree, and none is the sentinel. -/
theorem outside (hl : Located h head a p s t path) :
    ∀ x ∈ path.listL ++ path.listR, x ∉ t.toList ∧ x ≠ head := by
  have hf := (hl.2.fill hl.1).1
  have hnd := hf.nodup
  rw [RBTree.RBNode.Path.fill_toList] at hnd
  simp only [RBTree.RBNode.Path.withList, List.nodup_append, List.mem_append] at hnd
  intro x hx
  have hmem : x ∈ (path.fill t).toList := by
    rw [RBTree.RBNode.Path.fill_toList]
    simp only [RBTree.RBNode.Path.withList, List.mem_append] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  refine ⟨fun hxt => ?_, (hf.mem_ne hmem).1⟩
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · exact hnd.1.2.2 x hx x hxt rfl
  · exact hnd.2.2 x (.inr hxt) x hx rfl

/-- The slot's node is outside the subtree hanging from it. -/
theorem slot_not_mem (hl : Located h head a p s t path) : p ∉ t.toList := by
  rcases hl.2.slot with rfl | hpm
  · exact fun hx => (hl.1.mem_ne hx).1 rfl
  · exact (hl.outside p hpm).1

end Located

/-- A slot changes occupant, and nothing else on the path changes. If the new heap `H` holds `b`
in the slot `(p, s)`, keeps the slot node's other link, colour and `parent` word, keeps the
sentinel's right link and colour (and its left link, unless the slot is that link), and keeps the
record of every other address of the path, then the path is unchanged with `b` in the slot.
Nothing is required of addresses off the path, whatever the operation wrote there (the subtree
below, a node being attached, a chain member taking a tree position). Every operation that
replaces a subtree in place (`rotate`; in step 3, `attach_to`, `substitute_with` and
`switch_with`) ends with this step. -/
theorem RepPath.retarget {h H : Heap} {head a b p : Addr} {s : Side} {path : Path Addr}
    {t : RBNode Addr} (hp : RepPath h head a p s path) (hr : Rep h head a p s t)
    (hfr : ∀ x ∈ path.listL ++ path.listR, x ≠ p → H x = h x)
    (hright : (H head).right = (h head).right) (hred : (H head).red = (h head).red)
    (hleft : p ≠ head → (H head).left = (h head).left)
    (hslot : childAt H p s = b)
    (hp' : p ≠ head → childAt H p s.other = childAt h p s.other ∧ (H p).red = (h p).red ∧
      (H p).parent = (h p).parent ∧ (H p).side = (h p).side) :
    RepPath H head b p s path := by
  cases hp with
  | root e₁ e₂ e₃ => exact .root hslot (hright.trans e₂) (hred.trans e₃)
  | @left _ _ c₀ pp sib hy hny eA ec hsib hpp =>
    have hup : Located h head p (h p).parent (h p).side (.node c₀ t p sib) pp :=
      ⟨.node hy hny rfl rfl ec (by rw [eA]; exact hr) hsib, hpp⟩
    obtain ⟨-, -, -, hysib, -⟩ := nodup_node hup.1.nodup
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hp' hy
    refine .left hy hny hslot (e₂.trans ec) ?_ ?_
    · rw [show (H p).right = (h p).right from e₁]
      exact hsib.frame fun x hx => hfr x (by simp [hx]) (fun e => hysib (e ▸ hx))
    · rw [e₃, e₄]
      refine hpp.frame (fun x hx => ?_) (hleft hy) hright hred
      obtain ⟨hxt, -⟩ := hup.outside x hx
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hxt
      refine hfr x ?_ hxt.2.1
      simp only [Path.listL, Path.listR, List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]
  | @right _ _ c₀ pp sib hy hny eA ec hsib hpp =>
    have hup : Located h head p (h p).parent (h p).side (.node c₀ sib p t) pp :=
      ⟨.node hy hny rfl rfl ec hsib (by rw [eA]; exact hr), hpp⟩
    obtain ⟨-, -, hysib, -, -⟩ := nodup_node hup.1.nodup
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hp' hy
    refine .right hy hny hslot (e₂.trans ec) ?_ ?_
    · rw [show (H p).left = (h p).left from e₁]
      exact hsib.frame fun x hx => hfr x (by simp [hx]) (fun e => hysib (e ▸ hx))
    · rw [e₃, e₄]
      refine hpp.frame (fun x hx => ?_) (hleft hy) hright hred
      obtain ⟨hxt, -⟩ := hup.outside x hx
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hxt
      refine hfr x ?_ hxt.2.1
      simp only [Path.listL, Path.listR, List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]

/-- The sentinel's only slot is its left link. -/
theorem RepPath.head_side {h : Heap} {head a : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a head s path) : s = .left := by
  cases hp with
  | root => rfl
  | left hy => exact absurd rfl hy
  | right hy => exact absurd rfl hy

/-- The slot's link holds its occupant: `RepPath`'s first field, read back. -/
theorem RepPath.childAt_slot {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a p s path) : childAt h p s = a := by
  cases hp with
  | root e => exact e
  | left _ _ e => exact e
  | right _ _ e => exact e

/-! ### Per-address descriptions of the structural operations

Each operation's result, address by address, under the distinctness its callers guarantee: one
`if` chain per operation (`rotateAt_apply`), so that a proof reads a field of the new heap with one
`simp` instead of unfolding every write. -/

/-- `setChild`'s write on a single record. -/
def NodeRec.withChild (n : NodeRec) : Side → Addr → NodeRec
  | .left, v => { n with left := v }
  | .right, v => { n with right := v }

@[simp] theorem NodeRec.withChild_parent (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).parent = n.parent := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_side (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).side = n.side := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_red (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).red = n.red := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_prev (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).prev = n.prev := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_next (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).next = n.next := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_left_left (n : NodeRec) (v : Addr) :
    (n.withChild .left v).left = v := rfl
@[simp] theorem NodeRec.withChild_left_right (n : NodeRec) (v : Addr) :
    (n.withChild .left v).right = n.right := rfl
@[simp] theorem NodeRec.withChild_right_left (n : NodeRec) (v : Addr) :
    (n.withChild .right v).left = n.left := rfl
@[simp] theorem NodeRec.withChild_right_right (n : NodeRec) (v : Addr) :
    (n.withChild .right v).right = v := rfl

/-- `setChild` is `NodeRec.withChild` at one address. -/
theorem setChild_eq (h : Heap) (a : Addr) (s : Side) (v : Addr) :
    setChild h a s v = h.modify a (·.withChild s v) := by
  cases s <;> rfl

/-- **`rotateAt` touches four addresses.** On any heap, `rotateAt h this s` changes no record but
those of `this`, its side-`o` child `top` (`o = s.other`), `top`'s side-`s` child, and `this`'s
parent. -/
theorem rotateAt_frame (h : Heap) (this : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ childAt h this s.other) (h₃ : x ≠ childAt h (childAt h this s.other) s)
    (h₄ : x ≠ parent h this) : rotateAt h this s x = h x := by
  simp only [rotateAt, setChild, setParentPtr, setParentSide, Heap.modify]
  simp [h₁, h₂, h₃, h₄]

/-- Of `top`'s side-`s` child (the subtree that moves across), `rotateAt` writes only the `parent`
word's pointer and side bit: away from `this`, `top` and `this`'s parent, every record keeps its
child links and colour. When that child is the sentinel, these are its scratch fields. -/
theorem rotateAt_links (h : Heap) (this : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ childAt h this s.other) (h₄ : x ≠ parent h this) :
    (rotateAt h this s x).left = (h x).left ∧ (rotateAt h this s x).right = (h x).right ∧
      (rotateAt h this s x).red = (h x).red := by
  simp only [rotateAt, setChild, setParentPtr, setParentSide, Heap.modify]
  by_cases h₃ : x = childAt h (childAt h this s.other) s
  · subst h₃; simp [h₁, h₂, h₄]
  · simp [h₁, h₂, h₃, h₄]

/-- Of `this`'s parent, if it is neither `this` nor `top` (which `Located` guarantees: the slot's
node is outside the subtree), `rotateAt` writes only the child link `this` hung from, which now
holds `top`: the other link and the colour are kept, and so is the `parent` word unless the
parent is also `top`'s side-`s` child (a rotation at the root whose moving subtree is empty: both
are the sentinel, and its scratch `parent` and side are written). -/
theorem rotateAt_parent_fields (h : Heap) (this : Addr) (s : Side)
    (h₁ : parent h this ≠ this) (h₂ : parent h this ≠ childAt h this s.other) :
    childAt (rotateAt h this s) (parent h this) (parentSide h this) = childAt h this s.other ∧
      childAt (rotateAt h this s) (parent h this) (parentSide h this).other =
        childAt h (parent h this) (parentSide h this).other ∧
      (rotateAt h this s (parent h this)).red = (h (parent h this)).red ∧
      (parent h this ≠ childAt h (childAt h this s.other) s →
        (rotateAt h this s (parent h this)).parent = (h (parent h this)).parent ∧
        (rotateAt h this s (parent h this)).side = (h (parent h this)).side) := by
  by_cases h₃ : parent h this = childAt h (childAt h this s.other) s
  · refine ⟨?_, ?_, ?_, fun h₄ => absurd h₃ h₄⟩ <;>
      simp only [parent, parentSide, childAt] at h₁ h₂ h₃ ⊢ <;>
      cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]
  · simp only [parent, parentSide, childAt] at h₁ h₂ h₃ ⊢
    cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]

/-- **`rotateAt`, address by address.** With `top` `this`'s side-`o` child (`o = s.other`), `m`
`top`'s side-`s` child and `P` `this`'s parent, where `this`, `top` and `P` are distinct and
`top ≠ m`, `rotateAt h this s` gives `this` the child `m` on side `o` and the slot `(top, s)`;
`top` the child `this` on side `s` and `this`'s old slot; `m` the slot `(this, o)`; `P` the child
`top` in the link that held `this` (on `m`'s record too when `m = P`); and every other address its
old record. `m` may coincide with `P` (a rotation at the root whose moving subtree is empty: both
are then the sentinel) or with `this` (whose record the later writes then decide: the first
branch). The writes' order matters only where two of them hit the same field. -/
theorem rotateAt_apply (h : Heap) (this : Addr) (s : Side)
    (h₁ : this ≠ childAt h this s.other)
    (h₃ : childAt h this s.other ≠ childAt h (childAt h this s.other) s)
    (h₄ : this ≠ parent h this) (h₅ : childAt h this s.other ≠ parent h this) (x : Addr) :
    rotateAt h this s x =
      if x = this then
        { (h this).withChild s.other (childAt h (childAt h this s.other) s) with
          parent := childAt h this s.other, side := s }
      else if x = childAt h this s.other then
        { (h x).withChild s this with parent := parent h this, side := parentSide h this }
      else if x = childAt h (childAt h this s.other) s then
        { (if x = parent h this then (h x).withChild (parentSide h this) (childAt h this s.other)
            else h x) with parent := this, side := s.other }
      else if x = parent h this then (h x).withChild (parentSide h this) (childAt h this s.other)
      else h x := by
  generalize ht : childAt h this s.other = top at *
  generalize hm : childAt h top s = m at *
  generalize hP : parent h this = P at *
  generalize hps : parentSide h this = ps
  simp only [rotateAt, setChild_eq, setParentPtr, setParentSide, Heap.modify, ht, hm, hP, hps]
  by_cases e₁ : x = this
  · subst e₁
    by_cases e : x = m
    · subst e; simp [h₁, h₄]
    · simp [h₁, h₄, e]
  by_cases e₂ : x = top
  · subst e₂; simp [e₁, h₃, h₅]
    cases s <;> rfl
  by_cases e₃ : x = m
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; simp [e₁, e₂]
      cases s <;> cases ps <;> rfl
    · simp [e₁, e₂, e₄]
  by_cases e₄ : x = P
  · subst e₄; simp [e₁, e₂, e₃]
  · simp [e₁, e₂, e₃, e₄]

/-- **`NodeBase::rotate(this, Left)` performs the zipper rotation** (step 1 of the note's §4). If
the heap represents the located subtree `node c l a (node c' rl b rr)`, then after
`rotateAt h a .left` it represents `Oris.RB.rotate .left` of it, `node c' (node c l a rl) b rr`,
at the same slot and path, with `b` now in the slot. Nothing is assumed beyond `Located` (the
subtree and its path, which the proof needs: it is what puts the slot's node outside the subtree);
in particular, the writes to the sentinel's scratch fields when `rl` is empty need no hypothesis.
Which records change is `rotateAt_refines_left_frame` (and, field by field, `rotateAt_links` and
`rotateAt_parent_fields`). -/
theorem rotateAt_refines_left {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {l rl rr : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c l a (.node c' rl b rr)) path) :
    Located (rotateAt h a .left) head b p s
      (rotate .left (.node c l a (.node c' rl b rr))) path := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, ha, hna, hpa, hsa, hca, hal, har⟩ := hr.node_inv
  obtain ⟨hab, hb, hnb, -, -, hcb, hbl, hbr⟩ := har.node_inv
  generalize hm : (h b).left = m at hbl
  obtain ⟨-, -, hal', hai, hli⟩ := nodup_node hr.nodup
  obtain ⟨-, -, hbrl, hbrr, hrlrr⟩ := nodup_node har.nodup
  simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hai hli hpt
  -- `m` is the sentinel or the root of `rl`.
  have hmrl : m ≠ head → m ∈ rl.toList := hbl.root_mem
  have hab' : a ≠ b := hai.2.1
  have ham : a ≠ m := fun e => by
    by_cases hmh : m = head
    · exact ha (e.trans hmh)
    · exact hai.1 (e ▸ hmrl hmh)
  have hbm : b ≠ m := fun e => by
    by_cases hmh : m = head
    · exact hb (e.trans hmh)
    · exact hbrl (e ▸ hmrl hmh)
  have hap : a ≠ p := fun e => hpt.2.1 e.symm
  have hbp : b ≠ p := fun e => hpt.2.2.2.1 e.symm
  have hmp : m ≠ head → m ≠ p := fun hmh e => hpt.2.2.1 (e ▸ hmrl hmh)
  have RL := rotateAt_apply h a .left (by simpa [childAt, Side.other, hab] using hab')
    (by simpa [childAt, Side.other, hab, hm] using hbm) (by simpa [parent, hpa] using hap)
    (by simpa [childAt, Side.other, hab, parent, hpa] using hbp)
  simp only [childAt, Side.other, parent, parentSide, hab, hm, hpa, hsa] at RL
  have rfr : ∀ x, x ≠ a → x ≠ b → x ≠ m → x ≠ p → rotateAt h a .left x = h x :=
    fun x h₁ h₂ h₃ h₄ => by simp [RL, h₁, h₂, h₃, h₄]
  have RA : (rotateAt h a .left a).left = (h a).left ∧ (rotateAt h a .left a).right = m ∧
      (rotateAt h a .left a).parent = b ∧ (rotateAt h a .left a).side = .left ∧
      (rotateAt h a .left a).red = (h a).red := by
    simp [RL, NodeRec.withChild]
  have RB : (rotateAt h a .left b).left = a ∧ (rotateAt h a .left b).right = (h b).right ∧
      (rotateAt h a .left b).parent = p ∧ (rotateAt h a .left b).side = s ∧
      (rotateAt h a .left b).red = (h b).red := by
    simp [RL, hab'.symm]
  have RM : m ≠ head → (rotateAt h a .left m).left = (h m).left ∧
      (rotateAt h a .left m).right = (h m).right ∧ (rotateAt h a .left m).red = (h m).red ∧
      (rotateAt h a .left m).parent = a ∧ (rotateAt h a .left m).side = .right := fun hmh => by
    simp [RL, ham.symm, hbm.symm, hmp hmh]
  show Located _ head b p s (.node c' (.node c l a rl) b rr) path
  refine ⟨.node hb hnb RB.2.2.1 RB.2.2.2.1 (RB.2.2.2.2.trans hcb) ?_ ?_, ?_⟩
  · rw [RB.1]
    refine .node ha hna RA.2.2.1 RA.2.2.2.1 (RA.2.2.2.2.trans hca) ?_ ?_
    · rw [RA.1]
      refine hal.frame fun x hx => rfr x (fun e => hal' (e ▸ hx)) (hli x hx).2.1
        (fun e => ?_) (fun e => hpt.1 (e ▸ hx))
      by_cases hmh : m = head
      · exact (hal.mem_ne hx).1 (e.trans hmh)
      · exact (hli x hx).1 (e ▸ hmrl hmh)
    · rw [RA.2.1]
      refine hbl.reroot RM fun x hx hxm => rfr x (fun e => hai.1 (e ▸ hx))
        (fun e => hbrl (e ▸ hx)) hxm (fun e => hpt.2.2.1 (e ▸ hx))
  · rw [RB.2.1]
    refine hbr.frame fun x hx => rfr x (fun e => hai.2.2 (e ▸ hx)) (fun e => hbrr (e ▸ hx))
      (fun e => ?_) (fun e => hpt.2.2.2.2 (e ▸ hx))
    by_cases hmh : m = head
    · exact (hbr.mem_ne hx).1 (e.trans hmh)
    · exact hrlrr m (hmrl hmh) (e ▸ hx)
  · have memt : ∀ x, x ∈ l.toList ∨ x = a ∨ x ∈ rl.toList ∨ x = b ∨ x ∈ rr.toList →
        x ∈ (RBNode.node c l a (.node c' rl b rr)).toList := fun x hx => by
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons]; exact hx
    have hpm : p ≠ head → p ≠ m := fun hph e => by
      by_cases hmh : m = head
      · exact hph (e.trans hmh)
      · exact hpt.2.2.1 (by rw [e]; exact hmrl hmh)
    have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
    have HH : (rotateAt h a .left head).right = (h head).right ∧
        (rotateAt h a .left head).red = (h head).red ∧
        (p ≠ head → (rotateAt h a .left head).left = (h head).left) := by
      have hah := Ne.symm ha
      have hbh := Ne.symm hb
      cases s
      · by_cases h1 : head = m
        · subst h1
          by_cases h2 : head = p
          · subst h2; simp [RL, hah, hbh, NodeRec.withChild]
          · simp [RL, hah, hbh, h2]
        · by_cases h2 : head = p
          · subst h2; simp [RL, hah, hbh, h1, NodeRec.withChild]
          · simp [RL, hah, hbh, h1, h2]
      · have h2 : head ≠ p := fun e => by cases hs e.symm
        by_cases h1 : head = m
        · subst h1; simp [RL, hah, hbh, h2]
        · simp [RL, hah, hbh, h1, h2]
    refine hp.retarget hr (fun x hx hxp => rfr x
        (fun e => (hout x hx).1 (memt _ (.inr (.inl e))))
        (fun e => (hout x hx).1 (memt _ (.inr (.inr (.inr (.inl e))))))
        (fun e => by
          by_cases hmh : m = head
          · exact (hout x hx).2 (e.trans hmh)
          · exact (hout x hx).1 (memt _ (.inr (.inr (.inl (e ▸ hmrl hmh)))))) hxp)
      HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hpm' : p = m
      · subst hpm'; cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, NodeRec.withChild]
      · cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]
    · intro hph
      have hpm' := hpm hph
      cases s <;> simp [RL, childAt, Side.other, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]

/-- `rotateAt_frame` for `rotateAt_refines_left`, in the zipper's terms: the only records the
rotation changes are those of `a`, `b`, `b`'s left child (the first node of `rl`, or the sentinel
when `rl` is empty) and the slot's node `p`. -/
theorem rotateAt_refines_left_frame {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {l rl rr : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c l a (.node c' rl b rr)) path) {x : Addr}
    (h₁ : x ≠ a) (h₂ : x ≠ b) (h₃ : x ≠ (h b).left) (h₄ : x ≠ p) :
    rotateAt h a .left x = h x := by
  obtain ⟨-, -, -, hpa, -, -, -, har⟩ := hl.1.node_inv
  obtain ⟨hab, -⟩ := har.node_inv
  exact rotateAt_frame h a .left h₁ (by simpa [childAt, Side.other, hab] using h₂)
    (by simpa [childAt, Side.other, hab] using h₃) (by simpa [parent, hpa] using h₄)

/-- **`NodeBase::rotate(this, Right)` performs the zipper rotation**, the mirror image of
`rotateAt_refines_left`: `node c (node c' ll b lr) a r` becomes `node c' ll b (node c lr a r)`.
Which records change is `rotateAt_refines_right_frame`. -/
theorem rotateAt_refines_right {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {ll lr r : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c (.node c' ll b lr) a r) path) :
    Located (rotateAt h a .right) head b p s
      (rotate .right (.node c (.node c' ll b lr) a r)) path := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, ha, hna, hpa, hsa, hca, hal, har⟩ := hr.node_inv
  obtain ⟨hab, hb, hnb, -, -, hcb, hbl, hbr⟩ := hal.node_inv
  generalize hm : (h b).right = m at hbr
  obtain ⟨-, -, hai, har', hli⟩ := nodup_node hr.nodup
  obtain ⟨-, -, hbll, hblr, hlllr⟩ := nodup_node hal.nodup
  simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hai hpt
  obtain ⟨⟨hpll, hpb', hplr⟩, hpa', hpr⟩ := hpt
  have memi : ∀ x, x ∈ ll.toList ∨ x = b ∨ x ∈ lr.toList →
      x ∈ (RBNode.node c' ll b lr).toList := fun x hx => by
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons]; exact hx
  -- `m` is the sentinel or the root of `lr`.
  have hmlr : m ≠ head → m ∈ lr.toList := hbr.root_mem
  have hab' : a ≠ b := hai.2.1
  have ham : a ≠ m := fun e => by
    by_cases hmh : m = head
    · exact ha (e.trans hmh)
    · exact hai.2.2 (e ▸ hmlr hmh)
  have hbm : b ≠ m := fun e => by
    by_cases hmh : m = head
    · exact hb (e.trans hmh)
    · exact hblr (e ▸ hmlr hmh)
  have hap : a ≠ p := fun e => hpa' e.symm
  have hbp : b ≠ p := fun e => hpb' e.symm
  have hmp : m ≠ head → m ≠ p := fun hmh e => hplr (e ▸ hmlr hmh)
  have RL := rotateAt_apply h a .right (by simpa [childAt, Side.other, hab] using hab')
    (by simpa [childAt, Side.other, hab, hm] using hbm) (by simpa [parent, hpa] using hap)
    (by simpa [childAt, Side.other, hab, parent, hpa] using hbp)
  simp only [childAt, Side.other, parent, parentSide, hab, hm, hpa, hsa] at RL
  have rfr : ∀ x, x ≠ a → x ≠ b → x ≠ m → x ≠ p → rotateAt h a .right x = h x :=
    fun x h₁ h₂ h₃ h₄ => by simp [RL, h₁, h₂, h₃, h₄]
  have RA : (rotateAt h a .right a).right = (h a).right ∧ (rotateAt h a .right a).left = m ∧
      (rotateAt h a .right a).parent = b ∧ (rotateAt h a .right a).side = .right ∧
      (rotateAt h a .right a).red = (h a).red := by
    simp [RL, NodeRec.withChild]
  have RB : (rotateAt h a .right b).right = a ∧ (rotateAt h a .right b).left = (h b).left ∧
      (rotateAt h a .right b).parent = p ∧ (rotateAt h a .right b).side = s ∧
      (rotateAt h a .right b).red = (h b).red := by
    simp [RL, hab'.symm]
  have RM : m ≠ head → (rotateAt h a .right m).left = (h m).left ∧
      (rotateAt h a .right m).right = (h m).right ∧ (rotateAt h a .right m).red = (h m).red ∧
      (rotateAt h a .right m).parent = a ∧ (rotateAt h a .right m).side = .left := fun hmh => by
    simp [RL, ham.symm, hbm.symm, hmp hmh]
  show Located _ head b p s (.node c' ll b (.node c lr a r)) path
  refine ⟨.node hb hnb RB.2.2.1 RB.2.2.2.1 (RB.2.2.2.2.trans hcb) ?_ ?_, ?_⟩
  · rw [RB.2.1]
    refine hbl.frame fun x hx => rfr x (fun e => hai.1 (e ▸ hx)) (fun e => hbll (e ▸ hx))
      (fun e => ?_) (fun e => hpll (e ▸ hx))
    by_cases hmh : m = head
    · exact (hbl.mem_ne hx).1 (e.trans hmh)
    · exact hlllr x hx (e ▸ hmlr hmh)
  · rw [RB.1]
    refine .node ha hna RA.2.2.1 RA.2.2.2.1 (RA.2.2.2.2.trans hca) ?_ ?_
    · rw [RA.2.1]
      exact hbr.reroot RM fun x hx hxm => rfr x (fun e => hai.2.2 (e ▸ hx))
        (fun e => hblr (e ▸ hx)) hxm (fun e => hplr (e ▸ hx))
    · rw [RA.1]
      refine har.frame fun x hx => rfr x (fun e => har' (e ▸ hx))
        (fun e => hli b (memi b (.inr (.inl rfl))) (e ▸ hx)) (fun e => ?_)
        (fun e => hpr (e ▸ hx))
      by_cases hmh : m = head
      · exact (har.mem_ne hx).1 (e.trans hmh)
      · exact hli m (memi m (.inr (.inr (hmlr hmh)))) (e ▸ hx)
  · have memt : ∀ x, x ∈ ll.toList ∨ x = b ∨ x ∈ lr.toList ∨ x = a ∨ x ∈ r.toList →
        x ∈ (RBNode.node c (.node c' ll b lr) a r).toList := fun x hx => by
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons, List.append_assoc,
        List.cons_append]
      rcases hx with hx | hx | hx | hx | hx <;> simp [hx]
    have hpm : p ≠ head → p ≠ m := fun hph e => by
      by_cases hmh : m = head
      · exact hph (e.trans hmh)
      · exact hplr (by rw [e]; exact hmlr hmh)
    have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
    have HH : (rotateAt h a .right head).right = (h head).right ∧
        (rotateAt h a .right head).red = (h head).red ∧
        (p ≠ head → (rotateAt h a .right head).left = (h head).left) := by
      have hah := Ne.symm ha
      have hbh := Ne.symm hb
      cases s
      · by_cases h1 : head = m
        · subst h1
          by_cases h2 : head = p
          · subst h2; simp [RL, hah, hbh, NodeRec.withChild]
          · simp [RL, hah, hbh, h2]
        · by_cases h2 : head = p
          · subst h2; simp [RL, hah, hbh, h1, NodeRec.withChild]
          · simp [RL, hah, hbh, h1, h2]
      · have h2 : head ≠ p := fun e => by cases hs e.symm
        by_cases h1 : head = m
        · subst h1; simp [RL, hah, hbh, h2]
        · simp [RL, hah, hbh, h1, h2]
    refine hp.retarget hr (fun x hx hxp => rfr x
        (fun e => (hout x hx).1 (memt _ (.inr (.inr (.inr (.inl e))))))
        (fun e => (hout x hx).1 (memt _ (.inr (.inl e))))
        (fun e => by
          by_cases hmh : m = head
          · exact (hout x hx).2 (e.trans hmh)
          · exact (hout x hx).1 (memt _ (.inr (.inr (.inl (e ▸ hmlr hmh)))))) hxp)
      HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hpm' : p = m
      · subst hpm'; cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, NodeRec.withChild]
      · cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]
    · intro hph
      have hpm' := hpm hph
      cases s <;> simp [RL, childAt, Side.other, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]

/-- `rotateAt_frame` for `rotateAt_refines_right`: the only records changed are those of `a`, `b`,
`b`'s right child (the first node of `lr`, or the sentinel) and `p`. -/
theorem rotateAt_refines_right_frame {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {ll lr r : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c (.node c' ll b lr) a r) path) {x : Addr}
    (h₁ : x ≠ a) (h₂ : x ≠ b) (h₃ : x ≠ (h b).right) (h₄ : x ≠ p) :
    rotateAt h a .right x = h x := by
  obtain ⟨-, -, -, hpa, -, -, hal, -⟩ := hl.1.node_inv
  obtain ⟨hab, -⟩ := hal.node_inv
  exact rotateAt_frame h a .right h₁ (by simpa [childAt, Side.other, hab] using h₂)
    (by simpa [childAt, Side.other, hab] using h₃) (by simpa [parent, hpa] using h₄)

/-! ## Step 3a: `attach_to`, `substitute_with` and `switch_with`

Each performs the zipper step `Fixup.lean`'s `insert` or `eraseAt` takes at that point (the
note's §4, theorem 2): `attach_to` fills an empty hole with a red leaf, `substitute_with` splices
out a node with at most one child, and `switch_with` puts another address at a node's tree
position. Each comes with its per-address description (`_apply`), the list of records it changes
(`_frame`) and its refinement theorem (`_refines`). -/

/-- **`attachTo`, address by address**: `this` becomes a red leaf hanging at `(parent, s)`, both
children the slot's old occupant and both neighbours itself; `parent`'s side-`s` link takes
`this`; every other record is kept. -/
theorem attachTo_apply (h : Heap) (this parent : Addr) (s : Side) (h₁ : this ≠ parent)
    (x : Addr) :
    attachTo h this parent s x =
      if x = this then
        { left := childAt h parent s, right := childAt h parent s, prev := this, next := this,
          parent := parent, red := true, side := s }
      else if x = parent then (h x).withChild s this
      else h x := by
  by_cases e₁ : x = this
  · subst e₁
    cases s <;> simp [attachTo, setNeighbour, setChild, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, childAt, h₁, Ne.symm h₁]
  by_cases e₂ : x = parent
  · subst e₂
    cases s <;> simp [attachTo, setNeighbour, setChild, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, NodeRec.withChild, e₁]
  · simp [attachTo, setNeighbour, setChild_eq, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, e₁, e₂]

/-- **`attachTo` touches two addresses**: `this` and `parent`. -/
theorem attachTo_frame (h : Heap) (this parent : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ parent) : attachTo h this parent s x = h x := by
  simp only [attachTo, setNeighbour, setChild_eq, setParentPtr, setParentSide, makeRed,
    setColour, Heap.modify]
  simp [h₁, h₂]

/-- **`NodeBase::attach_to` fills the empty hole** (step 3a; the note's §4, theorem 2). If the
slot `(p, s)` holds the sentinel at `path` (the empty hole where `insert_counted`'s descent ends),
and `this` is a real address off the path, then after `attachTo h this p s` the heap represents
the red leaf `node red nil this nil` at that slot and path: the zipper state `Fixup.lean`'s
`insert` hands to `insFix`. Which records change is `attachTo_frame`. -/
theorem attachTo_refines {h : Heap} {head this p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head head p s path) (hn : this ≠ head) (hn0 : this ≠ null)
    (hfresh : this ∉ path.listL ++ path.listR) :
    Located (attachTo h this p s) head this p s (.node .red .nil this .nil) path := by
  have htp : this ≠ p := fun e => by
    rcases hp.slot with hph | hpm
    · exact hn (e.trans hph)
    · exact hfresh (e ▸ hpm)
  have AT := attachTo_apply h this p s htp
  have hslot := hp.childAt_slot
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  refine ⟨.node hn hn0 (by simp [AT]) (by simp [AT]) (by simp [AT, colourBit]) ?_ ?_, ?_⟩
  · have e : (attachTo h this p s this).left = head := by simp [AT, hslot]
    rw [e]; exact .nil
  · have e : (attachTo h this p s this).right = head := by simp [AT, hslot]
    rw [e]; exact .nil
  · have hht : head ≠ this := Ne.symm hn
    refine hp.retarget .nil (fun x hx hxp => ?_) ?_ ?_ ?_ ?_ ?_
    · exact attachTo_frame h this p s (fun e => hfresh (e ▸ hx)) hxp
    · by_cases hph : head = p
      · subst hph; obtain rfl := hs rfl; simp [AT, hht, NodeRec.withChild]
      · simp [AT, hht, hph]
    · by_cases hph : head = p
      · subst hph; simp [AT, hht]
      · simp [AT, hht, hph]
    · intro hph; simp [AT, hht, Ne.symm hph]
    · cases s <;> simp [AT, childAt, Ne.symm htp, NodeRec.withChild]
    · intro _
      cases s <;> simp [AT, childAt, Side.other, Ne.symm htp, NodeRec.withChild]

/-- **`substituteWith`, address by address**: `child` takes `this`'s slot (`this`'s parent and
side, read before any write), and that parent's link takes `child`; every other record is kept,
`this`'s included. `child` and the parent may coincide: both are the sentinel when the root, with
no children, is erased. -/
theorem substituteWith_apply (h : Heap) (this child : Addr) (x : Addr) :
    substituteWith h this child x =
      if x = child then
        { (if x = parent h this then (h x).withChild (parentSide h this) child else h x) with
          parent := parent h this, side := parentSide h this }
      else if x = parent h this then (h x).withChild (parentSide h this) child
      else h x := by
  generalize hP : parent h this = P
  generalize hps : parentSide h this = ps
  simp only [substituteWith, setChild_eq, setParentPtr, setParentSide, Heap.modify, hP, hps]
  by_cases e₁ : x = child
  · subst e₁
    by_cases e₂ : x = P
    · subst e₂; simp; cases ps <;> rfl
    · simp [e₂]
  by_cases e₂ : x = P
  · subst e₂; simp [e₁]
  · simp [e₁, e₂]

/-- **`substituteWith` touches two addresses**: `child` and `this`'s parent. -/
theorem substituteWith_frame (h : Heap) (this child : Addr) {x : Addr} (h₁ : x ≠ child)
    (h₂ : x ≠ parent h this) : substituteWith h this child x = h x := by
  simp [substituteWith_apply, h₁, h₂]

/-- The common part of `substituteWith_refines_left` and `_right`: `this` is the first node of the
located subtree `t`, and its side-`σ` child `k` represents `u`, a subtree of `t`. After
`substituteWith h this k`, the heap represents `u` at `this`'s slot and path, and `k`'s `parent`
word names the slot, also when `k` is the sentinel (the empty hole). -/
theorem substituteWith_refines_core {h : Heap} {head this p k : Addr} {s σ : Side}
    {t u : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s t path) (hthis : this ∈ t.toList)
    (hu : Rep h head k this σ u) (hut : ∀ x ∈ u.toList, x ∈ t.toList) :
    Located (substituteWith h this k) head k p s u path ∧
      (substituteWith h this k k).parent = p ∧ (substituteWith h this k k).side = s := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  have hk : k ≠ head → k ∈ u.toList := hu.root_mem
  obtain ⟨hr, hp⟩ := hl
  have hpa : parent h this = p := (hr.root_fields hthis).1
  have hsa : parentSide h this = s := (hr.root_fields hthis).2
  have SU := substituteWith_apply h this k
  simp only [hpa, hsa] at SU
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  -- `k` is the sentinel or an address of `u`, inside `t`; `p` is the sentinel or on the path.
  have hkp₀ : p ≠ head → k ≠ p := fun hph e => by
    by_cases hkh : k = head
    · exact hph (e ▸ hkh)
    · exact hpt (e ▸ hut k (hk hkh))
  have FK : (substituteWith h this k k).parent = p ∧ (substituteWith h this k k).side = s := by
    simp [SU]
  refine ⟨⟨?_, ?_⟩, FK⟩
  · refine hu.reroot (fun hkh => ?_) (fun x hx hxk => ?_)
    · have hkp : k ≠ p := fun e => by
        by_cases hph : p = head
        · exact hkh (e.trans hph)
        · exact hkp₀ hph e
      simp [SU, hkp]
    · have hxp : x ≠ p := fun e => hpt (e ▸ hut x hx)
      simp [SU, hxk, hxp]
  · have hkk : ∀ x ∈ path.listL ++ path.listR, x ≠ k := fun x hx e => by
      by_cases hkh : k = head
      · exact (hout x hx).2 (e.trans hkh)
      · exact (hout x hx).1 (e ▸ hut k (hk hkh))
    have HH : (substituteWith h this k head).right = (h head).right ∧
        (substituteWith h this k head).red = (h head).red ∧
        (p ≠ head → (substituteWith h this k head).left = (h head).left) := by
      by_cases hph : p = head
      · subst hph; obtain rfl := hs rfl
        by_cases hkh : p = k
        · subst hkh; simp [SU, NodeRec.withChild]
        · simp [SU, hkh, NodeRec.withChild]
      · have hhp : head ≠ p := Ne.symm hph
        by_cases hkh : head = k
        · subst hkh; simp [SU, hhp]
        · simp [SU, hkh, hhp]
    refine hp.retarget hr (fun x hx hxp => substituteWith_frame h this k (hkk x hx)
        (by rw [hpa]; exact hxp)) HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hph : p = head
      · subst hph; obtain rfl := hs rfl
        by_cases hkh : p = k
        · subst hkh; simp [SU, childAt, NodeRec.withChild]
        · simp [SU, childAt, hkh, NodeRec.withChild]
      · have hpk := Ne.symm (hkp₀ hph)
        cases s <;> simp [SU, childAt, hpk, NodeRec.withChild]
    · intro hph
      have hpk := Ne.symm (hkp₀ hph)
      cases s <;> simp [SU, childAt, Side.other, hpk, NodeRec.withChild]

/-- **`NodeBase::substitute_with` splices out a node with no right child** (step 3a, §4 theorem 2;
`erase_counted`'s `right == end` case). If the heap represents the located subtree
`node c l this nil`, then after `substituteWith h this (h this).left` it represents `l` at the same
slot and path: the zipper's `path.fill l` in `eraseAt`. And the left child's `parent` word names
that slot. When `l` is empty, that child is the sentinel, and these are its scratch fields: how
`erase_fixup` finds an empty hole's parent and side (unless `switch_with` then overwrites them,
`switchWith_refines`). `this` is detached, its record unchanged. -/
theorem substituteWith_refines_left {h : Heap} {head this p : Addr} {s : Side} {c : RBColor}
    {l : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s (.node c l this .nil) path) :
    Located (substituteWith h this (h this).left) head (h this).left p s l path ∧
      (substituteWith h this (h this).left (h this).left).parent = p ∧
      (substituteWith h this (h this).left (h this).left).side = s := by
  obtain ⟨-, -, -, -, -, -, hll, -⟩ := hl.1.node_inv
  exact substituteWith_refines_core hl (by simp) hll (fun x hx => by simp [hx])

/-- **`NodeBase::substitute_with` splices out a node with no left child**, the mirror image of
`substituteWith_refines_left` (`erase_counted`'s case `left == end`, and its two-child case, where
the in-order successor, which has no left child, is spliced out): `node c nil this r` gives `r`,
with the right child's `parent` word naming the slot. -/
theorem substituteWith_refines_right {h : Heap} {head this p : Addr} {s : Side} {c : RBColor}
    {r : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s (.node c .nil this r) path) :
    Located (substituteWith h this (h this).right) head (h this).right p s r path ∧
      (substituteWith h this (h this).right (h this).right).parent = p ∧
      (substituteWith h this (h this).right (h this).right).side = s := by
  obtain ⟨-, -, -, -, -, -, -, hrr⟩ := hl.1.node_inv
  exact substituteWith_refines_core hl (by simp) hrr (fun x hx => by simp [hx])

/-- **`switchWith`, address by address**: `this` takes `node`'s children, slot and colour; `node`'s
right child, then its left child, take the slot `(this, right)` and `(this, left)`; `node`'s parent
takes `this` in the link that held `node`; every other record is kept, `node`'s included (it is
detached). `node`'s children and parent may coincide, only at the sentinel: its `parent` word ends
as the right child's when both children are the sentinel, and its link is written when it is also
the parent. -/
theorem switchWith_apply (h : Heap) (this node : Addr) (h₁ : this ≠ node)
    (h₂ : node ≠ childAt h node .left) (h₃ : node ≠ childAt h node .right)
    (h₄ : node ≠ parent h node) (h₅ : this ≠ childAt h node .left)
    (h₆ : this ≠ childAt h node .right) (h₇ : this ≠ parent h node) (x : Addr) :
    switchWith h this node x =
      if x = this then
        { (h this) with
          left := childAt h node .left
          right := childAt h node .right
          parent := parent h node
          side := parentSide h node
          red := red h node }
      else if x = childAt h node .right then
        { (if x = parent h node then (h x).withChild (parentSide h node) this else h x) with
          parent := this, side := .right }
      else if x = childAt h node .left then
        { (if x = parent h node then (h x).withChild (parentSide h node) this else h x) with
          parent := this, side := .left }
      else if x = parent h node then (h x).withChild (parentSide h node) this
      else h x := by
  generalize hL : childAt h node .left = L at *
  generalize hR : childAt h node .right = R at *
  generalize hP : parent h node = P at *
  generalize hps : parentSide h node = ps
  generalize hc : red h node = c
  simp only [childAt, parent, parentSide, red] at hL hR hP hps hc
  have hn1 : node ≠ this := Ne.symm h₁
  simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
    childAt, parent, parentSide, red, hL, hR, hps, hn1, h₂, h₃]
  have hn5 := Ne.symm h₅
  have hn6 := Ne.symm h₆
  have hn7 := Ne.symm h₇
  by_cases e₁ : x = this
  · subst e₁; simp [*]
  by_cases e₂ : x = R
  · subst e₂
    by_cases e₃ : x = P <;> by_cases e₅ : x = L
    · subst e₃; subst e₅; simp [*]; cases ps <;> rfl
    · subst e₃; simp [*]; cases ps <;> rfl
    · subst e₅; simp [*]
    · simp [*]
  by_cases e₃ : x = L
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; simp [*]; cases ps <;> rfl
    · simp [*]
  by_cases e₄ : x = P
  · subst e₄; simp [*]
  · simp [*]

/-- **`switchWith` touches four addresses**: `this`, `node`'s two children and `node`'s parent. -/
theorem switchWith_frame (h : Heap) (this node : Addr) {x : Addr}
    (h₁ : x ≠ this) (h₂ : x ≠ childAt h node .left) (h₃ : x ≠ childAt h node .right)
    (h₄ : x ≠ parent h node) : switchWith h this node x = h x := by
  simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
    childAt, parent, parentSide, red] at h₂ h₃ h₄ ⊢
  by_cases h₀ : node = this
  · subst h₀; simp [h₁, h₂, h₃, h₄]
  · simp [h₁, h₂, h₃, h₄, h₀]

/-- **`NodeBase::switch_with` puts `this` at `node`'s tree position** (step 3a, §4 theorem 2). If
the heap represents the located subtree `node c l node r`, and `this` is a real address neither in
it nor on its path, then after `switchWith h this node` the heap represents `node c l this r` at
the same slot and path: the address at that position changes, the subtrees and the colour do not.
This is `erase_counted`'s last step in its two-child `Node` case (the in-order successor, already
spliced out by `substitute_with`, takes the erased node's place: the zipper's `.right c _ m path`
in `eraseAt`) and its whole tree effect in the `Promote` case (the next chain member, with an
equal key, takes the attached member's place).

The other conclusions are the children's `parent` words: `node`'s right child, and its left child
unless both are the sentinel, now name `this`. For a child that is the sentinel these are its
scratch fields. In a two-child erase whose successor `this` was `node`'s right child and had no
right child, `node`'s right child is the sentinel by the time of the call, so the scratch `parent`
now names `this`, side right, which is where the hole is, overwriting what `substitute_with` wrote
(step 3c's hole invariant). -/
theorem switchWith_refines {h : Heap} {head this node p : Addr} {s : Side} {c : RBColor}
    {l r : RBNode Addr} {path : Path Addr}
    (hl : Located h head node p s (.node c l node r) path) (hn : this ≠ head) (hn0 : this ≠ null)
    (hpath : this ∉ path.listL ++ path.listR) (htree : this ∉ (RBNode.node c l node r).toList) :
    Located (switchWith h this node) head this p s (.node c l this r) path ∧
      (switchWith h this node (h node).right).parent = this ∧
      (switchWith h this node (h node).right).side = .right ∧
      ((h node).left ≠ (h node).right →
        (switchWith h this node (h node).left).parent = this ∧
        (switchWith h this node (h node).left).side = .left) := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hnh, -, hpa, hsa, hca, hL, hR⟩ := hr.node_inv
  generalize hLe : (h node).left = L at hL
  generalize hRe : (h node).right = R at hR
  obtain ⟨-, -, hnl, hnr, hlr⟩ := nodup_node hr.nodup
  simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at htree hpt
  have hLm : L ≠ head → L ∈ l.toList := hL.root_mem
  have hRm : R ≠ head → R ∈ r.toList := hR.root_mem
  -- Distinctness, the sentinel being the only address `L`, `R` and `p` can share.
  have hnL : node ≠ L := fun e => by
    by_cases hLh : L = head
    · exact hnh (e.trans hLh)
    · exact hnl (e ▸ hLm hLh)
  have hnR : node ≠ R := fun e => by
    by_cases hRh : R = head
    · exact hnh (e.trans hRh)
    · exact hnr (e ▸ hRm hRh)
  have hnp : node ≠ p := fun e => hpt.2.1 e.symm
  have htn : this ≠ node := htree.2.1
  have htL : this ≠ L := fun e => by
    by_cases hLh : L = head
    · exact hn (e.trans hLh)
    · exact htree.1 (e ▸ hLm hLh)
  have htR : this ≠ R := fun e => by
    by_cases hRh : R = head
    · exact hn (e.trans hRh)
    · exact htree.2.2 (e ▸ hRm hRh)
  have htp : this ≠ p := fun e => by
    rcases hp.slot with hph | hpm
    · exact hn (e.trans hph)
    · exact hpath (e ▸ hpm)
  have hLR : L ≠ head → L ≠ R := fun hLh e => by
    by_cases hRh : R = head
    · exact hLh (e.trans hRh)
    · exact hlr L (hLm hLh) (e ▸ hRm hRh)
  have hLp : L ≠ head → L ≠ p := fun hLh e => hpt.1 (e ▸ hLm hLh)
  have hRp : R ≠ head → R ≠ p := fun hRh e => hpt.2.2 (e ▸ hRm hRh)
  have SW := switchWith_apply h this node htn (by simpa [childAt, hLe] using hnL)
    (by simpa [childAt, hRe] using hnR) (by simpa [parent, hpa] using hnp)
    (by simpa [childAt, hLe] using htL) (by simpa [childAt, hRe] using htR)
    (by simpa [parent, hpa] using htp)
  simp only [childAt, parent, parentSide, red, hLe, hRe, hpa, hsa, hca] at SW
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  have FR : (switchWith h this node R).parent = this ∧ (switchWith h this node R).side = .right :=
    by simp [SW, Ne.symm htR]
  have FL : L ≠ R → (switchWith h this node L).parent = this ∧
      (switchWith h this node L).side = .left := fun hne => by simp [SW, Ne.symm htL, hne]
  refine ⟨⟨.node hn hn0 (by simp [SW]) (by simp [SW]) (by simp [SW]) ?_ ?_, ?_⟩, FR.1, FR.2,
    FL⟩
  · have e : (switchWith h this node this).left = L := by simp [SW]
    rw [e]
    refine hL.reroot (fun hLh => ?_) (fun x hx hxL => ?_)
    · have h1 := hLR hLh
      have h2 := hLp hLh
      simp [SW, Ne.symm htL, h1, h2]
    · have h1 : x ≠ this := fun e => htree.1 (e ▸ hx)
      have h2 : x ≠ R := fun e => by
        by_cases hRh : R = head
        · exact (hL.mem_ne hx).1 (e.trans hRh)
        · exact hlr x hx (e ▸ hRm hRh)
      have h3 : x ≠ p := fun e => hpt.1 (e ▸ hx)
      simp [SW, h1, h2, hxL, h3]
  · have e : (switchWith h this node this).right = R := by simp [SW]
    rw [e]
    refine hR.reroot (fun hRh => ?_) (fun x hx hxR => ?_)
    · have h2 := hRp hRh
      simp [SW, Ne.symm htR, h2]
    · have h1 : x ≠ this := fun e => htree.2.2 (e ▸ hx)
      have h2 : x ≠ L := fun e => by
        by_cases hLh : L = head
        · exact (hR.mem_ne hx).1 (e.trans hLh)
        · exact hlr L (hLm hLh) (e ▸ hx)
      have h3 : x ≠ p := fun e => hpt.2.2 (e ▸ hx)
      simp [SW, h1, h2, hxR, h3]
  · have hfr : ∀ x ∈ path.listL ++ path.listR, x ≠ p → switchWith h this node x = h x :=
      fun x hx hxp => by
        have h1 : x ≠ this := fun e => hpath (e ▸ hx)
        have h2 : x ≠ L := fun e => by
          by_cases hLh : L = head
          · exact (hout x hx).2 (e.trans hLh)
          · exact (hout x hx).1 (by
              simp only [RBNode.toList_node, List.mem_append, List.mem_cons]
              exact .inl (e ▸ hLm hLh))
        have h3 : x ≠ R := fun e => by
          by_cases hRh : R = head
          · exact (hout x hx).2 (e.trans hRh)
          · exact (hout x hx).1 (by
              simp only [RBNode.toList_node, List.mem_append, List.mem_cons]
              exact .inr (.inr (e ▸ hRm hRh)))
        simp [SW, h1, h2, h3, hxp]
    -- Off `this`, a record keeps its right link and colour (its left link too, off the slot's
    -- node), and the slot's node gets `this` in the slot: whichever of `L`, `R` and `p` coincide.
    have GEN : ∀ x, x ≠ this → (x = p → s = .left) →
        (switchWith h this node x).right = (h x).right ∧
        (switchWith h this node x).red = (h x).red ∧
        (x ≠ p → (switchWith h this node x).left = (h x).left) ∧
        (x = p → (switchWith h this node x).left = this) := by
      intro x hxt hxs
      rw [SW, ite_eq_right hxt]
      by_cases e₁ : x = R
      · rw [ite_eq_left e₁]
        by_cases e₃ : x = p
        · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
        · rw [ite_eq_right e₃]; simp [e₃]
      · rw [ite_eq_right e₁]
        by_cases e₂ : x = L
        · rw [ite_eq_left e₂]
          by_cases e₃ : x = p
          · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
          · rw [ite_eq_right e₃]; simp [e₃]
        · rw [ite_eq_right e₂]
          by_cases e₃ : x = p
          · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
          · rw [ite_eq_right e₃]; simp [e₃]
    have HH := GEN head (Ne.symm hn) (fun e => hs e.symm)
    refine hp.retarget hr hfr HH.1 HH.2.1 (fun hph => HH.2.2.1 (Ne.symm hph)) ?_ ?_
    · by_cases hph : p = head
      · have G := GEN p (Ne.symm htp) (fun _ => hs hph)
        obtain rfl := hs hph
        exact G.2.2.2 rfl
      · have e₁ : p ≠ R := fun e => hRp (fun h' => hph (e.trans h')) e.symm
        have e₂ : p ≠ L := fun e => hLp (fun h' => hph (e.trans h')) e.symm
        cases s <;> simp [SW, childAt, Ne.symm htp, e₁, e₂, NodeRec.withChild]
    · intro hph
      have e₁ : p ≠ R := fun e => hRp (fun h' => hph (e.trans h')) e.symm
      have e₂ : p ≠ L := fun e => hLp (fun h' => hph (e.trans h')) e.symm
      cases s <;> simp [SW, childAt, Side.other, Ne.symm htp, e₁, e₂, NodeRec.withChild]

/-! ## Step 3b, the tools: colours, climbing the path, the final `make_black`

What `insert_fixup`'s refinement proof needs besides the structural operations of step 3a: how a
heap's colour bits read back through `Rep`, how a located subtree moves up and down its path,
what a colour write does to a located subtree, and what the final `make_black` of the root does
to a whole tree. -/

/-- A path's relation keeps the sentinel black: `RepPath`'s root case requires it, and every
other case carries it up. -/
theorem RepPath.head_red {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a p s path) : (h head).red = false := by
  induction hp with
  | root _ _ e => exact e
  | left _ _ _ _ _ _ ih => exact ih
  | right _ _ _ _ _ _ ih => exact ih

/-- **Colour bits read back.** The `red` bit at a subtree's starting address is the zipper's
`red?` of the subtree, for the sentinel too (black, as `NodeBase::red` reads it), provided the
sentinel's bit is clear. -/
theorem Rep.red_eq {h : Heap} {head a p : Addr} {s : Side} {u : RBNode Addr}
    (hr : Rep h head a p s u) (hh : (h head).red = false) : red h a = red? u := by
  cases hr with
  | nil => exact hh
  | @node _ _ _ c _ _ _ _ _ _ hc _ _ => cases c <;> exact hc

/-- A slot on a left path step is that step's node's left link. -/
theorem RepPath.left_inv {h : Heap} {head a p y : Addr} {s : Side} {c : RBColor}
    {pp : Path Addr} {b : RBNode Addr} (hp : RepPath h head a p s (.left c pp y b)) :
    p = y ∧ s = .left := by
  cases hp; exact ⟨rfl, rfl⟩

/-- A slot on a right path step is that step's node's right link. -/
theorem RepPath.right_inv {h : Heap} {head a p y : Addr} {s : Side} {c : RBColor}
    {pp : Path Addr} {b : RBNode Addr} (hp : RepPath h head a p s (.right c b y pp)) :
    p = y ∧ s = .right := by
  cases hp; exact ⟨rfl, rfl⟩

namespace Located

variable {h : Heap} {head a y P : Addr} {S : Side} {c : RBColor} {t l r b : RBNode Addr}
  {pp : Path Addr}

/-- **Climbing a left step**: a subtree located as `y`'s left child is part of `y`'s subtree,
located at `y`'s own slot, read from `y`'s `parent` word, one step up the path. -/
theorem up_left (hl : Located h head a y .left t (.left c pp y b)) :
    Located h head y (h y).parent (h y).side (.node c t y b) pp := by
  obtain ⟨hr, hp⟩ := hl
  cases hp with
  | left hy hn ha hc hb hpp => exact ⟨.node hy hn rfl rfl hc (ha ▸ hr) hb, hpp⟩

/-- **Climbing a right step**, the mirror image of `up_left`. -/
theorem up_right (hl : Located h head a y .right t (.right c b y pp)) :
    Located h head y (h y).parent (h y).side (.node c b y t) pp := by
  obtain ⟨hr, hp⟩ := hl
  cases hp with
  | right hy hn ha hc hb hpp => exact ⟨.node hy hn rfl rfl hc hb (ha ▸ hr), hpp⟩

/-- **Descending to the left child**: the converse of `up_left`. -/
theorem down_left (hl : Located h head y P S (.node c l y r) pp) :
    Located h head (h y).left y .left l (.left c pp y r) := by
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, hc, hll, hrr⟩ := hr.node_inv
  exact ⟨hll, .left hy hn rfl hc hrr (hpa ▸ hsa ▸ hp)⟩

/-- **Descending to the right child**: the converse of `up_right`. -/
theorem down_right (hl : Located h head y P S (.node c l y r) pp) :
    Located h head (h y).right y .right r (.right c l y pp) := by
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, hc, hll, hrr⟩ := hr.node_inv
  exact ⟨hrr, .right hy hn rfl hc hll (hpa ▸ hsa ▸ hp)⟩

/-- **`NodeBase::set_colour` on a located subtree's first node** gives it the new colour and
changes nothing else the relation reads: the zipper's `paint` at the hole. (`makeBlack` and
`makeRed` are `setColour` with `colourBit .black` and `colourBit .red`.) -/
theorem paint (hl : Located h head y P S (.node c l y r) pp) (c' : RBColor) :
    Located (setColour h y (colourBit c')) head y P S (.node c' l y r) pp := by
  have hout := hl.outside
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, -, hll, hrr⟩ := hr.node_inv
  obtain ⟨-, -, hyl, hyr, -⟩ := nodup_node hr.nodup
  have F : ∀ x, x ≠ y → setColour h y (colourBit c') x = h x := fun x hx => by
    simp [setColour, Heap.modify, hx]
  have Y : setColour h y (colourBit c') y = { h y with red := colourBit c' } := by
    simp [setColour, Heap.modify]
  refine ⟨.node hy hn (by rw [Y]; exact hpa) (by rw [Y]; exact hsa) (by rw [Y]) ?_ ?_, ?_⟩
  · rw [Y]; exact hll.frame fun x hx => F x (fun e => hyl (e ▸ hx))
  · rw [Y]; exact hrr.frame fun x hx => F x (fun e => hyr (e ▸ hx))
  · have hyh : head ≠ y := Ne.symm hy
    exact hp.frame (fun x hx => F x (fun e => (hout x hx).1 (by simp [e])))
      (by rw [F head hyh]) (by rw [F head hyh]) (by rw [F head hyh])

end Located

/-- `setColour` changes no `parent` pointer. -/
theorem setColour_parent (h : Heap) (a : Addr) (b : Bool) (x : Addr) :
    (setColour h a b x).parent = (h x).parent := by
  by_cases e : x = a <;> simp [setColour, Heap.modify, e]

/-- `setColour` changes no other address's colour. -/
theorem setColour_red_ne (h : Heap) (a : Addr) (b : Bool) {x : Addr} (hx : x ≠ a) :
    (setColour h a b x).red = (h x).red := by
  simp [setColour, Heap.modify, hx]

/-- `setColour` sets the colour it writes. -/
theorem setColour_red_eq (h : Heap) (a : Addr) (b : Bool) : (setColour h a b a).red = b := by
  simp [setColour, Heap.modify]

/-- A write that keeps colours keeps every address's colour. -/
theorem Heap.modify_red (h : Heap) (a : Addr) (f : NodeRec → NodeRec)
    (hf : ∀ n, (f n).red = n.red) (x : Addr) : (h.modify a f x).red = (h x).red := by
  by_cases e : x = a <;> simp [Heap.modify, e, hf]

/-- **`rotateAt` changes no colour**: its nine writes are child links and `parent` words. -/
theorem rotateAt_red (h : Heap) (this : Addr) (s : Side) (x : Addr) :
    (rotateAt h this s x).red = (h x).red := by
  simp only [rotateAt, setChild_eq, setParentPtr, setParentSide]
  repeat rw [Heap.modify_red _ _ _ (fun _ => by simp)]

/-- **`insert_fixup`'s final `make_black(head.child(Left))`** blackens the represented tree's root:
the zipper's `setBlack` of the whole tree. On an empty tree it writes the sentinel's colour bit,
black over black. -/
theorem Tree.makeBlack_root {h : Heap} {head : Addr} {T : RBNode Addr} (ht : Tree h head T) :
    Tree (makeBlack h (childAt h head .left)) head T.setBlack := by
  cases T with
  | nil =>
    obtain ⟨hr, e₂, e₃⟩ := ht
    have hroot : (h head).left = head := hr.nil_inv
    have H : makeBlack h (childAt h head .left) head = { h head with red := false } := by
      simp [makeBlack, setColour, Heap.modify, childAt, hroot]
    refine ⟨?_, by rw [H]; exact e₂, by rw [H]⟩
    rw [H]; show Rep _ head (h head).left head .left .nil; rw [hroot]; exact .nil
  | node c l v r =>
    obtain ⟨hv, hvh, -⟩ := ht.1.node_inv
    have hl : Located h head v head .left (.node c l v r) .root := by
      have := tree_iff_located.1 ht; rw [hv] at this; exact this
    have hl' := hl.paint .black
    have E : setColour h v (colourBit .black) head = h head := by
      simp [setColour, Heap.modify, Ne.symm hvh]
    apply tree_iff_located.2
    have e : childAt h head .left = v := hv
    simp only [makeBlack, e]
    rw [show (setColour h v false head).left = v by
      rw [show false = colourBit .black from rfl, E, hv]]
    exact hl'

/-! ## Step 3b: `insert_fixup` performs `insFix`

The loop invariant is a located subtree (`Located h head cur p s t path`, `cur` a real node), with
`p`, the slot's node, as the loop's `p`: its colour, and the sentinel's, are read through `Rep` and
`RepPath`. One more hypothesis: the tree's root is black (`rootColour`). On a path whose top node
is red and is `cur`'s parent, the Rust's loop would find a red parent with no grandparent and run
its black-uncle branch at the sentinel, where `insFix` stops (Fixup.lean's "unreachable red-root
shape"); the Rust's callers never reach it, the tree's root being black. -/

/-- The depth of a path's hole: the number of nodes above it. The loop's fuel is measured against
it (`insertFixupLoop_refines`). -/
def pathDepth : Path Addr → Nat
  | .root => 0
  | .left _ pp _ _ => pathDepth pp + 1
  | .right _ _ _ pp => pathDepth pp + 1

/-- The colour of a path's topmost node, the whole tree's root (`none` for the empty path, where
the hole is the root). -/
def rootColour : Path Addr → Option RBColor
  | .root => none
  | .left c pp _ _ => (rootColour pp).getD c |> some
  | .right c _ _ pp => (rootColour pp).getD c |> some

/-- A black (or absent) root stays so when the hole climbs one step. -/
theorem rootColour_up_left {c : RBColor} {pp : Path Addr} {y : Addr} {b : RBNode Addr}
    (h : rootColour (.left c pp y b) ≠ some .red) : rootColour pp ≠ some .red := by
  cases e : rootColour pp with
  | none => simp
  | some c₀ => simp only [rootColour, e, Option.getD_some] at h; exact h

/-- The mirror image of `rootColour_up_left`. -/
theorem rootColour_up_right {c : RBColor} {pp : Path Addr} {y : Addr} {b : RBNode Addr}
    (h : rootColour (.right c b y pp) ≠ some .red) : rootColour pp ≠ some .red := by
  cases e : rootColour pp with
  | none => simp
  | some c₀ => simp only [rootColour, e, Option.getD_some] at h; exact h

/-- The loop's exit: a black `p` ends it with the final `make_black` of the root. -/
theorem insertFixupLoop_exit {head : Addr} {fuel : Nat} {h : Heap} {cur p : Addr} {rot : Nat}
    (hp : red h p = false) :
    insertFixupLoop head (fuel + 1) h cur p rot =
      some (makeBlack h (childAt h head .left), rot) := by
  simp [insertFixupLoop, hp]

/-- **`insert_fixup`'s loop performs `insFix`** (step 3b; the note's §4, theorem 3). If the heap
represents the located subtree `t` at `path`, `cur` (its first node) is a real node, the tree's root
is black (`rootColour path ≠ some .red`, vacuous when `cur` is the root) and the fuel is at least
the depth of the hole plus one, then the loop, started from `cur` and its parent `P` with `rot`
rotations counted, returns a heap representing the whole tree `(insFix path t).1`, with
`rot + (insFix path t).2` rotations: the zipper's result and rotation count, for every input of
these shapes, valid red-black tree or not.

The proof follows `insFix` case by case: the root and a black parent (the loop's exit), and for a
red parent the eight combinations of `p`'s side, `cur`'s side and the uncle's colour. A red uncle
recolours three nodes and climbs two levels (the induction hypothesis, with one unit of fuel less);
a black uncle rotates once (`cur` outer) or twice (`cur` inner), and the next test ends the loop,
`p` being black. -/
theorem insertFixupLoop_refines (head : Addr) : ∀ (fuel : Nat) {h : Heap} {cur P : Addr}
    {S : Side} {t : RBNode Addr} {path : Path Addr} (rot : Nat),
    Located h head cur P S t path → cur ≠ head → rootColour path ≠ some .red →
    pathDepth path + 1 ≤ fuel →
    ∃ H, insertFixupLoop head fuel h cur P rot = some (H, rot + (insFix path t).2) ∧
      Tree H head (insFix path t).1
  | 0, _, _, _, _, _, _, _, _, _, _, hf => absurd hf (by omega)
  | fuel + 1, h, cur, P, S, t, path, rot, hl, hcur, hroot, hf => by
    have hhead := hl.2.head_red
    have exit : red h P = false → insFix path t = ((path.fill t).setBlack, 0) →
        ∃ H, insertFixupLoop head (fuel + 1) h cur P rot = some (H, rot + (insFix path t).2) ∧
          Tree H head (insFix path t).1 := fun hp hz =>
      ⟨_, by rw [insertFixupLoop_exit hp, hz]; rfl,
        by rw [hz]; exact (hl.2.fill hl.1).makeBlack_root⟩
    have hcm : cur ∈ t.toList := hl.1.root_mem hcur
    match path, hl, hroot, hf with
    | .root, hl, _, _ =>
      cases hl.2
      exact exit hhead (by simp [insFix])
    | .left .black pp y b, hl, _, _ =>
      obtain ⟨e₁, e₂⟩ := hl.2.left_inv; subst P S
      have hy := hl.up_left.1.node_inv.2.2.2.2.2.1
      exact exit hy (by cases pp <;> simp [insFix])
    | .right .black b y pp, hl, _, _ =>
      obtain ⟨e₁, e₂⟩ := hl.2.right_inv; subst P S
      have hy := hl.up_right.1.node_inv.2.2.2.2.2.1
      exact exit hy (by cases pp <;> simp [insFix])
    | .left .red .root y b, _, hroot, _ => exact absurd (by simp [rootColour]) hroot
    | .right .red b y .root, _, hroot, _ => exact absurd (by simp [rootColour]) hroot
    -- `p` is `pp`'s left child, `cur` is `p`'s left child (outer).
    | .left .red (.left c' gp z u) y b, hl, hroot, hf =>
      obtain ⟨e₁, e₂⟩ := hl.2.left_inv; subst P S
      have Ly := hl.up_left
      obtain ⟨hyz, hys⟩ := Ly.2.left_inv
      rw [hyz, hys] at Ly
      have hyr : (h y).red = true := Ly.1.node_inv.2.2.2.2.2.1
      have Lz := Ly.up_left
      have hzh : z ≠ head := Lz.1.node_inv.2.1
      have hyz' : y ≠ z := fun e => (nodup_node Lz.1.nodup).2.2.1 (by simp [e])
      have Lu := Lz.down_right
      have hur : red h (h z).right = red? u := Lu.1.red_eq hhead
      have hroot' := rootColour_up_left (rootColour_up_left hroot)
      simp only [pathDepth] at hf
      by_cases hu : red? u = true
      · -- Red uncle: recolour, climb two levels.
        obtain ⟨ul, uv, ur, rfl⟩ : ∃ ul uv ur, u = .node .red ul uv ur := by
          match u, hu with
          | .node .red ul uv ur, _ => exact ⟨ul, uv, ur, rfl⟩
        have huv : (h z).right = uv := Lu.1.node_inv.1
        have hcol : (h uv).red = true := by rw [← huv]; exact hur.trans hu
        have Lz1 := (Ly.paint .black).up_left
        have Lu1 := Lz1.down_right
        rw [Lu1.1.node_inv.1] at Lu1
        have Lz3 := ((Lu1.paint .black).up_right).paint .red
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.left .red (.left c' gp z (.node .red ul uv ur)) y b) t =
            insFix gp (.node .red (.node .black t y b) z (.node .black ul uv ur)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH]
        simp only [insertFixupLoop, red, hyr, parent, parentSide, hyz, hys, Side.other, childAt,
          huv, hcol, makeBlack, makeRed, setColour_parent, colourBit, ite_true]
      · -- Black uncle, `cur` outer: `make_black(p); make_red(pp); rotate(pp, o)`; then the loop
        -- exits, `p` being black.
        have hcol : (h (h z).right).red = false := by
          have := hur; simp only [red] at this; rw [this]; simpa using hu
        obtain ⟨-, -, -, -, -, -, -, hrb⟩ := Ly.1.node_inv
        obtain ⟨-, -, -, -, htb⟩ := nodup_node Ly.1.nodup
        have hcy : cur ≠ (h y).right := fun e => by
          by_cases hrh : (h y).right = head
          · exact hcur (e.trans hrh)
          · exact htb cur hcm (e ▸ hrb.root_mem hrh)
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have L2 := ((Ly.paint .black).up_left).paint .red
        have L3 := rotateAt_refines_right L2
        have hT := (L3.2.fill L3.1).makeBlack_root
        have hz : insFix (.left .red (.left c' gp z u) y b) t =
            ((gp.fill (rotate .right (.node .red (.node .black t y b) z u))).setBlack, 1) := by
          rw [insFix, ite_eq_right hu]
        rw [hz]
        refine ⟨_, ?_, hT⟩
        have hy3 : red (rotateAt (setColour (setColour h y false) z true) z .right) y = false := by
          simp only [red, rotateAt_red, setColour_red_ne _ _ _ hyz', setColour_red_eq]
        rw [insertFixupLoop]
        simp only [red, hyr, parent, parentSide, hyz, hys, Side.other, childAt, hcol,
          Bool.false_eq_true, ite_true, ite_false, hcy, makeBlack, makeRed]
        rw [insertFixupLoop_exit hy3]; rfl
    -- `p` is `pp`'s right child, `cur` is `p`'s right child (outer).
    | .right .red a y (.right c' u z gp), hl, hroot, hf =>
      obtain ⟨e₁, e₂⟩ := hl.2.right_inv; subst P S
      have Ly := hl.up_right
      obtain ⟨hyz, hys⟩ := Ly.2.right_inv
      rw [hyz, hys] at Ly
      have hyr : (h y).red = true := Ly.1.node_inv.2.2.2.2.2.1
      have Lz := Ly.up_right
      have hzh : z ≠ head := Lz.1.node_inv.2.1
      have hyz' : y ≠ z := fun e => (nodup_node Lz.1.nodup).2.2.2.1 (by simp [e])
      have Lu := Lz.down_left
      have hur : red h (h z).left = red? u := Lu.1.red_eq hhead
      have hroot' := rootColour_up_right (rootColour_up_right hroot)
      simp only [pathDepth] at hf
      by_cases hu : red? u = true
      · -- Red uncle: recolour, climb two levels.
        obtain ⟨ul, uv, ur, rfl⟩ : ∃ ul uv ur, u = .node .red ul uv ur := by
          match u, hu with
          | .node .red ul uv ur, _ => exact ⟨ul, uv, ur, rfl⟩
        have huv : (h z).left = uv := Lu.1.node_inv.1
        have hcol : (h uv).red = true := by rw [← huv]; exact hur.trans hu
        have Lz1 := (Ly.paint .black).up_right
        have Lu1 := Lz1.down_left
        rw [Lu1.1.node_inv.1] at Lu1
        have Lz3 := ((Lu1.paint .black).up_left).paint .red
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.right .red a y (.right c' (.node .red ul uv ur) z gp)) t =
            insFix gp (.node .red (.node .black ul uv ur) z (.node .black a y t)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH]
        simp only [insertFixupLoop, red, hyr, parent, parentSide, hyz, hys, Side.other, childAt,
          huv, hcol, makeBlack, makeRed, setColour_parent, colourBit, ite_true]
      · -- Black uncle, `cur` outer: `make_black(p); make_red(pp); rotate(pp, o)`; then the loop
        -- exits, `p` being black.
        have hcol : (h (h z).left).red = false := by
          have := hur; simp only [red] at this; rw [this]; simpa using hu
        obtain ⟨-, -, -, -, -, -, hla, -⟩ := Ly.1.node_inv
        obtain ⟨-, -, -, -, hat⟩ := nodup_node Ly.1.nodup
        have hcy : cur ≠ (h y).left := fun e => by
          by_cases hlh : (h y).left = head
          · exact hcur (e.trans hlh)
          · exact hat _ (hla.root_mem hlh) (e ▸ hcm)
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have L2 := ((Ly.paint .black).up_right).paint .red
        have L3 := rotateAt_refines_left L2
        have hT := (L3.2.fill L3.1).makeBlack_root
        have hz : insFix (.right .red a y (.right c' u z gp)) t =
            ((gp.fill (rotate .left (.node .red u z (.node .black a y t)))).setBlack, 1) := by
          rw [insFix, ite_eq_right hu]
        rw [hz]
        refine ⟨_, ?_, hT⟩
        have hy3 : red (rotateAt (setColour (setColour h y false) z true) z .left) y = false := by
          simp only [red, rotateAt_red, setColour_red_ne _ _ _ hyz', setColour_red_eq]
        rw [insertFixupLoop]
        simp only [red, hyr, parent, parentSide, hyz, hys, Side.other, childAt, hcol,
          Bool.false_eq_true, ite_true, ite_false, hcy, makeBlack, makeRed]
        rw [insertFixupLoop_exit hy3]; rfl
    -- `p` is `pp`'s left child, `cur` is `p`'s right child (inner): `rotate(p, Left)` first.
    | .right .red a y (.left c' gp z u), hl, hroot, hf =>
      obtain ⟨e₁, e₂⟩ := hl.2.right_inv; subst P S
      have Ly := hl.up_right
      obtain ⟨hyz, hys⟩ := Ly.2.left_inv
      rw [hyz, hys] at Ly
      have hyr : (h y).red = true := Ly.1.node_inv.2.2.2.2.2.1
      have Lz := Ly.up_left
      have hzh : z ≠ head := Lz.1.node_inv.2.1
      have Lu := Lz.down_right
      have hur : red h (h z).right = red? u := Lu.1.red_eq hhead
      have hroot' := rootColour_up_left (rootColour_up_right hroot)
      simp only [pathDepth] at hf
      by_cases hu : red? u = true
      · -- Red uncle: recolour, climb two levels.
        obtain ⟨ul, uv, ur, rfl⟩ : ∃ ul uv ur, u = .node .red ul uv ur := by
          match u, hu with
          | .node .red ul uv ur, _ => exact ⟨ul, uv, ur, rfl⟩
        have huv : (h z).right = uv := Lu.1.node_inv.1
        have hcol : (h uv).red = true := by rw [← huv]; exact hur.trans hu
        have Lz1 := (Ly.paint .black).up_left
        have Lu1 := Lz1.down_right
        rw [Lu1.1.node_inv.1] at Lu1
        have Lz3 := ((Lu1.paint .black).up_right).paint .red
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.right .red a y (.left c' gp z (.node .red ul uv ur))) t =
            insFix gp (.node .red (.node .black a y t) z (.node .black ul uv ur)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH]
        simp only [insertFixupLoop, red, hyr, parent, parentSide, hyz, hys, Side.other, childAt,
          huv, hcol, makeBlack, makeRed, setColour_parent, colourBit, ite_true]
      · -- Black uncle, `cur` inner: `cur = p; rotate(cur, s)`, then `make_black(p); make_red(pp);
        -- rotate(pp, o)` with `p` now the old `cur`; then the loop exits.
        have hcol : (h (h z).right).red = false := by
          have := hur; simp only [red] at this; rw [this]; simpa using hu
        obtain ⟨ct, tl, x, tr, rfl⟩ : ∃ ct tl x tr, t = .node ct tl x tr := by
          match t, hcm with
          | .node ct tl x tr, _ => exact ⟨ct, tl, x, tr, rfl⟩
        have hcx : cur = x := hl.1.node_inv.1
        subst hcx
        have hyc : (h y).right = cur := Ly.1.node_inv.2.2.2.2.2.2.2.node_inv.1
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have L1 : Located (rotateAt h y .left) head cur z .left
            (.node ct (.node .red a y tl) cur tr) (.left c' gp z u) := rotateAt_refines_left Ly
        have hyx : (rotateAt h y .left y).parent = cur := by
          obtain ⟨-, -, -, -, -, -, hlx, -⟩ := L1.1.node_inv
          exact hlx.node_inv.2.2.2.1
        have hxz : cur ≠ z := fun e => (nodup_node L1.up_left.1.nodup).2.2.1 (by simp [e])
        have L3 := ((L1.paint .black).up_left).paint .red
        have L4 := rotateAt_refines_right L3
        have hT := (L4.2.fill L4.1).makeBlack_root
        have hz : insFix (.right .red a y (.left c' gp z u)) (.node ct tl cur tr) =
            ((gp.fill (rotate .right (.node .red (.node .black (.node .red a y tl) cur tr) z u))
              ).setBlack, 2) := by
          rw [insFix, ite_eq_right hu]; rfl
        rw [hz]
        refine ⟨_, ?_, hT⟩
        have hx4 : red (rotateAt (setColour (setColour (rotateAt h y .left) cur false) z true)
            z .right) cur = false := by
          simp only [red, rotateAt_red, setColour_red_ne _ _ _ hxz, setColour_red_eq]
        rw [insertFixupLoop]
        simp only [red, hyr, parent, parentSide, hyz, hys, Side.other, childAt, hcol,
          Bool.false_eq_true, ite_true, ite_false, hyc, makeBlack, makeRed, hyx]
        rw [insertFixupLoop_exit hx4]; rfl
    -- `p` is `pp`'s right child, `cur` is `p`'s left child (inner): `rotate(p, Right)` first.
    | .left .red (.right c' u z gp) y b, hl, hroot, hf =>
      obtain ⟨e₁, e₂⟩ := hl.2.left_inv; subst P S
      have Ly := hl.up_left
      obtain ⟨hyz, hys⟩ := Ly.2.right_inv
      rw [hyz, hys] at Ly
      have hyr : (h y).red = true := Ly.1.node_inv.2.2.2.2.2.1
      have Lz := Ly.up_right
      have hzh : z ≠ head := Lz.1.node_inv.2.1
      have Lu := Lz.down_left
      have hur : red h (h z).left = red? u := Lu.1.red_eq hhead
      have hroot' := rootColour_up_right (rootColour_up_left hroot)
      simp only [pathDepth] at hf
      by_cases hu : red? u = true
      · -- Red uncle: recolour, climb two levels.
        obtain ⟨ul, uv, ur, rfl⟩ : ∃ ul uv ur, u = .node .red ul uv ur := by
          match u, hu with
          | .node .red ul uv ur, _ => exact ⟨ul, uv, ur, rfl⟩
        have huv : (h z).left = uv := Lu.1.node_inv.1
        have hcol : (h uv).red = true := by rw [← huv]; exact hur.trans hu
        have Lz1 := (Ly.paint .black).up_right
        have Lu1 := Lz1.down_left
        rw [Lu1.1.node_inv.1] at Lu1
        have Lz3 := ((Lu1.paint .black).up_left).paint .red
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.left .red (.right c' (.node .red ul uv ur) z gp) y b) t =
            insFix gp (.node .red (.node .black ul uv ur) z (.node .black t y b)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH]
        simp only [insertFixupLoop, red, hyr, parent, parentSide, hyz, hys, Side.other, childAt,
          huv, hcol, makeBlack, makeRed, setColour_parent, colourBit, ite_true]
      · -- Black uncle, `cur` inner: `cur = p; rotate(cur, s)`, then `make_black(p); make_red(pp);
        -- rotate(pp, o)` with `p` now the old `cur`; then the loop exits.
        have hcol : (h (h z).left).red = false := by
          have := hur; simp only [red] at this; rw [this]; simpa using hu
        obtain ⟨ct, tl, x, tr, rfl⟩ : ∃ ct tl x tr, t = .node ct tl x tr := by
          match t, hcm with
          | .node ct tl x tr, _ => exact ⟨ct, tl, x, tr, rfl⟩
        have hcx : cur = x := hl.1.node_inv.1
        subst hcx
        have hyc : (h y).left = cur := Ly.1.node_inv.2.2.2.2.2.2.1.node_inv.1
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have L1 : Located (rotateAt h y .right) head cur z .right
            (.node ct tl cur (.node .red tr y b)) (.right c' u z gp) := rotateAt_refines_right Ly
        have hyx : (rotateAt h y .right y).parent = cur := by
          obtain ⟨-, -, -, -, -, -, -, hrx⟩ := L1.1.node_inv
          exact hrx.node_inv.2.2.2.1
        have hxz : cur ≠ z := fun e => (nodup_node L1.up_right.1.nodup).2.2.2.1 (by simp [e])
        have L3 := ((L1.paint .black).up_right).paint .red
        have L4 := rotateAt_refines_left L3
        have hT := (L4.2.fill L4.1).makeBlack_root
        have hz : insFix (.left .red (.right c' u z gp) y b) (.node ct tl cur tr) =
            ((gp.fill (rotate .left (.node .red u z (.node .black tl cur (.node .red tr y b))))
              ).setBlack, 2) := by
          rw [insFix, ite_eq_right hu]; rfl
        rw [hz]
        refine ⟨_, ?_, hT⟩
        have hx4 : red (rotateAt (setColour (setColour (rotateAt h y .right) cur false) z true)
            z .left) cur = false := by
          simp only [red, rotateAt_red, setColour_red_ne _ _ _ hxz, setColour_red_eq]
        rw [insertFixupLoop]
        simp only [red, hyr, parent, parentSide, hyz, hys, Side.other, childAt, hcol,
          Bool.false_eq_true, ite_true, ite_false, hyc, makeBlack, makeRed, hyx]
        rw [insertFixupLoop_exit hx4]; rfl

/-- **The heap-level `insert_fixup` performs `insFix`**: `insertFixupLoop_refines` from the
Rust's entry, `insert_fixup(node)` with `p = parent(node)` and no rotation counted yet. -/
theorem insertFixup_refines {fuel : Nat} {h : Heap} {head node P : Addr} {S : Side}
    {t : RBNode Addr} {path : Path Addr} (hl : Located h head node P S t path)
    (hn : node ≠ head) (hroot : rootColour path ≠ some .red) (hf : pathDepth path + 1 ≤ fuel) :
    ∃ H, insertFixup fuel h head node = some (H, (insFix path t).2) ∧
      Tree H head (insFix path t).1 := by
  have hP : parent h node = P := (hl.1.root_fields (hl.1.root_mem hn)).1
  obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines head fuel 0 hl hn hroot hf
  refine ⟨H, ?_, hT⟩
  rw [insertFixup, hP, hH, Nat.zero_add]

/-- The hole of a path lies above the subtree in it: the depth of the filled tree is at least the
hole's depth plus the subtree's. -/
theorem pathDepth_add_depth_le (path : Path Addr) (t : RBNode Addr) :
    pathDepth path + t.depth ≤ (path.fill t).depth := by
  induction path generalizing t with
  | root => simp [pathDepth, Path.fill]
  | left c pp y b ih =>
    have := ih (.node c t y b)
    simp only [pathDepth, Path.fill, RBNode.depth] at this ⊢
    have := Nat.le_max_left t.depth b.depth
    omega
  | right c b y pp ih =>
    have := ih (.node c b y t)
    simp only [pathDepth, Path.fill, RBNode.depth] at this ⊢
    have := Nat.le_max_right b.depth t.depth
    omega

/-- **The first fuel theorem**: fuel at least the depth of the tree `insert_fixup` starts from
(`RBNode.depth`, the number of nodes on its longest branch: its height in edges plus one)
suffices, under `insertFixup_refines`'s other hypotheses (a located real node, a black root), so
the loop's one departure from the Rust (the module doc) never shows. -/
theorem insertFixup_refines_depth {fuel : Nat} {h : Heap} {head node P : Addr} {S : Side}
    {t : RBNode Addr} {path : Path Addr} (hl : Located h head node P S t path)
    (hn : node ≠ head) (hroot : rootColour path ≠ some .red) (hf : (path.fill t).depth ≤ fuel) :
    ∃ H, insertFixup fuel h head node = some (H, (insFix path t).2) ∧
      Tree H head (insFix path t).1 := by
  refine insertFixup_refines hl hn hroot ?_
  have h1 := pathDepth_add_depth_le path t
  obtain ⟨c, l, v, r, rfl⟩ : ∃ c l v r, t = .node c l v r := by
    match t, hl.1.root_mem hn with
    | .node c l v r, _ => exact ⟨c, l, v, r, rfl⟩
  simp only [RBNode.depth] at h1
  omega

end Heap

end Oris.RB
