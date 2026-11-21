-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Fixup

/-!
# `rbtree.rs`'s pointer code, on a model heap

Steps 1 and 2 of the heap layer, as numbered in the plan of `Lean/docs/heap-layer.md` (§5;
§4 numbers the theorems, `rotateAt_refines` being its first).

- **Step 1, the definitions.** Every function below transcribes one function of
  `Rust/src/rbtree.rs`, **one heap update per Rust write, in the Rust's order**, with every read
  where the Rust reads it.
- **Step 2, the abstraction relation and the first refinement theorem.** `Rep`, `RepPath`,
  `Located` and `Tree` say when a heap represents a zipper state of `Oris/RB/Fixup.lean`, and
  `rotateAt_refines_left` and `rotateAt_refines_right` prove that `rotateAt` (`NodeBase::rotate`)
  performs the zipper's rotation.

That the other functions perform their zipper steps is the plan's steps 3 and 4.

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
  `none` when it runs out. That is this file's one departure from the Rust's behaviour, and it
  is not yet proven unreachable: the Rust loops until the tree's structure stops them. Each loop
  spends one unit of fuel on its final, failing test, so the plan's steps 3 and 4 will prove
  that fuel at least the tree's height **plus one** (its size plus one, for the descents)
  always suffices. Each loop's doc repeats this.
- `erase_fixup`'s root comes in two readings: `eraseFixup` reads it once on entry, as the Rust
  does, and `eraseFixupHpha` re-reads it, as `Cpp/hpha.cpp` does. The note's §6 plans the theorem
  that they agree.

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
it runs out. -/
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
doc): `none` when it runs out. -/
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

/-- Of `this`'s parent, `rotateAt` writes only the child link `this` hung from, which now holds
`top`: the other link and the colour are kept, and so is the `parent` word unless the parent is
also `top`'s side-`s` child (a rotation at the root whose moving subtree is empty: both are the
sentinel, and its scratch `parent` and side are written). -/
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
`top`'s side-`s` child and `P` `this`'s parent, all distinct except that `m` and `P` may coincide (a
rotation at the root whose moving subtree is empty: both are then the sentinel), `rotateAt h this s`
gives `this` the child `m` on side `o` and the slot `(top, s)`; `top` the child `this` on side `s`
and `this`'s old slot; `m` the slot `(this, o)`; `P` the child `top` in the link that held `this`
(on `m`'s record too when `m = P`); and every other address its old record. The writes' order
matters only where two of them hit the same field, which the distinctness rules out. -/
theorem rotateAt_apply (h : Heap) (this : Addr) (s : Side)
    (h₁ : this ≠ childAt h this s.other) (h₂ : this ≠ childAt h (childAt h this s.other) s)
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
  · subst e₁; simp [h₁, h₂, h₄]
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
    (by simpa [childAt, Side.other, hab, hm] using ham)
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
    (by simpa [childAt, Side.other, hab, hm] using ham)
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

Each performs the zipper step `Fixup.lean`'s `insert` or `eraseAt` takes at that point (the note's
§4, step 2): `attach_to` fills an empty hole with a red leaf, `substitute_with` splices out a node
with at most one child, and `switch_with` puts another address at a node's tree position. Each
comes with its per-address description (`_apply`), the list of records it changes (`_frame`) and
its refinement theorem (`_refines`). -/

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

/-- **`NodeBase::attach_to` fills the empty hole** (the note's §4, step 2). If the slot `(p, s)`
holds the sentinel at `path` (the empty hole where `insert_counted`'s descent ends), and `this` is
a real address off the path, then after `attachTo h this p s` the heap represents the red leaf
`node red nil this nil` at that slot and path: the zipper state `Fixup.lean`'s `insert` hands to
`insFix`. Which records change is `attachTo_frame`. -/
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

end Heap

end Oris.RB
