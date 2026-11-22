-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Fixup

/-!
# `rbtree.rs`'s pointer code, on a model heap: the definitions

Step 1 of the heap layer (`Lean/docs/heap-layer.md`, §5). Every function below transcribes one
function of `Rust/src/rbtree.rs`, **one heap update per Rust write, in the Rust's order**, with
every read where the Rust reads it. This is the file the pointer-code rule of `CONVENTIONS.md`
(§ *Keeping the model in step with the Rust*) points to; the theorems about these definitions are
in the other modules of `Oris/RB/Heap/` (overview: `Oris/RB/Heap.lean`).

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
  plus one); for `erase_fixup` in HPHA's reading too (`eraseFixupHpha_refines_depth`: the depth
  plus one, the hole possibly empty); for the Rust's reading it follows from step 3d, and for the
  descents it is step 4. Each loop's doc repeats this.
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

end Heap

end Oris.RB
