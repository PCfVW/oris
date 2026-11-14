-- SPDX-License-Identifier: MIT OR Apache-2.0
import RBTree

/-!
# `rbtree.rs`'s red-black fix-ups, on zippers

The Rust tree navigates with parent pointers; here the same navigation is a zipper
(`RBTree.RBNode.Path`). A node of the Rust tree together with its chain of parents *is* a pair
`(subtree, path)`: each parent contributes its colour (the colour bit of its tagged parent
pointer), its key, the sibling subtree, and which side we came down (the side bit). This file
writes `insert_fixup` and `erase_fixup`, and the `Node` branches of `insert_counted` and
`erase_counted` around them, as functions on that pair, case for case and rotation for rotation,
and proves them correct against the vendored library's red-black invariants.

What this file establishes is about the *algorithm* `rbtree.rs` runs. That the pointer code
implements this algorithm is the next layer (`Oris/RB/Heap.lean`, to come); this file's
definitions are written so that each case can be checked against the Rust line by line, and each
case's doc names the lines it transcribes.

## Fidelity rules followed below

- `rotate` never touches colours: in Rust a node's colour lives in its own tagged parent pointer,
  and `NodeBase::rotate` rewrites only pointers and side bits (`set_parent_ptr` preserves the
  colour bit).
- Every colour the Rust sets is set here, in the same case: even where it changes nothing (the
  final `make_black(root)` on a root that is already black), and without looking at the colour it
  overwrites (`insFix` matches the grandparent's colour as `_` and paints it red, as the Rust does
  without testing it). So the model agrees with the Rust on *every* input of the shapes it
  matches, not only on valid trees.
- Where the model deliberately does *not* follow the Rust, it is on states the theorems prove
  unreachable (they all assume a valid tree with a black root, `Path.Balanced black`), with one
  exception, the last item. The complete list:
  * `insFix`, a red parent with no grandparent (a red root): the Rust would take the sentinel for
    the grandparent and rotate it; the model stops. HPHA asserts `pp != &mHead`;
    `hpha_grandparent_not_sentinel_left` and `_right` prove it cannot happen.
  * `rotate` without the child that comes up: the Rust precondition fails; the model is the
    identity.
  * `stage2L`/`stage2R`, a `nil` sibling (HPHA asserts `w != &mHead`;
    `hpha_sibling_not_sentinel_left` and `_right` prove it cannot happen): the Rust would read the
    sentinel's links; the model goes on as in the second case.
  * `eraseAt` on `nil`, or with a leftmost node that is `nil`: impossible shapes; the model returns
    the tree with an empty hole and no rotation.
  * **`erase_fixup`'s `root`.** HPHA re-reads the root on every loop test; the Rust (and Zig) read
    it once, on entry. At this level nodes have no identity, so the model follows HPHA (see
    `delFix`). This is the one departure that is not about an unreachable state: whether the two
    readings ever differ is a question for the heap layer. The model's agreement with the running
    Rust code on 20,000 operations (`Lean/README.md`) is evidence that they do not.
-/

open RBTree RBTree.RBNode RBTree.RBColor

namespace Oris.RB

variable {α : Type _}

/-- `rbtree.rs` `Side`. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

/-- `NodeBase::rotate(this, s)` applied at the root of a subtree: `this` goes down on side `s`
and its child on the other side comes up into its place. Colours stay with their nodes. On a
subtree without the needed child (the Rust precondition "`this`'s side-`o` child must be a live,
non-nil node" fails) it is the identity. That case never matters to a theorem: every rotation the
proofs below reason about is applied to a subtree whose shape the proof has already established. -/
def rotate : Side → RBNode α → RBNode α
  | .left, node c a x (node c' b y d) => node c' (node c a x b) y d
  | .right, node c (node c' a x b) y d => node c' a x (node c b y d)
  | _, t => t

/-- A rotation changes no element and no in-order position. -/
@[simp] theorem rotate_toList (s : Side) (t : RBNode α) : (rotate s t).toList = t.toList := by
  unfold rotate; split <;> simp

/-- `NodeBase::red`: whether a node is red. The sentinel (`nil` here) is black. -/
def red? : RBNode α → Bool
  | node red .. => true
  | _ => false

@[simp] theorem red?_nil : red? (nil : RBNode α) = false := rfl
@[simp] theorem red?_red {a : RBNode α} : red? (node red a x b) = true := rfl
@[simp] theorem red?_black {a : RBNode α} : red? (node black a x b) = false := rfl

/-! ## `insert_fixup` -/

/-- `rbtree.rs` `insert_fixup`, on the zipper. The arguments are the path from `cur` to the root
and the subtree at `cur`; the result is the whole tree after the fix-up (root blackened, as the
Rust's final `make_black(root)` does) and the number of rotations performed (the value the Rust
returns, recorded as the `rot=` field of a `tree+` event).

The loop `while red(p)` is the recursion: each case below matches a red parent `p`, a
grandparent `pp` of any colour, and the uncle `u = pp.child(o)`.

* `u` red (Rust: `make_black(p); make_black(pp_right); make_red(pp); cur = pp`): recolour and
  continue from `pp`, two levels up, with no rotation.
* `u` black, `cur` on the same side of `p` as `p` is of `pp` (Rust: the `cur == p_o_child` test
  is false): `make_black(p); make_red(pp); rotate(pp, o)`, one rotation, and the loop ends
  because the new parent of `cur` is black.
* `u` black, `cur` on the other side (Rust: `cur == p_o_child`): first `cur = p; rotate(cur, s)`,
  so the old `cur` takes `p`'s place, then as in the previous case: two rotations.

The last arm is the loop's exit with `p` black (or no parent at all: `cur` is the root), plus the
unreachable red-root shape discussed in the module doc. -/
def insFix : Path α → RBNode α → RBNode α × Nat
  | .root, t => (t.setBlack, 0)
  -- `p` is `pp`'s left child (`s = Left`, `o = Right`), `cur` is `p`'s left child (outer).
  | .left red (.left _ gp z u) y b, t =>
    if red? u then insFix gp (node red (node black t y b) z u.setBlack)
    else ((gp.fill (rotate .right (node red (node black t y b) z u))).setBlack, 1)
  -- `p` is `pp`'s left child, `cur` is `p`'s right child (inner): `rotate(p, Left)` first.
  | .right red a y (.left _ gp z u), t =>
    if red? u then insFix gp (node red (node black a y t) z u.setBlack)
    else
      ((gp.fill (rotate .right (node red (rotate .left (node red a y t)).setBlack z u))).setBlack,
        2)
  -- `p` is `pp`'s right child (`s = Right`, `o = Left`), `cur` is `p`'s right child (outer).
  | .right red a y (.right _ u z gp), t =>
    if red? u then insFix gp (node red u.setBlack z (node black a y t))
    else ((gp.fill (rotate .left (node red u z (node black a y t)))).setBlack, 1)
  -- `p` is `pp`'s right child, `cur` is `p`'s left child (inner): `rotate(p, Right)` first.
  | .left red (.right _ u z gp) y b, t =>
    if red? u then insFix gp (node red u.setBlack z (node black t y b))
    else
      ((gp.fill (rotate .left (node red u z (rotate .right (node red t y b)).setBlack))).setBlack,
        2)
  | path, t => ((path.fill t).setBlack, 0)

/-- **The insert fix-up only rearranges**: the in-order sequence of elements is exactly that of
the tree with `cur` put in its hole. -/
theorem insFix_toList (path : Path α) (t : RBNode α) :
    (insFix path t).1.toList = (path.fill t).toList := by
  fun_induction insFix path t <;> simp_all [Path.fill]

/-- **At most two rotations per insert**, as `insert_fixup`'s doc claims. -/
theorem insFix_rotations (path : Path α) (t : RBNode α) : (insFix path t).2 ≤ 2 := by
  fun_induction insFix path t <;> simp_all

/-- A subtree that is not red and is balanced is balanced as a black subtree. -/
theorem balanced_black_of_not_red {u : RBNode α} {c : RBColor} {n : Nat}
    (hr : red? u = false) (hu : u.Balanced c n) : u.Balanced black n := by
  cases hu with
  | nil => exact .nil
  | red => simp at hr
  | black ha hb => exact .black ha hb

/-- HPHA's `insert_fixup` assertion `assert(pp != &mHead)` (`cur` a left child): under a red
parent there is always a grandparent, because the root is black. This is why `insFix`'s one
departure from the Rust (it stops on a red parent with no grandparent) is unreachable. -/
theorem hpha_grandparent_not_sentinel_left {pp : Path α} {y : α} {b : RBNode α} {c : RBColor}
    {n n₀ : Nat} (hp : (Path.left red pp y b).Balanced black n₀ c n) : pp ≠ .root := by
  rintro rfl
  cases hp with
  | redL _ hpar => cases hpar

/-- `hpha_grandparent_not_sentinel_left`'s mirror image (`cur` a right child). -/
theorem hpha_grandparent_not_sentinel_right {pp : Path α} {y : α} {a : RBNode α} {c : RBColor}
    {n n₀ : Nat} (hp : (Path.right red a y pp).Balanced black n₀ c n) : pp ≠ .root := by
  rintro rfl
  cases hp with
  | redR _ hpar => cases hpar

/-- **The insert fix-up restores the red-black invariant.** Its loop invariant is the
hypothesis: `cur` is a red node with black children of black-height `n` (`t.Balanced red n`),
sitting in a hole that a black-rooted tree of black-height `n₀` has around it. The only possible
violation, a red `cur` under a red parent, is what the fix-up repairs; the result is a valid
red-black tree with a black root.

The proof follows `insFix` case by case, with all nine path shapes written out. It relies on
what the Rust takes on trust, obtaining each fact from the invariant in the case that needs it:
the grandparent of a red parent exists (HPHA's assertion, stated separately as
`hpha_grandparent_not_sentinel_left`/`_right`) and is black, and the uncle, when not red, is a
black subtree of the same black-height. -/
theorem insFix_balanced : ∀ {path : Path α} {t : RBNode α} {c : RBColor} {n n₀ : Nat},
    path.Balanced black n₀ c n → t.Balanced red n → ∃ m, (insFix path t).1.Balanced black m
  | .root, _, _, _, _, _, ht => by
    simp only [insFix]; exact ht.setBlack
  -- `p` black: the loop exits; a red `cur` is allowed under a black parent.
  | .left black _ _ _, _, _, _, _, hp, ht => by
    simp only [insFix]
    cases hp with
    | blackL hb hpar => exact Balanced.setBlack ((Path.Balanced.blackL hb hpar).fill ht)
  | .right black _ _ _, _, _, _, _, hp, ht => by
    simp only [insFix]
    cases hp with
    | blackR ha hpar => exact Balanced.setBlack ((Path.Balanced.blackR ha hpar).fill ht)
  -- `p` red and the root: impossible, the root is black.
  | .left red .root _ _, _, _, _, _, hp, _ => by
    cases hp with
    | redL _ hpar => cases hpar
  | .right red _ _ .root, _, _, _, _, hp, _ => by
    cases hp with
    | redR _ hpar => cases hpar
  -- `p` red, left child of `pp`; `cur` left child of `p` (outer).
  | .left red (.left _ gp z u) y b, t, _, n, _, hp, ht => by
    cases hp with
    | redL hb hpar =>
    cases hpar with
    | blackL hu hgp =>
    simp only [insFix]
    split
    · rename_i hr
      cases hu with
      | nil => simp at hr
      | black => simp at hr
      | red hul hur => exact insFix_balanced hgp (.red (.black ht hb) (.black hul hur))
    · rename_i hr
      have hu' := balanced_black_of_not_red (by simpa using hr) hu
      exact Balanced.setBlack (hgp.fill (by simp only [rotate]; exact .black ht (.red hb hu')))
  -- `p` red, left child of `pp`; `cur` right child of `p` (inner).
  | .right red a y (.left _ gp z u), t, _, n, _, hp, ht => by
    cases hp with
    | redR ha hpar =>
    cases hpar with
    | blackL hu hgp =>
    simp only [insFix]
    split
    · rename_i hr
      cases hu with
      | nil => simp at hr
      | black => simp at hr
      | red hul hur => exact insFix_balanced hgp (.red (.black ha ht) (.black hul hur))
    · rename_i hr
      have hu' := balanced_black_of_not_red (by simpa using hr) hu
      cases ht with
      | red h1 h2 =>
      exact Balanced.setBlack (hgp.fill (by
        simp only [rotate, setBlack]; exact .black (.red ha h1) (.red h2 hu')))
  -- `p` red, right child of `pp`; `cur` right child of `p` (outer).
  | .right red a y (.right _ u z gp), t, _, n, _, hp, ht => by
    cases hp with
    | redR ha hpar =>
    cases hpar with
    | blackR hu hgp =>
    simp only [insFix]
    split
    · rename_i hr
      cases hu with
      | nil => simp at hr
      | black => simp at hr
      | red hul hur => exact insFix_balanced hgp (.red (.black hul hur) (.black ha ht))
    · rename_i hr
      have hu' := balanced_black_of_not_red (by simpa using hr) hu
      exact Balanced.setBlack (hgp.fill (by simp only [rotate]; exact .black (.red hu' ha) ht))
  -- `p` red, right child of `pp`; `cur` left child of `p` (inner).
  | .left red (.right _ u z gp) y b, t, _, n, _, hp, ht => by
    cases hp with
    | redL hb hpar =>
    cases hpar with
    | blackR hu hgp =>
    simp only [insFix]
    split
    · rename_i hr
      cases hu with
      | nil => simp at hr
      | black => simp at hr
      | red hul hur => exact insFix_balanced hgp (.red (.black hul hur) (.black ht hb))
    · rename_i hr
      have hu' := balanced_black_of_not_red (by simpa using hr) hu
      cases ht with
      | red h1 h2 =>
      exact Balanced.setBlack (hgp.fill (by
        simp only [rotate, setBlack]; exact .black (.red hu' h1) (.red h2 hb)))

/-! ## `insert_counted`: descent, attach, fix-up -/

/-- `rbtree.rs` `InsertKind`. -/
inductive InsertKind where
  | chain
  | node
  deriving DecidableEq, Repr

/-- `IntrusiveMultiRbTree::insert_counted`, on the tree of keys. The descent loop
(`while cur != end`, going left on `Less` and right on `Greater`) is the library's `zoom` with the
cut `cmp v`, which builds the path to the hole as it goes; `Equal` stops the descent on the node
whose equal-key chain the new element joins (`link_into_chain`, tree untouched: `Chain`, no
rotation). Otherwise the descent ends at an empty subtree, where `attach_to` hangs the new node as
a red leaf, and `insert_fixup` rebalances (`Node`). Chain membership itself is not visible at this
level (the tree of keys does not change); it belongs to the heap layer. -/
def insert (cmp : α → α → Ordering) (t : RBNode α) (v : α) : RBNode α × InsertKind × Nat :=
  match zoom (cmp v) t with
  | (nil, path) => let r := insFix path (node red nil v nil); (r.1, .node, r.2)
  | (node .., _) => (t, .chain, 0)

/-- **Oris's insert is correct.** On a valid red-black tree with a black root (Oris's tree always
has one), `insert_counted` either finds an equal key and leaves the tree as it is (`Chain`, no
rotation), or returns a valid red-black tree with a black root, ordered, holding **exactly the
same elements in the same order as the library's verified `RBNode.insert`** (whose tree has a
different shape: it balances the Okasaki way), after at most two rotations. -/
theorem insert_spec [Std.TransCmp cmp] {t : RBNode α} {n : Nat}
    (ho : t.Ordered cmp) (hb : t.Balanced black n) (v : α) :
    match insert cmp t v with
    | (t', .chain, rot) => t' = t ∧ rot = 0
    | (t', .node, rot) =>
      t'.toList = (t.insert cmp v).toList ∧ t'.Ordered cmp ∧
      (∃ m, t'.Balanced black m) ∧ rot ≤ 2 := by
  unfold insert
  rcases hz : zoom (cmp v) t with ⟨_ | ⟨_, _, _, _⟩, path⟩
  · simp only
    have htl : (insFix path (node red nil v nil)).1.toList = (t.insert cmp v).toList := by
      rw [insFix_toList, Path.fill_toList, ← setBlack_toList (t := t.insert cmp v),
        ← Path.insertNew_eq_insert hz, Path.insertNew_toList]
      simp
    refine ⟨htl, ?_, ?_, insFix_rotations _ _⟩
    · rw [ordered_iff, htl, ← ordered_iff]
      exact ho.insert
    · obtain ⟨c', n', hnil, hpath⟩ := hb.zoom (path := .root) .root hz
      cases hnil
      exact insFix_balanced hpath (.red .nil .nil)
  · exact ⟨rfl, rfl⟩

/-! ## `erase_fixup` -/

/-- `NodeBase::set_colour` applied to the root of a subtree (the sentinel, `nil`, is left alone). -/
def paint (c : RBColor) : RBNode α → RBNode α
  | node _ a x b => node c a x b
  | nil => nil

/-- Applies `f` to a node's child on side `s` (the Rust's `make_black(w.child(o))` and the like). -/
def mapChild (s : Side) (f : RBNode α → RBNode α) : RBNode α → RBNode α
  | node c a x b => match s with
    | .left => node c (f a) x b
    | .right => node c a x (f b)
  | nil => nil

/-- `NodeBase::child`: the child of a node on side `s` (`nil` for `nil`). -/
def child (s : Side) : RBNode α → RBNode α
  | node _ a _ b => match s with
    | .left => a
    | .right => b
  | nil => nil

/-- The part of one `erase_fixup` iteration that follows its first case (`w` red), for `cur` the
**left** child of `p` (`s = Left`, `o = Right`), `p` of colour `pc` and key `y`, `w` the sibling,
`pp` the path above `p`. Returns `none` for the second case (`w`'s children both black: the Rust
makes `w` red and continues from `p`; the caller performs that step), or the finished tree and
the rotations of the third and fourth cases:

* third case, `w.child(o)` black: `make_black(w.child(s)); make_red(w); rotate(w, o); w = c`;
* fourth case: `set_colour(w, colour(p)); make_black(p); make_black(w.child(o)); rotate(p, s);
  cur = root`, which ends the loop; the final `make_black(cur)` is `setBlack` of the whole tree
  (see `delFix` on why this is HPHA's "fresh root" reading).

A `nil` sibling is unreachable (HPHA asserts `w != &mHead`; `hpha_sibling_not_sentinel_left`
proves it); the model returns `none` there. -/
def stage2L (pc : RBColor) (pp : Path α) (y : α) (w x : RBNode α) : Option (RBNode α × Nat) :=
  match w with
  | nil => none
  | node cw wl wv wr =>
    if !red? wl && !red? wr then none
    else
      let w3 : RBNode α × Nat :=
        if !red? wr then (rotate .right (node red wl.setBlack wv wr), 1)
        else (node cw wl wv wr, 0)
      let sub := rotate .left (node black x y (mapChild .right setBlack (paint pc w3.1)))
      some ((pp.fill sub).setBlack, w3.2 + 1)

/-- `stage2L`'s mirror image: `cur` is the **right** child of `p` (`s = Right`, `o = Left`). -/
def stage2R (pc : RBColor) (pp : Path α) (y : α) (w x : RBNode α) : Option (RBNode α × Nat) :=
  match w with
  | nil => none
  | node cw wl wv wr =>
    if !red? wl && !red? wr then none
    else
      let w3 : RBNode α × Nat :=
        if !red? wl then (rotate .left (node red wl wv wr.setBlack), 1)
        else (node cw wl wv wr, 0)
      let sub := rotate .right (node black (mapChild .left setBlack (paint pc w3.1)) y x)
      some ((pp.fill sub).setBlack, w3.2 + 1)

/-- `rbtree.rs` `erase_fixup`, on the zipper: `cur` (the subtree `x`, possibly empty: the Rust's
sentinel) sits one black level short at the end of `path`. Returns the whole tree after the
fix-up and the number of rotations (the `rot=` field of a `tree-` event).

The loop `while !red(cur) && cur != root` is the recursion: a red `cur` or an empty path ends it
with `make_black(cur)`. Otherwise, for `cur` a left child (the right-child arms mirror it), the
first case `w` red is `make_black(w); make_red(p); w = w.child(s); rotate(p, s)`: after it `cur`
hangs two levels deeper, below a now-red `p`, with the old `w.child(s)` as its sibling, which is
the path written out in that arm (`delFix_case1_fill_left`/`_right` check it is exactly that
rotation). Then
`stage2L` decides between the second case (continue from `p`, here: recurse on `p`'s path with
`p`'s subtree, `w` made red) and the finishing third and fourth cases.

**On `root`.** HPHA re-reads the root on every test (`mHead.child(LEFT)`) and finishes with
`cur = mHead.child(LEFT)`; both Rust and Zig read it once, on entry. At this level nodes have no
identity, so the model follows HPHA: the loop's "is root" test is "the path is empty", and the
finishing `make_black` blackens the whole tree's root. Whether the Rust's stale root changes
anything is a question about node identity, settled in the heap layer (a differential test of
one million operations found no difference; the expectation, to be proven there, is that the
root changes only in iterations that then stop before the stale value is used, and that its
final `make_black` is then a no-op). -/
def delFix (path : Path α) (x : RBNode α) : RBNode α × Nat :=
  if red? x then (path.fill x.setBlack, 0)
  else match path with
  | .root => (x.setBlack, 0)
  | .left _ pp y (node red wl wv wr) =>
    match stage2L red (.left black pp wv wr) y wl x with
    | some r => (r.1, r.2 + 1)
    | none =>
      let q := delFix (.left black pp wv wr) (node red x y wl.setRed)
      (q.1, q.2 + 1)
  | .left pc pp y w =>
    match stage2L pc pp y w x with
    | some r => r
    | none => delFix pp (node pc x y w.setRed)
  | .right _ (node red wl wv wr) y pp =>
    match stage2R red (.right black wl wv pp) y wr x with
    | some r => (r.1, r.2 + 1)
    | none =>
      let q := delFix (.right black wl wv pp) (node red wr.setRed y x)
      (q.1, q.2 + 1)
  | .right pc w y pp =>
    match stage2R pc pp y w x with
    | some r => r
    | none => delFix pp (node pc w.setRed y x)
termination_by path
decreasing_by all_goals simp_wf; omega

/-- **Fidelity check for `delFix`'s first case** (`cur` a left child): the path the model writes
out is exactly where `cur` ends up after the Rust's `make_black(w); make_red(p); rotate(p, s)`,
with `w.child(s)` as its new sibling. -/
theorem delFix_case1_fill_left (pp : Path α) (y wv : α) (x wl wr : RBNode α) :
    (Path.left red (.left black pp wv wr) y wl).fill x =
      pp.fill (rotate .left (node red x y (setBlack (node red wl wv wr)))) := rfl

/-- The mirror image of `delFix_case1_fill_left` (`cur` a right child). -/
theorem delFix_case1_fill_right (pp : Path α) (y wv : α) (x wl wr : RBNode α) :
    (Path.right red wr y (.right black wl wv pp)).fill x =
      pp.fill (rotate .right (node red (setBlack (node red wl wv wr)) y x)) := rfl

@[simp] theorem paint_toList (c : RBColor) (t : RBNode α) : (paint c t).toList = t.toList := by
  cases t <;> rfl

@[simp] theorem mapChild_setBlack_toList (s : Side) (t : RBNode α) :
    (mapChild s setBlack t).toList = t.toList := by
  cases t <;> cases s <;> simp [mapChild]

/-- A red `cur` ends the erase loop at once: `make_black(cur)`, no rotation. -/
theorem delFix_red {path : Path α} {x : RBNode α} (h : red? x = true) :
    delFix path x = (path.fill x.setBlack, 0) := by
  rw [delFix.eq_def]; simp [h]

theorem stage2L_toList {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α} {r : RBNode α × Nat}
    (h : stage2L pc pp y w x = some r) : r.1.toList = (pp.fill (node pc x y w)).toList := by
  unfold stage2L at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases h; split <;> simp

theorem stage2R_toList {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α} {r : RBNode α × Nat}
    (h : stage2R pc pp y w x = some r) : r.1.toList = (pp.fill (node pc w y x)).toList := by
  unfold stage2R at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases h; split <;> simp

theorem stage2L_rotations {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α}
    {r : RBNode α × Nat} (h : stage2L pc pp y w x = some r) : r.2 ≤ 2 := by
  unfold stage2L at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases h; split <;> simp

theorem stage2R_rotations {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α}
    {r : RBNode α × Nat} (h : stage2R pc pp y w x = some r) : r.2 ≤ 2 := by
  unfold stage2R at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · cases h; split <;> simp

/-- **The erase fix-up only rearranges**: the in-order sequence of elements is exactly that of
the tree with `cur` in its hole. -/
theorem delFix_toList (path : Path α) (x : RBNode α) :
    (delFix path x).1.toList = (path.fill x).toList := by
  fun_induction delFix path x with
  | case1 => simp
  | case2 => simp
  | case3 _ _ _ _ _ _ _ _ _ h => rw [stage2L_toList h]; simp [Path.fill]
  | case4 => simp_all (config := { zetaDelta := true }) [Path.fill]
  | case5 _ _ _ _ _ _ _ _ h => rw [stage2L_toList h]; rfl
  | case6 => simp_all [Path.fill]
  | case7 _ _ _ _ _ _ _ _ _ h => rw [stage2R_toList h]; simp [Path.fill]
  | case8 => simp_all (config := { zetaDelta := true }) [Path.fill]
  | case9 _ _ _ _ _ _ _ _ h => rw [stage2R_toList h]; rfl
  | case10 => simp_all [Path.fill]

/-- **At most three rotations per erase**, as `erase_fixup`'s doc claims: one for the first
case, then at most two for the third and fourth; after the first case a second-case step lands on
a red `p` and stops without rotating. -/
theorem delFix_rotations (path : Path α) (x : RBNode α) : (delFix path x).2 ≤ 3 := by
  fun_induction delFix path x with
  | case1 => simp
  | case2 => simp
  | case3 _ _ _ _ _ _ _ _ _ h => have := stage2L_rotations h; simp; omega
  | case4 =>
    show (delFix (Path.left black _ _ _) (node red _ _ _)).2 + 1 ≤ 3
    rw [delFix_red] <;> simp
  | case5 _ _ _ _ _ _ _ _ h => exact Nat.le_trans (stage2L_rotations h) (by decide)
  | case6 => simp_all
  | case7 _ _ _ _ _ _ _ _ _ h => have := stage2R_rotations h; simp; omega
  | case8 =>
    show (delFix (Path.right black _ _ _) (node red _ _ _)).2 + 1 ≤ 3
    rw [delFix_red] <;> simp
  | case9 _ _ _ _ _ _ _ _ h => exact Nat.le_trans (stage2R_rotations h) (by decide)
  | case10 => simp_all

/-! ### `erase_fixup` restores the red-black invariant -/

/-- The black-height of `p`'s position when `cur`, one of `p`'s children, has black-height `n`
and its sibling `n + 1`: the hole above `p` of colour `pc` needs this height. -/
def bh : RBColor → Nat → Nat
  | red, n => n + 1
  | black, n => n + 2

/-- In a tree with a black root, every hole accepts a black subtree of its black-height (a hole
that "requires red" sits under a black parent, which accepts either colour). -/
theorem hole_toBlack {path : Path α} {c : RBColor} {m n₀ : Nat}
    (hp : path.Balanced black n₀ c m) : path.Balanced black n₀ black m := by
  cases hp with
  | root => exact .root
  | redL hy hpar => exact .redL hy hpar
  | redR hx hpar => exact .redR hx hpar
  | blackL hy hpar => exact .blackL hy hpar
  | blackR hx hpar => exact .blackR hx hpar

theorem stage2L_none {pc cw : RBColor} {pp : Path α} {y wv : α} {wl wr x : RBNode α}
    (h : stage2L pc pp y (node cw wl wv wr) x = none) : red? wl = false ∧ red? wr = false := by
  dsimp only [stage2L] at h
  split at h
  · simp_all
  · simp at h

theorem stage2R_none {pc cw : RBColor} {pp : Path α} {y wv : α} {wl wr x : RBNode α}
    (h : stage2R pc pp y (node cw wl wv wr) x = none) : red? wl = false ∧ red? wr = false := by
  dsimp only [stage2R] at h
  split at h
  · simp_all
  · simp at h

/-- The third and fourth cases (`cur` a left child) finish with a valid tree. Hypotheses: `cur`
is black of height `n`, its sibling `w` black of height `n + 1` (never red here: `delFix`'s first
case has already handled a red sibling), and `p`'s position is a hole of colour `pc` and the
matching height. -/
theorem stage2L_balanced {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α}
    {r : RBNode α × Nat} {n n₀ : Nat}
    (hx : x.Balanced black n) (hw : w.Balanced black (n + 1))
    (hpp : pp.Balanced black n₀ pc (bh pc n)) (h : stage2L pc pp y w x = some r) :
    ∃ m, r.1.Balanced black m := by
  have fin : ∀ {a b : RBNode α} {v : α}, a.Balanced black (n + 1) → b.Balanced black (n + 1) →
      ∃ m, ((pp.fill (node pc a v b)).setBlack).Balanced black m := by
    intro a b v ha hb
    refine Balanced.setBlack (hpp.fill ?_)
    cases pc
    · exact .red ha hb
    · exact .black ha hb
  cases hw with
  | black hwl hwr =>
  dsimp only [stage2L] at h
  split at h
  · simp at h
  · cases h
    split
    · rename_i hwr_nr
      cases hwl with
      | nil => simp_all
      | black => simp_all
      | red ha hc =>
        have hwr' := balanced_black_of_not_red (by simpa using hwr_nr) hwr
        simp only [rotate, setBlack, paint, mapChild]
        exact fin (.black hx ha) (.black hc hwr')
    · rename_i hwr_r
      cases hwr with
      | nil => simp at hwr_r
      | black => simp at hwr_r
      | red ha hc =>
        simp only [rotate, setBlack, paint, mapChild]
        exact fin (.black hx hwl) (.black ha hc)

/-- `stage2L_balanced`'s mirror image (`cur` a right child). -/
theorem stage2R_balanced {pc : RBColor} {pp : Path α} {y : α} {w x : RBNode α}
    {r : RBNode α × Nat} {n n₀ : Nat}
    (hx : x.Balanced black n) (hw : w.Balanced black (n + 1))
    (hpp : pp.Balanced black n₀ pc (bh pc n)) (h : stage2R pc pp y w x = some r) :
    ∃ m, r.1.Balanced black m := by
  have fin : ∀ {a b : RBNode α} {v : α}, a.Balanced black (n + 1) → b.Balanced black (n + 1) →
      ∃ m, ((pp.fill (node pc a v b)).setBlack).Balanced black m := by
    intro a b v ha hb
    refine Balanced.setBlack (hpp.fill ?_)
    cases pc
    · exact .red ha hb
    · exact .black ha hb
  cases hw with
  | black hwl hwr =>
  dsimp only [stage2R] at h
  split at h
  · simp at h
  · cases h
    split
    · rename_i hwl_nr
      cases hwr with
      | nil => simp_all
      | black => simp_all
      | red ha hc =>
        have hwl' := balanced_black_of_not_red (by simpa using hwl_nr) hwl
        simp only [rotate, setBlack, paint, mapChild]
        exact fin (.black hwl' ha) (.black hc hx)
    · rename_i hwl_r
      cases hwl with
      | nil => simp at hwl_r
      | black => simp at hwl_r
      | red ha hc =>
        simp only [rotate, setBlack, paint, mapChild]
        exact fin (.black ha hc) (.black hwr hx)

/-! ### HPHA's `erase_fixup` assertions, as theorems

`Cpp/hpha.cpp`'s `erase_fixup` asserts three facts that the Rust neither checks nor states. Each is
a theorem here, under the invariant `delFix` runs with (`cur`'s hole has black-height `n + 1`,
`cur` itself one less). -/

/-- `assert(w != &mHead)` (`cur` a left child): the sibling is never the sentinel, because the
sibling's black-height is `n + 1 ≥ 1` and the sentinel's is 0. -/
theorem hpha_sibling_not_sentinel_left {pc c : RBColor} {pp : Path α} {y : α} {w : RBNode α}
    {n n₀ : Nat} (hp : (Path.left pc pp y w).Balanced black n₀ c (n + 1)) : w ≠ nil := by
  rintro rfl
  cases hp with
  | redL hw => cases hw
  | blackL hw => cases hw

/-- `hpha_sibling_not_sentinel_left`'s mirror image (`cur` a right child). -/
theorem hpha_sibling_not_sentinel_right {pc c : RBColor} {pp : Path α} {y : α} {w : RBNode α}
    {n n₀ : Nat} (hp : (Path.right pc w y pp).Balanced black n₀ c (n + 1)) : w ≠ nil := by
  rintro rfl
  cases hp with
  | redR hw => cases hw
  | blackR hw => cases hw

/-- `assert(w->child(LEFT)->black() && w->child(RIGHT)->black())` in the first case (`cur` a left
child): a red sibling has black children. -/
theorem hpha_red_sibling_children_black_left {pc c : RBColor} {pp : Path α} {y wv : α}
    {wl wr : RBNode α} {m n₀ : Nat}
    (hp : (Path.left pc pp y (node red wl wv wr)).Balanced black n₀ c m) :
    red? wl = false ∧ red? wr = false := by
  cases hp with
  | redL hw => cases hw
  | blackL hw =>
    cases hw with
    | red hl hr => exact ⟨by cases hl <;> rfl, by cases hr <;> rfl⟩

/-- `hpha_red_sibling_children_black_left`'s mirror image (`cur` a right child). -/
theorem hpha_red_sibling_children_black_right {pc c : RBColor} {pp : Path α} {y wv : α}
    {wl wr : RBNode α} {m n₀ : Nat}
    (hp : (Path.right pc (node red wl wv wr) y pp).Balanced black n₀ c m) :
    red? wl = false ∧ red? wr = false := by
  cases hp with
  | redR hw => cases hw
  | blackR hw =>
    cases hw with
    | red hl hr => exact ⟨by cases hl <;> rfl, by cases hr <;> rfl⟩

/-- `assert(w->child(o)->red())` before the fourth case (`cur` a left child, `o = Right`): once the
second case is ruled out (not both of `w`'s children black), the sibling after the optional third
case (exactly as `stage2L` computes it) has a red child on side `o`. -/
theorem hpha_far_child_red_left {cw : RBColor} {wl wr : RBNode α} {wv : α}
    (h : (!red? wl && !red? wr) = false) :
    red? (child .right
      (if !red? wr then rotate .right (node red wl.setBlack wv wr) else node cw wl wv wr)) =
      true := by
  cases hr : red? wr
  · have hl : red? wl = true := by simpa [hr] using h
    cases wl with
    | nil => simp at hl
    | node cl a b d =>
      cases cl with
      | black => simp at hl
      | red => simp [rotate, setBlack, child]
  · simpa [child] using hr

/-- `hpha_far_child_red_left`'s mirror image (`cur` a right child, `o = Left`, as `stage2R`
computes it). -/
theorem hpha_far_child_red_right {cw : RBColor} {wl wr : RBNode α} {wv : α}
    (h : (!red? wl && !red? wr) = false) :
    red? (child .left
      (if !red? wl then rotate .left (node red wl wv wr.setBlack) else node cw wl wv wr)) =
      true := by
  cases hl : red? wl
  · have hr : red? wr = true := by simpa [hl] using h
    cases wr with
    | nil => simp at hr
    | node cr a b d =>
      cases cr with
      | black => simp at hr
      | red => simp [rotate, setBlack, child]
  · simpa [child] using hl

/-- **The erase fix-up restores the red-black invariant.** Its loop invariant is the hypothesis:
`cur` sits in a hole of black-height `n + 1` but has black-height only `n` (the "double black"
left by splicing out a black node), and is a valid subtree except that, when it is red, it may
have one red child (the state the second case leaves after the first: `p` red with `w` made
red). The result is a valid red-black tree with a black root.

The proof follows `delFix` case by case. HPHA's three assertions, which it relies on
implicitly, are stated and proven separately above (`hpha_sibling_not_sentinel_left` and its
neighbours). -/
theorem delFix_balanced_aux : ∀ (k : Nat) {path : Path α} {x : RBNode α} {c : RBColor}
    {n n₀ : Nat}, sizeOf path < k → path.Balanced black n₀ c (n + 1) → x.RedRed True n →
    ∃ m, (delFix path x).1.Balanced black m
  | 0, _, _, _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | k + 1, path, x, c, n, n₀, hk, hp, hx => by
    by_cases hr : red? x = true
    · rw [delFix_red hr]
      cases x with
      | nil => simp at hr
      | node cx a v b =>
        cases cx with
        | black => simp at hr
        | red =>
          obtain ⟨_, _, ha, hb⟩ := hx.of_red
          exact ⟨n₀, (hole_toBlack hp).fill (.black ha hb)⟩
    have hxb : x.Balanced black n := by
      cases hx with
      | balanced h => exact balanced_black_of_not_red (by simpa using hr) h
      | redred => simp at hr
    cases path with
    | root =>
      rw [delFix.eq_def]; simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact hxb.setBlack
    | left pc pp y w =>
      cases w with
      | nil => cases hp with
        | redL hw => cases hw
        | blackL hw => cases hw
      | node cw wl wv wr =>
        cases cw with
        | red =>
          -- First case: `w` red (so `p` black).
          cases hp with
          | redL hw => cases hw
          | blackL hw hpp =>
          cases hw with
          | red hwl hwr =>
          have hpp' : (Path.left black pp wv wr).Balanced black n₀ red (bh red n) :=
            .blackL hwr hpp
          rw [delFix.eq_def]; simp only [hr, Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i r hs
            obtain ⟨m, hm⟩ := stage2L_balanced hxb hwl hpp' hs
            exact ⟨m, hm⟩
          · rename_i hs
            show ∃ m,
              (delFix (Path.left black pp wv wr) (node red x y wl.setRed)).1.Balanced black m
            rw [delFix_red (by rfl)]
            cases hwl with
            | black hl1 hl2 =>
            obtain ⟨h1, h2⟩ := stage2L_none hs
            exact ⟨n₀, (hole_toBlack hpp').fill (.black hxb (.red (balanced_black_of_not_red h1 hl1)
              (balanced_black_of_not_red h2 hl2)))⟩
        | black =>
          -- `w` black: straight to the second, third and fourth cases.
          have key : (node black wl wv wr).Balanced black (n + 1) →
              pp.Balanced black n₀ pc (bh pc n) →
              (red? wl = false → red? wr = false → wl.Balanced black n → wr.Balanced black n →
                ∃ m, (delFix pp (node pc x y (node red wl wv wr))).1.Balanced black m) →
              ∃ m, (delFix (Path.left pc pp y (node black wl wv wr)) x).1.Balanced black m := by
            intro hw hpp hup
            rw [delFix.eq_def]; simp only [hr, Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i r hs
              exact stage2L_balanced hxb hw hpp hs
            · rename_i hs
              obtain ⟨h1, h2⟩ := stage2L_none hs
              cases hw with
              | black hwl hwr =>
              exact hup h1 h2 (balanced_black_of_not_red h1 hwl) (balanced_black_of_not_red h2 hwr)
          cases hp with
          | redL hw hpp =>
            exact key hw hpp fun _ _ hl hr' =>
              delFix_balanced_aux k (by simp at hk; omega) hpp (.redred trivial hxb (.red hl hr'))
          | blackL hw hpp =>
            cases hw with
            | black hwl hwr =>
            exact key (.black hwl hwr) hpp fun _ _ hl hr' =>
              delFix_balanced_aux k (by simp at hk; omega) hpp
                (.balanced (.black hxb (.red hl hr')))
    | right pc w y pp =>
      cases w with
      | nil => cases hp with
        | redR hw => cases hw
        | blackR hw => cases hw
      | node cw wl wv wr =>
        cases cw with
        | red =>
          cases hp with
          | redR hw => cases hw
          | blackR hw hpp =>
          cases hw with
          | red hwl hwr =>
          have hpp' : (Path.right black wl wv pp).Balanced black n₀ red (bh red n) :=
            .blackR hwl hpp
          rw [delFix.eq_def]; simp only [hr, Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i r hs
            obtain ⟨m, hm⟩ := stage2R_balanced hxb hwr hpp' hs
            exact ⟨m, hm⟩
          · rename_i hs
            show ∃ m,
              (delFix (Path.right black wl wv pp) (node red wr.setRed y x)).1.Balanced black m
            rw [delFix_red (by rfl)]
            cases hwr with
            | black hl1 hl2 =>
            obtain ⟨h1, h2⟩ := stage2R_none hs
            exact ⟨n₀, (hole_toBlack hpp').fill (.black (.red (balanced_black_of_not_red h1 hl1)
              (balanced_black_of_not_red h2 hl2)) hxb)⟩
        | black =>
          have key : (node black wl wv wr).Balanced black (n + 1) →
              pp.Balanced black n₀ pc (bh pc n) →
              (red? wl = false → red? wr = false → wl.Balanced black n → wr.Balanced black n →
                ∃ m, (delFix pp (node pc (node red wl wv wr) y x)).1.Balanced black m) →
              ∃ m, (delFix (Path.right pc (node black wl wv wr) y pp) x).1.Balanced black m := by
            intro hw hpp hup
            rw [delFix.eq_def]; simp only [hr, Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i r hs
              exact stage2R_balanced hxb hw hpp hs
            · rename_i hs
              obtain ⟨h1, h2⟩ := stage2R_none hs
              cases hw with
              | black hwl hwr =>
              exact hup h1 h2 (balanced_black_of_not_red h1 hwl) (balanced_black_of_not_red h2 hwr)
          cases hp with
          | redR hw hpp =>
            exact key hw hpp fun _ _ hl hr' =>
              delFix_balanced_aux k (by simp at hk; omega) hpp (.redred trivial (.red hl hr') hxb)
          | blackR hw hpp =>
            cases hw with
            | black hwl hwr =>
            exact key (.black hwl hwr) hpp fun _ _ hl hr' =>
              delFix_balanced_aux k (by simp at hk; omega) hpp
                (.balanced (.black (.red hl hr') hxb))
/-- **The erase fix-up restores the red-black invariant** (see `delFix_balanced_aux`, which
carries the size bound its recursion needs). -/
theorem delFix_balanced {path : Path α} {x : RBNode α} {c : RBColor} {n n₀ : Nat}
    (hp : path.Balanced black n₀ c (n + 1)) (hx : x.RedRed True n) :
    ∃ m, (delFix path x).1.Balanced black m :=
  delFix_balanced_aux _ (Nat.lt_succ_self _) hp hx

/-! ## `erase_counted`: splice, switch, fix-up -/

/-- `rbtree.rs` `EraseKind`. -/
inductive EraseKind where
  | link
  | promote
  | node
  deriving DecidableEq, Repr

/-- The descent to the in-order successor in `erase_counted` (`repl = right; while
repl.child(Left) != end { repl = repl.child(Left) }`), recording the path as it goes: returns the
leftmost node of `t` and the path to it, extending `p`. -/
def leftmost : RBNode α → Path α → RBNode α × Path α
  | node c (node cl ll lv lr) v r, p => leftmost (node cl ll lv lr) (.left c p v r)
  | t, p => (t, p)

theorem leftmost_fill (t : RBNode α) (p : Path α) :
    (leftmost t p).2.fill (leftmost t p).1 = p.fill t := by
  fun_induction leftmost t p <;> simp_all [Path.fill]

theorem leftmost_fst (t : RBNode α) (p q : Path α) : (leftmost t p).1 = (leftmost t q).1 := by
  fun_induction leftmost t p generalizing q with
  | case1 c cl ll lv lr v r p ih => rw [ih (.left c q v r)]; simp [leftmost]
  | case2 t p h =>
    cases t with
    | nil => simp [leftmost]
    | node c l v r =>
      cases l with
      | nil => simp [leftmost]
      | node => exact absurd rfl (h _ _ _ _ _ _ _)

/-- Going down-left never adds to the elements before the hole. -/
theorem leftmost_listL (t : RBNode α) (p : Path α) : (leftmost t p).2.listL = p.listL := by
  fun_induction leftmost t p <;> simp_all

theorem leftmost_node {c : RBColor} {l r : RBNode α} {v : α} (p : Path α) :
    ∃ cm m mr, (leftmost (node c l v r) p).1 = node cm nil m mr := by
  induction l generalizing c v r p with
  | nil => exact ⟨c, v, r, by simp [leftmost]⟩
  | node cl ll lv lr ih _ =>
    obtain ⟨cm, m, mr, h⟩ := ih (c := cl) (v := lv) (r := lr) (.left c p v r)
    exact ⟨cm, m, mr, by simp only [leftmost]; exact h⟩

theorem leftmost_balanced {t : RBNode α} {p : Path α} {c c₀ : RBColor} {n n₀ : Nat}
    (ht : t.Balanced c n) (hp : p.Balanced c₀ n₀ c n) :
    ∃ c' n', (leftmost t p).1.Balanced c' n' ∧ (leftmost t p).2.Balanced c₀ n₀ c' n' := by
  induction ht generalizing p with
  | nil => exact ⟨_, _, .nil, hp⟩
  | @red x n y v ha hb iha _ =>
    cases ha with
    | nil => exact ⟨_, _, .red .nil hb, hp⟩
    | black h1 h2 => simp only [leftmost]; exact iha (.redL hb hp)
  | @black x c₁ n y c₂ v ha hb iha _ =>
    cases ha with
    | nil => exact ⟨_, _, .black .nil hb, hp⟩
    | red h1 h2 => simp only [leftmost]; exact iha (.blackL hb hp)
    | black h1 h2 => simp only [leftmost]; exact iha (.blackL hb hp)

/-- `rbtree.rs` `erase_counted`'s `Node` branch (the erased element has no equal-key duplicates),
on the zipper: `t` is the erased node's subtree, `path` the path to it.

* No right child (`right == end`): `repl` is the node itself, `s = Left`, and its left subtree
  takes its place.
* A right child but no left child: `repl` is the node itself, `s = Right`.
* Both children: `repl` is the leftmost node of the right subtree (key `m`); it is spliced out
  (`substitute_with(repl, repl.child(Right))`) and then takes the erased node's position, children
  and colour (`switch_with(repl, node)`): the path to `repl`'s old position is therefore built
  under a node of the erased node's colour `c` carrying `m`.

Then, if `repl` was black, `erase_fixup` runs from `repl`'s old child (`repl_child`, possibly the
sentinel); if it was red, nothing more happens (no rotation, no final `make_black`). -/
def eraseAt (path : Path α) : RBNode α → RBNode α × Nat
  | nil => (path.fill nil, 0)
  | node c l _ nil => match c with
    | red => (path.fill l, 0)
    | black => delFix path l
  | node c nil _ (node cr rl rv rr) => match c with
    | red => (path.fill (node cr rl rv rr), 0)
    | black => delFix path (node cr rl rv rr)
  | node c (node cl ll lv lr) _ (node cr rl rv rr) =>
    match (leftmost (node cr rl rv rr) .root).1 with
    | node cm _ m mr =>
      let p' := (leftmost (node cr rl rv rr) (.right c (node cl ll lv lr) m path)).2
      match cm with
      | red => (p'.fill mr, 0)
      | black => delFix p' mr
    | nil => (path.fill nil, 0)

/-- **Oris's erase is correct.** On a valid red-black tree with a black root, erasing the element
the descent finds (`zoom` returns its subtree `node c l x r` and the path to it) removes exactly
that element, keeps every other element in order, and leaves a valid red-black tree with a black
root, after at most three rotations. -/
theorem eraseAt_spec [Std.TransCmp cmp] {t : RBNode α} {n : Nat} {c : RBColor} {l r : RBNode α}
    {x : α} {path : Path α}
    (ho : t.Ordered cmp) (hb : t.Balanced black n) (hz : zoom cut t = (node c l x r, path)) :
    t.toList = path.withList (l.toList ++ x :: r.toList) ∧
    (eraseAt path (node c l x r)).1.toList = path.withList (l.toList ++ r.toList) ∧
    (eraseAt path (node c l x r)).1.Ordered cmp ∧
    (∃ m, (eraseAt path (node c l x r)).1.Balanced black m) ∧
    (eraseAt path (node c l x r)).2 ≤ 3 := by
  have hfill : t = path.fill (node c l x r) := by
    have := Path.zoom_fill (path := .root) hz; simpa [Path.fill] using this
  have htl : t.toList = path.withList (l.toList ++ x :: r.toList) := by
    rw [hfill, Path.fill_toList]; simp
  obtain ⟨c', h', hnode, hpath⟩ := hb.zoom (path := .root) .root hz
  -- The list claim, from which order follows: the result's list is `t`'s with `x` removed.
  have hlist : (eraseAt path (node c l x r)).1.toList = path.withList (l.toList ++ r.toList) := by
    unfold eraseAt
    split
    · rename_i hrr; cases hrr
    · rename_i c₁ l₁ x₁ hm
      cases hm
      split <;> simp [delFix_toList]
    · rename_i c₁ x₁ cr rl rv rr hm
      cases hm
      split <;> simp [delFix_toList]
    · rename_i c₁ cl ll lv lr x₁ cr rl rv rr hm
      cases hm
      obtain ⟨cm, m, mr, hlm⟩ := leftmost_node (c := cr) (l := rl) (v := rv) (r := rr) .root
      rw [hlm]
      simp only
      have hlm' := leftmost_fst (node cr rl rv rr) (.right c (node cl ll lv lr) m path) .root
      rw [hlm] at hlm'
      have hf := leftmost_fill (node cr rl rv rr) (.right c (node cl ll lv lr) m path)
      rw [hlm'] at hf
      have hL := leftmost_listL (node cr rl rv rr) (.right c (node cl ll lv lr) m path)
      have hft := congrArg RBNode.toList hf
      simp only [Path.fill_toList, Path.withList, RBNode.toList_node, RBNode.toList_nil,
        List.nil_append, Path.fill, hL, Path.listL] at hft
      have key : (m :: (mr.toList ++
          (leftmost (node cr rl rv rr) (.right c (node cl ll lv lr) m path)).2.listR)) =
          (node cr rl rv rr).toList ++ path.listR := by
        simp only [List.append_assoc, List.cons_append] at hft
        simpa using hft
      split
      · simp only [Path.fill_toList, Path.withList, hL, Path.listL]
        simp only [List.append_assoc, List.cons_append, List.nil_append,
          RBNode.toList_node] at key ⊢
        rw [key]
      · rw [delFix_toList]
        simp only [Path.fill_toList, Path.withList, hL, Path.listL]
        simp only [List.append_assoc, List.cons_append, List.nil_append,
          RBNode.toList_node] at key ⊢
        rw [key]
  refine ⟨htl, hlist, ?_, ?_, ?_⟩
  · -- Order: a sublist of a sorted list is sorted.
    rw [ordered_iff, hlist]
    have hs := ordered_iff.1 ho
    rw [htl] at hs
    refine hs.sublist ?_
    simp only [Path.withList, List.append_assoc]
    exact List.Sublist.append_left (List.Sublist.append_left
      (List.Sublist.append_right (List.sublist_cons_self _ _) _) _) _
  · -- Balance.
    unfold eraseAt
    split
    · rename_i hrr; cases hrr
    · rename_i c₁ l₁ x₁ hm
      cases hm
      split
      · cases hnode with
        | red hl hr => cases hr; exact ⟨n, (hole_toBlack hpath).fill hl⟩
      · cases hnode with
        | black hl hr => cases hr; exact delFix_balanced hpath (.balanced hl)
    · rename_i c₁ x₁ cr rl rv rr hm
      cases hm
      split
      · cases hnode with
        | red hl hr => cases hl; exact ⟨n, (hole_toBlack hpath).fill hr⟩
      · cases hnode with
        | black hl hr => cases hl; exact delFix_balanced hpath (.balanced hr)
    · rename_i c₁ cl ll lv lr x₁ cr rl rv rr hm
      cases hm
      obtain ⟨cm, m, mr, hlm⟩ := leftmost_node (c := cr) (l := rl) (v := rv) (r := rr) .root
      rw [hlm]
      simp only
      have hlm' := leftmost_fst (node cr rl rv rr) (.right c (node cl ll lv lr) m path) .root
      rw [hlm] at hlm'
      -- The path to the erased node's right subtree, under a node of colour `c` holding `m`.
      obtain ⟨cR, hR, hRt, hRp⟩ : ∃ cR hR, (node cr rl rv rr).Balanced cR hR ∧
          (Path.right c (node cl ll lv lr) m path).Balanced black n cR hR := by
        cases hnode with
        | red hl hr => exact ⟨_, _, hr, .redR hl hpath⟩
        | black hl hr => exact ⟨_, _, hr, .blackR hl hpath⟩
      obtain ⟨c'', n'', hmin, hp'⟩ := leftmost_balanced hRt hRp
      rw [hlm'] at hmin
      split
      · cases hmin with
        | red hl hr => cases hl; cases hr; exact ⟨n, (hole_toBlack hp').fill .nil⟩
      · cases hmin with
        | black hl hr => cases hl; exact delFix_balanced hp' (.balanced hr)
  · -- Rotations.
    unfold eraseAt
    split
    · simp
    · split
      · simp
      · exact delFix_rotations _ _
    · split
      · simp
      · exact delFix_rotations _ _
    · split
      · split
        · simp
        · exact delFix_rotations _ _
      · simp

/-- `IntrusiveMultiRbTree::erase_counted`, on the tree of keys, for an element with no equal-key
duplicates (`Node`). The Rust is handed the node itself; here it is found by key (`zoom`, the same
descent as `insert`). `none` if no element has that key, which the Rust's contract (the node is in
the tree) excludes. The `Link` and `Promote` branches change only the equal-key chains, so they
leave the tree of keys as it is and belong to the heap layer. -/
def erase (cmp : α → α → Ordering) (t : RBNode α) (v : α) : Option (RBNode α × EraseKind × Nat) :=
  match zoom (cmp v) t with
  | (node c l x r, path) => let q := eraseAt path (node c l x r); some (q.1, .node, q.2)
  | (nil, _) => none

/-- **Oris's erase is correct** (`eraseAt_spec` at the key the descent finds): on a valid
red-black tree with a black root, erasing a key that is present removes exactly that element,
keeps all the others in order, and leaves a valid red-black tree with a black root, after at most
three rotations. -/
theorem erase_spec [Std.TransCmp cmp] {t : RBNode α} {n : Nat}
    (ho : t.Ordered cmp) (hb : t.Balanced black n) (v : α) :
    match erase cmp t v with
    | some (t', _, rot) =>
      ∃ (l : RBNode α) (x : α) (r : RBNode α) (path : Path α),
        t.toList = Path.withList path (l.toList ++ x :: r.toList) ∧
        t'.toList = Path.withList path (l.toList ++ r.toList) ∧
        t'.Ordered cmp ∧ (∃ m, t'.Balanced black m) ∧ rot ≤ 3
    | none => True := by
  unfold erase
  rcases hz : zoom (cmp v) t with ⟨_ | ⟨c, l, x, r⟩, path⟩
  · trivial
  · obtain ⟨h1, h2, h3, h4, h5⟩ := eraseAt_spec ho hb hz
    exact ⟨l, x, r, path, h1, h2, h3, h4, h5⟩

end Oris.RB
