-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.InsertFixup

/-!
# Step 3c: `erase_fixup` performs `delFix`

`Lean/docs/heap-layer.md`, §4, theorem 4. HPHA's reading of the loop (`eraseFixupHpha`, the root
re-read at each test) performs `Fixup.lean`'s `delFix`: the same tree and the same rotation count.
The Rust's own reading, the root read once, is step 3d (§6).

The loop invariant is a located subtree (`Located h head cur p s x path`), `cur` possibly the
sentinel (an empty hole), with the **hole invariant**: when `cur` is the sentinel, its scratch
`parent` and side name the hole's slot (for a real `cur`, `Rep` says it). The loop reads `cur`'s
`parent` word only at the top of an iteration, before any write, and every iteration after the
first starts from a real node, so the writes that can reach the scratch (a rotation whose moving
child is the sentinel) never matter. Two more hypotheses: `DelFixClean path x`, that `delFix`
never reaches its nil-sibling departure (on an unbalanced tree the Rust, like the heap model,
paints the sentinel red there; `delFixClean_of_balanced` gives it on a valid tree), and fuel.

The proof works in three layers:
- the **step lemmas** (`eraseFixupLoop_exit`, `_case2`, `_finish`, `_case1_case2`, `_case1_finish`)
  unfold one iteration each, for either side, in terms of two proof devices, `case1Heap` and
  `finishHeap` (the writes of the first case, and of the third and fourth);
- the **case lemmas** (`case1_left`, ..., `finish_right`) say what those writes do to a located
  subtree, from `Located.paint` and `rotateAt_refines_*`;
- `eraseFixupLoop_refines` follows `delFix` arm by arm, by induction on fuel.
-/

namespace Oris.RB

namespace Heap

open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-! ## The step lemmas -/

/-- The root as the loop's test reads it. -/
abbrev rootOf (head : Addr) (reread : Bool) (root₀ : Addr) (h : Heap) : Addr :=
  if reread then childAt h head .left else root₀

/-- The first case's writes. -/
def case1Heap (h : Heap) (p w : Addr) (s : Side) : Heap :=
  rotateAt (makeRed (makeBlack h w) p) p s

/-- The first case's new sibling. -/
def case1Sibling (h : Heap) (p w : Addr) (s : Side) : Addr :=
  childAt (makeRed (makeBlack h w) p) w s

/-- The third (if needed) and fourth cases' writes, and their rotations. -/
def finishHeap (h : Heap) (p w : Addr) (s : Side) : Heap × Nat :=
  let o := s.other
  let (h, w, k) :=
    if !red h (childAt h w o) then
      let wSChild := childAt h w s
      (rotateAt (makeRed (makeBlack h wSChild) w) w o, wSChild, 2)
    else (h, w, 1)
  let h := makeBlack (setColour h w (red h p)) p
  (rotateAt (makeBlack h (childAt h w o)) p s, k)

/-- The loop's exit: a red `cur`, or `cur` the root, ends it with `make_black(cur)`. -/
theorem eraseFixupLoop_exit {head : Addr} {reread : Bool} {root₀ : Addr} {fuel : Nat} {h : Heap}
    {cur : Addr} {rot : Nat} (hx : red h cur = true ∨ cur = rootOf head reread root₀ h) :
    eraseFixupLoop head reread root₀ (fuel + 1) h cur rot = some (makeBlack h cur, rot) := by
  rw [eraseFixupLoop]
  rcases hx with hx | hx
  · simp only [hx, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · simp only [rootOf] at hx
    simp only [← hx, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- **One iteration, the second case** (no first case): `w` black with both children black,
`make_red(w); cur = p`. The step lemmas are the only places that unfold the loop. -/
theorem eraseFixupLoop_case2 {head : Addr} {reread : Bool} {root₀ : Addr} {fuel : Nat} {h : Heap}
    {cur p : Addr} {s : Side} {rot : Nat} (hb : red h cur = false)
    (hne : cur ≠ rootOf head reread root₀ h) (hp : parent h cur = p) (hs : parentSide h cur = s)
    (hw : red h (childAt h p s.other) = false)
    (hl : red h (childAt h (childAt h p s.other) .left) = false)
    (hr : red h (childAt h (childAt h p s.other) .right) = false) :
    eraseFixupLoop head reread root₀ (fuel + 1) h cur rot =
      eraseFixupLoop head reread root₀ fuel (makeRed h (childAt h p s.other)) p rot := by
  rw [eraseFixupLoop]
  simp only [rootOf] at hne
  simp only [hb, hp, hs, hw, hl, hr, bne_iff_ne, ne_eq, hne, not_false_eq_true, Bool.not_false,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte, Bool.and_self]

/-- **One iteration, the third and fourth cases** (no first case): `w` black, its children not
both black. The loop then goes on from the root, `cur = root`. -/
theorem eraseFixupLoop_finish {head : Addr} {reread : Bool} {root₀ : Addr} {fuel : Nat} {h : Heap}
    {cur p : Addr} {s : Side} {rot : Nat} (hb : red h cur = false)
    (hne : cur ≠ rootOf head reread root₀ h) (hp : parent h cur = p) (hs : parentSide h cur = s)
    (hw : red h (childAt h p s.other) = false)
    (hnb : (!red h (childAt h (childAt h p s.other) .left) &&
      !red h (childAt h (childAt h p s.other) .right)) = false) :
    eraseFixupLoop head reread root₀ (fuel + 1) h cur rot =
      eraseFixupLoop head reread root₀ fuel (finishHeap h p (childAt h p s.other) s).1
        (rootOf head reread root₀ (finishHeap h p (childAt h p s.other) s).1)
        (rot + (finishHeap h p (childAt h p s.other) s).2) := by
  rw [eraseFixupLoop]
  simp only [rootOf] at hne ⊢
  simp only [hb, hp, hs, hw, hnb, bne_iff_ne, ne_eq, hne, not_false_eq_true, Bool.not_false,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte, finishHeap]
  by_cases h3 : red h (childAt h (childAt h p s.other) s.other) = true
  · simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [h3, Bool.not_false, ↓reduceIte, Nat.add_assoc]

/-- **One iteration, the first case then the second**: `w` red, then the new sibling's children
both black. The loop goes on from `p`, now red. -/
theorem eraseFixupLoop_case1_case2 {head : Addr} {reread : Bool} {root₀ : Addr} {fuel : Nat}
    {h : Heap} {cur p : Addr} {s : Side} {rot : Nat} (hb : red h cur = false)
    (hne : cur ≠ rootOf head reread root₀ h) (hp : parent h cur = p) (hs : parentSide h cur = s)
    (hw : red h (childAt h p s.other) = true)
    (hl : red (case1Heap h p (childAt h p s.other) s)
      (childAt (case1Heap h p (childAt h p s.other) s)
        (case1Sibling h p (childAt h p s.other) s) .left) = false)
    (hr : red (case1Heap h p (childAt h p s.other) s)
      (childAt (case1Heap h p (childAt h p s.other) s)
        (case1Sibling h p (childAt h p s.other) s) .right) = false) :
    eraseFixupLoop head reread root₀ (fuel + 1) h cur rot =
      eraseFixupLoop head reread root₀ fuel
        (makeRed (case1Heap h p (childAt h p s.other) s)
          (case1Sibling h p (childAt h p s.other) s)) p (rot + 1) := by
  rw [eraseFixupLoop]
  simp only [rootOf] at hne
  simp only [case1Heap, case1Sibling] at hl hr ⊢
  simp only [hb, hp, hs, hw, hl, hr, bne_iff_ne, ne_eq, hne, not_false_eq_true, Bool.not_false,
    Bool.true_and, ↓reduceIte, Bool.and_self]

/-- **One iteration, the first case then the third and fourth**: the loop goes on from the root. -/
theorem eraseFixupLoop_case1_finish {head : Addr} {reread : Bool} {root₀ : Addr} {fuel : Nat}
    {h : Heap} {cur p : Addr} {s : Side} {rot : Nat} (hb : red h cur = false)
    (hne : cur ≠ rootOf head reread root₀ h) (hp : parent h cur = p) (hs : parentSide h cur = s)
    (hw : red h (childAt h p s.other) = true)
    (hnb : (!red (case1Heap h p (childAt h p s.other) s)
        (childAt (case1Heap h p (childAt h p s.other) s)
          (case1Sibling h p (childAt h p s.other) s) .left) &&
      !red (case1Heap h p (childAt h p s.other) s)
        (childAt (case1Heap h p (childAt h p s.other) s)
          (case1Sibling h p (childAt h p s.other) s) .right)) = false) :
    eraseFixupLoop head reread root₀ (fuel + 1) h cur rot =
      eraseFixupLoop head reread root₀ fuel
        (finishHeap (case1Heap h p (childAt h p s.other) s) p
          (case1Sibling h p (childAt h p s.other) s) s).1
        (rootOf head reread root₀ (finishHeap (case1Heap h p (childAt h p s.other) s) p
          (case1Sibling h p (childAt h p s.other) s) s).1)
        (rot + 1 + (finishHeap (case1Heap h p (childAt h p s.other) s) p
          (case1Sibling h p (childAt h p s.other) s) s).2) := by
  rw [eraseFixupLoop]
  simp only [rootOf] at hne ⊢
  simp only [case1Heap, case1Sibling] at hnb ⊢
  simp only [hb, hp, hs, hw, hnb, bne_iff_ne, ne_eq, hne, not_false_eq_true, Bool.not_false,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte, finishHeap]
  generalize rotateAt (makeRed (makeBlack h (childAt h p s.other)) p) p s = H
  generalize childAt (makeRed (makeBlack h (childAt h p s.other)) p) (childAt h p s.other) s = w
  by_cases h3 : red H (childAt H w s.other) = true
  · simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [h3, Bool.not_false, ↓reduceIte, Nat.add_assoc]

/-! ## The cases, on a located subtree

For `cur` a left child (`s = Left`, `o = Right`), then the mirror images. Each says what the
Rust's statements of that case do to the located subtree of `p`. -/

/-- The second case (`cur` a left child): `make_red(w)`, whatever `w`'s colour. -/
theorem case2_left {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x wl wr : RBNode Addr} {wv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc x y (.node cw wl wv wr)) pp) :
    Located (makeRed h wv) head y P S (.node pc x y (.node .red wl wv wr)) pp := by
  obtain ⟨-, -, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_right
  rw [Lw.1.node_inv.eq] at Lw
  have L := (Lw.paint .red).up_right
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := wv) (colourBit .red) hpa hsa
  rw [e₁, e₂] at L
  exact L

/-- The fourth case (`cur` a left child, the far child `b` red): `set_colour(w, colour(p));
make_black(p); make_black(w.child(o)); rotate(p, s)`. -/
theorem case4_left {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a b1 b2 : RBNode Addr} {w bv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc x y (.node cw a w (.node .red b1 bv b2))) pp) :
    Located (rotateAt (makeBlack (makeBlack (setColour h w (red h y)) y)
        (childAt (makeBlack (setColour h w (red h y)) y) w Side.left.other)) y .left) head w P S
      (rotate .left (.node .black x y (.node pc a w (.node .black b1 bv b2)))) pp := by
  obtain ⟨-, -, -, hpa, hsa, hcy, -⟩ := hl.1.node_inv
  have hry : red h y = colourBit pc := hcy
  rw [hry]
  have Lw := hl.down_right
  rw [Lw.1.node_inv.eq] at Lw
  have Lp1 := (Lw.paint pc).up_right
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := w) (colourBit pc) hpa hsa
  rw [e₁, e₂] at Lp1
  have Lp2 := Lp1.paint .black
  have Lw2 := Lp2.down_right
  rw [Lw2.1.node_inv.eq] at Lw2
  have Lb := Lw2.down_right
  have hbv : (setColour (setColour h w (colourBit pc)) y (colourBit .black) w).right = bv :=
    Lb.1.node_inv.eq
  rw [hbv] at Lb
  have L1 := (Lb.paint .black).up_right
  obtain ⟨-, -, -, hwp, hws, -⟩ := Lw2.1.node_inv
  obtain ⟨e₅, e₆⟩ := setColour_slot (a := bv) (colourBit .black) hwp hws
  rw [e₅, e₆] at L1
  have Lp3 := L1.up_right
  have e₃ : (setColour (setColour (setColour h w (colourBit pc)) y (colourBit .black)) bv
      (colourBit .black) y).parent = P := by
    rw [setColour_parent, setColour_parent, setColour_parent, hpa]
  have e₄ : (setColour (setColour (setColour h w (colourBit pc)) y (colourBit .black)) bv
      (colourBit .black) y).side = S := by
    rw [setColour_side, setColour_side, setColour_side, hsa]
  rw [e₃, e₄] at Lp3
  have L := rotateAt_refines_left Lp3
  have hc : childAt (makeBlack (setColour h w (colourBit pc)) y) w Side.left.other = bv := hbv
  rw [hc]
  exact L

/-- The third case (`cur` a left child, the far child black, the near child red):
`make_black(w.child(s)); make_red(w); rotate(w, o); w = c`. -/
theorem case3_left {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a1 a2 b : RBNode Addr} {av w : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc x y (.node cw (.node .red a1 av a2) w b)) pp) :
    childAt h w .left = av ∧
    Located (rotateAt (makeRed (makeBlack h (childAt h w .left)) w) w Side.left.other) head y P S
      (.node pc x y (.node .black a1 av (.node .red a2 w b))) pp := by
  obtain ⟨-, hyh, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_right
  rw [Lw.1.node_inv.eq] at Lw
  obtain ⟨-, -, -, hwp, hws, -⟩ := Lw.1.node_inv
  have La := Lw.down_left
  have hav : (h w).left = av := La.1.node_inv.eq
  rw [hav] at La
  refine ⟨hav, ?_⟩
  have Lw1 := (La.paint .black).up_left
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := av) (colourBit .black) hwp hws
  rw [e₁, e₂] at Lw1
  have Lw2 := Lw1.paint .red
  have Lr := rotateAt_refines_right Lw2
  have hsl := rotateAt_slot_right Lw2 hyh
  have Lp := Lr.up_right
  rw [hsl.1, hsl.2] at Lp
  obtain ⟨e₃, e₄⟩ := setColour_slot (a := w) (colourBit .red)
    (setColour_slot (a := av) (colourBit .black) hpa hsa).1
    (setColour_slot (a := av) (colourBit .black) hpa hsa).2
  rw [e₃, e₄] at Lp
  have hc : childAt h w .left = av := hav
  rw [hc]
  exact Lp

/-- **The finish (`cur` a left child)**: when `stage2L` returns the finished tree, the third case
(if the far child is black) and the fourth leave a heap whose final `make_black` of the root
represents it, after `stage2L`'s rotations. -/
theorem finish_left {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a b : RBNode Addr} {w : Addr} {pp : Path Addr} {r : RBNode Addr × Nat}
    (hl : Located h head y P S (.node pc x y (.node cw a w b)) pp)
    (hs : stage2L pc pp y (.node cw a w b) x = some r) :
    Tree (makeBlack (finishHeap h y w .left).1 (childAt (finishHeap h y w .left).1 head .left))
      head r.1 ∧ (finishHeap h y w .left).2 = r.2 := by
  have hhead := hl.2.head_red
  have Lw := hl.down_right
  rw [Lw.1.node_inv.eq] at Lw
  obtain ⟨-, -, -, -, -, -, -, hbR⟩ := Lw.1.node_inv
  have hrb : red h (childAt h w Side.left.other) = red? b := hbR.red_eq hhead
  cases hb : red? b with
  | true =>
    obtain ⟨b1, bv, b2, rfl⟩ : ∃ b1 bv b2, b = .node .red b1 bv b2 := by
      match b, hb with
      | .node .red b1 bv b2, _ => exact ⟨b1, bv, b2, rfl⟩
    simp only [stage2L, red?_red, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at hs
    subst hs
    have hF : finishHeap h y w .left =
        (rotateAt (makeBlack (makeBlack (setColour h w (red h y)) y)
          (childAt (makeBlack (setColour h w (red h y)) y) w Side.left.other)) y .left, 1) := by
      simp only [finishHeap, hrb, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hF]
    have L := case4_left hl
    exact ⟨(L.2.fill L.1).makeBlack_root, rfl⟩
  | false =>
    have ha : red? a = true := by
      cases ha' : red? a
      · simp only [stage2L, ha', hb, Bool.not_false, Bool.and_self, ↓reduceIte,
          reduceCtorEq] at hs
      · rfl
    obtain ⟨a1, av, a2, rfl⟩ : ∃ a1 av a2, a = .node .red a1 av a2 := by
      match a, ha with
      | .node .red a1 av a2, _ => exact ⟨a1, av, a2, rfl⟩
    simp only [stage2L, red?_red, hb, Bool.not_true, Bool.not_false, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
    subst hs
    obtain ⟨hc, L3⟩ := case3_left hl
    have hF : finishHeap h y w .left =
        (rotateAt (makeBlack (makeBlack (setColour
            (rotateAt (makeRed (makeBlack h (childAt h w .left)) w) w Side.left.other) av
            (red (rotateAt (makeRed (makeBlack h (childAt h w .left)) w) w Side.left.other) y)) y)
          (childAt (makeBlack (setColour
            (rotateAt (makeRed (makeBlack h (childAt h w .left)) w) w Side.left.other) av
            (red (rotateAt (makeRed (makeBlack h (childAt h w .left)) w) w Side.left.other) y)) y)
            av Side.left.other)) y .left, 2) := by
      simp only [finishHeap, hrb, hb, Bool.not_false, ↓reduceIte, hc]
    rw [hF]
    have L := case4_left L3
    exact ⟨(L.2.fill L.1).makeBlack_root, rfl⟩

/-- **The first case (`cur` a left child, `w` red)**: `make_black(w); make_red(p); w =
w.child(s); rotate(p, s)`. Afterwards `p`, now red, hangs one level deeper under `w`, with the
old near child as `cur`'s sibling, which the loop reads back as `p`'s side-`o` child. -/
theorem case1_left {h : Heap} {head y P : Addr} {S : Side} {pc : RBColor}
    {x wl wr : RBNode Addr} {wv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc x y (.node .red wl wv wr)) pp) :
    case1Sibling h y wv .left = childAt (case1Heap h y wv .left) y Side.left.other ∧
    Located (case1Heap h y wv .left) head y wv .left (.node .red x y wl)
      (.left .black pp wv wr) := by
  obtain ⟨-, -, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_right
  rw [Lw.1.node_inv.eq] at Lw
  have Lp1 := (Lw.paint .black).up_right
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := wv) (colourBit .black) hpa hsa
  rw [e₁, e₂] at Lp1
  have Lp2 := Lp1.paint .red
  have Lr := rotateAt_refines_left Lp2
  have Lp3 := Lr.down_left
  rw [Lp3.1.node_inv.eq] at Lp3
  refine ⟨?_, Lp3⟩
  -- The sibling: `wv`'s left link before the rotation, `y`'s right link after; both start `wl`.
  have hb := (Lp2.down_right).1.node_inv.left
  have ha := Lp3.1.node_inv.right
  exact hb.addr_eq ha

/-- The mirror image of `case2_left`. -/
theorem case2_right {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x wl wr : RBNode Addr} {wv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc (.node cw wl wv wr) y x) pp) :
    Located (makeRed h wv) head y P S (.node pc (.node .red wl wv wr) y x) pp := by
  obtain ⟨-, -, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_left
  rw [Lw.1.node_inv.eq] at Lw
  have L := (Lw.paint .red).up_left
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := wv) (colourBit .red) hpa hsa
  rw [e₁, e₂] at L
  exact L

/-- The mirror image of `case4_left` (the far child is `w`'s left child). -/
theorem case4_right {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a b1 b2 : RBNode Addr} {w bv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc (.node cw (.node .red b1 bv b2) w a) y x) pp) :
    Located (rotateAt (makeBlack (makeBlack (setColour h w (red h y)) y)
        (childAt (makeBlack (setColour h w (red h y)) y) w Side.right.other)) y .right) head w P S
      (rotate .right (.node .black (.node pc (.node .black b1 bv b2) w a) y x)) pp := by
  obtain ⟨-, -, -, hpa, hsa, hcy, -⟩ := hl.1.node_inv
  have hry : red h y = colourBit pc := hcy
  rw [hry]
  have Lw := hl.down_left
  rw [Lw.1.node_inv.eq] at Lw
  have Lp1 := (Lw.paint pc).up_left
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := w) (colourBit pc) hpa hsa
  rw [e₁, e₂] at Lp1
  have Lp2 := Lp1.paint .black
  have Lw2 := Lp2.down_left
  rw [Lw2.1.node_inv.eq] at Lw2
  have Lb := Lw2.down_left
  have hbv : (setColour (setColour h w (colourBit pc)) y (colourBit .black) w).left = bv :=
    Lb.1.node_inv.eq
  rw [hbv] at Lb
  have L1 := (Lb.paint .black).up_left
  obtain ⟨-, -, -, hwp, hws, -⟩ := Lw2.1.node_inv
  obtain ⟨e₅, e₆⟩ := setColour_slot (a := bv) (colourBit .black) hwp hws
  rw [e₅, e₆] at L1
  have Lp3 := L1.up_left
  have e₃ : (setColour (setColour (setColour h w (colourBit pc)) y (colourBit .black)) bv
      (colourBit .black) y).parent = P := by
    rw [setColour_parent, setColour_parent, setColour_parent, hpa]
  have e₄ : (setColour (setColour (setColour h w (colourBit pc)) y (colourBit .black)) bv
      (colourBit .black) y).side = S := by
    rw [setColour_side, setColour_side, setColour_side, hsa]
  rw [e₃, e₄] at Lp3
  have L := rotateAt_refines_right Lp3
  have hc : childAt (makeBlack (setColour h w (colourBit pc)) y) w Side.right.other = bv := hbv
  rw [hc]
  exact L

/-- The mirror image of `case3_left` (the near child is `w`'s right child). -/
theorem case3_right {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a1 a2 b : RBNode Addr} {av w : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc (.node cw b w (.node .red a1 av a2)) y x) pp) :
    childAt h w .right = av ∧
    Located (rotateAt (makeRed (makeBlack h (childAt h w .right)) w) w Side.right.other) head y P S
      (.node pc (.node .black (.node .red b w a1) av a2) y x) pp := by
  obtain ⟨-, hyh, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_left
  rw [Lw.1.node_inv.eq] at Lw
  obtain ⟨-, -, -, hwp, hws, -⟩ := Lw.1.node_inv
  have La := Lw.down_right
  have hav : (h w).right = av := La.1.node_inv.eq
  rw [hav] at La
  refine ⟨hav, ?_⟩
  have Lw1 := (La.paint .black).up_right
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := av) (colourBit .black) hwp hws
  rw [e₁, e₂] at Lw1
  have Lw2 := Lw1.paint .red
  have Lr := rotateAt_refines_left Lw2
  have hsl := rotateAt_slot_left Lw2 hyh
  have Lp := Lr.up_left
  rw [hsl.1, hsl.2] at Lp
  obtain ⟨e₃, e₄⟩ := setColour_slot (a := w) (colourBit .red)
    (setColour_slot (a := av) (colourBit .black) hpa hsa).1
    (setColour_slot (a := av) (colourBit .black) hpa hsa).2
  rw [e₃, e₄] at Lp
  have hc : childAt h w .right = av := hav
  rw [hc]
  exact Lp

/-- The mirror image of `finish_left`. -/
theorem finish_right {h : Heap} {head y P : Addr} {S : Side} {pc cw : RBColor}
    {x a b : RBNode Addr} {w : Addr} {pp : Path Addr} {r : RBNode Addr × Nat}
    (hl : Located h head y P S (.node pc (.node cw a w b) y x) pp)
    (hs : stage2R pc pp y (.node cw a w b) x = some r) :
    Tree (makeBlack (finishHeap h y w .right).1 (childAt (finishHeap h y w .right).1 head .left))
      head r.1 ∧ (finishHeap h y w .right).2 = r.2 := by
  have hhead := hl.2.head_red
  have Lw := hl.down_left
  rw [Lw.1.node_inv.eq] at Lw
  obtain ⟨-, -, -, -, -, -, haL, -⟩ := Lw.1.node_inv
  have hra : red h (childAt h w Side.right.other) = red? a := haL.red_eq hhead
  cases ha : red? a with
  | true =>
    obtain ⟨b1, bv, b2, rfl⟩ : ∃ b1 bv b2, a = .node .red b1 bv b2 := by
      match a, ha with
      | .node .red b1 bv b2, _ => exact ⟨b1, bv, b2, rfl⟩
    simp only [stage2R, red?_red, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq] at hs
    subst hs
    have hF : finishHeap h y w .right =
        (rotateAt (makeBlack (makeBlack (setColour h w (red h y)) y)
          (childAt (makeBlack (setColour h w (red h y)) y) w Side.right.other)) y .right, 1) := by
      simp only [finishHeap, hra, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hF]
    have L := case4_right hl
    exact ⟨(L.2.fill L.1).makeBlack_root, rfl⟩
  | false =>
    have hb : red? b = true := by
      cases hb' : red? b
      · simp only [stage2R, ha, hb', Bool.not_false, Bool.and_self, ↓reduceIte,
          reduceCtorEq] at hs
      · rfl
    obtain ⟨a1, av, a2, rfl⟩ : ∃ a1 av a2, b = .node .red a1 av a2 := by
      match b, hb with
      | .node .red a1 av a2, _ => exact ⟨a1, av, a2, rfl⟩
    simp only [stage2R, red?_red, ha, Bool.not_true, Bool.not_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
    subst hs
    obtain ⟨hc, L3⟩ := case3_right hl
    have hF : finishHeap h y w .right =
        (rotateAt (makeBlack (makeBlack (setColour
            (rotateAt (makeRed (makeBlack h (childAt h w .right)) w) w Side.right.other) av
            (red (rotateAt (makeRed (makeBlack h (childAt h w .right)) w) w Side.right.other) y)) y)
          (childAt (makeBlack (setColour
            (rotateAt (makeRed (makeBlack h (childAt h w .right)) w) w Side.right.other) av
            (red (rotateAt (makeRed (makeBlack h (childAt h w .right)) w) w Side.right.other) y)) y)
            av Side.right.other)) y .right, 2) := by
      simp only [finishHeap, hra, ha, Bool.not_false, ↓reduceIte, hc]
    rw [hF]
    have L := case4_right L3
    exact ⟨(L.2.fill L.1).makeBlack_root, rfl⟩

/-- The mirror image of `case1_left`. -/
theorem case1_right {h : Heap} {head y P : Addr} {S : Side} {pc : RBColor}
    {x wl wr : RBNode Addr} {wv : Addr} {pp : Path Addr}
    (hl : Located h head y P S (.node pc (.node .red wl wv wr) y x) pp) :
    case1Sibling h y wv .right = childAt (case1Heap h y wv .right) y Side.right.other ∧
    Located (case1Heap h y wv .right) head y wv .right (.node .red wr y x)
      (.right .black wl wv pp) := by
  obtain ⟨-, -, -, hpa, hsa, -⟩ := hl.1.node_inv
  have Lw := hl.down_left
  rw [Lw.1.node_inv.eq] at Lw
  have Lp1 := (Lw.paint .black).up_left
  obtain ⟨e₁, e₂⟩ := setColour_slot (a := wv) (colourBit .black) hpa hsa
  rw [e₁, e₂] at Lp1
  have Lp2 := Lp1.paint .red
  have Lr := rotateAt_refines_right Lp2
  have Lp3 := Lr.down_right
  rw [Lp3.1.node_inv.eq] at Lp3
  refine ⟨?_, Lp3⟩
  have hb := (Lp2.down_left).1.node_inv.right
  have ha := Lp3.1.node_inv.left
  exact hb.addr_eq ha

/-! ## The refinement theorems -/

/-- **`erase_fixup`'s loop performs `delFix`** (step 3c; the note's §4, theorem 4), in HPHA's
reading (the root re-read at each test; `root₀` is then unused). If the heap represents the
located subtree `x` at `path` (`x` empty when `cur` is the sentinel), the hole invariant holds
(for the sentinel, its scratch `parent` and side name the slot), `delFix` never reaches its
departure from there (`DelFixClean`), and the fuel is at least the hole's depth plus one, then the
loop, with `rot` rotations counted, returns a heap representing `(delFix path x).1`, with
`rot + (delFix path x).2` rotations: the zipper's tree and count, for every input of these
shapes, valid red-black tree or not.

The proof follows `delFix`: a red `cur` or the root ends the loop; otherwise, for each side, a red
sibling (the first case, then the second, which stops at once on the now-red `p`, or the finish)
or a black one (the second case, climbing to `p`: the induction hypothesis, with one unit of fuel
less, or the finish). -/
theorem eraseFixupLoop_refines (head root₀ : Addr) : ∀ (fuel : Nat) {h : Heap} {cur P : Addr}
    {S : Side} {x : RBNode Addr} {path : Path Addr} (rot : Nat),
    Located h head cur P S x path → (cur = head → parent h cur = P ∧ parentSide h cur = S) →
    DelFixClean path x → pathDepth path + 1 ≤ fuel →
    ∃ H, eraseFixupLoop head true root₀ fuel h cur rot = some (H, rot + (delFix path x).2) ∧
      Tree H head (delFix path x).1
  | 0, _, _, _, _, _, _, _, _, _, _, hf => absurd hf (by omega)
  | fuel + 1, h, cur, P, S, x, path, rot, hl, hhole, hc, hf => by
    -- The hole invariant: for a real `cur`, `Rep` gives its slot; for the sentinel, the scratch.
    obtain ⟨hP, hS⟩ : parent h cur = P ∧ parentSide h cur = S := by
      by_cases hch : cur = head
      · exact hhole hch
      · exact hl.1.root_fields (hl.1.root_mem hch)
    have hhead := hl.2.head_red
    have hrx : red h cur = red? x := hl.1.red_eq hhead
    -- A red `cur` ends the loop: `make_black(cur)`.
    by_cases hr : red? x = true
    · obtain ⟨xl, xv, xr, rfl⟩ : ∃ xl xv xr, x = .node .red xl xv xr := by
        match x, hr with
        | .node .red xl xv xr, _ => exact ⟨xl, xv, xr, rfl⟩
      rw [delFix_red hr]
      refine ⟨_, by rw [eraseFixupLoop_exit (.inl (hrx.trans hr))]; rfl, ?_⟩
      have e := hl.1.node_inv.eq
      subst e
      have L := hl.paint .black
      exact L.2.fill L.1
    have hr' : red? x = false := by simpa using hr
    have hb : red h cur = false := hrx.trans hr'
    -- At the root: `make_black(cur)`, the final `make_black` of the root.
    cases path with
    | root =>
      rw [delFix_root hr']
      obtain ⟨e₁, e₂⟩ : P = head ∧ S = .left := by cases hl.2; exact ⟨rfl, rfl⟩
      subst e₁ e₂
      have hcr : cur = (h P).left := (hl.eq_root_iff).2 rfl
      refine ⟨_, by rw [eraseFixupLoop_exit (.inr hcr)]; rfl, ?_⟩
      have hT : Tree h P x := tree_iff_located.2 (hcr ▸ hl)
      have := hT.makeBlack_root
      rw [show childAt h P .left = cur from hcr.symm] at this
      exact this
    | left pc pp y w =>
      obtain ⟨e₁, e₂⟩ := hl.2.left_inv
      subst e₁ e₂
      have hne : cur ≠ rootOf head true root₀ h := fun e => nomatch (hl.eq_root_iff).1 e
      have Lp := hl.up_left
      simp only [pathDepth] at hf
      cases w with
      | nil => simp [DelFixClean, hr'] at hc
      | node cw wl wv wr =>
        have Lw := Lp.down_right
        have hwv : (h P).right = wv := Lw.1.node_inv.eq
        have hcw : red h (childAt h P Side.left.other) = red? (RBNode.node cw wl wv wr) := by
          show red h (h P).right = _; exact Lw.1.red_eq hhead
        cases cw with
        | red =>
          -- The first case, then the second (and an exit) or the finish.
          have hcl : wl ≠ .nil := by simpa [DelFixClean, hr'] using hc
          obtain ⟨hsib, L1⟩ := case1_left Lp
          obtain ⟨cl, al, av, bl, rfl⟩ : ∃ cl al av bl, wl = .node cl al av bl := by
            match wl, hcl with
            | .node cl al av bl, _ => exact ⟨cl, al, av, bl, rfl⟩
          have hw : red h (childAt h P Side.left.other) = true := hcw
          have hw' : childAt h P Side.left.other = wv := hwv
          have L1d := L1.down_right
          have hav : case1Sibling h P wv .left = av := hsib.trans L1d.1.node_inv.eq
          obtain ⟨-, -, -, -, -, -, hal, hbl⟩ := L1d.1.node_inv
          have hral : red (case1Heap h P wv .left)
              (childAt (case1Heap h P wv .left) av .left) = red? al := hal.red_eq L1.2.head_red
          have hrbl : red (case1Heap h P wv .left)
              (childAt (case1Heap h P wv .left) av .right) = red? bl := hbl.red_eq L1.2.head_red
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          cases hs : stage2L .red (.left .black pp wv wr) P (.node cl al av bl) x with
          | none =>
            -- The second case on the new sibling; `p`, now red, then ends the loop.
            obtain ⟨h1, h2⟩ := stage2L_none hs
            rw [eraseFixupLoop_case1_case2 hb hne hP hS hw
              (by rw [hw', hav]; exact hral.trans h1) (by rw [hw', hav]; exact hrbl.trans h2),
              hw', hav, delFix_left_red_none hr' hs, delFix_red rfl]
            have L2 := case2_left L1
            have hred : red (makeRed (case1Heap h P wv .left) av) P = true := L2.1.node_inv.red
            refine ⟨_, by rw [eraseFixupLoop_exit (.inl hred)], ?_⟩
            have L3 := L2.paint .black
            exact L3.2.fill L3.1
          | some r =>
            -- The third (if needed) and fourth cases, then the loop ends at the root.
            rw [eraseFixupLoop_case1_finish hb hne hP hS hw
              (by rw [hw', hav]; rw [hral, hrbl]; exact stage2L_some hs),
              hw', hav, delFix_left_red_some hr' hs]
            obtain ⟨hT, hk⟩ := finish_left L1 hs
            refine ⟨_, ?_, hT⟩
            rw [eraseFixupLoop_exit (.inr rfl), hk, Nat.add_assoc, Nat.add_comm 1]
            rfl
        | black =>
          have hw : red h (childAt h P Side.left.other) = false := hcw
          have hw' : childAt h P Side.left.other = wv := hwv
          obtain ⟨-, -, -, -, -, -, hwl, hwr⟩ := Lw.1.node_inv
          have hrwl : red h (childAt h wv .left) = red? wl := hwl.red_eq hhead
          have hrwr : red h (childAt h wv .right) = red? wr := hwr.red_eq hhead
          cases hs : stage2L pc pp P (.node .black wl wv wr) x with
          | none =>
            -- The second case: `w` made red, the loop climbs to `p`.
            obtain ⟨h1, h2⟩ := stage2L_none hs
            rw [eraseFixupLoop_case2 hb hne hP hS hw (by rw [hw']; exact hrwl.trans h1)
              (by rw [hw']; exact hrwr.trans h2), hw', delFix_left_black_none hr' hs]
            have hcl : DelFixClean pp (.node pc x P (.node .red wl wv wr)) := by
              simp only [DelFixClean, hr', Bool.false_eq_true, false_or] at hc
              exact hc.2 hs
            exact eraseFixupLoop_refines head root₀ fuel rot (case2_left Lp)
              (fun e => absurd e Lp.1.node_inv.ne_head) hcl (by omega)
          | some r =>
            obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [eraseFixupLoop_finish hb hne hP hS hw
              (by rw [hw']; rw [hrwl, hrwr]; exact stage2L_some hs),
              hw', delFix_left_black_some hr' hs]
            obtain ⟨hT, hk⟩ := finish_left Lp hs
            refine ⟨_, ?_, hT⟩
            rw [eraseFixupLoop_exit (.inr rfl), hk]
            rfl
    | right pc w y pp =>
      obtain ⟨e₁, e₂⟩ := hl.2.right_inv
      subst e₁ e₂
      have hne : cur ≠ rootOf head true root₀ h := fun e => nomatch (hl.eq_root_iff).1 e
      have Lp := hl.up_right
      simp only [pathDepth] at hf
      cases w with
      | nil => simp [DelFixClean, hr'] at hc
      | node cw wl wv wr =>
        have Lw := Lp.down_left
        have hwv : (h P).left = wv := Lw.1.node_inv.eq
        have hcw : red h (childAt h P Side.right.other) = red? (RBNode.node cw wl wv wr) := by
          show red h (h P).left = _; exact Lw.1.red_eq hhead
        cases cw with
        | red =>
          -- The first case, then the second (and an exit) or the finish.
          have hcl : wr ≠ .nil := by simpa [DelFixClean, hr'] using hc
          obtain ⟨hsib, L1⟩ := case1_right Lp
          obtain ⟨cl, al, av, bl, rfl⟩ : ∃ cl al av bl, wr = .node cl al av bl := by
            match wr, hcl with
            | .node cl al av bl, _ => exact ⟨cl, al, av, bl, rfl⟩
          have hw : red h (childAt h P Side.right.other) = true := hcw
          have hw' : childAt h P Side.right.other = wv := hwv
          have L1d := L1.down_left
          have hav : case1Sibling h P wv .right = av := hsib.trans L1d.1.node_inv.eq
          obtain ⟨-, -, -, -, -, -, hal, hbl⟩ := L1d.1.node_inv
          have hral : red (case1Heap h P wv .right)
              (childAt (case1Heap h P wv .right) av .left) = red? al := hal.red_eq L1.2.head_red
          have hrbl : red (case1Heap h P wv .right)
              (childAt (case1Heap h P wv .right) av .right) = red? bl := hbl.red_eq L1.2.head_red
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          cases hs : stage2R .red (.right .black wl wv pp) P (.node cl al av bl) x with
          | none =>
            -- The second case on the new sibling; `p`, now red, then ends the loop.
            obtain ⟨h1, h2⟩ := stage2R_none hs
            rw [eraseFixupLoop_case1_case2 hb hne hP hS hw
              (by rw [hw', hav]; exact hral.trans h1) (by rw [hw', hav]; exact hrbl.trans h2),
              hw', hav, delFix_right_red_none hr' hs, delFix_red rfl]
            have L2 := case2_right L1
            have hred : red (makeRed (case1Heap h P wv .right) av) P = true := L2.1.node_inv.red
            refine ⟨_, by rw [eraseFixupLoop_exit (.inl hred)], ?_⟩
            have L3 := L2.paint .black
            exact L3.2.fill L3.1
          | some r =>
            -- The third (if needed) and fourth cases, then the loop ends at the root.
            rw [eraseFixupLoop_case1_finish hb hne hP hS hw
              (by rw [hw', hav]; rw [hral, hrbl]; exact stage2R_some hs),
              hw', hav, delFix_right_red_some hr' hs]
            obtain ⟨hT, hk⟩ := finish_right L1 hs
            refine ⟨_, ?_, hT⟩
            rw [eraseFixupLoop_exit (.inr rfl), hk, Nat.add_assoc, Nat.add_comm 1]
            rfl
        | black =>
          have hw : red h (childAt h P Side.right.other) = false := hcw
          have hw' : childAt h P Side.right.other = wv := hwv
          obtain ⟨-, -, -, -, -, -, hwl, hwr⟩ := Lw.1.node_inv
          have hrwl : red h (childAt h wv .left) = red? wl := hwl.red_eq hhead
          have hrwr : red h (childAt h wv .right) = red? wr := hwr.red_eq hhead
          cases hs : stage2R pc pp P (.node .black wl wv wr) x with
          | none =>
            -- The second case: `w` made red, the loop climbs to `p`.
            obtain ⟨h1, h2⟩ := stage2R_none hs
            rw [eraseFixupLoop_case2 hb hne hP hS hw (by rw [hw']; exact hrwl.trans h1)
              (by rw [hw']; exact hrwr.trans h2), hw', delFix_right_black_none hr' hs]
            have hcl : DelFixClean pp (.node pc (.node .red wl wv wr) P x) := by
              simp only [DelFixClean, hr', Bool.false_eq_true, false_or] at hc
              exact hc.2 hs
            exact eraseFixupLoop_refines head root₀ fuel rot (case2_right Lp)
              (fun e => absurd e Lp.1.node_inv.ne_head) hcl (by omega)
          | some r =>
            obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
            rw [eraseFixupLoop_finish hb hne hP hS hw
              (by rw [hw']; rw [hrwl, hrwr]; exact stage2R_some hs),
              hw', delFix_right_black_some hr' hs]
            obtain ⟨hT, hk⟩ := finish_right Lp hs
            refine ⟨_, ?_, hT⟩
            rw [eraseFixupLoop_exit (.inr rfl), hk]
            rfl

/-- **The heap-level `erase_fixup`, HPHA's reading, performs `delFix`**: `eraseFixupLoop_refines`
from the entry, `erase_fixup(node)` with no rotation counted yet. -/
theorem eraseFixupHpha_refines {fuel : Nat} {h : Heap} {head cur P : Addr} {S : Side}
    {x : RBNode Addr} {path : Path Addr} (hl : Located h head cur P S x path)
    (hhole : cur = head → parent h cur = P ∧ parentSide h cur = S) (hc : DelFixClean path x)
    (hf : pathDepth path + 1 ≤ fuel) :
    ∃ H, eraseFixupHpha fuel h head cur = some (H, (delFix path x).2) ∧
      Tree H head (delFix path x).1 := by
  obtain ⟨H, hH, hT⟩ := eraseFixupLoop_refines head (childAt h head .left) fuel 0 hl hhole hc hf
  exact ⟨H, by rw [eraseFixupHpha, eraseFixupWith, hH, Nat.zero_add], hT⟩

/-- **The second fuel theorem**: fuel at least the depth of the tree `erase_fixup` starts from,
plus one, suffices (the hole may be empty, so its depth can equal the tree's). -/
theorem eraseFixupHpha_refines_depth {fuel : Nat} {h : Heap} {head cur P : Addr} {S : Side}
    {x : RBNode Addr} {path : Path Addr} (hl : Located h head cur P S x path)
    (hhole : cur = head → parent h cur = P ∧ parentSide h cur = S) (hc : DelFixClean path x)
    (hf : (path.fill x).depth + 1 ≤ fuel) :
    ∃ H, eraseFixupHpha fuel h head cur = some (H, (delFix path x).2) ∧
      Tree H head (delFix path x).1 := by
  refine eraseFixupHpha_refines hl hhole hc ?_
  have := pathDepth_add_depth_le path x
  omega

end Heap

end Oris.RB
