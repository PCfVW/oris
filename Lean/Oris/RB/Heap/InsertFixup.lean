-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.Structural

/-!
# Step 3b: `insert_fixup` performs `insFix`

The loop invariant is a located subtree (`Located h head cur p s t path`, `cur` a real node), with
`p`, the slot's node, as the loop's `p`: its colour, and the sentinel's, are read through `Rep` and
`RepPath`. One more hypothesis: the tree's root is black (`rootColour`). On a path whose top node
is red and is `cur`'s parent, the Rust's loop would find a red parent with no grandparent and run
its black-uncle branch at the sentinel, where `insFix` stops (Fixup.lean's "unreachable red-root
shape"); the Rust's callers never reach it, the tree's root being black. -/

namespace Oris.RB

namespace Heap

open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- The loop's exit: a black `p` ends it with the final `make_black` of the root. -/
private theorem insertFixupLoop_exit {head : Addr} {fuel : Nat} {h : Heap} {cur p : Addr}
    {rot : Nat} (hp : red h p = false) :
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
