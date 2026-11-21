-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- Proposed: the sentinel-or-member split, once. -/
theorem Rep.ne_root {h : Heap} {head k q x : Addr} {σ : Side} {u : RBNode Addr}
    (hr : Rep h head k q σ u) (hxh : x ≠ head) (hxu : x ∉ u.toList) : x ≠ k := fun e => by
  by_cases hk : k = head
  · exact hxh (e.trans hk)
  · exact hxu (e ▸ hr.root_mem hk)

/-- Proposed variant: members of a disjoint tree. -/
theorem Rep.ne_root_of_mem {h : Heap} {head k q : Addr} {σ : Side} {u v : RBNode Addr}
    {p' : Addr} {σ' : Side} {a : Addr}
    (hr : Rep h head k q σ u) (hv : Rep h head a p' σ' v) {x : Addr} (hx : x ∈ v.toList)
    (hdis : x ∉ u.toList) : x ≠ k := hr.ne_root (hv.mem_ne hx).1 hdis

-- `rfl` on insFix replaced by its equation lemma
example {gp : Path Addr} {c' : RBColor} {z y : Addr} {ul ur b t : RBNode Addr} {uv : Addr} :
    insFix (.left .red (.left c' gp z (.node .red ul uv ur)) y b) t =
      insFix gp (.node .red (.node .black t y b) z (.node .black ul uv ur)) := by
  rw [insFix]; rfl

example {gp : Path Addr} {c' : RBColor} {z y : Addr} {ul ur b t : RBNode Addr} {uv : Addr} :
    insFix (.left .red (.left c' gp z (.node .red ul uv ur)) y b) t =
      insFix gp (.node .red (.node .black t y b) z (.node .black ul uv ur)) := by
  simp only [insFix, red?, ite_true, RBNode.setBlack]

/-- Proposed step lemma: red uncle. -/
theorem insertFixupLoop_red_uncle {head : Addr} {fuel : Nat} {h : Heap} {cur p pp : Addr}
    {s : Side} {rot : Nat} (hp : red h p = true) (hpp : parent h p = pp)
    (hs : parentSide h p = s) (hu : red h (childAt h pp s.other) = true) :
    insertFixupLoop head (fuel + 1) h cur p rot =
      insertFixupLoop head fuel
        (makeRed (makeBlack (makeBlack h p) (childAt h pp s.other)) pp) pp (parent h pp) rot := by
  rw [insertFixupLoop]
  subst hpp hs
  simp only [hp, hu, ite_true]
  simp only [makeRed, makeBlack, parent, setColour_parent]

/-- Proposed step lemma: black uncle, `cur` outer. -/
theorem insertFixupLoop_black_uncle_outer {head : Addr} {fuel : Nat} {h : Heap} {cur p pp : Addr}
    {s : Side} {rot : Nat} (hp : red h p = true) (hpp : parent h p = pp)
    (hs : parentSide h p = s) (hu : red h (childAt h pp s.other) = false)
    (hc : cur ≠ childAt h p s.other) :
    insertFixupLoop head (fuel + 1) h cur p rot =
      insertFixupLoop head fuel (rotateAt (makeRed (makeBlack h p) pp) pp s.other) cur p
        (rot + 1) := by
  rw [insertFixupLoop]
  simp only [hp, hpp, hs, hu, hc, ite_true, ite_false, Bool.false_eq_true]

/-- Proposed step lemma: black uncle, `cur` inner. -/
theorem insertFixupLoop_black_uncle_inner {head : Addr} {fuel : Nat} {h : Heap} {cur p pp : Addr}
    {s : Side} {rot : Nat} (hp : red h p = true) (hpp : parent h p = pp)
    (hs : parentSide h p = s) (hu : red h (childAt h pp s.other) = false)
    (hc : cur = childAt h p s.other) :
    insertFixupLoop head (fuel + 1) h cur p rot =
      insertFixupLoop head fuel
        (rotateAt (makeRed (makeBlack (rotateAt h p s) (parent (rotateAt h p s) p)) pp) pp s.other)
        p (parent (rotateAt h p s) p) (rot + 2) := by
  rw [insertFixupLoop]
  simp only [hp, hpp, hs, hu, hc, ite_true, ite_false, Bool.false_eq_true]

theorem insertFixupLoop_refines2 (head : Addr) : ∀ (fuel : Nat) {h : Heap} {cur P : Addr}
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
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines2 head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.left .red (.left c' gp z (.node .red ul uv ur)) y b) t =
            insFix gp (.node .red (.node .black t y b) z (.node .black ul uv ur)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH, insertFixupLoop_red_uncle hyr hyz hys
          (by simpa only [red, childAt, Side.other, huv] using hcol)]
        simp only [makeRed, makeBlack, childAt, Side.other, huv, colourBit, parent, setColour_parent]
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
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines2 head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.right .red a y (.right c' (.node .red ul uv ur) z gp)) t =
            insFix gp (.node .red (.node .black ul uv ur) z (.node .black a y t)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH, insertFixupLoop_red_uncle hyr hyz hys
          (by simpa only [red, childAt, Side.other, huv] using hcol)]
        simp only [makeRed, makeBlack, childAt, Side.other, huv, colourBit, parent, setColour_parent]
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
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines2 head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.right .red a y (.left c' gp z (.node .red ul uv ur))) t =
            insFix gp (.node .red (.node .black a y t) z (.node .black ul uv ur)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH, insertFixupLoop_red_uncle hyr hyz hys
          (by simpa only [red, childAt, Side.other, huv] using hcol)]
        simp only [makeRed, makeBlack, childAt, Side.other, huv, colourBit, parent, setColour_parent]
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
        obtain ⟨H, hH, hT⟩ := insertFixupLoop_refines2 head fuel rot Lz3 hzh hroot' (by omega)
        have hz : insFix (.left .red (.right c' (.node .red ul uv ur) z gp) y b) t =
            insFix gp (.node .red (.node .black ul uv ur) z (.node .black t y b)) := by
          rfl
        rw [hz]
        refine ⟨H, ?_, hT⟩
        rw [← hH, insertFixupLoop_red_uncle hyr hyz hys
          (by simpa only [red, childAt, Side.other, huv] using hcol)]
        simp only [makeRed, makeBlack, childAt, Side.other, huv, colourBit, parent, setColour_parent]
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
