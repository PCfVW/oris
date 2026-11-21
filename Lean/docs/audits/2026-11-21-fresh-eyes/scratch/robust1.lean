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
