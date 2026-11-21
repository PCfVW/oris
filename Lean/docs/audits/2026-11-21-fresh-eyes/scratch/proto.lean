-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- Writing the colour bit a record already holds changes nothing. -/
theorem setColour_of_eq {h : Heap} {a : Addr} {b : Bool} (e : (h a).red = b) :
    setColour h a b = h := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [setColour, Heap.modify, ← e]
  · simp [setColour, Heap.modify, hx]

/-- `make_black(cur)` on a located subtree's first address, the sentinel included. -/
theorem Located.makeBlack_fill {h : Heap} {head a p : Addr} {s : Side} {t : RBNode Addr}
    {path : Path Addr} (hl : Located h head a p s t path) :
    Tree (makeBlack h a) head (path.fill t.setBlack) := by
  cases t with
  | nil =>
    obtain rfl := hl.1.nil_inv
    rw [makeBlack, setColour_of_eq hl.2.head_red]
    exact hl.2.fill hl.1
  | node c l v r =>
    obtain rfl := hl.1.node_inv.1
    have := hl.paint .black
    exact this.2.fill this.1

/-- The root address is the slot's occupant at `.root`, otherwise a path address. -/
theorem RepPath.root_mem {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a p s path) :
    path = .root ∧ childAt h head .left = a ∨ childAt h head .left ∈ path.listL ++ path.listR := by
  induction hp with
  | root e => exact .inl ⟨rfl, e⟩
  | left _ _ _ _ _ _ ih =>
    rcases ih with ⟨rfl, e⟩ | hm
    · exact .inr (by simp [e])
    · simp only [List.mem_append] at hm; exact .inr (by rcases hm with hm | hm <;> simp [Path.listL, Path.listR, hm])
  | right _ _ _ _ _ _ ih =>
    rcases ih with ⟨rfl, e⟩ | hm
    · exact .inr (by simp [e])
    · simp only [List.mem_append] at hm; exact .inr (by rcases hm with hm | hm <;> simp [Path.listL, Path.listR, hm])
end Oris.RB.Heap
