-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
open RBTree (RBNode RBColor)
theorem Rep.reroot2 {h h' : Heap} {head a p : Addr} {s : Side} {t : RBNode Addr}
    {p' : Addr} {s' : Side} (hr : Rep h head a p s t)
    (hroot : a ≠ head → (h' a).left = (h a).left ∧ (h' a).right = (h a).right ∧
      (h' a).red = (h a).red ∧ (h' a).parent = p' ∧ (h' a).side = s')
    (hrest : ∀ x ∈ t.toList, x ≠ a → h' x = h x) : Rep h' head a p' s' t := by
  have hnd := hr.nodup
  cases hr with
  | nil => exact .nil
  | node ha hn _ _ hc hl hr =>
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := hroot ha
    obtain ⟨-, -, hal, har, -⟩ := nodup_node hnd
    refine .node ha hn e₄ e₅ (e₃.trans hc) ?_ ?_
    · rw [e₁]
      exact hl.frame fun x hx => hrest x (by simp [hx]) (by rintro rfl; exact hal hx)
    · rw [e₂]
      exact hr.frame fun x hx => hrest x (by simp [hx]) (by rintro rfl; exact har hx)
