-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)
namespace Oris.RB.Scratch
variable {α : Type _}
def pathDepth : Path α → Nat
  | .root => 0
  | .left _ pp _ _ => pathDepth pp + 1
  | .right _ _ _ pp => pathDepth pp + 1
theorem pathDepth_add_depth_le (path : Path α) (t : RBNode α) :
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
theorem nodup_node {c : RBColor} {l r : RBNode α} {v : α}
    (hnd : (RBNode.node c l v r).toList.Nodup) :
    l.toList.Nodup ∧ r.toList.Nodup ∧ v ∉ l.toList ∧ v ∉ r.toList ∧
      ∀ x ∈ l.toList, x ∉ r.toList := by
  simp only [RBNode.toList_node, List.nodup_append, List.nodup_cons, List.mem_cons] at hnd
  obtain ⟨hl, ⟨hvr, hr⟩, hlr⟩ := hnd
  exact ⟨hl, hr, fun hv => hlr v hv v (.inl rfl) rfl, hvr,
    fun x hx hxr => hlr x hx x (.inr hxr) rfl⟩
end Oris.RB.Scratch
