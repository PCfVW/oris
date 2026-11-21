-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- A node whose side-`s` child is `near` and whose other child is `far`. -/
def nodeOn : Side → RBColor → RBNode Addr → Addr → RBNode Addr → RBNode Addr
  | .left, c, near, v, far => .node c near v far
  | .right, c, near, v, far => .node c far v near

/-- A path step down side `s` of `y`, `b` the sibling. -/
def stepOn : Side → RBColor → Path Addr → Addr → RBNode Addr → Path Addr
  | .left, c, pp, y, b => .left c pp y b
  | .right, c, pp, y, b => .right c b y pp

theorem rotateAt_refines (s : Side) {h : Heap} {head a b p : Addr} {σ : Side} {c c' : RBColor}
    {l rl rr : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p σ (nodeOn s c l a (nodeOn s c' rl b rr)) path) :
    Located (rotateAt h a s) head b p σ (nodeOn s c' (nodeOn s c l a rl) b rr) path := by
  cases s
  · exact rotateAt_refines_left hl
  · exact rotateAt_refines_right hl

theorem Located.up (s : Side) {h : Heap} {head a y : Addr} {c : RBColor} {t b : RBNode Addr}
    {pp : Path Addr} (hl : Located h head a y s t (stepOn s c pp y b)) :
    Located h head y (h y).parent (h y).side (nodeOn s c t y b) pp := by
  cases s
  · exact hl.up_left
  · exact hl.up_right

theorem Located.down (s : Side) {h : Heap} {head y P : Addr} {S : Side} {c : RBColor}
    {near far : RBNode Addr} {pp : Path Addr}
    (hl : Located h head y P S (nodeOn s c near y far) pp) :
    Located h head (childAt h y s) y s near (stepOn s c pp y far) := by
  cases s
  · exact hl.down_left
  · exact hl.down_right
end Oris.RB.Heap
