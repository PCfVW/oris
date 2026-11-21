-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)
example (pp : Path Nat) (y : Nat) (x : RBNode Nat) :
    delFix (.left .black pp y .nil) (.node .red x 1 .nil) =
      ((Path.left .black pp y .nil).fill (RBNode.node .red x 1 .nil).setBlack, 0) := by rfl
example (pp : Path Nat) (y : Nat) (x : RBNode Nat) :
    delFix (.left .black pp y .nil) (.node .red x 1 .nil) =
      ((Path.left .black pp y .nil).fill (RBNode.node .red x 1 .nil).setBlack, 0) := by
  rw [delFix]; rfl
