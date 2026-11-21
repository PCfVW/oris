-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
open Oris.RB Oris.RB.Heap

def h0 : Heap := fun a =>
  if a = 1 then { left := 2, right := 1, parent := 1, red := false }
  else if a = 2 then { left := 3, right := 1, parent := 1, side := .left, red := false }
  else if a = 3 then { left := 1, right := 1, parent := 2, side := .left, red := false }
  else {}

#eval (eraseFixup 10 h0 1 3).map fun (h, r) => ((h 1).red, (h 2).red, (h 3).red, r)
#eval (eraseFixupHpha 10 h0 1 3).map fun (h, r) => ((h 1).red, (h 2).red, (h 3).red, r)
-- the zipper: path .left black .root 2 nil, x = node black nil 3 nil
#eval (delFix (.left .black .root (2:Nat) .nil) (.node .black .nil 3 .nil)).1
