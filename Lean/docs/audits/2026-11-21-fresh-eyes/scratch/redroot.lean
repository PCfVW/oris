-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
open Oris.RB Oris.RB.Heap

def h0 : Heap := fun a =>
  if a = 1 then { left := 2, right := 1, parent := 1, red := false }
  else if a = 2 then { left := 3, right := 4, parent := 1, side := .left, red := true }
  else if a = 3 then { left := 1, right := 1, parent := 2, side := .left, red := false }
  else if a = 4 then { left := 1, right := 5, parent := 2, side := .right, red := false }
  else if a = 5 then { left := 1, right := 1, parent := 4, side := .right, red := true }
  else {}

#eval (eraseFixup 10 h0 1 3).map fun (h, r) => ((h 1).left, (h 4).red, (h 2).red, r)
#eval (eraseFixupHpha 10 h0 1 3).map fun (h, r) => ((h 1).left, (h 4).red, (h 2).red, r)
