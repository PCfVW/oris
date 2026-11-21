-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
theorem switchWith_apply2 (h : Heap) (this node : Addr) (h₁ : this ≠ node)
    (h₂ : node ≠ childAt h node .left) (h₃ : node ≠ childAt h node .right)
    (h₄ : node ≠ parent h node) (h₅ : this ≠ childAt h node .left)
    (h₆ : this ≠ childAt h node .right) (h₇ : this ≠ parent h node) (x : Addr) :
    switchWith h this node x =
      if x = this then
        { (h this) with
          left := childAt h node .left
          right := childAt h node .right
          parent := parent h node
          side := parentSide h node
          red := red h node }
      else if x = childAt h node .right then
        { (if x = parent h node then (h x).withChild (parentSide h node) this else h x) with
          parent := this, side := .right }
      else if x = childAt h node .left then
        { (if x = parent h node then (h x).withChild (parentSide h node) this else h x) with
          parent := this, side := .left }
      else if x = parent h node then (h x).withChild (parentSide h node) this
      else h x := by
  generalize hL : childAt h node .left = L at *
  generalize hR : childAt h node .right = R at *
  generalize hP : parent h node = P at *
  generalize hps : parentSide h node = ps
  generalize hc : red h node = c
  simp only [childAt, parent, parentSide, red] at hL hR hP hps hc
  have hn1 : node ≠ this := Ne.symm h₁
  simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
    childAt, parent, parentSide, red, hL, hR, hps, hn1, h₂, h₃]
  have hn5 := Ne.symm h₅
  have hn6 := Ne.symm h₆
  have hn7 := Ne.symm h₇
  by_cases e₁ : x = this
  · subst e₁; simp [hP, hc, h₂, h₃, hn5, hn6, hn7]
  by_cases e₂ : x = R
  · subst e₂
    by_cases e₃ : x = P <;> by_cases e₅ : x = L
    · subst e₃; subst e₅; simp [hP, hn1]; cases ps <;> rfl
    · subst e₃; simp [hP, hn1, e₅]; cases ps <;> rfl
    · subst e₅; simp [hP, hn1, e₃]
    · simp [hP, hn1, e₃, e₅]
  by_cases e₃ : x = L
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; simp [hP, hn1, e₂]; cases ps <;> rfl
    · simp [hP, hn1, e₂, e₄]
  by_cases e₄ : x = P
  · subst e₄; simp [hP, hn1, e₁, e₂, e₃]
  · simp [hP, hn1, e₁, e₂, e₃, e₄]
