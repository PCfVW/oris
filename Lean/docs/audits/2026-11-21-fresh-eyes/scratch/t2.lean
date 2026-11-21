-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
open Oris.RB Oris.RB.Heap

theorem switchWith_apply' (h : Heap) (this node : Addr)
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
  by_cases h₁ : this = node
  · subst h₁
    generalize hL : childAt h this .left = L at *
    generalize hR : childAt h this .right = R at *
    generalize hP : parent h this = P at *
    generalize hps : parentSide h this = ps
    generalize hc : red h this = c
    simp only [childAt, parent, parentSide, red] at hL hR hP hps hc
    simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
      childAt, parent, parentSide, red, hL, hR, hps, h₂, h₃]
    have hn5 := Ne.symm h₅
    have hn6 := Ne.symm h₆
    have hn7 := Ne.symm h₇
    by_cases e₁ : x = this
    · subst e₁; simp [*]
    by_cases e₂ : x = R
    · subst e₂
      by_cases e₃ : x = P <;> by_cases e₅ : x = L
      · subst e₃; subst e₅; simp [*]; cases ps <;> rfl
      · subst e₃; simp [*]; cases ps <;> rfl
      · subst e₅; simp [*]
      · simp [*]
    by_cases e₃ : x = L
    · subst e₃
      by_cases e₄ : x = P
      · subst e₄; simp [*]; cases ps <;> rfl
      · simp [*]
    by_cases e₄ : x = P
    · subst e₄; simp [*]
    · simp [*]
  · exact switchWith_apply h this node h₁ h₂ h₃ h₄ h₅ h₆ h₇ x

-- rotateAt_parent_fields without h₂
theorem rpf (h : Heap) (this : Addr) (s : Side)
    (h₁ : parent h this ≠ this) :
    childAt (rotateAt h this s) (parent h this) (parentSide h this) = childAt h this s.other := by
  by_cases h₃ : parent h this = childAt h (childAt h this s.other) s
  · simp only [parent, parentSide, childAt] at h₁ h₃ ⊢ <;>
      cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]
  · simp only [parent, parentSide, childAt] at h₁ h₃ ⊢
    cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]
