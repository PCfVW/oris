-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB
namespace Heap
open RBTree (RBNode RBColor)

theorem switchWith_frame' (h : Heap) (this node : Addr) {x : Addr}
    (h₁ : x ≠ this) (h₂ : x ≠ childAt h node .left) (h₃ : x ≠ childAt h node .right)
    (h₄ : x ≠ parent h node) : switchWith h this node x = h x := by
  simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
    childAt, parent, parentSide, red] at h₂ h₃ h₄ ⊢
  by_cases h₀ : node = this
  · subst h₀; simp [h₁, h₂, h₃, h₄]
  · simp [h₁, h₂, h₃, h₄, h₀]

theorem rotateAt_apply' (h : Heap) (this : Addr) (s : Side)
    (h₁ : this ≠ childAt h this s.other)
    (h₃ : childAt h this s.other ≠ childAt h (childAt h this s.other) s)
    (h₄ : this ≠ parent h this) (h₅ : childAt h this s.other ≠ parent h this) (x : Addr) :
    rotateAt h this s x =
      if x = this then
        { (h this).withChild s.other (childAt h (childAt h this s.other) s) with
          parent := childAt h this s.other, side := s }
      else if x = childAt h this s.other then
        { (h x).withChild s this with parent := parent h this, side := parentSide h this }
      else if x = childAt h (childAt h this s.other) s then
        { (if x = parent h this then (h x).withChild (parentSide h this) (childAt h this s.other)
            else h x) with parent := this, side := s.other }
      else if x = parent h this then (h x).withChild (parentSide h this) (childAt h this s.other)
      else h x := by
  generalize ht : childAt h this s.other = top at *
  generalize hm : childAt h top s = m at *
  generalize hP : parent h this = P at *
  generalize hps : parentSide h this = ps
  simp only [rotateAt, setChild_eq, setParentPtr, setParentSide, Heap.modify, ht, hm, hP, hps]
  by_cases e₁ : x = this
  · subst e₁
    by_cases e : x = m
    · subst e; simp [h₁, h₄]
    · simp [h₁, h₄, e]
  by_cases e₂ : x = top
  · subst e₂; simp [e₁, h₃, h₅]
    cases s <;> rfl
  by_cases e₃ : x = m
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; simp [e₁, e₂]
      cases s <;> cases ps <;> rfl
    · simp [e₁, e₂, e₄]
  by_cases e₄ : x = P
  · subst e₄; simp [e₁, e₂, e₃]
  · simp [e₁, e₂, e₃, e₄]

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

-- F4: is h₂ needed? counterexample search: show statement false without h₂ is hard; just check h₁ needed
end Heap
end Oris.RB
