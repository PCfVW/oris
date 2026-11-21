-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
namespace Oris.RB.Heap
open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)
theorem rotateAt_apply2 (h : Heap) (this : Addr) (s : Side)
    (h₁ : this ≠ childAt h this s.other) (h₂ : this ≠ childAt h (childAt h this s.other) s)
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
  · subst e₁; simp [h₁, h₂, h₄]
  by_cases e₂ : x = top
  · subst e₂; simp [e₁, h₃, h₅]
    cases s <;> simp [NodeRec.withChild]
  by_cases e₃ : x = m
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; simp [e₁, e₂]
      cases s <;> cases ps <;> simp [NodeRec.withChild]
    · simp [e₁, e₂, e₄]
  by_cases e₄ : x = P
  · subst e₄; simp [e₁, e₂, e₃]
  · simp [e₁, e₂, e₃, e₄]

theorem substituteWith_apply2 (h : Heap) (this child : Addr) (x : Addr) :
    substituteWith h this child x =
      if x = child then
        { (if x = parent h this then (h x).withChild (parentSide h this) child else h x) with
          parent := parent h this, side := parentSide h this }
      else if x = parent h this then (h x).withChild (parentSide h this) child
      else h x := by
  generalize hP : parent h this = P
  generalize hps : parentSide h this = ps
  simp only [substituteWith, setChild_eq, setParentPtr, setParentSide, Heap.modify, hP, hps]
  by_cases e₁ : x = child
  · subst e₁
    by_cases e₂ : x = P
    · subst e₂; cases ps <;> simp [NodeRec.withChild]
    · simp [e₂]
  by_cases e₂ : x = P
  · subst e₂; simp [e₁]
  · simp [e₁, e₂]

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
  · subst e₁; simp [*]
  by_cases e₂ : x = R
  · subst e₂
    by_cases e₃ : x = P <;> by_cases e₅ : x = L
    · subst e₃; subst e₅; cases ps <;> simp [*, NodeRec.withChild]
    · subst e₃; cases ps <;> simp [*, NodeRec.withChild]
    · subst e₅; simp [*]
    · simp [*]
  by_cases e₃ : x = L
  · subst e₃
    by_cases e₄ : x = P
    · subst e₄; cases ps <;> simp [*, NodeRec.withChild]
    · simp [*]
  by_cases e₄ : x = P
  · subst e₄; simp [*]
  · simp [*]
