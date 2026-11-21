-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.Model

/-!
# The structural operations, address by address

Each operation's result, address by address, under the distinctness its callers guarantee: one
`if` chain per operation (`rotateAt_apply`, `attachTo_apply`, `substituteWith_apply`,
`switchWith_apply`), so that a proof reads a field of the new heap with one `simp` instead of
unfolding every write; and the list of the addresses each leaves unchanged (`_frame`). Plus the
colour writes' lemmas (`setColour_*`, `rotateAt_red`). These mention the model only, not the
abstraction relation.
-/

namespace Oris.RB

namespace Heap

/-- `setChild`'s write on a single record. -/
def NodeRec.withChild (n : NodeRec) : Side → Addr → NodeRec
  | .left, v => { n with left := v }
  | .right, v => { n with right := v }

@[simp] theorem NodeRec.withChild_parent (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).parent = n.parent := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_side (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).side = n.side := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_red (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).red = n.red := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_prev (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).prev = n.prev := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_next (n : NodeRec) (s : Side) (v : Addr) :
    (n.withChild s v).next = n.next := by cases s <;> rfl
@[simp] theorem NodeRec.withChild_left_left (n : NodeRec) (v : Addr) :
    (n.withChild .left v).left = v := rfl
@[simp] theorem NodeRec.withChild_left_right (n : NodeRec) (v : Addr) :
    (n.withChild .left v).right = n.right := rfl
@[simp] theorem NodeRec.withChild_right_left (n : NodeRec) (v : Addr) :
    (n.withChild .right v).left = n.left := rfl
@[simp] theorem NodeRec.withChild_right_right (n : NodeRec) (v : Addr) :
    (n.withChild .right v).right = v := rfl

/-- `setChild` is `NodeRec.withChild` at one address. -/
theorem setChild_eq (h : Heap) (a : Addr) (s : Side) (v : Addr) :
    setChild h a s v = h.modify a (·.withChild s v) := by
  cases s <;> rfl

/-- **`rotateAt` touches four addresses.** On any heap, `rotateAt h this s` changes no record but
those of `this`, its side-`o` child `top` (`o = s.other`), `top`'s side-`s` child, and `this`'s
parent. -/
theorem rotateAt_frame (h : Heap) (this : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ childAt h this s.other) (h₃ : x ≠ childAt h (childAt h this s.other) s)
    (h₄ : x ≠ parent h this) : rotateAt h this s x = h x := by
  simp only [rotateAt, setChild, setParentPtr, setParentSide, Heap.modify]
  simp [h₁, h₂, h₃, h₄]

/-- Of `top`'s side-`s` child (the subtree that moves across), `rotateAt` writes only the `parent`
word's pointer and side bit: away from `this`, `top` and `this`'s parent, every record keeps its
child links and colour. When that child is the sentinel, these are its scratch fields. -/
theorem rotateAt_links (h : Heap) (this : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ childAt h this s.other) (h₄ : x ≠ parent h this) :
    (rotateAt h this s x).left = (h x).left ∧ (rotateAt h this s x).right = (h x).right ∧
      (rotateAt h this s x).red = (h x).red := by
  simp only [rotateAt, setChild, setParentPtr, setParentSide, Heap.modify]
  by_cases h₃ : x = childAt h (childAt h this s.other) s
  · subst h₃; simp [h₁, h₂, h₄]
  · simp [h₁, h₂, h₃, h₄]

/-- Of `this`'s parent, if it is neither `this` nor `top` (which `Located` guarantees: the slot's
node is outside the subtree), `rotateAt` writes only the child link `this` hung from, which now
holds `top`: the other link and the colour are kept, and so is the `parent` word unless the
parent is also `top`'s side-`s` child (a rotation at the root whose moving subtree is empty: both
are the sentinel, and its scratch `parent` and side are written). -/
theorem rotateAt_parent_fields (h : Heap) (this : Addr) (s : Side)
    (h₁ : parent h this ≠ this) (h₂ : parent h this ≠ childAt h this s.other) :
    childAt (rotateAt h this s) (parent h this) (parentSide h this) = childAt h this s.other ∧
      childAt (rotateAt h this s) (parent h this) (parentSide h this).other =
        childAt h (parent h this) (parentSide h this).other ∧
      (rotateAt h this s (parent h this)).red = (h (parent h this)).red ∧
      (parent h this ≠ childAt h (childAt h this s.other) s →
        (rotateAt h this s (parent h this)).parent = (h (parent h this)).parent ∧
        (rotateAt h this s (parent h this)).side = (h (parent h this)).side) := by
  by_cases h₃ : parent h this = childAt h (childAt h this s.other) s
  · refine ⟨?_, ?_, ?_, fun h₄ => absurd h₃ h₄⟩ <;>
      simp only [parent, parentSide, childAt] at h₁ h₂ h₃ ⊢ <;>
      cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]
  · simp only [parent, parentSide, childAt] at h₁ h₂ h₃ ⊢
    cases s <;> cases hps : (h this).side <;>
      simp_all [rotateAt, parent, parentSide, childAt, Side.other, setChild, setParentPtr,
        setParentSide, Heap.modify]

/-- **`rotateAt`, address by address.** With `top` `this`'s side-`o` child (`o = s.other`), `m`
`top`'s side-`s` child and `P` `this`'s parent, where `this`, `top` and `P` are distinct and
`top ≠ m`, `rotateAt h this s` gives `this` the child `m` on side `o` and the slot `(top, s)`;
`top` the child `this` on side `s` and `this`'s old slot; `m` the slot `(this, o)`; `P` the child
`top` in the link that held `this` (on `m`'s record too when `m = P`); and every other address its
old record. `m` may coincide with `P` (a rotation at the root whose moving subtree is empty: both
are then the sentinel) or with `this` (whose record the later writes then decide: the first
branch). The writes' order matters only where two of them hit the same field. -/
theorem rotateAt_apply (h : Heap) (this : Addr) (s : Side)
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

/-- **`attachTo`, address by address**: `this` becomes a red leaf hanging at `(parent, s)`, both
children the slot's old occupant and both neighbours itself; `parent`'s side-`s` link takes
`this`; every other record is kept. -/
theorem attachTo_apply (h : Heap) (this parent : Addr) (s : Side) (h₁ : this ≠ parent)
    (x : Addr) :
    attachTo h this parent s x =
      if x = this then
        { left := childAt h parent s, right := childAt h parent s, prev := this, next := this,
          parent := parent, red := true, side := s }
      else if x = parent then (h x).withChild s this
      else h x := by
  by_cases e₁ : x = this
  · subst e₁
    cases s <;> simp [attachTo, setNeighbour, setChild, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, childAt, h₁, Ne.symm h₁]
  by_cases e₂ : x = parent
  · subst e₂
    cases s <;> simp [attachTo, setNeighbour, setChild, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, NodeRec.withChild, e₁]
  · simp [attachTo, setNeighbour, setChild_eq, setParentPtr, setParentSide, makeRed,
      setColour, Heap.modify, e₁, e₂]

/-- **`attachTo` touches two addresses**: `this` and `parent`. -/
theorem attachTo_frame (h : Heap) (this parent : Addr) (s : Side) {x : Addr} (h₁ : x ≠ this)
    (h₂ : x ≠ parent) : attachTo h this parent s x = h x := by
  simp only [attachTo, setNeighbour, setChild_eq, setParentPtr, setParentSide, makeRed,
    setColour, Heap.modify]
  simp [h₁, h₂]

/-- **`substituteWith`, address by address**: `child` takes `this`'s slot (`this`'s parent and
side, read before any write), and that parent's link takes `child`; every other record is kept,
`this`'s included. `child` and the parent may coincide: both are the sentinel when the root, with
no children, is erased. -/
theorem substituteWith_apply (h : Heap) (this child : Addr) (x : Addr) :
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
    · subst e₂; simp; cases ps <;> rfl
    · simp [e₂]
  by_cases e₂ : x = P
  · subst e₂; simp [e₁]
  · simp [e₁, e₂]

/-- **`substituteWith` touches two addresses**: `child` and `this`'s parent. -/
theorem substituteWith_frame (h : Heap) (this child : Addr) {x : Addr} (h₁ : x ≠ child)
    (h₂ : x ≠ parent h this) : substituteWith h this child x = h x := by
  simp [substituteWith_apply, h₁, h₂]

/-- **`switchWith`, address by address**: `this` takes `node`'s children, slot and colour; `node`'s
right child, then its left child, take the slot `(this, right)` and `(this, left)`; `node`'s parent
takes `this` in the link that held `node`; every other record is kept, `node`'s included (it is
detached). `node`'s children and parent may coincide, only at the sentinel: its `parent` word ends
as the right child's when both children are the sentinel, and its link is written when it is also
the parent. -/
theorem switchWith_apply (h : Heap) (this node : Addr) (h₁ : this ≠ node)
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

/-- **`switchWith` touches four addresses**: `this`, `node`'s two children and `node`'s parent. -/
theorem switchWith_frame (h : Heap) (this node : Addr) {x : Addr}
    (h₁ : x ≠ this) (h₂ : x ≠ childAt h node .left) (h₃ : x ≠ childAt h node .right)
    (h₄ : x ≠ parent h node) : switchWith h this node x = h x := by
  simp only [switchWith, setChild_eq, setParentPtr, setParentSide, setColour, Heap.modify,
    childAt, parent, parentSide, red] at h₂ h₃ h₄ ⊢
  by_cases h₀ : node = this
  · subst h₀; simp [h₁, h₂, h₃, h₄]
  · simp [h₁, h₂, h₃, h₄, h₀]

/-- **The sentinel's fields under a rotation**, for either side: if the sentinel is neither
`this` nor `top`, `rotateAt` keeps its right link and colour, and its left link unless it is
`this`'s parent, given that a rotation at the root hangs from the sentinel's left link. (It may be
`top`'s side-`s` child or `this`'s parent, or both: only its `parent` word and the link that held
`this` are then written.) -/
theorem rotateAt_sentinel (h : Heap) (this : Addr) (s : Side) {head : Addr}
    (h₁ : this ≠ childAt h this s.other)
    (h₃ : childAt h this s.other ≠ childAt h (childAt h this s.other) s)
    (h₄ : this ≠ parent h this) (h₅ : childAt h this s.other ≠ parent h this)
    (hh₁ : head ≠ this) (hh₂ : head ≠ childAt h this s.other)
    (hs : parent h this = head → parentSide h this = .left) :
    (rotateAt h this s head).right = (h head).right ∧
      (rotateAt h this s head).red = (h head).red ∧
      (parent h this ≠ head → (rotateAt h this s head).left = (h head).left) := by
  rw [rotateAt_apply h this s h₁ h₃ h₄ h₅ head, ite_eq_right hh₁, ite_eq_right hh₂]
  by_cases hP : head = parent h this
  · have hl := hs hP.symm
    by_cases hm : head = childAt h (childAt h this s.other) s
    · rw [ite_eq_left hm, ite_eq_left hP, hl]
      exact ⟨rfl, rfl, fun hne => absurd hP.symm hne⟩
    · rw [ite_eq_right hm, ite_eq_left hP, hl]
      exact ⟨rfl, rfl, fun hne => absurd hP.symm hne⟩
  · by_cases hm : head = childAt h (childAt h this s.other) s
    · rw [ite_eq_left hm, ite_eq_right hP]
      exact ⟨rfl, rfl, fun _ => rfl⟩
    · rw [ite_eq_right hm, ite_eq_right hP]
      exact ⟨rfl, rfl, fun _ => rfl⟩

/-- `setColour` changes no `parent` pointer. -/
theorem setColour_parent (h : Heap) (a : Addr) (b : Bool) (x : Addr) :
    (setColour h a b x).parent = (h x).parent := by
  by_cases e : x = a <;> simp [setColour, Heap.modify, e]

/-- `setColour` changes no other address's colour. -/
theorem setColour_red_ne (h : Heap) (a : Addr) (b : Bool) {x : Addr} (hx : x ≠ a) :
    (setColour h a b x).red = (h x).red := by
  simp [setColour, Heap.modify, hx]

/-- `setColour` sets the colour it writes. -/
theorem setColour_red_eq (h : Heap) (a : Addr) (b : Bool) : (setColour h a b a).red = b := by
  simp [setColour, Heap.modify]

/-- A write that keeps colours keeps every address's colour. -/
theorem Heap.modify_red (h : Heap) (a : Addr) (f : NodeRec → NodeRec)
    (hf : ∀ n, (f n).red = n.red) (x : Addr) : (h.modify a f x).red = (h x).red := by
  by_cases e : x = a <;> simp [Heap.modify, e, hf]

/-- **`rotateAt` changes no colour**: its nine writes are child links and `parent` words. -/
theorem rotateAt_red (h : Heap) (this : Addr) (s : Side) (x : Addr) :
    (rotateAt h this s x).red = (h x).red := by
  simp only [rotateAt, setChild_eq, setParentPtr, setParentSide]
  repeat rw [Heap.modify_red _ _ _ (fun _ => by simp)]

end Heap

end Oris.RB
