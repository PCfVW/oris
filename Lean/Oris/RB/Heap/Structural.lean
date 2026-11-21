-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.Rep
import Oris.RB.Heap.Apply

/-!
# The structural operations perform their zipper steps

`rotateAt` performs the zipper's rotation (`rotateAt_refines_left`, `_right`: step 2 of the heap
layer, the note's §4, theorem 1), and `attach_to`, `substitute_with` and `switch_with` perform the
zipper steps of insert and erase (step 3a, theorem 2). Also the two write lemmas the fix-ups build
on: a colour write on a located node (`Located.paint`) and the final `make_black` of the root
(`Tree.makeBlack_root`).
-/

namespace Oris.RB

namespace Heap

open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- **`NodeBase::rotate(this, Left)` performs the zipper rotation** (step 2; the note's §4, theorem
1). If the heap represents the located subtree `node c l a (node c' rl b rr)`, then after
`rotateAt h a .left` it represents `Oris.RB.rotate .left` of it, `node c' (node c l a rl) b rr`, at
the same slot and path, with `b` now in the slot. Nothing is assumed beyond `Located` (the subtree
and its path, which the proof needs: it is what puts the slot's node outside the subtree); in
particular, the writes to the sentinel's scratch fields when `rl` is empty need no hypothesis. Which
records change is `rotateAt_refines_left_frame` (and, field by field, `rotateAt_links` and
`rotateAt_parent_fields`). -/
theorem rotateAt_refines_left {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {l rl rr : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c l a (.node c' rl b rr)) path) :
    Located (rotateAt h a .left) head b p s
      (rotate .left (.node c l a (.node c' rl b rr))) path := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, ha, hna, hpa, hsa, hca, hal, har⟩ := hr.node_inv
  obtain ⟨hab, hb, hnb, -, -, hcb, hbl, hbr⟩ := har.node_inv
  generalize hm : (h b).left = m at hbl
  obtain ⟨-, -, hal', hai, hli⟩ := nodup_node hr.nodup
  obtain ⟨-, -, hbrl, hbrr, hrlrr⟩ := nodup_node har.nodup
  -- Distinctness: `m` (the sentinel or the root of `rl`) through `Rep.ne_root`; `p` is outside.
  have hab' : a ≠ b := fun e => hai (by simp [e])
  have ham : a ≠ m := hbl.ne_root ha fun hx => hai (by simp [hx])
  have hbm : b ≠ m := hbl.ne_root hb hbrl
  have hap : a ≠ p := fun e => hpt (by simp [e])
  have hbp : b ≠ p := fun e => hpt (by simp [e])
  have hmp : m ≠ head → m ≠ p := fun hmh e => hpt (by simp [← e, hbl.root_mem hmh])
  have hpm : p ≠ head → p ≠ m := fun hph => hbl.ne_root hph fun hx => hpt (by simp [hx])
  have ap₁ : a ≠ childAt h a Side.left.other := by simpa [childAt, Side.other, hab] using hab'
  have ap₃ : childAt h a Side.left.other ≠ childAt h (childAt h a Side.left.other) .left := by
    simpa [childAt, Side.other, hab, hm] using hbm
  have ap₄ : a ≠ parent h a := by simpa [parent, hpa] using hap
  have ap₅ : childAt h a Side.left.other ≠ parent h a := by
    simpa [childAt, Side.other, hab, parent, hpa] using hbp
  have RL := rotateAt_apply h a .left ap₁ ap₃ ap₄ ap₅
  simp only [childAt, Side.other, parent, parentSide, hab, hm, hpa, hsa] at RL
  have rfr : ∀ x, x ≠ a → x ≠ b → x ≠ m → x ≠ p → rotateAt h a .left x = h x :=
    fun x h₁ h₂ h₃ h₄ => by simp [RL, h₁, h₂, h₃, h₄]
  obtain ⟨RAl, RAr, RAp, RAs, RAc⟩ : (rotateAt h a .left a).left = (h a).left ∧
      (rotateAt h a .left a).right = m ∧ (rotateAt h a .left a).parent = b ∧
      (rotateAt h a .left a).side = .left ∧ (rotateAt h a .left a).red = (h a).red := by
    simp [RL, NodeRec.withChild]
  obtain ⟨RBl, RBr, RBp, RBs, RBc⟩ : (rotateAt h a .left b).left = a ∧
      (rotateAt h a .left b).right = (h b).right ∧ (rotateAt h a .left b).parent = p ∧
      (rotateAt h a .left b).side = s ∧ (rotateAt h a .left b).red = (h b).red := by
    simp [RL, hab'.symm]
  have RM : m ≠ head → (rotateAt h a .left m).left = (h m).left ∧
      (rotateAt h a .left m).right = (h m).right ∧ (rotateAt h a .left m).red = (h m).red ∧
      (rotateAt h a .left m).parent = a ∧ (rotateAt h a .left m).side = .right := fun hmh => by
    simp [RL, ham.symm, hbm.symm, hmp hmh]
  show Located _ head b p s (.node c' (.node c l a rl) b rr) path
  refine ⟨.node hb hnb RBp RBs (RBc.trans hcb) ?_ ?_, ?_⟩
  · rw [RBl]
    refine .node ha hna RAp RAs (RAc.trans hca) ?_ ?_
    · rw [RAl]
      exact hal.frame fun x hx => rfr x (fun e => hal' (e ▸ hx))
        (fun e => hli x hx (by simp [e]))
        (hbl.ne_root (hal.mem_ne hx).1 fun h' => hli x hx (by simp [h']))
        (fun e => hpt (by simp [← e, hx]))
    · rw [RAr]
      exact hbl.reroot RM fun x hx hxm => rfr x (fun e => hai (by simp [← e, hx]))
        (fun e => hbrl (e ▸ hx)) hxm (fun e => hpt (by simp [← e, hx]))
  · rw [RBr]
    exact hbr.frame fun x hx => rfr x (fun e => hai (by simp [← e, hx]))
      (fun e => hbrr (e ▸ hx)) (hbl.ne_root (hbr.mem_ne hx).1 fun h' => hrlrr x h' hx)
      (fun e => hpt (by simp [← e, hx]))
  · have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
    have HH := rotateAt_sentinel h a .left ap₁ ap₃ ap₄ ap₅ (Ne.symm ha)
      (by simpa [childAt, Side.other, hab] using Ne.symm hb)
      (fun e => by simp only [parent, parentSide, hpa, hsa] at e ⊢; exact hs e)
    simp only [parent, hpa] at HH
    refine hp.retarget hr (fun x hx hxp => rfr x
        (fun e => (hout x hx).1 (by simp [e])) (fun e => (hout x hx).1 (by simp [e]))
        (hbl.ne_root (hout x hx).2 fun h' => (hout x hx).1 (by simp [h'])) hxp)
      HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hpm' : p = m
      · subst hpm'; cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, NodeRec.withChild]
      · cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]
    · intro hph
      have hpm' := hpm hph
      cases s <;> simp [RL, childAt, Side.other, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]

/-- `rotateAt_frame` for `rotateAt_refines_left`, in the zipper's terms: the only records the
rotation changes are those of `a`, `b`, `b`'s left child (the first node of `rl`, or the sentinel
when `rl` is empty) and the slot's node `p`. -/
theorem rotateAt_refines_left_frame {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {l rl rr : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c l a (.node c' rl b rr)) path) {x : Addr}
    (h₁ : x ≠ a) (h₂ : x ≠ b) (h₃ : x ≠ (h b).left) (h₄ : x ≠ p) :
    rotateAt h a .left x = h x := by
  obtain ⟨-, -, -, hpa, -, -, -, har⟩ := hl.1.node_inv
  obtain ⟨hab, -⟩ := har.node_inv
  exact rotateAt_frame h a .left h₁ (by simpa [childAt, Side.other, hab] using h₂)
    (by simpa [childAt, Side.other, hab] using h₃) (by simpa [parent, hpa] using h₄)

/-- **`NodeBase::rotate(this, Right)` performs the zipper rotation**, the mirror image of
`rotateAt_refines_left`: `node c (node c' ll b lr) a r` becomes `node c' ll b (node c lr a r)`.
Which records change is `rotateAt_refines_right_frame`. -/
theorem rotateAt_refines_right {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {ll lr r : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c (.node c' ll b lr) a r) path) :
    Located (rotateAt h a .right) head b p s
      (rotate .right (.node c (.node c' ll b lr) a r)) path := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, ha, hna, hpa, hsa, hca, hal, har⟩ := hr.node_inv
  obtain ⟨hab, hb, hnb, -, -, hcb, hbl, hbr⟩ := hal.node_inv
  generalize hm : (h b).right = m at hbr
  obtain ⟨-, -, hai, har', hli⟩ := nodup_node hr.nodup
  obtain ⟨-, -, hbll, hblr, hlllr⟩ := nodup_node hal.nodup
  -- Distinctness: `m` (the sentinel or the root of `lr`) through `Rep.ne_root`; `p` is outside.
  have hab' : a ≠ b := fun e => hai (by simp [e])
  have ham : a ≠ m := hbr.ne_root ha fun hx => hai (by simp [hx])
  have hbm : b ≠ m := hbr.ne_root hb hblr
  have hap : a ≠ p := fun e => hpt (by simp [e])
  have hbp : b ≠ p := fun e => hpt (by simp [e])
  have hmp : m ≠ head → m ≠ p := fun hmh e => hpt (by simp [← e, hbr.root_mem hmh])
  have hpm : p ≠ head → p ≠ m := fun hph => hbr.ne_root hph fun hx => hpt (by simp [hx])
  have ap₁ : a ≠ childAt h a Side.right.other := by simpa [childAt, Side.other, hab] using hab'
  have ap₃ : childAt h a Side.right.other ≠ childAt h (childAt h a Side.right.other) .right := by
    simpa [childAt, Side.other, hab, hm] using hbm
  have ap₄ : a ≠ parent h a := by simpa [parent, hpa] using hap
  have ap₅ : childAt h a Side.right.other ≠ parent h a := by
    simpa [childAt, Side.other, hab, parent, hpa] using hbp
  have RL := rotateAt_apply h a .right ap₁ ap₃ ap₄ ap₅
  simp only [childAt, Side.other, parent, parentSide, hab, hm, hpa, hsa] at RL
  have rfr : ∀ x, x ≠ a → x ≠ b → x ≠ m → x ≠ p → rotateAt h a .right x = h x :=
    fun x h₁ h₂ h₃ h₄ => by simp [RL, h₁, h₂, h₃, h₄]
  obtain ⟨RAr, RAl, RAp, RAs, RAc⟩ : (rotateAt h a .right a).right = (h a).right ∧
      (rotateAt h a .right a).left = m ∧ (rotateAt h a .right a).parent = b ∧
      (rotateAt h a .right a).side = .right ∧ (rotateAt h a .right a).red = (h a).red := by
    simp [RL, NodeRec.withChild]
  obtain ⟨RBr, RBl, RBp, RBs, RBc⟩ : (rotateAt h a .right b).right = a ∧
      (rotateAt h a .right b).left = (h b).left ∧ (rotateAt h a .right b).parent = p ∧
      (rotateAt h a .right b).side = s ∧ (rotateAt h a .right b).red = (h b).red := by
    simp [RL, hab'.symm]
  have RM : m ≠ head → (rotateAt h a .right m).left = (h m).left ∧
      (rotateAt h a .right m).right = (h m).right ∧ (rotateAt h a .right m).red = (h m).red ∧
      (rotateAt h a .right m).parent = a ∧ (rotateAt h a .right m).side = .left := fun hmh => by
    simp [RL, ham.symm, hbm.symm, hmp hmh]
  show Located _ head b p s (.node c' ll b (.node c lr a r)) path
  refine ⟨.node hb hnb RBp RBs (RBc.trans hcb) ?_ ?_, ?_⟩
  · rw [RBl]
    exact hbl.frame fun x hx => rfr x (fun e => hai (by simp [← e, hx]))
      (fun e => hbll (e ▸ hx)) (hbr.ne_root (hbl.mem_ne hx).1 fun h' => hlllr x hx h')
      (fun e => hpt (by simp [← e, hx]))
  · rw [RBr]
    refine .node ha hna RAp RAs (RAc.trans hca) ?_ ?_
    · rw [RAl]
      exact hbr.reroot RM fun x hx hxm => rfr x (fun e => hai (by simp [← e, hx]))
        (fun e => hblr (e ▸ hx)) hxm (fun e => hpt (by simp [← e, hx]))
    · rw [RAr]
      exact har.frame fun x hx => rfr x (fun e => har' (e ▸ hx))
        (fun e => hli b (by simp) (by simp [← e, hx]))
        (hbr.ne_root (har.mem_ne hx).1 fun h' => hli x (by simp [h']) hx)
        (fun e => hpt (by simp [← e, hx]))
  · have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
    have HH := rotateAt_sentinel h a .right ap₁ ap₃ ap₄ ap₅ (Ne.symm ha)
      (by simpa [childAt, Side.other, hab] using Ne.symm hb)
      (fun e => by simp only [parent, parentSide, hpa, hsa] at e ⊢; exact hs e)
    simp only [parent, hpa] at HH
    refine hp.retarget hr (fun x hx hxp => rfr x
        (fun e => (hout x hx).1 (by simp [e])) (fun e => (hout x hx).1 (by simp [e]))
        (hbr.ne_root (hout x hx).2 fun h' => (hout x hx).1 (by simp [h'])) hxp)
      HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hpm' : p = m
      · subst hpm'; cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, NodeRec.withChild]
      · cases s <;> simp [RL, childAt, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]
    · intro hph
      have hpm' := hpm hph
      cases s <;> simp [RL, childAt, Side.other, Ne.symm hap, Ne.symm hbp, hpm', NodeRec.withChild]

/-- `rotateAt_frame` for `rotateAt_refines_right`: the only records changed are those of `a`, `b`,
`b`'s right child (the first node of `lr`, or the sentinel) and `p`. -/
theorem rotateAt_refines_right_frame {h : Heap} {head a b p : Addr} {s : Side} {c c' : RBColor}
    {ll lr r : RBNode Addr} {path : Path Addr}
    (hl : Located h head a p s (.node c (.node c' ll b lr) a r) path) {x : Addr}
    (h₁ : x ≠ a) (h₂ : x ≠ b) (h₃ : x ≠ (h b).right) (h₄ : x ≠ p) :
    rotateAt h a .right x = h x := by
  obtain ⟨-, -, -, hpa, -, -, hal, -⟩ := hl.1.node_inv
  obtain ⟨hab, -⟩ := hal.node_inv
  exact rotateAt_frame h a .right h₁ (by simpa [childAt, Side.other, hab] using h₂)
    (by simpa [childAt, Side.other, hab] using h₃) (by simpa [parent, hpa] using h₄)

/-! ## Step 3a: `attach_to`, `substitute_with` and `switch_with`

Each performs the zipper step `Fixup.lean`'s `insert` or `eraseAt` takes at that point (the
note's §4, theorem 2): `attach_to` fills an empty hole with a red leaf, `substitute_with` splices
out a node with at most one child, and `switch_with` puts another address at a node's tree
position. Each comes with its per-address description (`_apply`), the list of records it changes
(`_frame`) and its refinement theorem (`_refines`). -/

/-- **`NodeBase::attach_to` fills the empty hole** (step 3a; the note's §4, theorem 2). If the
slot `(p, s)` holds the sentinel at `path` (the empty hole where `insert_counted`'s descent ends),
and `this` is a real address off the path, then after `attachTo h this p s` the heap represents
the red leaf `node red nil this nil` at that slot and path: the zipper state `Fixup.lean`'s
`insert` hands to `insFix`. Which records change is `attachTo_frame`. -/
theorem attachTo_refines {h : Heap} {head this p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head head p s path) (hn : this ≠ head) (hn0 : this ≠ null)
    (hfresh : this ∉ path.listL ++ path.listR) :
    Located (attachTo h this p s) head this p s (.node .red .nil this .nil) path := by
  have htp : this ≠ p := fun e => by
    rcases hp.slot with hph | hpm
    · exact hn (e.trans hph)
    · exact hfresh (e ▸ hpm)
  have AT := attachTo_apply h this p s htp
  have hslot := hp.childAt_slot
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  refine ⟨.node hn hn0 (by simp [AT]) (by simp [AT]) (by simp [AT, colourBit]) ?_ ?_, ?_⟩
  · have e : (attachTo h this p s this).left = head := by simp [AT, hslot]
    rw [e]; exact .nil
  · have e : (attachTo h this p s this).right = head := by simp [AT, hslot]
    rw [e]; exact .nil
  · have hht : head ≠ this := Ne.symm hn
    refine hp.retarget .nil (fun x hx hxp => ?_) ?_ ?_ ?_ ?_ ?_
    · exact attachTo_frame h this p s (fun e => hfresh (e ▸ hx)) hxp
    · by_cases hph : head = p
      · subst hph; obtain rfl := hs rfl; simp [AT, hht, NodeRec.withChild]
      · simp [AT, hht, hph]
    · by_cases hph : head = p
      · subst hph; simp [AT, hht]
      · simp [AT, hht, hph]
    · intro hph; simp [AT, hht, Ne.symm hph]
    · cases s <;> simp [AT, childAt, Ne.symm htp, NodeRec.withChild]
    · intro _
      cases s <;> simp [AT, childAt, Side.other, Ne.symm htp, NodeRec.withChild]

/-- The common part of `substituteWith_refines_left` and `_right`: `this` is the first node of the
located subtree `t`, and its side-`σ` child `k` represents `u`, a subtree of `t`. After
`substituteWith h this k`, the heap represents `u` at `this`'s slot and path, and `k`'s `parent`
word names the slot, also when `k` is the sentinel (the empty hole). -/
theorem substituteWith_refines_core {h : Heap} {head this p k : Addr} {s σ : Side}
    {t u : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s t path) (hthis : this ∈ t.toList)
    (hu : Rep h head k this σ u) (hut : ∀ x ∈ u.toList, x ∈ t.toList) :
    Located (substituteWith h this k) head k p s u path ∧
      (substituteWith h this k k).parent = p ∧ (substituteWith h this k k).side = s := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  have hk : k ≠ head → k ∈ u.toList := hu.root_mem
  obtain ⟨hr, hp⟩ := hl
  have hpa : parent h this = p := (hr.root_fields hthis).1
  have hsa : parentSide h this = s := (hr.root_fields hthis).2
  have SU := substituteWith_apply h this k
  simp only [hpa, hsa] at SU
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  -- `k` is the sentinel or an address of `u`, inside `t`; `p` is the sentinel or on the path.
  have hkp₀ : p ≠ head → k ≠ p := fun hph e => by
    by_cases hkh : k = head
    · exact hph (e ▸ hkh)
    · exact hpt (e ▸ hut k (hk hkh))
  have FK : (substituteWith h this k k).parent = p ∧ (substituteWith h this k k).side = s := by
    simp [SU]
  refine ⟨⟨?_, ?_⟩, FK⟩
  · refine hu.reroot (fun hkh => ?_) (fun x hx hxk => ?_)
    · have hkp : k ≠ p := fun e => by
        by_cases hph : p = head
        · exact hkh (e.trans hph)
        · exact hkp₀ hph e
      simp [SU, hkp]
    · have hxp : x ≠ p := fun e => hpt (e ▸ hut x hx)
      simp [SU, hxk, hxp]
  · have hkk : ∀ x ∈ path.listL ++ path.listR, x ≠ k := fun x hx e => by
      by_cases hkh : k = head
      · exact (hout x hx).2 (e.trans hkh)
      · exact (hout x hx).1 (e ▸ hut k (hk hkh))
    have HH : (substituteWith h this k head).right = (h head).right ∧
        (substituteWith h this k head).red = (h head).red ∧
        (p ≠ head → (substituteWith h this k head).left = (h head).left) := by
      by_cases hph : p = head
      · subst hph; obtain rfl := hs rfl
        by_cases hkh : p = k
        · subst hkh; simp [SU, NodeRec.withChild]
        · simp [SU, hkh, NodeRec.withChild]
      · have hhp : head ≠ p := Ne.symm hph
        by_cases hkh : head = k
        · subst hkh; simp [SU, hhp]
        · simp [SU, hkh, hhp]
    refine hp.retarget hr (fun x hx hxp => substituteWith_frame h this k (hkk x hx)
        (by rw [hpa]; exact hxp)) HH.1 HH.2.1 HH.2.2 ?_ ?_
    · by_cases hph : p = head
      · subst hph; obtain rfl := hs rfl
        by_cases hkh : p = k
        · subst hkh; simp [SU, childAt, NodeRec.withChild]
        · simp [SU, childAt, hkh, NodeRec.withChild]
      · have hpk := Ne.symm (hkp₀ hph)
        cases s <;> simp [SU, childAt, hpk, NodeRec.withChild]
    · intro hph
      have hpk := Ne.symm (hkp₀ hph)
      cases s <;> simp [SU, childAt, Side.other, hpk, NodeRec.withChild]

/-- **`NodeBase::substitute_with` splices out a node with no right child** (step 3a, §4 theorem 2;
`erase_counted`'s `right == end` case). If the heap represents the located subtree
`node c l this nil`, then after `substituteWith h this (h this).left` it represents `l` at the same
slot and path: the zipper's `path.fill l` in `eraseAt`. And the left child's `parent` word names
that slot. When `l` is empty, that child is the sentinel, and these are its scratch fields: how
`erase_fixup` finds an empty hole's parent and side (unless `switch_with` then overwrites them,
`switchWith_refines`). `this` is detached, its record unchanged. -/
theorem substituteWith_refines_left {h : Heap} {head this p : Addr} {s : Side} {c : RBColor}
    {l : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s (.node c l this .nil) path) :
    Located (substituteWith h this (h this).left) head (h this).left p s l path ∧
      (substituteWith h this (h this).left (h this).left).parent = p ∧
      (substituteWith h this (h this).left (h this).left).side = s := by
  obtain ⟨-, -, -, -, -, -, hll, -⟩ := hl.1.node_inv
  exact substituteWith_refines_core hl (by simp) hll (fun x hx => by simp [hx])

/-- **`NodeBase::substitute_with` splices out a node with no left child**, the mirror image of
`substituteWith_refines_left` (`erase_counted`'s case `left == end`, and its two-child case, where
the in-order successor, which has no left child, is spliced out): `node c nil this r` gives `r`,
with the right child's `parent` word naming the slot. -/
theorem substituteWith_refines_right {h : Heap} {head this p : Addr} {s : Side} {c : RBColor}
    {r : RBNode Addr} {path : Path Addr}
    (hl : Located h head this p s (.node c .nil this r) path) :
    Located (substituteWith h this (h this).right) head (h this).right p s r path ∧
      (substituteWith h this (h this).right (h this).right).parent = p ∧
      (substituteWith h this (h this).right (h this).right).side = s := by
  obtain ⟨-, -, -, -, -, -, -, hrr⟩ := hl.1.node_inv
  exact substituteWith_refines_core hl (by simp) hrr (fun x hx => by simp [hx])

/-- **`NodeBase::switch_with` puts `this` at `node`'s tree position** (step 3a, §4 theorem 2). If
the heap represents the located subtree `node c l node r`, and `this` is a real address neither in
it nor on its path, then after `switchWith h this node` the heap represents `node c l this r` at
the same slot and path: the address at that position changes, the subtrees and the colour do not.
This is `erase_counted`'s last step in its two-child `Node` case (the in-order successor, already
spliced out by `substitute_with`, takes the erased node's place: the zipper's `.right c _ m path`
in `eraseAt`) and its whole tree effect in the `Promote` case (the next chain member, with an
equal key, takes the attached member's place).

The other conclusions are the children's `parent` words: `node`'s right child, and its left child
unless both are the sentinel, now name `this`. For a child that is the sentinel these are its
scratch fields. In a two-child erase whose successor `this` was `node`'s right child and had no
right child, `node`'s right child is the sentinel by the time of the call, so the scratch `parent`
now names `this`, side right, which is where the hole is, overwriting what `substitute_with` wrote
(step 3c's hole invariant). -/
theorem switchWith_refines {h : Heap} {head this node p : Addr} {s : Side} {c : RBColor}
    {l r : RBNode Addr} {path : Path Addr}
    (hl : Located h head node p s (.node c l node r) path) (hn : this ≠ head) (hn0 : this ≠ null)
    (hpath : this ∉ path.listL ++ path.listR) (htree : this ∉ (RBNode.node c l node r).toList) :
    Located (switchWith h this node) head this p s (.node c l this r) path ∧
      (switchWith h this node (h node).right).parent = this ∧
      (switchWith h this node (h node).right).side = .right ∧
      ((h node).left ≠ (h node).right →
        (switchWith h this node (h node).left).parent = this ∧
        (switchWith h this node (h node).left).side = .left) := by
  have hout := hl.outside
  have hpt := hl.slot_not_mem
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hnh, -, hpa, hsa, hca, hL, hR⟩ := hr.node_inv
  generalize hLe : (h node).left = L at hL
  generalize hRe : (h node).right = R at hR
  obtain ⟨-, -, hnl, hnr, hlr⟩ := nodup_node hr.nodup
  simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at htree hpt
  have hLm : L ≠ head → L ∈ l.toList := hL.root_mem
  have hRm : R ≠ head → R ∈ r.toList := hR.root_mem
  -- Distinctness, the sentinel being the only address `L`, `R` and `p` can share.
  have hnL : node ≠ L := fun e => by
    by_cases hLh : L = head
    · exact hnh (e.trans hLh)
    · exact hnl (e ▸ hLm hLh)
  have hnR : node ≠ R := fun e => by
    by_cases hRh : R = head
    · exact hnh (e.trans hRh)
    · exact hnr (e ▸ hRm hRh)
  have hnp : node ≠ p := fun e => hpt.2.1 e.symm
  have htn : this ≠ node := htree.2.1
  have htL : this ≠ L := fun e => by
    by_cases hLh : L = head
    · exact hn (e.trans hLh)
    · exact htree.1 (e ▸ hLm hLh)
  have htR : this ≠ R := fun e => by
    by_cases hRh : R = head
    · exact hn (e.trans hRh)
    · exact htree.2.2 (e ▸ hRm hRh)
  have htp : this ≠ p := fun e => by
    rcases hp.slot with hph | hpm
    · exact hn (e.trans hph)
    · exact hpath (e ▸ hpm)
  have hLR : L ≠ head → L ≠ R := fun hLh e => by
    by_cases hRh : R = head
    · exact hLh (e.trans hRh)
    · exact hlr L (hLm hLh) (e ▸ hRm hRh)
  have hLp : L ≠ head → L ≠ p := fun hLh e => hpt.1 (e ▸ hLm hLh)
  have hRp : R ≠ head → R ≠ p := fun hRh e => hpt.2.2 (e ▸ hRm hRh)
  have SW := switchWith_apply h this node htn (by simpa [childAt, hLe] using hnL)
    (by simpa [childAt, hRe] using hnR) (by simpa [parent, hpa] using hnp)
    (by simpa [childAt, hLe] using htL) (by simpa [childAt, hRe] using htR)
    (by simpa [parent, hpa] using htp)
  simp only [childAt, parent, parentSide, red, hLe, hRe, hpa, hsa, hca] at SW
  have hs : p = head → s = .left := fun e => by rw [e] at hp; exact hp.head_side
  have FR : (switchWith h this node R).parent = this ∧ (switchWith h this node R).side = .right :=
    by simp [SW, Ne.symm htR]
  have FL : L ≠ R → (switchWith h this node L).parent = this ∧
      (switchWith h this node L).side = .left := fun hne => by simp [SW, Ne.symm htL, hne]
  refine ⟨⟨.node hn hn0 (by simp [SW]) (by simp [SW]) (by simp [SW]) ?_ ?_, ?_⟩, FR.1, FR.2,
    FL⟩
  · have e : (switchWith h this node this).left = L := by simp [SW]
    rw [e]
    refine hL.reroot (fun hLh => ?_) (fun x hx hxL => ?_)
    · have h1 := hLR hLh
      have h2 := hLp hLh
      simp [SW, Ne.symm htL, h1, h2]
    · have h1 : x ≠ this := fun e => htree.1 (e ▸ hx)
      have h2 : x ≠ R := fun e => by
        by_cases hRh : R = head
        · exact (hL.mem_ne hx).1 (e.trans hRh)
        · exact hlr x hx (e ▸ hRm hRh)
      have h3 : x ≠ p := fun e => hpt.1 (e ▸ hx)
      simp [SW, h1, h2, hxL, h3]
  · have e : (switchWith h this node this).right = R := by simp [SW]
    rw [e]
    refine hR.reroot (fun hRh => ?_) (fun x hx hxR => ?_)
    · have h2 := hRp hRh
      simp [SW, Ne.symm htR, h2]
    · have h1 : x ≠ this := fun e => htree.2.2 (e ▸ hx)
      have h2 : x ≠ L := fun e => by
        by_cases hLh : L = head
        · exact (hR.mem_ne hx).1 (e.trans hLh)
        · exact hlr L (hLm hLh) (e ▸ hx)
      have h3 : x ≠ p := fun e => hpt.2.2 (e ▸ hx)
      simp [SW, h1, h2, hxR, h3]
  · have hfr : ∀ x ∈ path.listL ++ path.listR, x ≠ p → switchWith h this node x = h x :=
      fun x hx hxp => by
        have h1 : x ≠ this := fun e => hpath (e ▸ hx)
        have h2 : x ≠ L := fun e => by
          by_cases hLh : L = head
          · exact (hout x hx).2 (e.trans hLh)
          · exact (hout x hx).1 (by
              simp only [RBNode.toList_node, List.mem_append, List.mem_cons]
              exact .inl (e ▸ hLm hLh))
        have h3 : x ≠ R := fun e => by
          by_cases hRh : R = head
          · exact (hout x hx).2 (e.trans hRh)
          · exact (hout x hx).1 (by
              simp only [RBNode.toList_node, List.mem_append, List.mem_cons]
              exact .inr (.inr (e ▸ hRm hRh)))
        simp [SW, h1, h2, h3, hxp]
    -- Off `this`, a record keeps its right link and colour (its left link too, off the slot's
    -- node), and the slot's node gets `this` in the slot: whichever of `L`, `R` and `p` coincide.
    have GEN : ∀ x, x ≠ this → (x = p → s = .left) →
        (switchWith h this node x).right = (h x).right ∧
        (switchWith h this node x).red = (h x).red ∧
        (x ≠ p → (switchWith h this node x).left = (h x).left) ∧
        (x = p → (switchWith h this node x).left = this) := by
      intro x hxt hxs
      rw [SW, ite_eq_right hxt]
      by_cases e₁ : x = R
      · rw [ite_eq_left e₁]
        by_cases e₃ : x = p
        · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
        · rw [ite_eq_right e₃]; simp [e₃]
      · rw [ite_eq_right e₁]
        by_cases e₂ : x = L
        · rw [ite_eq_left e₂]
          by_cases e₃ : x = p
          · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
          · rw [ite_eq_right e₃]; simp [e₃]
        · rw [ite_eq_right e₂]
          by_cases e₃ : x = p
          · rw [ite_eq_left e₃]; obtain rfl := hxs e₃; simp [e₃]
          · rw [ite_eq_right e₃]; simp [e₃]
    have HH := GEN head (Ne.symm hn) (fun e => hs e.symm)
    refine hp.retarget hr hfr HH.1 HH.2.1 (fun hph => HH.2.2.1 (Ne.symm hph)) ?_ ?_
    · by_cases hph : p = head
      · have G := GEN p (Ne.symm htp) (fun _ => hs hph)
        obtain rfl := hs hph
        exact G.2.2.2 rfl
      · have e₁ : p ≠ R := fun e => hRp (fun h' => hph (e.trans h')) e.symm
        have e₂ : p ≠ L := fun e => hLp (fun h' => hph (e.trans h')) e.symm
        cases s <;> simp [SW, childAt, Ne.symm htp, e₁, e₂, NodeRec.withChild]
    · intro hph
      have e₁ : p ≠ R := fun e => hRp (fun h' => hph (e.trans h')) e.symm
      have e₂ : p ≠ L := fun e => hLp (fun h' => hph (e.trans h')) e.symm
      cases s <;> simp [SW, childAt, Side.other, Ne.symm htp, e₁, e₂, NodeRec.withChild]

/-! ## Colour writes and the final `make_black` -/

namespace Located

variable {h : Heap} {head a y P : Addr} {S : Side} {c : RBColor} {t l r b : RBNode Addr}
  {pp : Path Addr}

/-- **`NodeBase::set_colour` on a located subtree's first node** gives it the new colour and
changes nothing else the relation reads: the zipper's `paint` at the hole. (`makeBlack` and
`makeRed` are `setColour` with `colourBit .black` and `colourBit .red`.) -/
theorem paint (hl : Located h head y P S (.node c l y r) pp) (c' : RBColor) :
    Located (setColour h y (colourBit c')) head y P S (.node c' l y r) pp := by
  have hout := hl.outside
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, -, hll, hrr⟩ := hr.node_inv
  obtain ⟨-, -, hyl, hyr, -⟩ := nodup_node hr.nodup
  have F : ∀ x, x ≠ y → setColour h y (colourBit c') x = h x := fun x hx => by
    simp [setColour, Heap.modify, hx]
  have Y : setColour h y (colourBit c') y = { h y with red := colourBit c' } := by
    simp [setColour, Heap.modify]
  refine ⟨.node hy hn (by rw [Y]; exact hpa) (by rw [Y]; exact hsa) (by rw [Y]) ?_ ?_, ?_⟩
  · rw [Y]; exact hll.frame fun x hx => F x (fun e => hyl (e ▸ hx))
  · rw [Y]; exact hrr.frame fun x hx => F x (fun e => hyr (e ▸ hx))
  · have hyh : head ≠ y := Ne.symm hy
    exact hp.frame (fun x hx => F x (fun e => (hout x hx).1 (by simp [e])))
      (by rw [F head hyh]) (by rw [F head hyh]) (by rw [F head hyh])

end Located

/-- **`insert_fixup`'s final `make_black(head.child(Left))`** blackens the represented tree's root:
the zipper's `setBlack` of the whole tree. On an empty tree it writes the sentinel's colour bit,
black over black. -/
theorem Tree.makeBlack_root {h : Heap} {head : Addr} {T : RBNode Addr} (ht : Tree h head T) :
    Tree (makeBlack h (childAt h head .left)) head T.setBlack := by
  cases T with
  | nil =>
    obtain ⟨hr, e₂, e₃⟩ := ht
    have hroot : (h head).left = head := hr.nil_inv
    have H : makeBlack h (childAt h head .left) head = { h head with red := false } := by
      simp [makeBlack, setColour, Heap.modify, childAt, hroot]
    refine ⟨?_, by rw [H]; exact e₂, by rw [H]⟩
    rw [H]; show Rep _ head (h head).left head .left .nil; rw [hroot]; exact .nil
  | node c l v r =>
    obtain ⟨hv, hvh, -⟩ := ht.1.node_inv
    have hl : Located h head v head .left (.node c l v r) .root := by
      have := tree_iff_located.1 ht; rw [hv] at this; exact this
    have hl' := hl.paint .black
    have E : setColour h v (colourBit .black) head = h head := by
      simp [setColour, Heap.modify, Ne.symm hvh]
    apply tree_iff_located.2
    have e : childAt h head .left = v := hv
    simp only [makeBlack, e]
    rw [show (setColour h v false head).left = v by
      rw [show false = colourBit .black from rfl, E, hv]]
    exact hl'

end Heap

end Oris.RB
