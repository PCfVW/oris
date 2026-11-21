-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.Model

/-!
# The abstraction relation

Step 2 of the heap layer (`Lean/docs/heap-layer.md`, §3 and §5): when a heap *is* a zipper state
of `Oris/RB/Fixup.lean`. `Rep` for a subtree, `RepPath` for its ancestors, `Located` for the
pair, `Tree` for a whole tree. Their basic lemmas: no address occurs twice in a represented tree
(`Rep.nodup`), writes outside a tree preserve it (`Rep.frame`, `RepPath.frame`), a slot can change
occupant (`RepPath.retarget`), colour bits read back as the zipper's colours (`Rep.red_eq`), and a
located subtree moves up and down its path (`Located.up_left`, ..., `Located.down_right`).
-/

namespace Oris.RB

namespace Heap

open RBTree (RBNode RBColor)
open RBTree.RBNode (Path)

/-- The colour bit `NodeBase` stores for a colour (`TaggedPtr`'s bit `BIT_COLOUR`): set for
red. It links `RBColor`, the zipper level's colours, to `NodeRec.red`. -/
def colourBit : RBColor → Bool
  | .red => true
  | .black => false

/-- Distinct colours have distinct bits. -/
theorem colourBit_inj {c c' : RBColor} (h : colourBit c = colourBit c') : c = c' := by
  cases c <;> cases c' <;> first | rfl | cases h

/-- The abstraction relation (the note's §3). `Rep h head a p s t`: in heap `h`, with sentinel
`head`, the subtree starting at address `a` *is* the tree of addresses `t`, and its first node's
tagged `parent` word names the slot `(p, s)`: side `s` of `p`. That `p`'s link points back to `a`
is `RepPath`'s part.

* An empty subtree is the sentinel itself (`nil`), and constrains nothing. `Rep` never reads the
  sentinel's record, so no write to the sentinel (its scratch `parent` and side included) can
  break it (`Rep.frame`, with `Rep.mem_ne`).
* A node (`node`) is a real address (neither the sentinel nor null) whose tagged `parent` word
  names `p` and `s` and holds `c`'s colour bit, and whose two children represent `l` and `r`.

The represented tree is a tree of *distinct* addresses (`Rep.nodup`), which is what makes frame
reasoning sound (`Rep.frame`). The tree stores addresses, not keys, so node identity survives
(the note's §2). -/
inductive Rep (h : Heap) (head : Addr) : Addr → Addr → Side → RBNode Addr → Prop
  | nil {p : Addr} {s : Side} : Rep h head head p s .nil
  | node {a p : Addr} {s : Side} {c : RBColor} {l r : RBNode Addr} :
      a ≠ head → a ≠ null → (h a).parent = p → (h a).side = s → (h a).red = colourBit c →
      Rep h head (h a).left a .left l → Rep h head (h a).right a .right r →
      Rep h head a p s (.node c l a r)

/-- `x`'s ancestor `n` levels up, read along `parent` pointers. Used by `Rep.nodup`'s proof. -/
private def ancestor (h : Heap) (x : Addr) : Nat → Addr
  | 0 => x
  | n + 1 => (h (ancestor h x n)).parent

namespace Rep

variable {h h' : Heap} {head a p : Addr} {s : Side} {t : RBNode Addr}

/-- An empty subtree starts at the sentinel. -/
theorem nil_inv (hr : Rep h head a p s .nil) : a = head := by
  cases hr; rfl

/-- What a node's `Rep` says, read back (`Rep.node_inv`), one named field per premise of
`Rep.node`: the subtree starts at its root address `v` (`eq`), a real address, whose `parent` word
names the slot and holds the colour, and whose children represent the two subtrees. -/
structure NodeView (h : Heap) (head a p : Addr) (s : Side) (c : RBColor) (l : RBNode Addr)
    (v : Addr) (r : RBNode Addr) : Prop where
  eq : a = v
  ne_head : v ≠ head
  ne_null : v ≠ null
  parent : (h v).parent = p
  side : (h v).side = s
  red : (h v).red = colourBit c
  left : Rep h head (h v).left v .left l
  right : Rep h head (h v).right v .right r

/-- What a node's `Rep` says, read back: the inversion of `Rep.node`. -/
theorem node_inv {c : RBColor} {l r : RBNode Addr} {v : Addr}
    (hr : Rep h head a p s (.node c l v r)) : NodeView h head a p s c l v r := by
  cases hr with
  | node ha hn hp hs hc hl hr => exact ⟨rfl, ha, hn, hp, hs, hc, hl, hr⟩

/-- No address of a represented tree is the sentinel or null. -/
theorem mem_ne (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    x ≠ head ∧ x ≠ null := by
  induction hr with
  | nil => simp at hx
  | node ha hn _ _ _ _ _ ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact ihl hx
    · exact ⟨ha, hn⟩
    · exact ihr hx

/-- A subtree that does not start at the sentinel contains its starting address. -/
theorem root_mem (hr : Rep h head a p s t) (ha : a ≠ head) : a ∈ t.toList := by
  cases hr with
  | nil => exact absurd rfl ha
  | node => simp

/-- **The sentinel-or-member argument**, once: an address that is neither the sentinel nor in
`t` is not the address a subtree representing `t` starts at (the sentinel when `t` is empty, an
address of `t` otherwise). -/
theorem ne_root (hr : Rep h head a p s t) {x : Addr} (hxh : x ≠ head) (hxt : x ∉ t.toList) :
    x ≠ a := fun e => by
  by_cases ha : a = head
  · exact hxh (e.trans ha)
  · exact hxt (e ▸ hr.root_mem ha)

/-- A non-empty subtree's first node points back to the slot it hangs in. -/
theorem root_fields (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    (h a).parent = p ∧ (h a).side = s := by
  cases hr with
  | nil => simp at hx
  | node _ _ hp hs => exact ⟨hp, hs⟩

/-- From any address of a subtree, following `parent` pointers reaches the subtree's first node,
staying inside the subtree on the way. -/
theorem climb (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    ∃ n, ancestor h x n = a ∧ ∀ k ≤ n, ancestor h x k ∈ t.toList := by
  induction hr with
  | nil => simp at hx
  | @node a p s c l r _ _ _ _ _ hl hr ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | rfl | hx
    · obtain ⟨n, hn, hk⟩ := ihl hx
      have hup : ancestor h x (n + 1) = a := by
        show (h (ancestor h x n)).parent = _
        rw [hn]; exact (hl.root_fields hx).1
      refine ⟨n + 1, hup, fun k hk' => ?_⟩
      by_cases hkn : k ≤ n
      · exact .inl (hk k hkn)
      · obtain rfl : k = n + 1 := by omega
        exact .inr (.inl hup)
    · refine ⟨0, rfl, fun k hk => ?_⟩
      obtain rfl : k = 0 := by omega
      exact .inr (.inl rfl)
    · obtain ⟨n, hn, hk⟩ := ihr hx
      have hup : ancestor h x (n + 1) = a := by
        show (h (ancestor h x n)).parent = _
        rw [hn]; exact (hr.root_fields hx).1
      refine ⟨n + 1, hup, fun k hk' => ?_⟩
      by_cases hkn : k ≤ n
      · exact .inr (.inr (hk k hkn))
      · obtain rfl : k = n + 1 := by omega
        exact .inr (.inl hup)

/-- Every address of a subtree starts a subtree of its own, no larger. -/
theorem sub (hr : Rep h head a p s t) {x : Addr} (hx : x ∈ t.toList) :
    ∃ q σ u, Rep h head x q σ u ∧ u.size ≤ t.size := by
  induction hr with
  | nil => simp at hx
  | node ha hn hp hs hc hl hr ihl ihr =>
    simp only [RBNode.toList_node, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · obtain ⟨q, σ, u, hu, hsz⟩ := ihl hx
      exact ⟨q, σ, u, hu, by simp only [RBNode.size]; omega⟩
    · exact ⟨_, _, _, .node ha hn hp hs hc hl hr, Nat.le_refl _⟩
    · obtain ⟨q, σ, u, hu, hsz⟩ := ihr hx
      exact ⟨q, σ, u, hu, by simp only [RBNode.size]; omega⟩

/-- The heap determines the tree: two `Rep`s from the same address represent the same tree,
whatever slot each claims. -/
theorem unique {p' : Addr} {s' : Side} {t' : RBNode Addr}
    (h₁ : Rep h head a p s t) (h₂ : Rep h head a p' s' t') : t = t' := by
  induction h₁ generalizing p' s' t' with
  | nil =>
    cases h₂ with
    | nil => rfl
    | node ha => exact absurd rfl ha
  | node ha _ _ _ hc _ _ ihl ihr =>
    cases h₂ with
    | nil => exact absurd rfl ha
    | node _ _ _ _ hc' hl' hr' => rw [ihl hl', ihr hr', colourBit_inj (hc.symm.trans hc')]

/-- **No address occurs twice in a represented tree** (the note's `Repr.nodup`), from `Rep` alone,
with no separate distinctness hypothesis. A node cannot occur below itself: by `unique` (the heap
determines the tree) it would start a tree as large as the one containing it. Its two subtrees are
disjoint thanks to the back-pointers: climbing `parent` pointers from a shared address would reach
the node's left and right children at the same height (whose side bits differ), or reach the node
inside one of them. -/
theorem nodup (hr : Rep h head a p s t) : t.toList.Nodup := by
  induction hr with
  | nil => simp
  | @node a p s c l r ha hn hp hs hc hl hr ihl ihr =>
    have hself : Rep h head a p s (.node c l a r) := .node ha hn hp hs hc hl hr
    have hal : a ∉ l.toList := fun hx => by
      obtain ⟨q, σ, u, hu, hsz⟩ := hl.sub hx
      obtain rfl := hself.unique hu
      simp only [RBNode.size] at hsz; omega
    have har : a ∉ r.toList := fun hx => by
      obtain ⟨q, σ, u, hu, hsz⟩ := hr.sub hx
      obtain rfl := hself.unique hu
      simp only [RBNode.size] at hsz; omega
    have hdis : ∀ x ∈ l.toList, x ∉ r.toList := fun x hxl hxr => by
      obtain ⟨n₁, h₁, hk₁⟩ := hl.climb hxl
      obtain ⟨n₂, h₂, hk₂⟩ := hr.climb hxr
      have sl := hl.root_fields hxl
      have sr := hr.root_fields hxr
      rcases Nat.lt_trichotomy n₁ n₂ with hlt | rfl | hgt
      · apply har
        have := hk₂ (n₁ + 1) hlt
        have e : ancestor h x (n₁ + 1) = a := by
          show (h (ancestor h x n₁)).parent = a
          rw [h₁]; exact sl.1
        rwa [e] at this
      · have e : (h a).left = (h a).right := h₁.symm.trans h₂
        rw [e] at sl
        cases sl.2.symm.trans sr.2
      · apply hal
        have := hk₁ (n₂ + 1) hgt
        have e : ancestor h x (n₂ + 1) = a := by
          show (h (ancestor h x n₂)).parent = a
          rw [h₂]; exact sr.1
        rwa [e] at this
    exact nodup_node_intro ⟨ihl, ihr, hal, har, hdis⟩

/-- **The frame lemma.** A heap that agrees with `h` on every address of `t` represents `t` at
the same slot. Writes elsewhere, to any field of the sentinel included, preserve `Rep`. -/
theorem frame (hr : Rep h head a p s t) (hf : ∀ x ∈ t.toList, h' x = h x) :
    Rep h' head a p s t := by
  induction hr with
  | nil => exact .nil
  | @node a p s c l r ha hn hp hs hc _ _ ihl ihr =>
    have haa : h' a = h a := hf a (by simp)
    refine .node ha hn (by rw [haa]; exact hp) (by rw [haa]; exact hs) (by rw [haa]; exact hc)
      ?_ ?_
    · rw [haa]; exact ihl fun x hx => hf x (by simp [hx])
    · rw [haa]; exact ihr fun x hx => hf x (by simp [hx])

/-- The frame lemma for a subtree that moves to a new slot: when the first node keeps its
children and colour but takes a new `parent` and side (as the subtree `rotateAt` moves across does),
and every other address of `t` keeps its record, the subtree is represented at the new slot. -/
theorem reroot {p' : Addr} {s' : Side} (hr : Rep h head a p s t)
    (hroot : a ≠ head → (h' a).left = (h a).left ∧ (h' a).right = (h a).right ∧
      (h' a).red = (h a).red ∧ (h' a).parent = p' ∧ (h' a).side = s')
    (hrest : ∀ x ∈ t.toList, x ≠ a → h' x = h x) : Rep h' head a p' s' t := by
  have hnd := hr.nodup
  cases hr with
  | nil => exact .nil
  | node ha hn _ _ hc hl hr =>
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := hroot ha
    have hn' := nodup_node hnd
    refine .node ha hn e₄ e₅ (e₃.trans hc) ?_ ?_
    · rw [e₁]
      exact hl.frame fun x hx => hrest x (by simp [hx])
        (by rintro rfl; exact hn'.not_mem_left hx)
    · rw [e₂]
      exact hr.frame fun x hx => hrest x (by simp [hx]) (by rintro rfl; exact hn'.not_mem_right hx)

end Rep

/-- The ancestors' half of the abstraction relation (the note's `ReprPath`). `RepPath h head a p s
path`: the slot `(p, s)`, the side-`s` child link of `p`, holds `a` and lies at `path` in the
tree. At the top (`root`), the slot is the sentinel's left link, the sentinel's right link points
to itself and the sentinel is black. Below a node `y` (`left`, `right`), `y` is a real address
holding `a` in that child link, with the path's colour for `y`, its other child representing the
path's sibling subtree, and `y`'s own slot, read from its tagged `parent` word, lying at the rest
of the path.

The slot's occupant `a` is an index, not read from `a` itself, so the relation holds equally of an
empty hole (`a` the sentinel, whose own `parent` field is scratch). -/
inductive RepPath (h : Heap) (head : Addr) : Addr → Addr → Side → Path Addr → Prop
  | root {a : Addr} : (h head).left = a → (h head).right = head → (h head).red = false →
      RepPath h head a head .left .root
  | left {a y : Addr} {c : RBColor} {pp : Path Addr} {b : RBNode Addr} :
      y ≠ head → y ≠ null → (h y).left = a → (h y).red = colourBit c →
      Rep h head (h y).right y .right b → RepPath h head y (h y).parent (h y).side pp →
      RepPath h head a y .left (.left c pp y b)
  | right {a y : Addr} {c : RBColor} {pp : Path Addr} {b : RBNode Addr} :
      y ≠ head → y ≠ null → (h y).right = a → (h y).red = colourBit c →
      Rep h head (h y).left y .left b → RepPath h head y (h y).parent (h y).side pp →
      RepPath h head a y .right (.right c b y pp)

/-- A located subtree, the heap counterpart of a zipper pair `(t, path)`: the subtree `t` hangs at
the slot `(p, s)`, which holds `a` and lies at `path`. -/
def Located (h : Heap) (head a p : Addr) (s : Side) (t : RBNode Addr) (path : Path Addr) :
    Prop :=
  Rep h head a p s t ∧ RepPath h head a p s path

/-- A whole tree: the sentinel's left link represents `t` (as the root slot), its right link
points to itself (what `is_nil` tests), and it is black. -/
def Tree (h : Heap) (head : Addr) (t : RBNode Addr) : Prop :=
  Rep h head (h head).left head .left t ∧ (h head).right = head ∧ (h head).red = false

/-- A whole tree is a tree located at the root. -/
theorem tree_iff_located {h : Heap} {head : Addr} {t : RBNode Addr} :
    Tree h head t ↔ Located h head (h head).left head .left t .root := by
  constructor
  · rintro ⟨hr, e₂, e₃⟩; exact ⟨hr, .root rfl e₂ e₃⟩
  · rintro ⟨hr, hp⟩
    cases hp with
    | root _ e₂ e₃ => exact ⟨hr, e₂, e₃⟩

namespace RepPath

variable {h h' : Heap} {head a p : Addr} {s : Side} {path : Path Addr} {t : RBNode Addr}

/-- Filling the path: a located subtree is part of a whole tree, `path.fill t`. -/
theorem fill (hp : RepPath h head a p s path) (hr : Rep h head a p s t) :
    Tree h head (path.fill t) := by
  induction hp generalizing t with
  | root e₁ e₂ e₃ => exact ⟨e₁ ▸ hr, e₂, e₃⟩
  | left hy hn ha hc hb _ ih => exact ih (.node hy hn rfl rfl hc (ha ▸ hr) hb)
  | right hy hn ha hc hb _ ih => exact ih (.node hy hn rfl rfl hc hb (ha ▸ hr))

/-- The slot's node is the sentinel (at the root) or one of the path's addresses. -/
theorem slot (hp : RepPath h head a p s path) : p = head ∨ p ∈ path.listL ++ path.listR := by
  cases hp with
  | root => exact .inl rfl
  | left => exact .inr (by simp)
  | right => exact .inr (by simp)

/-- The frame lemma for paths: a heap that agrees with `h` on every address of the path and on
the sentinel's links and colour keeps the path. -/
theorem frame (hp : RepPath h head a p s path)
    (hf : ∀ x ∈ path.listL ++ path.listR, h' x = h x)
    (e₁ : (h' head).left = (h head).left) (e₂ : (h' head).right = (h head).right)
    (e₃ : (h' head).red = (h head).red) : RepPath h' head a p s path := by
  induction hp with
  | root f₁ f₂ f₃ => exact .root (e₁.trans f₁) (e₂.trans f₂) (e₃.trans f₃)
  | @left a y c pp b hy hn ha hc hb _ ih =>
    have hyy : h' y = h y := hf y (by simp)
    refine .left hy hn (by rw [hyy]; exact ha) (by rw [hyy]; exact hc) ?_ ?_
    · rw [hyy]; exact hb.frame fun x hx => hf x (by simp [hx])
    · rw [hyy]
      exact ih fun x hx => hf x (by
        simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> simp [hx])
  | @right a y c pp b hy hn ha hc hb _ ih =>
    have hyy : h' y = h y := hf y (by simp)
    refine .right hy hn (by rw [hyy]; exact ha) (by rw [hyy]; exact hc) ?_ ?_
    · rw [hyy]; exact hb.frame fun x hx => hf x (by simp [hx])
    · rw [hyy]
      exact ih fun x hx => hf x (by
        simp only [List.mem_append] at hx
        rcases hx with hx | hx <;> simp [hx])

end RepPath

namespace Located

variable {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr} {t : RBNode Addr}

/-- The path's addresses are outside the located subtree, and none is the sentinel. -/
theorem outside (hl : Located h head a p s t path) :
    ∀ x ∈ path.listL ++ path.listR, x ∉ t.toList ∧ x ≠ head := by
  have hf := (hl.2.fill hl.1).1
  have hnd := hf.nodup
  rw [RBTree.RBNode.Path.fill_toList] at hnd
  intro x hx
  have hmem : x ∈ (path.fill t).toList := by
    rw [RBTree.RBNode.Path.fill_toList]
    simp only [RBTree.RBNode.Path.withList, List.mem_append] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  exact ⟨(nodup_withList hnd).2 x hx, (hf.mem_ne hmem).1⟩

/-- The slot's node is outside the subtree hanging from it. -/
theorem slot_not_mem (hl : Located h head a p s t path) : p ∉ t.toList := by
  rcases hl.2.slot with rfl | hpm
  · exact fun hx => (hl.1.mem_ne hx).1 rfl
  · exact (hl.outside p hpm).1

end Located

/-- A slot changes occupant, and nothing else on the path changes. If the new heap `H` holds `b`
in the slot `(p, s)`, keeps the slot node's other link, colour and `parent` word, keeps the
sentinel's right link and colour (and its left link, unless the slot is that link), and keeps the
record of every other address of the path, then the path is unchanged with `b` in the slot.
Nothing is required of addresses off the path, whatever the operation wrote there (the subtree
below, a node being attached, a chain member taking a tree position). Every operation that
replaces a subtree in place (`rotate`; in step 3, `attach_to`, `substitute_with` and
`switch_with`) ends with this step. -/
theorem RepPath.retarget {h H : Heap} {head a b p : Addr} {s : Side} {path : Path Addr}
    {t : RBNode Addr} (hp : RepPath h head a p s path) (hr : Rep h head a p s t)
    (hfr : ∀ x ∈ path.listL ++ path.listR, x ≠ p → H x = h x)
    (hright : (H head).right = (h head).right) (hred : (H head).red = (h head).red)
    (hleft : p ≠ head → (H head).left = (h head).left)
    (hslot : childAt H p s = b)
    (hp' : p ≠ head → childAt H p s.other = childAt h p s.other ∧ (H p).red = (h p).red ∧
      (H p).parent = (h p).parent ∧ (H p).side = (h p).side) :
    RepPath H head b p s path := by
  cases hp with
  | root e₁ e₂ e₃ => exact .root hslot (hright.trans e₂) (hred.trans e₃)
  | @left _ _ c₀ pp sib hy hny eA ec hsib hpp =>
    have hup : Located h head p (h p).parent (h p).side (.node c₀ t p sib) pp :=
      ⟨.node hy hny rfl rfl ec (by rw [eA]; exact hr) hsib, hpp⟩
    obtain ⟨-, -, -, hysib, -⟩ := nodup_node hup.1.nodup
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hp' hy
    refine .left hy hny hslot (e₂.trans ec) ?_ ?_
    · rw [show (H p).right = (h p).right from e₁]
      exact hsib.frame fun x hx => hfr x (by simp [hx]) (fun e => hysib (e ▸ hx))
    · rw [e₃, e₄]
      refine hpp.frame (fun x hx => ?_) (hleft hy) hright hred
      obtain ⟨hxt, -⟩ := hup.outside x hx
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hxt
      refine hfr x ?_ hxt.2.1
      simp only [Path.listL, Path.listR, List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]
  | @right _ _ c₀ pp sib hy hny eA ec hsib hpp =>
    have hup : Located h head p (h p).parent (h p).side (.node c₀ sib p t) pp :=
      ⟨.node hy hny rfl rfl ec hsib (by rw [eA]; exact hr), hpp⟩
    obtain ⟨-, -, hysib, -, -⟩ := nodup_node hup.1.nodup
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hp' hy
    refine .right hy hny hslot (e₂.trans ec) ?_ ?_
    · rw [show (H p).left = (h p).left from e₁]
      exact hsib.frame fun x hx => hfr x (by simp [hx]) (fun e => hysib (e ▸ hx))
    · rw [e₃, e₄]
      refine hpp.frame (fun x hx => ?_) (hleft hy) hright hred
      obtain ⟨hxt, -⟩ := hup.outside x hx
      simp only [RBNode.toList_node, List.mem_append, List.mem_cons, not_or] at hxt
      refine hfr x ?_ hxt.2.1
      simp only [Path.listL, Path.listR, List.mem_append, List.mem_cons] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]

/-- The sentinel's only slot is its left link. -/
theorem RepPath.head_side {h : Heap} {head a : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a head s path) : s = .left := by
  cases hp with
  | root => rfl
  | left hy => exact absurd rfl hy
  | right hy => exact absurd rfl hy

/-- The slot's link holds its occupant: `RepPath`'s first field, read back. -/
theorem RepPath.childAt_slot {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a p s path) : childAt h p s = a := by
  cases hp with
  | root e => exact e
  | left _ _ e => exact e
  | right _ _ e => exact e

/-- A path's relation keeps the sentinel black: `RepPath`'s root case requires it, and every
other case carries it up. -/
theorem RepPath.head_red {h : Heap} {head a p : Addr} {s : Side} {path : Path Addr}
    (hp : RepPath h head a p s path) : (h head).red = false := by
  induction hp with
  | root _ _ e => exact e
  | left _ _ _ _ _ _ ih => exact ih
  | right _ _ _ _ _ _ ih => exact ih

/-- **Colour bits read back.** The `red` bit at a subtree's starting address is the zipper's
`red?` of the subtree, for the sentinel too (black, as `NodeBase::red` reads it), provided the
sentinel's bit is clear. -/
theorem Rep.red_eq {h : Heap} {head a p : Addr} {s : Side} {u : RBNode Addr}
    (hr : Rep h head a p s u) (hh : (h head).red = false) : red h a = red? u := by
  cases hr with
  | nil => exact hh
  | @node _ _ _ c _ _ _ _ _ _ hc _ _ => cases c <;> exact hc

/-- A slot on a left path step is that step's node's left link. -/
theorem RepPath.left_inv {h : Heap} {head a p y : Addr} {s : Side} {c : RBColor}
    {pp : Path Addr} {b : RBNode Addr} (hp : RepPath h head a p s (.left c pp y b)) :
    p = y ∧ s = .left := by
  cases hp; exact ⟨rfl, rfl⟩

/-- A slot on a right path step is that step's node's right link. -/
theorem RepPath.right_inv {h : Heap} {head a p y : Addr} {s : Side} {c : RBColor}
    {pp : Path Addr} {b : RBNode Addr} (hp : RepPath h head a p s (.right c b y pp)) :
    p = y ∧ s = .right := by
  cases hp; exact ⟨rfl, rfl⟩

namespace Located

variable {h : Heap} {head a y P : Addr} {S : Side} {c : RBColor} {t l r b : RBNode Addr}
  {pp : Path Addr}

/-- **Climbing a left step**: a subtree located as `y`'s left child is part of `y`'s subtree,
located at `y`'s own slot, read from `y`'s `parent` word, one step up the path. -/
theorem up_left (hl : Located h head a y .left t (.left c pp y b)) :
    Located h head y (h y).parent (h y).side (.node c t y b) pp := by
  obtain ⟨hr, hp⟩ := hl
  cases hp with
  | left hy hn ha hc hb hpp => exact ⟨.node hy hn rfl rfl hc (ha ▸ hr) hb, hpp⟩

/-- **Climbing a right step**, the mirror image of `up_left`. -/
theorem up_right (hl : Located h head a y .right t (.right c b y pp)) :
    Located h head y (h y).parent (h y).side (.node c b y t) pp := by
  obtain ⟨hr, hp⟩ := hl
  cases hp with
  | right hy hn ha hc hb hpp => exact ⟨.node hy hn rfl rfl hc hb (ha ▸ hr), hpp⟩

/-- **Descending to the left child**: the converse of `up_left`. -/
theorem down_left (hl : Located h head y P S (.node c l y r) pp) :
    Located h head (h y).left y .left l (.left c pp y r) := by
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, hc, hll, hrr⟩ := hr.node_inv
  exact ⟨hll, .left hy hn rfl hc hrr (hpa ▸ hsa ▸ hp)⟩

/-- **Descending to the right child**: the converse of `up_right`. -/
theorem down_right (hl : Located h head y P S (.node c l y r) pp) :
    Located h head (h y).right y .right r (.right c l y pp) := by
  obtain ⟨hr, hp⟩ := hl
  obtain ⟨-, hy, hn, hpa, hsa, hc, hll, hrr⟩ := hr.node_inv
  exact ⟨hrr, .right hy hn rfl hc hll (hpa ▸ hsa ▸ hp)⟩

end Located

end Heap

end Oris.RB
