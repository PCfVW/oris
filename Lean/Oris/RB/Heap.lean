-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris.RB.Heap.Model
import Oris.RB.Heap.Rep
import Oris.RB.Heap.Apply
import Oris.RB.Heap.Structural
import Oris.RB.Heap.InsertFixup
import Oris.RB.Heap.EraseFixup

/-!
# `rbtree.rs`'s pointer code, on a model heap

Steps 1, 2, 3a and 3b of the heap layer, as numbered in the plan of `Lean/docs/heap-layer.md`
(§5, whose steps 3a–3d prove §4's theorems 2–5; theorem 1 is `rotateAt_refines`, in step 2).

- **Step 1, the definitions** (`Heap/Model.lean`). Every function there transcribes one function
  of `Rust/src/rbtree.rs`, **one heap update per Rust write, in the Rust's order**, with every
  read where the Rust reads it.
- **Step 2, the abstraction relation and the first refinement theorem.** `Rep`, `RepPath`,
  `Located` and `Tree` say when a heap represents a zipper state of `Oris/RB/Fixup.lean`, and
  `rotateAt_refines_left` and `rotateAt_refines_right` prove that `rotateAt` (`NodeBase::rotate`)
  performs the zipper's rotation.
- **Step 3a, the structural operations.** `attachTo_refines`, `substituteWith_refines_left` and
  `_right`, and `switchWith_refines` prove that `attach_to`, `substitute_with` and `switch_with`
  perform the zipper steps `insert` and `eraseAt` take: fill an empty hole with a red leaf,
  splice out a node with at most one child, put another address at a node's position. Each
  operation, `rotateAt` included, also has a per-address description of its result (`_apply`)
  and the list of records it changes (`_frame`).
- **Step 3b, `insert_fixup`.** `insertFixupLoop_refines` and `insertFixup_refines` prove that
  `insert_fixup` performs `insFix`: the same tree and the same rotation count, from any located
  node in a tree with a black root, given enough fuel. `insertFixup_refines_depth` is the first
  fuel theorem: fuel at least the tree's depth is enough.
- **Step 3c, `erase_fixup`.** `eraseFixupLoop_refines` and `eraseFixupHpha_refines` prove that
  `erase_fixup`, in HPHA's reading (the root re-read), performs `delFix`: the same tree and the
  same rotation count, from any located subtree, the hole possibly empty, given the hole invariant
  (for the sentinel, its scratch `parent` and side name the slot), `DelFixClean` and enough fuel.
  `eraseFixupHpha_refines_depth` is the second fuel theorem.

Steps 3d (the cached root: the Rust's reading) and 4 (the counted operations, the chains and the
transfer theorems) remain.

## The files

Every declaration lives in the namespace `Oris.RB.Heap`, whichever file defines it.

- `Heap/Model.lean`: the model (the note's §2) and the transcriptions, with the list of
  departures.
- `Heap/Rep.lean`: the abstraction relation and its lemmas.
- `Heap/Apply.lean`: each structural operation address by address (`_apply`, `_frame`), and the
  colour writes.
- `Heap/Structural.lean`: `rotate`, `attach_to`, `substitute_with` and `switch_with` perform their
  zipper steps.
- `Heap/InsertFixup.lean`: `insert_fixup` performs `insFix`; the first fuel theorem.
- `Heap/EraseFixup.lean`: `erase_fixup`, HPHA's reading, performs `delFix`; the second fuel
  theorem.

The type `Heap` lives at `Oris.RB.Heap.Heap`, so `Heap.modify` is `Oris.RB.Heap.Heap.modify`.
-/
