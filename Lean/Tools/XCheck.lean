-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris

/-!
# `xcheck`: the Lean model against the running Rust code

Reads, on standard input, the trace that `rbtree.rs`'s ignored test
`print_lean_model_cross_check_trace` prints: one line per operation,

```
XC <I|E> <key> <rotations> <shape>
```

where `<shape>` is the whole tree after the operation, preorder, each node written
`(<R|B> <key> <left> <right>)` and each empty subtree `.`. Replays the same operations, from an
empty tree, through two models, and compares every line with each:

- the zipper model, `Oris.RB.insert` and `Oris.RB.erase` (`Oris/RB/Fixup.lean`);
- the heap model, `Oris.RB.Heap.insertCounted` and `eraseCounted` (`Oris/RB/Heap.lean`), on a
  heap where the sentinel is at address 1 and the node of key `k` at address `k + 2` (the trace's
  keys are distinct, in `[0, 1000)`). On every erase it also runs `eraseCountedHpha`, which
  re-reads `erase_fixup`'s root as HPHA does, and requires the same rotation count and the same
  whole heap, every field of every address, as the Rust's reading.

The heap is copied into a table after each operation, so that reads stay one lookup
(`docs/heap-layer.md`, §5); the loop keeps the table itself (see `toTable`). Exits 0 only if at
least one line was read and every line matched both models with the two root readings agreeing;
otherwise prints the first mismatches and exits 1.

Run from `Lean/` (the CI job `lean-ci.yml` does exactly this):

```
cargo test --manifest-path ../Rust/Cargo.toml --lib \
  rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
  | grep '^XC ' | lake exe xcheck
```
-/

open RBTree RBTree.RBNode RBTree.RBColor

namespace Oris.XCheck

/-- The trace's shape notation for a tree of keys. -/
def shape : RBNode Int → String
  | nil => "."
  | node c l v r =>
    let colour := match c with
      | red => "R"
      | black => "B"
    s!"({colour} {v} {shape l} {shape r})"

/-- One trace operation on the zipper model; `none` for a malformed line or an erase of an absent
key. -/
def step (t : RBNode Int) (op : String) (k : Int) : Option (RBNode Int × Nat) :=
  if op == "I" then
    let (t', _, rot) := Oris.RB.insert compare t k
    some (t', rot)
  else if op == "E" then
    (Oris.RB.erase compare t k).map fun (t', _, rot) => (t', rot)
  else none

open Oris.RB.Heap in
/-- The heap model's addresses: null `0`, the sentinel `1`, the node of key `k` at `k + 2`. -/
def heapSize : Nat := 1002

/-- The sentinel's address. -/
def headAddr : Oris.RB.Heap.Addr := 1

/-- The key of the node at an address. -/
def keyOf (a : Oris.RB.Heap.Addr) : Int := (a : Int) - 2

/-- Enough fuel for every loop on a tree of at most `heapSize` nodes. -/
def fuel : Nat := 2 * heapSize

open Oris.RB.Heap in
/-- A heap's records, address by address, as a table. The replay keeps the table, not the heap:
a `def` returning a `Heap` (a function) is compiled with the function's argument as one more
parameter, which would rebuild the table on every read. -/
def toTable (h : Heap) : Array NodeRec := Array.ofFn (n := heapSize) fun i => h i.val

open Oris.RB.Heap in
/-- A table read as a heap: one lookup per read, whatever the number of writes that built it. -/
def ofTable (table : Array NodeRec) : Heap := fun a => table.getD a default

open Oris.RB.Heap in
/-- The empty tree: every node `UNLINKED`, the sentinel self-linked (`initHead`). -/
def emptyTable : Array NodeRec := toTable (initHead (fun _ => default) headAddr)

open Oris.RB.Heap in
/-- One subtree of `heapShape`: recursion on the depth `fuel`, while the state counts the nodes
still allowed. -/
def heapShapeAux (h : Heap) : Nat → Addr → StateT Nat Option String
  | 0, _ => failure
  | fuel + 1, a => do
    if a == headAddr then return "."
    let budget ← get
    if budget == 0 then failure
    set (budget - 1)
    let n := h a
    let colour := if n.red then "R" else "B"
    let l ← heapShapeAux h fuel n.left
    let r ← heapShapeAux h fuel n.right
    return s!"({colour} {keyOf a} {l} {r})"

open Oris.RB.Heap in
/-- The trace's shape notation, read off the heap from the root (`head.child(Left)`). At most
`heapSize` nodes are visited, whatever the links: a heap whose links form a cycle (a bug in the
model) yields `"?"` after that many steps, instead of an exponential walk. -/
def heapShape (h : Heap) : String :=
  match (heapShapeAux h heapSize (h headAddr).left).run heapSize with
  | some (str, _) => str
  | none => "?"

open Oris.RB.Heap in
/-- Two heaps agree on every field of every address of the table. -/
def sameHeap (h₁ h₂ : Heap) : Bool := (List.range heapSize).all fun a => h₁ a == h₂ a

open Oris.RB.Heap in
/-- One trace operation on the heap model: the new heap (the Rust's reading of `erase_fixup`'s
root), the rotations, and whether HPHA's reading gave the same rotations and the same heap.
`none` for a malformed line, a key out of range, or fuel running out. -/
def heapStep (h : Heap) (op : String) (k : Int) : Option (Heap × Nat × Bool) :=
  if k < 0 ∨ k ≥ (heapSize : Int) - 2 then none
  else
    let a : Addr := (k + 2).toNat
    if op == "I" then
      (insertCounted compare keyOf fuel h headAddr a).map fun (h', _, rot) => (h', rot, true)
    else if op == "E" then
      match eraseCounted fuel h headAddr a, eraseCountedHpha fuel h headAddr a with
      | some (h₁, _, r₁), some (h₂, _, r₂) => some (h₁, r₁, r₁ == r₂ && sameHeap h₁ h₂)
      | _, _ => none
    else none

end Oris.XCheck

open Oris.XCheck Oris.RB.Heap in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut t : RBNode Int := nil
  let mut table : Array NodeRec := emptyTable
  let mut lines := 0
  let mut bad := 0
  let mut heapBad := 0
  let mut erases := 0
  let mut rootDiffer := 0
  repeat
    let raw ← stdin.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    lines := lines + 1
    let ws := line.splitOn " "
    let parsed := match ws[1]?, ws[2]?.bind String.toInt? with
      | some op, some k =>
        match step t op k, heapStep (ofTable table) op k with
        | some r, some hr => some (op, k, r, hr)
        | _, _ => none
      | _, _ => none
    match parsed with
    | none =>
      bad := bad + 1
      if bad ≤ 3 then IO.println s!"line {lines}: cannot replay `{line}`"
    | some (op, k, (t', rot), (h', hrot, rootsAgree)) =>
      t := t'
      table := toTable h'
      let h := ofTable table
      let mine := s!"XC {op} {k} {rot} {shape t}"
      let heapLine := s!"XC {op} {k} {hrot} {heapShape h}"
      if op == "E" then erases := erases + 1
      if !rootsAgree then rootDiffer := rootDiffer + 1
      if heapLine != line then heapBad := heapBad + 1
      if mine != line || heapLine != line || !rootsAgree then
        bad := bad + 1
        if bad ≤ 3 then
          IO.println s!"MISMATCH at line {lines}:
 rust: {line}
 lean: {mine}
 heap: {heapLine}"
          if !rootsAgree then IO.println " erase_fixup's two root readings disagree"
  IO.println s!"{lines} operations compared, {bad} mismatches"
  IO.println s!"heap model: {heapBad} mismatches"
  IO.println s!"erase_fixup's root, read once or re-read: {rootDiffer} of {erases} erases differ"
  if lines == 0 then
    IO.println "no input: nothing was checked"
    return 1
  return (if bad == 0 then 0 else 1)
