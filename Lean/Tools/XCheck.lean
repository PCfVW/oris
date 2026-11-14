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
`(<R|B> <key> <left> <right>)` and each empty subtree `.`. Replays the same operations through
`Oris.RB.insert` and `Oris.RB.erase` from an empty tree and compares every line. Exits 0 only
if at least one line was read and every line matched; otherwise prints the first mismatches and
exits 1.

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

/-- One trace operation on the model; `none` for a malformed line or an erase of an absent key. -/
def step (t : RBNode Int) (op : String) (k : Int) : Option (RBNode Int × Nat) :=
  if op == "I" then
    let (t', _, rot) := Oris.RB.insert compare t k
    some (t', rot)
  else if op == "E" then
    (Oris.RB.erase compare t k).map fun (t', _, rot) => (t', rot)
  else none

end Oris.XCheck

open Oris.XCheck in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut t : RBNode Int := nil
  let mut lines := 0
  let mut bad := 0
  repeat
    let raw ← stdin.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    lines := lines + 1
    let ws := line.splitOn " "
    let parsed := match ws[1]?, ws[2]?.bind String.toInt? with
      | some op, some k => (step t op k).map fun r => (op, k, r)
      | _, _ => none
    match parsed with
    | none =>
      bad := bad + 1
      if bad ≤ 3 then IO.println s!"line {lines}: cannot replay `{line}`"
    | some (op, k, t', rot) =>
      t := t'
      let mine := s!"XC {op} {k} {rot} {shape t}"
      if mine != line then
        bad := bad + 1
        if bad ≤ 3 then IO.println s!"MISMATCH at line {lines}:\n rust: {line}\n lean: {mine}"
  IO.println s!"{lines} operations compared, {bad} mismatches"
  if lines == 0 then
    IO.println "no input: nothing was checked"
    return 1
  return (if bad == 0 then 0 else 1)
