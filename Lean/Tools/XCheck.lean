-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris

/-!
# `xcheck`: the Lean model against the running Rust code

Reads, on standard input, the trace that `rbtree.rs`'s ignored test
`print_lean_model_cross_check_trace` prints: one line per operation,

```
XC <I|E> <id> <key> <rotations> <C|N|L|P> <key shape> | <heap shape> | <sentinel>
```

then a last line `XC-END <steps> <erases>`. (The test's doc describes the fields.) Replays the
same operations, from an empty tree, through two models, and compares every line with each:

- **The zipper model**, `Oris.RB.insert` and `Oris.RB.erase` (`Oris/RB/Fixup.lean`): the tree of
  keys, so it must reproduce the rotation count, the kind and the key shape. An erase of a key
  that other live nodes share is a chain operation (`Link` or `Promote`), which leaves the tree of
  keys unchanged; the zipper model is then not run, and the line must report a chain kind and no
  rotation.
- **The heap model**, `Oris.RB.Heap.insertCounted` and `eraseCounted` (`Oris/RB/Heap.lean`), on a
  heap where null is `0`, the sentinel is at address `1` and the node of id `i` at `i + 2`: it
  must reproduce the whole line, so also every node's tagged `parent` word (pointer and side bit)
  and its equal-key chain in both directions, and the sentinel's `parent` word and colour. On
  every erase it also runs `eraseCountedHpha`, which re-reads `erase_fixup`'s root as HPHA does,
  and requires the same rotation count and the same heap, every field of every address the erase
  could reach, as the Rust's reading.

The run fails (exit 1) on any mismatch, on a line it cannot parse or replay, on a missing,
misplaced or inconsistent `XC-END` line (so a truncated trace fails), and when the trace does not
exercise every operation kind and every rotation count, or never empties the tree or changes the
root during a fix-up.

Run from `Lean/` (the CI job `lean-ci.yml` does exactly this):

```
cargo test --manifest-path ../Rust/Cargo.toml --lib \
  rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
  | grep '^XC' | lake exe xcheck
```
-/

open RBTree RBTree.RBNode RBTree.RBColor

namespace Oris.XCheck

/-- The trace's key-shape notation for a tree of keys. -/
def shape : RBNode Int → String
  | nil => "."
  | node c l v r =>
    let colour := match c with
      | red => "R"
      | black => "B"
    s!"({colour} {v} {shape l} {shape r})"

/-- The trace's letter for an insert's kind. -/
def insertLetter : Oris.RB.InsertKind → String
  | .chain => "C"
  | .node => "N"

/-- The trace's letter for an erase's kind. -/
def eraseLetter : Oris.RB.EraseKind → String
  | .link => "L"
  | .promote => "P"
  | .node => "N"

open Oris.RB.Heap

/-- The sentinel's address. -/
def headAddr : Addr := 1

/-- The address of the node of id `i`. -/
def addrOf (i : Nat) : Addr := i + 2

/-- More than enough fuel for every loop: the trace never has more than 150 live nodes. -/
def fuel : Nat := 1000

/-- A table read as a heap: one lookup per read. -/
def ofTable (table : Array NodeRec) : Heap := fun a => table.getD a default

/-- A pointer in the trace's notation: `h` for the sentinel, `-` for null, otherwise the id. -/
def ref (a : Addr) : String :=
  if a == headAddr then "h" else if a == 0 then "-" else toString (a - 2)

/-- One subtree, in the key-shape or the heap-shape notation. Recursion on the depth `fuel`;
the state counts the nodes still allowed, so a heap whose links form a cycle (a bug in the model)
yields `"?"` instead of an exponential walk. -/
def walk (h : Heap) (node : Addr → String) : Nat → Addr → StateT Nat Option String
  | 0, _ => failure
  | fuel + 1, a => do
    if a == headAddr then return "."
    let budget ← get
    if budget == 0 then failure
    set (budget - 1)
    let n := h a
    let colour := if n.red then "R" else "B"
    let l ← walk h node fuel n.left
    let r ← walk h node fuel n.right
    return s!"({colour} {node a} {l} {r})"

/-- The whole tree from the root (`head.child(Left)`), with `node` printing each node. -/
def tree (h : Heap) (node : Addr → String) : String :=
  match (walk h node 1000 (h headAddr).left).run 1000 with
  | some (str, _) => str
  | none => "?"

/-- The ids of `a`'s chain along `next` (`forward`) or `prev`, up to (not including) `a`. -/
def chain (h : Heap) (a : Addr) (forward : Bool) : String := Id.run do
  let step := fun x => if forward then (h x).next else (h x).prev
  let mut out : Array String := #[]
  let mut x := step a
  for _ in [0:1000] do
    if x == a then return " ".intercalate out.toList
    out := out.push (ref x)
    x := step x
  return "?"

/-- A node in the heap-shape notation: id, `parent` pointer and side, chain both ways. -/
def heapNode (h : Heap) (a : Addr) : String :=
  let n := h a
  let side := match n.side with
    | .left => "L"
    | .right => "R"
  s!"{ref a} {ref n.parent} {side} [{chain h a true}|{chain h a false}]"

/-- The sentinel's `parent` word and colour, in the trace's notation. -/
def headInfo (h : Heap) : String :=
  let n := h headAddr
  let side := match n.side with
    | .left => "L"
    | .right => "R"
  s!"{ref n.parent} {side}{if n.red then "R" else "B"}"

/-- Two heaps agree on every field of the given addresses. -/
def sameOn (h₁ h₂ : Heap) (as : Array Addr) : Bool := as.all fun a => h₁ a == h₂ a

/-- The replay's state. -/
structure State where
  /-- The zipper model's tree of keys. -/
  t : RBNode Int := nil
  /-- How many live nodes have each key. -/
  counts : Std.HashMap Int Nat := {}
  /-- The heap model, as a table. -/
  table : Array NodeRec := #[]
  /-- The key of the node at each address. -/
  keys : Array Int := #[]
  /-- The addresses of the live nodes. -/
  live : Array Addr := #[]

/-- What one line changes, and what it is compared with. -/
structure Outcome where
  state : State
  /-- The zipper model's `<rotations> <kind> <key shape>`. -/
  zipper : String
  /-- The heap model's whole line. -/
  heap : String
  /-- Whether `erase_fixup`'s two root readings gave the same rotations and the same heap. -/
  rootsAgree : Bool
  /-- Whether the root's address changed (an erase that rebalanced only). -/
  rootChanged : Bool

/-- Replays one line; `none` if it cannot be parsed or replayed (an unknown operation, an id
already used, an erase of a node not live, fuel running out). -/
def replay (s : State) (op : String) (id : Nat) (key : Int) (kind : String) : Option Outcome := do
  let a := addrOf id
  let isInsert := op == "I"
  unless isInsert || op == "E" do failure
  if isInsert && s.live.contains a then failure
  if !isInsert && !s.live.contains a then failure
  -- Grow the tables to cover `a`.
  let size := max (s.table.size) (a + 1)
  let table0 := if s.table.isEmpty then
      let empty : Heap := initHead (fun _ => default) headAddr
      Array.ofFn (n := size) fun i => empty i.val
    else s.table ++ Array.replicate (size - s.table.size) default
  let keys0 := s.keys ++ Array.replicate (size - s.keys.size) 0
  let keys := if isInsert then keys0.set! a key else keys0
  let keyOf : Addr → Int := fun x => keys.getD x 0
  let h := ofTable table0
  let rootBefore := (h headAddr).left
  -- The zipper model.
  let count := s.counts.getD key 0
  let (t', zipper) ←
    if isInsert then
      let (t', k, rot) := Oris.RB.insert compare s.t key
      pure (t', s!"{rot} {insertLetter k} {shape t'}")
    else if count > 1 then
      let k := if kind == "L" || kind == "P" then kind else "(a chain kind)"
      pure (s.t, s!"0 {k} {shape s.t}")
    else
      let (t', k, rot) ← Oris.RB.erase compare s.t key
      pure (t', s!"{rot} {eraseLetter k} {shape t'}")
  -- The heap model.
  let reach := s.live.push headAddr |>.push a
  let (h', letter, rot, rootsAgree) ←
    if isInsert then
      let (h', k, rot) ← insertCounted compare keyOf fuel h headAddr a
      pure (h', insertLetter k, rot, true)
    else
      let (h₁, k, r₁) ← eraseCounted fuel h headAddr a
      let (h₂, _, r₂) ← eraseCountedHpha fuel h headAddr a
      pure (h₁, eraseLetter k, r₁, r₁ == r₂ && sameOn h₁ h₂ reach)
  let heap := s!"XC {op} {id} {key} {rot} {letter} {tree h' (fun x => toString (keyOf x))} | \
    {tree h' (heapNode h')} | {headInfo h'}"
  let rootChanged := !isInsert && letter == "N" && (h' headAddr).left != rootBefore
  -- Copy the addresses the operation could reach into the table.
  let updates := reach.map fun x => (x, h' x)
  let table := updates.foldl (fun tb (x, r) => tb.set! x r) table0
  let live := if isInsert then s.live.push a else s.live.filter (· != a)
  let counts := s.counts.insert key (if isInsert then count + 1 else count - 1)
  return { state := { t := t', counts, table, keys, live }, zipper, heap, rootsAgree, rootChanged }

end Oris.XCheck

open Oris.XCheck in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut s : State := {}
  let mut lines := 0
  let mut bad := 0
  let mut zipperBad := 0
  let mut heapBad := 0
  let mut erases := 0
  let mut rootDiffer := 0
  let mut endLine : Option (Nat × Nat) := none
  let mut afterEnd := false
  -- Coverage: kinds, rotation counts, emptied trees, root changes.
  let mut seen : Std.HashMap String Nat := {}
  let note := fun (m : Std.HashMap String Nat) (k : String) => m.insert k (m.getD k 0 + 1)
  let report := fun (bad : Nat) (msg : String) => do
    if bad ≤ 3 then IO.println msg
  repeat
    let raw ← stdin.getLine
    if raw.isEmpty then break
    let line := raw.trimAscii.toString
    if endLine.isSome then
      afterEnd := true
      break
    if line.startsWith "XC-END " then
      match (line.splitOn " ")[1]?.bind String.toNat?, (line.splitOn " ")[2]?.bind String.toNat? with
      | some n, some e => endLine := some (n, e)
      | _, _ =>
        bad := bad + 1
        report bad s!"cannot parse `{line}`"
      continue
    lines := lines + 1
    let ws := ((line.splitOn " | ").headD "").splitOn " "
    let parsed := match ws[1]?, ws[2]?.bind String.toNat?, ws[3]?.bind String.toInt?, ws[5]? with
      | some op, some id, some key, some kind =>
        (replay s op id key kind).map fun o => (op, kind, o)
      | _, _, _, _ => none
    match parsed with
    | none =>
      bad := bad + 1
      report bad s!"line {lines}: cannot replay `{line}`"
    | some (op, kind, o) =>
      s := o.state
      let rustZipper := " ".intercalate (ws.drop 4)
      if op == "E" then erases := erases + 1
      if !o.rootsAgree then rootDiffer := rootDiffer + 1
      let zipperOk := o.zipper == rustZipper
      let heapOk := o.heap == line
      if !zipperOk then zipperBad := zipperBad + 1
      if !heapOk then heapBad := heapBad + 1
      if !zipperOk || !heapOk || !o.rootsAgree then
        bad := bad + 1
        report bad s!"MISMATCH at line {lines}:\n rust:   {line}\n zipper: {o.zipper}\n heap:   {o.heap}"
        if !o.rootsAgree then report bad " erase_fixup's two root readings disagree"
      seen := note seen s!"{op}{kind}"
      seen := note seen s!"{op} rot {(ws[4]?).getD "?"}"
      if op == "E" && s.live.isEmpty then seen := note seen "emptied"
      if o.rootChanged then seen := note seen "root changed"
  IO.println s!"{lines} operations compared, {bad} mismatches \
    (zipper model {zipperBad}, heap model {heapBad})"
  IO.println s!"erase_fixup's root, read once or re-read: {rootDiffer} of {erases} erases differ"
  let required := ["IN", "IC", "EN", "EL", "EP", "I rot 0", "I rot 1", "I rot 2", "E rot 0",
    "E rot 1", "E rot 2", "E rot 3", "emptied", "root changed"]
  IO.println s!"coverage: {", ".intercalate (required.map fun k => s!"{k} {seen.getD k 0}")}"
  let mut failed := bad != 0
  for k in required do
    if seen.getD k 0 == 0 then
      IO.println s!"the trace never exercises `{k}`"
      failed := true
  match endLine with
  | none =>
    IO.println "no XC-END line: the trace is truncated"
    failed := true
  | some (n, e) =>
    if n != lines || e != erases then
      IO.println s!"XC-END announces {n} operations and {e} erases, the trace has {lines} and \
        {erases}"
      failed := true
  if afterEnd then
    IO.println "lines after XC-END"
    failed := true
  if lines == 0 then
    IO.println "no input: nothing was checked"
    failed := true
  return (if failed then 1 else 0)
