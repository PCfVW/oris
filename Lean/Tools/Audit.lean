-- SPDX-License-Identifier: MIT OR Apache-2.0
import Lean

/-!
# `audit`: the axiom audit, run outside the proofs

Checks, after `lake build`, that every proof in the project rests on Lean's kernel and its three
standard axioms alone. It runs as a separate executable, not as a command inside the build, so
that no code in a proof module can intercept or imitate it: this file imports `Lean` only, never a
proof module, and loads the proofs' compiled environment with `importModules`, which runs none of
their code.

Four checks, each failing the run:

1. **Every module is audited.** Every `.lean` file under `Oris/` and `RBTree/` (plus `RBTree.lean`)
   is imported, found on disk rather than through any import list. `Oris.lean` must import every
   module under `Oris/`, read with Lean's own header parser (so an `import` line inside a comment
   does not count), since the kernel replay (`lake env leanchecker --fresh Oris`) checks what
   `Oris.lean` imports. (`lake build` builds every module under `Oris/` anyway: the lakefile's
   `Oris.*` glob.)
2. **Axioms, by defining module.** Every constant defined in one of those modules, `private` and
   auxiliary ones included, whatever its name, depends on `propext`, `Classical.choice` and
   `Quot.sound` at most (`collectAxioms`, transitively). A `sorry` shows up as `sorryAx`, a
   `native_decide` or a `bv_decide` that reaches its checker as an auxiliary axiom per use, and a
   hand-written `axiom` as itself.
3. **Namespaces.** Every constant defined in an `Oris` module lives under the `Oris` namespace, or
   is one of Lean's internal auxiliary names (a name component starting with `_`), or is an
   equation lemma Lean generated about a constant defined outside the `Oris` modules.
4. **Lint.** The source of every module under `Oris/`, comments and string literals removed, uses
   none of the constructs that could bypass the kernel or tamper with tooling: metaprogramming
   (`elab`, `macro`, `syntax`, `run_cmd`, `run_meta`, `initialize`, any name with a `Lean`
   component, `_root_.Lean...` included, ...), any `#` command (`#eval`, `#eval!`, `#print`, ...),
   `set_option` other than `maxHeartbeats` and `maxRecDepth` (in particular
   `debug.skipKernelTC`), and the constructs `CONVENTIONS.md` bans (`sorry`, `axiom`,
   `native_decide`, `implemented_by`, ...). And every line, comments included, stays within 100
   characters (`CONVENTIONS.md`, § Doc comments).

What this does not check: that each proof was actually checked by the kernel. A module can add a
declaration with the kernel check switched off; checks 2 and 4 make that hard to do unnoticed, and
the kernel replay `lake env leanchecker --fresh Oris` (run by `lean-ci.yml`) re-checks every
declaration from scratch.

Run from `Lean/`, after `lake build --wfail`: `lake exe audit`.
-/

open Lean System

namespace Oris.AuditTool

/-- The axioms a proof may depend on: Lean's three standard axioms. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The roots of the audited modules. -/
def auditedRoots : List Name := [`Oris, `RBTree]

/-- `set_option`s a proof module may use: resource limits only. -/
def allowedOptions : List String := ["maxHeartbeats", "maxRecDepth"]

/-- Tokens no proof module may contain, outside comments and string literals. -/
def forbiddenTokens : List String :=
  [ -- Unproven or untrusted results.
    "sorry", "admit", "axiom", "native_decide", "bv_decide", "implemented_by", "extern",
    "unsafe", "partial", "opaque",
    -- Metaprogramming: code that runs during elaboration and could add declarations without
    -- the kernel check, or change how later commands (the tools' included) behave.
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "run_cmd", "run_meta", "run_elab", "#eval", "#exit",
    "initialize", "builtin_initialize", "command_elab", "term_elab", "tactic", "declare_syntax_cat",
    "IO" ]

/-- The module name of a file path relative to `Lean/` (`Oris/RB/Heap.lean` ↦ `Oris.RB.Heap`). -/
def moduleOf (p : FilePath) : Name :=
  let parts := (p.withExtension "").components.filter (· != ".")
  parts.foldl Name.str .anonymous

/-- The `.lean` files under a directory, sorted. -/
def leanFiles (dir : FilePath) : IO (Array FilePath) := do
  let all ← dir.walkDir
  return (all.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)

/-- The source with comments (`--`, nested `/- -/`, doc comments included) and the contents of
string literals replaced by spaces, newlines kept. -/
partial def stripComments (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '-' :: '-' :: rest => line rest
  | '/' :: '-' :: rest => block 1 rest
  | '"' :: rest => ' ' :: str rest
  | c :: rest => c :: stripComments rest
where
  line : List Char → List Char
    | [] => []
    | '\n' :: rest => '\n' :: stripComments rest
    | _ :: rest => line rest
  block : Nat → List Char → List Char
    | _, [] => []
    | d, '/' :: '-' :: rest => block (d + 1) rest
    | d, '-' :: '/' :: rest => if d == 1 then ' ' :: stripComments rest else block (d - 1) rest
    | d, '\n' :: rest => '\n' :: block d rest
    | d, _ :: rest => block d rest
  str : List Char → List Char
    | [] => []
    | '\\' :: _ :: rest => str rest
    | '"' :: rest => ' ' :: stripComments rest
    | '\n' :: rest => '\n' :: str rest
    | _ :: rest => str rest

/-- Characters that continue a token: ASCII letters and digits, `_ . ' ! ? # @`, and the non-ASCII
letters Lean identifiers use (Greek, subscripts, ...). Brackets, arrows and other symbols end a
token, so `⟨sorry⟩` yields `sorry`. -/
def tokenChar (c : Char) : Bool :=
  c.isAlphanum || "_.'!?#@".contains c ||
    (c.toNat ≥ 0x370 && c.toNat < 0x400) ||   -- Greek
    (c.toNat ≥ 0x2080 && c.toNat < 0x209d) || -- subscripts
    (c.toNat ≥ 0x1d00 && c.toNat < 0x1dc0)    -- phonetic extensions (ᵢ, ...)

/-- The tokens of a stripped source, with their line numbers. -/
def tokens (cs : List Char) : Array (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  let mut cur : String := ""
  let mut lineNo := 1
  for c in cs do
    if tokenChar c then
      cur := cur.push c
    else
      if !cur.isEmpty then out := out.push (cur, lineNo)
      cur := ""
      if c == '\n' then lineNo := lineNo + 1
  if !cur.isEmpty then out := out.push (cur, lineNo)
  return out

/-- The longest line a source file may have, in characters (`CONVENTIONS.md`, § Doc comments). -/
def maxColumns : Nat := 100

/-- The lint findings for one file. -/
def lintFile (path : FilePath) : IO (Array String) := do
  let src ← IO.FS.readFile path
  let toks := tokens (stripComments src.toList)
  let mut bad : Array String := #[]
  for h : i in [0:toks.size] do
    let (tok, ln) := toks[i]
    let at_ := s!"{path}:{ln}"
    if forbiddenTokens.contains tok then
      bad := bad.push s!"{at_}: forbidden `{tok}`"
    else if tok.startsWith "#" then
      bad := bad.push s!"{at_}: forbidden `{tok}` (no `#` command in proof modules)"
    else if (tok.splitOn ".").contains "Lean" then
      bad := bad.push s!"{at_}: forbidden `{tok}` (no metaprogramming in proof modules)"
    else if tok == "set_option" then
      let opt := (toks[i + 1]?.map (·.1)).getD ""
      unless allowedOptions.contains opt do
        bad := bad.push s!"{at_}: forbidden `set_option {opt}`"
  let mut ln := 0
  for line in src.splitOn "\n" do
    ln := ln + 1
    let n := line.length - (if line.endsWith "\r" then 1 else 0)
    if n > maxColumns then
      bad := bad.push s!"{path}:{ln}: line of {n} characters (at most {maxColumns})"
  return bad

/-- An equation lemma Lean generated, on first use, about a constant defined outside the `Oris`
modules (`RBTree.RBNode.forM.match_1.eq_1`, ...): the lemma is filed under the module that used it,
but its name is the foreign constant's. -/
def generatedForeign (env : Environment) (names : Array Name) (user : Name) : Bool :=
  let isEqn := match user with
    | .str _ s => s == "eq_def" || s == "splitter" || s == "eq_unfold" ||
        (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && s.length > 3)
    | _ => false
  isEqn && match env.getModuleIdxFor? user.getPrefix with
    | some idx => names[idx.toNat]?.map (fun m => m.components.headD .anonymous != `Oris)
        |>.getD false
    | none => false

/-- The root namespace of a module name. -/
def rootOf (n : Name) : Name := n.components.headD .anonymous

end Oris.AuditTool

open Oris.AuditTool in
def main : IO UInt32 := do
  let mut problems : Array String := #[]
  -- 1. The modules, from the files on disk.
  let orisFiles ← leanFiles "Oris"
  let rbFiles ← leanFiles "RBTree"
  let orisMods := orisFiles.map moduleOf
  let mods : Array Name := orisMods ++ rbFiles.map moduleOf ++ #[`RBTree]
  if orisMods.isEmpty || rbFiles.isEmpty then
    problems := problems.push "no module found under Oris/ or RBTree/: run from Lean/"
  let (imports, _, _) ← Lean.Elab.parseImports (← IO.FS.readFile "Oris.lean") (some "Oris.lean")
  let imported := imports.map (·.module)
  for m in orisMods do
    unless imported.contains m do
      problems := problems.push
        s!"Oris.lean does not import {m}, so the kernel replay does not check it"
  -- 2 and 3. Axioms and namespaces, by defining module.
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 0)
  let names := env.header.moduleNames
  let mut counts : Std.HashMap Name Nat := {}
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some modName := names[idx.toNat]? | continue
    let root := rootOf modName
    unless auditedRoots.contains root do continue
    counts := counts.insert root (counts.getD root 0 + 1)
    try
      let axs ← (collectAxioms n : CoreM _).toIO'
        { fileName := "audit", fileMap := default } { env }
      let bad := axs.filter (!allowedAxioms.contains ·)
      unless bad.isEmpty do
        problems := problems.push s!"{n} (in {modName}) depends on non-standard axioms: {bad}"
    catch _ =>
      problems := problems.push s!"{n}: could not collect its axioms"
    if root == `Oris then
      let user := (privateToUserName? n).getD n
      unless (`Oris).isPrefixOf user || user.isInternal || generatedForeign env names user do
        problems := problems.push s!"{n} (in {modName}) is outside the Oris namespace"
  -- 4. Lint.
  for f in orisFiles do
    problems := problems ++ (← lintFile f)
  -- Report.
  let orisCount := counts.getD `Oris 0
  let rbCount := counts.getD `RBTree 0
  if orisCount == 0 || rbCount == 0 then
    problems := problems.push "no declaration found in the Oris or RBTree modules"
  for p in problems do IO.println s!"FAIL {p}"
  if problems.isEmpty then
    IO.println s!"audited {orisCount} declarations from {orisMods.size} Oris modules and \
      {rbCount} from {rbFiles.size + 1} RBTree modules: standard axioms only"
    IO.println s!"namespaces, imports and lint ({orisFiles.size} files): clean"
    return 0
  IO.println s!"audit failed: {problems.size} problems"
  return 1
