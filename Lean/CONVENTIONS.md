# Oris Lean Conventions (Grit-ORIS, proof dialect)

This document describes the conventions for the Lean 4 proofs under `Lean/`. They follow the
spirit of the [Amphigraphic](https://github.com/PCfVW/Amphigraphic-Strict) `Grit` discipline that
[`Rust/CONVENTIONS.md`](../Rust/CONVENTIONS.md) and [`Zig/CONVENTIONS.md`](../Zig/CONVENTIONS.md)
apply to the ports, adapted to what proofs are for.

**What is inverted here.** The ports' conventions make code safe to run; these make a theorem
safe to *believe*. A Lean proof that compiles can still mislead in three ways: it rests on
something other than the kernel (an axiom, `sorry`, compiled code); it proves something about a
model that is not what the Rust does; or its statement is weaker than its doc claims. Each rule
below closes one of those three gaps. Mechanical checks enforce the first; the second is held by
transcription discipline plus a running cross-check against the Rust; the third is held by doc
discipline.

The proofs are about `orisnik` (the Rust port). The two ports run the same algorithm transition
for transition ([the cross-port invariant](../ROADMAP.md)), so a theorem about the algorithm
carries over to `orisnitsa` to the extent that invariant holds; the trace gate checks it, nothing
proves it, and the cross-check runs against the Rust.

## Trigger Checklist

**Before writing any line, check which triggers apply.**

| You are about to... | Check these rules |
|---|---|
| Create a `.lean` file | [File layout](#file-layout), [the audit covers it](#the-audit-covers-every-module) |
| Write a `def` that models Rust code | [Transcription](#transcription-rules), [departures](#departures-are-listed) |
| Write a theorem | [Kernel-only](#kernel-only-proofs), [statement honesty](#statements-say-what-the-doc-says), [naming](#naming), [proof robustness](#proof-robustness) |
| Write a recursive `def` or theorem | [Termination](#termination) |
| Prove that heap code performs a zipper step | [Heap-layer proof patterns](#heap-layer-proof-patterns) |
| Write a `def` that is not a model of Rust code | [Proof devices](#proof-devices) |
| Try something out, or audit the proofs | [Scratch work and audits](#scratch-work-and-audits) |
| Change `Tools/Audit.lean` | [What the checks reject](#what-the-checks-reject) |
| Reach for `native_decide`, `bv_decide`, `sorry`, `axiom`, `admit` | [Kernel-only](#kernel-only-proofs) — don't |
| Model a `usize` computation | [Machine arithmetic](#machine-arithmetic) |
| Write a `-- ...` or `/-- ... -/` comment | [Doc comments](#doc-comments) |
| Touch `RBTree/` | [Vendored code](#vendored-code) |
| Change `rbtree.rs`, `tree.rs`, `bucket.rs` or `align.rs` | [Keeping the model in step](#keeping-the-model-in-step-with-the-rust) |
| Bump `lean-toolchain` or the Batteries pin | [Toolchain](#toolchain) |

---

## Kernel-only proofs

Every theorem must be checked by Lean's kernel and depend on nothing beyond the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). Concretely, never commit:

| Construct | Why it is banned |
|---|---|
| `sorry`, `admit` | elaborates to the axiom `sorryAx`: the theorem is unproven |
| `axiom` | an assumption, not a proof |
| `native_decide` | trusts compiled code: each use adds an auxiliary axiom (`<thm>._native.native_decide.ax_…`) asserting what the code computed |
| `bv_decide` | trusts a compiled SAT-certificate checker, through the same kind of auxiliary axiom |
| `implemented_by`, `@[extern]` on a definition a theorem unfolds | the theorem is about the reference definition, the run is about other code |
| metaprogramming (`elab`, `macro`, `syntax`, `run_cmd`, `run_meta`, `initialize`, any `Lean.` name) | code that runs during elaboration can add a declaration without the kernel check, or change how later commands, the tools' included, behave |
| `set_option` other than `maxHeartbeats` and `maxRecDepth` | `debug.skipKernelTC`, for one, switches the kernel check off |

`decide`, `omega`, `simp`, `rfl` and every other kernel-checked tactic are fine. A `decide` that
is too slow for the kernel is a sign to restate the lemma (prove it for a symbolic `k`, as
`and_not_two_pow_sub_one` does), not to switch to `native_decide`.

**Enforced by** two checks, both run by `lean-ci.yml` on every pull request:

- **The audit**, `lake exe audit` (`Tools/Audit.lean`). It runs after the build, as a separate
  executable that imports no proof module and loads their compiled environment without running
  any of their code, so a proof module cannot intercept it (a command run inside the build
  could be redefined by a module it imports). It checks every declaration *defined in* an Oris
  or RBTree module, whatever its name, `private` declarations and Lean's auxiliary ones
  included, against the three standard axioms; and it lints the source of every proof module,
  comments and strings removed, for the banned constructs above.
- **The kernel replay**, `lake env leanchecker --fresh Oris`, which re-checks every declaration
  from scratch: the axiom audit alone cannot see a declaration that was added with the kernel
  check switched off.

### What the checks reject

Each case below was added to a module of a scratch copy of the project and rejected. If you change
`Tools/Audit.lean`, re-run them all on a scratch copy (last re-run: 2026-11-21).

| Case | Rejected by |
|---|---|
| a `sorry` | the audit's axiom check (`sorryAx`) |
| a `native_decide` | the audit's axiom check (an auxiliary `..._native.native_decide.ax_...` axiom) |
| a hand-written `axiom`, inside or outside the `Oris` namespace | the audit's axiom check |
| a theorem added with `set_option debug.skipKernelTC true` | the audit's lint (`set_option`), and the kernel replay (checked 2026-11-15) |
| an `#eval!` (added 2026-11-21) | the audit's lint (any `#` command) |
| a `_root_.Lean...` name (added 2026-11-21) | the audit's lint (any `Lean` name component) |
| a line over 100 characters (added 2026-11-21) | the audit's lint |
| a module redefining the audit's command | nothing can: the audit runs outside the build and imports no proof module (the old in-build gate could be fooled this way) |

A `bv_decide` whose preprocessing closes the goal leaves an ordinary kernel proof, which the audit
rightly accepts.

### The audit covers every module

The audit imports every `.lean` file under `Oris/` and `RBTree/`, found on disk. The kernel
replay (`lake env leanchecker --fresh Oris`) checks what `Oris.lean` imports, so the audit also
fails if `Oris.lean` does not import a module under `Oris/` (read with Lean's own header parser).
(`lake build` builds every module under `Oris/` whatever `Oris.lean` imports: the lakefile's
`Oris.*` glob takes them all.) Every declaration of an Oris module must live
under the `Oris` namespace (Lean's internal auxiliary names, and the equation lemmas it generates
about constants defined elsewhere, excepted); the audit checks that too.

---

## Transcription rules

A `def` that models Rust code is a **transcription**, not a re-derivation:

1. **Name the Rust.** Its doc comment opens with the Rust item it models, in backticks
   (`` `rbtree.rs` `insert_fixup` ``, `` `NodeBase::rotate` ``, `` `tree.rs` `normalize_size` ``).
2. **Follow the operations in order**, case for case, rotation for rotation. Each case of a
   pattern match says which Rust case it is (which side, which branch of the Rust's `if`), in a
   comment on the arm or in the definition's doc, and the doc quotes the Rust statements it
   performs.
3. **Set every colour (or field) the Rust sets**, even where it changes nothing (the final
   `make_black(root)` on a root already black), and without looking at what it overwrites when
   the Rust does not look (`insFix` matches the grandparent's colour as `_` and paints it red).
   The model then agrees with the Rust on *every* input of the shapes it matches, not only on
   valid ones, and the cross-check can compare whole states.
4. **Keep Rust's structure where Lean allows.** A Rust helper (`rotate`, `set_colour`,
   `make_black(w.child(o))`) becomes a Lean function used the same way (`rotate`, `paint`,
   `mapChild`), not an inlined result. Where a step must be written out (a path after a
   rotation), add an `rfl` lemma that it *is* that step (`delFix_case1_fill_left`).
5. **Model the tree of keys at the zipper level.** Rust's parent pointers are `RBTree`'s
   `Path`; a node with its chain of parents is a `(subtree, Path)` pair. Pointer identity, the
   equal-key chains and the sentinel's scratch fields belong to the heap layer, not here.

### Departures are listed

Where a model deliberately does not follow the Rust (only ever on states the theorems prove
unreachable, unless stated otherwise), say so in **two** places: the definition's doc, and the
module doc's complete list of departures (`Fixup.lean`'s and `Heap/Model.lean`'s module docs
hold them). A theorem about the heap code takes, as a hypothesis, what rules out the zipper
model's departures on its input (`rootColour path ≠ some .red` for `insFix`'s red-root shape,
`DelFixClean` for `delFix`'s nil sibling), and the spec theorems derive it from a valid tree.

A departure that is *not* about a state proven unreachable must be called out as such, with what
settles it. The current ones (update this table with the module docs):

| Where | Departure | Settled by |
|---|---|---|
| `Fixup.lean` | `erase_fixup`'s root: the model re-reads it, as HPHA does; the Rust reads it once | step 3d, the cached-root theorem (it needs a black root: on a red root the readings differ) |
| `Fixup.lean` | `paint`, `setBlack`, `setRed` leave `nil` alone where the Rust's `make_black` writes the sentinel's colour bit | harmless: reachable only when an erase empties the tree, black over black |
| `Heap/Model.lean` | the loops' fuel: `none` when it runs out | `insertFixup_refines_depth`; `eraseFixupHpha_refines_depth` (HPHA's reading); step 3d (the Rust's reading of `erase_fixup`); step 4 (the descents) |
| `Heap/Model.lean` | `eraseFixupHpha` reads the root before testing `cur`'s colour, where HPHA's `&&` short-circuits | harmless: a read |

Lean's unused-variable linter does not see instance arguments: check by hand, by deleting it in
a scratch copy, that every `[Std.TransCmp cmp]` a theorem takes is needed.

---

## Statements say what the doc says

- A doc that says a proof "derives" or "proves" a fact needs a theorem whose statement is that
  fact. If the fact is only used inside a proof, either state it as its own theorem (as the
  `hpha_*` theorems state HPHA's `erase_fixup` assertions) or word the doc as "relies on".
- Every hypothesis must be needed. If Lean's unused-variable linter flags a hypothesis of a
  theorem, drop it (the theorem becomes stronger) rather than silencing the linter.
- Give the result its strongest honest form: prefer an equation with an independent reference
  (`insert_spec`: the same `toList` as the library's verified `RBNode.insert`) over a property
  checked in isolation.
- Specification theorems (`*_spec`) take only hypotheses the Rust's callers guarantee (a valid
  tree with a black root, a request at or below `MAX_ALLOCATION`); their docs say what those are.

---

## Proof robustness

A proof that compiles today should still compile after a toolchain or library bump, and after a
small change to a definition, or fail where the change is. These rules came out of the audit of
2026-11-21 (`docs/audits/2026-11-21-fresh-eyes/`, robustness findings R1–R10):

- **No `simp [*]`.** Name the facts `simp` may use.
- **A plain `simp` or `simp_all` only to close a goal.** In the middle of a proof, use
  `simp only [...]` with its lemmas (`simp?` prints the list). When a case split must follow, split
  first and close each case with a terminal `simp`.
- **No `rfl` that unfolds a recursive definition.** Rewrite with its equations (`rw [insFix]`,
  `simp only [insFix, ...]`). A well-founded definition such as `delFix` does not unfold by
  `rfl` at all: give it per-arm equation lemmas next to its definition.
- **A loop's definition is unfolded in one place**: one lemma per branch
  (`insertFixupLoop_red_uncle`, `_black_uncle_outer`, `_black_uncle_inner`), which the proofs
  about the loop use.
- **No positional projections into a long conjunction** (`.2.2.2.1`). Return a structure with
  named fields (`Rep.NodeView`, `NodupNode`), or destructure with `obtain ⟨name, ...⟩` right where
  the conjunction is stated.
- **Core's list normal forms are unpacked in one place each**: `List.nodup_append`'s in
  `nodup_node`, `nodup_node_intro` and `nodup_withList`.
- **No generated names.** No `fun_induction ... with | case1 ...`; no `rename_i` binding the
  fields of a match after `split` (case on the scrutinee, or `cases h : e with`). One `rename_i`
  naming the single condition that `split` on an `if` brings in is fine.
- **An argument made more than twice becomes a lemma** (`Rep.ne_root`, the sentinel-or-member
  argument; `rotateAt_sentinel`, the sentinel's fields under a rotation).

---

## Heap-layer proof patterns

How the refinement proofs of `Oris/RB/Heap/` are built; follow the same shapes for new ones.

- **Two descriptions of every write.** Address by address: an `if` chain under the distinctness
  the callers guarantee (`rotateAt_apply`, `switchWith_apply`) and the addresses it leaves alone
  (`_frame`). On a located subtree: what the write does to the zipper state (`Located.paint` for
  a colour, `rotateAt_refines_left`/`_right` for a rotation, `attachTo_refines`, ...). Proofs
  combine the second kind; the first kind proves the second.
- **Moving along the path.** `Located.up_left`/`_right` climb from a child to its parent's
  subtree, `down_left`/`_right` descend. After a write, a climb needs the slot node's `parent`
  word in the *new* heap: rewrite the indices first, with `setColour_slot` after a colour write
  and `rotateAt_slot_left`/`_right` after a rotation.
- **Distinctness.** `Rep.ne_root`: an address that is neither the sentinel nor in a subtree is not
  that subtree's first address. Membership in `toList` (`fun e => hxt (by simp [e])`) for the
  rest; `Rep.addr_eq` when two heaps represent the same subtree.
- **Colours read back** through `Rep.red_eq` (the sentinel reads black), and **the root test**
  through `Located.eq_root_iff` (`cur` is the root exactly when the path is empty).
- **Loops.** One step lemma per branch of an iteration, each for either side, stated with the
  loop's own reads (`insertFixupLoop_red_uncle`, `eraseFixupLoop_case1_finish`); the refinement
  theorem by induction on fuel, following the zipper function's arms through its equation lemmas
  (`delFix_left_black_none`, ...); at an exit, `Located.fill` or `Tree.makeBlack_root`.
- **Mirror images.** Each case comes as `_left` and `_right`, written out; a side-generic lemma is
  preferred wherever the statement does not depend on the side (`rotateAt_sentinel`, the step
  lemmas).

### Proof devices

A proof module may define something that is not a model of Rust code, to name a segment of a
transcription that several proofs use (`case1Heap`, `case1Sibling`, `finishHeap` in
`Heap/EraseFixup.lean`: the writes of `erase_fixup`'s first case, and of its third and fourth).
Such a **proof device** is allowed when:

1. its doc says it is a proof device and names the transcription and the statements it covers;
2. a step lemma proves that the transcription performs exactly it (`eraseFixupLoop_finish`,
   ...), so it adds nothing a reader must trust;
3. it is never defined in `Heap/Model.lean`, which holds only transcriptions.

---

## Scratch work and audits

- **Scratch files** go outside `Oris/` (a `Scratch.lean` next to `Oris.lean`, or outside the
  repository), are checked with `lake env lean <file>`, which reads the built project without
  changing it, and are never committed. Before committing, delete them; `lake build` does not see
  them, but they confuse a reader of `git status`.
- **Audits.** A full audit keeps its record in `docs/audits/<date>-<name>/`: `findings.json`
  (every finding with its verdict, and the corrected fix where a verifier changed it), the scratch
  files behind the findings in `scratch/` (each with the SPDX header, not built, not maintained),
  and a `README.md` (the method, the results, the decisions, the follow-up). Local paths are made
  relative before committing.

---

## Machine arithmetic

Rust's `usize` is `BitVec 64` (the crate is 64-bit only), and expressions are transcribed with
the Rust's operators (`&&& ~~~(a - 1)` for `& !(a - 1)`, `>>>` for `>>`). Rust's `+`/`-` panic
on overflow in debug builds and wrap in release builds, while `BitVec` wraps, so theorems about
a computation that adds or subtracts come in two halves: **the operation does not overflow**
(stated on `toNat`), and **the mathematical value is what the caller needs**. Layout constants
(`size_of::<BlockHeader>()`, ...) are the values of the Rust's compile-time assertions or
constants; the module doc names them.

---

## Termination

Prefer structural recursion (Lean checks it with no annotation). When a `def` needs
well-founded recursion, give `termination_by` a measure the Rust's own loop obviously decreases
(the zipper path, which shrinks as the loop climbs), and prove `decreasing_by` with `simp_wf;
omega`, not `decreasing_tactic` magic you cannot read. A theorem about such a `def` that does
case analysis on its argument may recurse on an explicit size bound instead
(`delFix_balanced_aux`), which keeps the size relation visible after `cases`.

---

## Naming

| Kind | Form | Examples |
|---|---|---|
| Model of a Rust function | short camel case after the Rust name | `insFix` (`insert_fixup`), `delFix`, `eraseAt`, `normalizeSize` |
| Heap-level model whose zipper-level model has the same name | the same, suffixed `At` (it acts at an address) | `childAt` (`NodeBase::child`), `rotateAt` (`NodeBase::rotate`) |
| A heap operation's result, address by address | `<op>_apply` | `rotateAt_apply`, `switchWith_apply` |
| The addresses a heap operation leaves unchanged | `<op>_frame` | `rotateAt_frame`, `attachTo_frame` |
| A heap operation performs its zipper step | `<op>_refines` | `attachTo_refines`, `insertFixup_refines` |
| A lemma about a relation or structure `R` | `R.<lemma>` | `Rep.frame`, `Located.up_left`, `Heap.modify_red` |
| An inversion (what a constructor's premises say, read back) | `_inv` | `Rep.node_inv`, `RepPath.left_inv` |
| One iteration of a loop, one branch | `<loop>_<branch>` | `insertFixupLoop_red_uncle`, `eraseFixupLoop_case1_finish` |
| What one case's writes do to a located subtree | `case<N>_left` / `_right`, `finish_left` / `_right` | `case1_left`, `finish_right` |
| A zipper function's arm, as an equation | `<def>_<arm>` | `delFix_root`, `delFix_left_red_none` |
| Mirror-image definitions | suffix `L` / `R` (the side `cur` is on) | `stage2L`, `stage2R` |
| Lemma about a definition | `<def>_<property>` | `insFix_toList`, `delFix_rotations`, `stage2L_balanced` |
| Mirror-image standalone theorems | suffix `_left` / `_right` | `hpha_sibling_not_sentinel_left` |
| Correctness theorem of an operation | `<def>_spec` | `insert_spec`, `erase_spec`, `normalizeSize_spec` |
| A fact HPHA asserts | `hpha_<fact>` | `hpha_far_child_red_left` |
| A fact about HPHA's own code | `hpha_<function>_...`, or `<def>_<property>` for a model of HPHA's code | `hpha_normalize_SIZE_MAX`; `hphaMask_eq` (about the model `hphaMask`) |

Properties use the same words everywhere: `_toList` (only rearranges), `_rotations` (rotation
bound), `_balanced` (red-black invariant), `_spec` (the operation's full contract).

---

## Doc comments

- Every file begins with `-- SPDX-License-Identifier: MIT OR Apache-2.0`, then its `import`s,
  then a `/-! ... -/` module doc (Lean requires imports first).
- The module doc says what the file models, where its definitions come from, and lists its
  departures from the Rust.
- Every `def` and every theorem that a reader outside the file would cite has a `/-- ... -/` doc.
  Lemmas that only serve one proof may go without.
- Backtick Rust and Lean identifiers. Name Rust functions as the Rust spells them, and say which
  file they are in the first time.
- Lines stay within 100 columns, as in the ports.

## File layout

| Path | Contents |
|---|---|
| `Oris/Arith.lean` | Size arithmetic |
| `Oris/RB/Fixup.lean` | The red-black tree at the zipper level, and the path facts the heap layer uses |
| `Oris/RB/Heap.lean` | The pointer level's overview: imports its parts, says what is proven, file by file |
| `Oris/RB/Heap/Model.lean` | The pointer level's definitions: the model heap and the transcriptions, with their departures |
| `Oris/RB/Heap/Rep.lean` | The abstraction relation (`Rep`, `RepPath`, `Located`, `Tree`) and its lemmas |
| `Oris/RB/Heap/Apply.lean` | Each structural operation address by address (`_apply`, `_frame`), the colour writes |
| `Oris/RB/Heap/Structural.lean` | `rotate`, `attach_to`, `substitute_with`, `switch_with` perform their zipper steps |
| `Oris/RB/Heap/InsertFixup.lean` | `insert_fixup` performs `insFix` |
| `Oris/RB/Heap/EraseFixup.lean` | `erase_fixup`, HPHA's reading, performs `delFix` (later parts: `CachedRoot.lean`, `Counted.lean`, ...) |
| `Tools/` | Executables, run after the build (`Audit.lean`, the axiom audit and lint; `XCheck.lean`, the cross-check consumer) |
| `docs/` | Design notes (`heap-layer.md`), agreed before the proofs they plan; audit records (`audits/`), each with its findings and the scratch files behind them, not built |
| `RBTree/` | Vendored, verbatim |

---

## Vendored code

`RBTree/` is copied verbatim from `leanprover-community/batteries-recycling`. Do not edit it in
place casually: any change is recorded in `RBTree/NOTICE.md`, file by file, with its reason, the
way `Cpp/ERRATA.md` records departures from HPHA. New lemmas about the library go in `Oris/`,
under the `Oris` namespace, not into `RBTree/`.

---

## Keeping the model in step with the Rust

The cross-check holds the model to the running code: `rbtree.rs`'s ignored test
`print_lean_model_cross_check_trace` prints, for 20,000 operations, each rotation count and the
whole tree's shape and colours; `lake exe xcheck` replays the operations through the model and
fails on any difference (the `xcheck` job of `lean-ci.yml`).

- A change to `rbtree.rs`'s tree logic that changes shapes or rotation counts changes the
  cross-port transition records too (see the root `CLAUDE.md`), and must update
  `Oris/RB/Fixup.lean` in the same commit so the cross-check passes.
- A change to `rbtree.rs`'s pointer code (any read or write of a `NodeBase` field, or their
  order) must update `Oris/RB/Heap/Model.lean` in the same commit: the heap model transcribes it
  write by write, and the cross-check runs it.
- A change to `tree.rs`'s, `bucket.rs`'s or `align.rs`'s size arithmetic must update
  `Oris/Arith.lean` in the same commit.
- A change to the trace format must change both the Rust producer and `Tools/XCheck.lean`.

## Toolchain

`lean-toolchain` and the Batteries pin in `lakefile.toml` move together, to a Batteries release
tag named after the toolchain. After a bump, the vendored library must still build unchanged (or
its patch is recorded in `RBTree/NOTICE.md`), and every check of `CLAUDE.md` must pass. No
Mathlib: the project needs only Batteries, and a heavy dependency would slow every CI run for
nothing.
