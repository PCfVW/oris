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

The audit was checked to reject a `sorry`, a `native_decide`, a hand-written axiom (inside and
outside the `Oris` namespace), a module redefining the audit command of the old in-build gate,
and a theorem added with `debug.skipKernelTC`, which the kernel replay rejects too; since the
audit of 2026-11-21, also an `#eval!`, a `_root_.Lean...` name and a line over 100 characters,
which an earlier lint let through. (A `bv_decide` whose preprocessing closes the goal leaves an
ordinary kernel proof, which the audit rightly accepts.) If you change `Tools/Audit.lean`, re-run
those checks on a scratch copy of the project (the sorry, `native_decide`, both axioms,
`skipKernelTC` and the three later cases were re-run then).

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
module doc's complete list of departures. A departure that is *not* about a state proven
unreachable must be called out as such, with what settles it. Today: in `Fixup.lean`, the cached
`root` of `erase_fixup` (settled by the heap layer's planned cached-root theorem) and `setBlack`
leaving the sentinel alone where the Rust writes black over black (harmless); in `Heap/Model.lean`, the
loops' fuel (proven sufficient for `insert_fixup` by `insertFixup_refines_depth`; for `erase_fixup`
and the descents, to be proven by the heap layer's steps 3c and 4).

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
| `Oris/RB/Heap/InsertFixup.lean` | `insert_fixup` performs `insFix` (later parts: `EraseFixup.lean`, `CachedRoot.lean`, ...) |
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
