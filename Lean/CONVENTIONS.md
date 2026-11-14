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

The proofs are about `orisnik` (the Rust port). Because the two ports run the same algorithm
transition for transition ([the cross-port invariant](../ROADMAP.md)), a theorem about the
algorithm holds for `orisnitsa` too, but the cross-check runs against the Rust.

## Trigger Checklist

**Before writing any line, check which triggers apply.**

| You are about to... | Check these rules |
|---|---|
| Create a `.lean` file | [File layout](#file-layout), [the gate covers it](#the-gate-covers-every-module) |
| Write a `def` that models Rust code | [Transcription](#transcription-rules), [departures](#departures-are-listed) |
| Write a theorem | [Kernel-only](#kernel-only-proofs), [statement honesty](#statements-say-what-the-doc-says), [naming](#naming) |
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
| `native_decide` | trusts compiled code through `Lean.ofReduceBool` (and an auxiliary axiom per use) |
| `bv_decide` | trusts a compiled SAT-certificate checker through `Lean.ofReduceBool` |
| `implemented_by`, `@[extern]` on a definition a theorem unfolds | the theorem is about the reference definition, the run is about other code |

`decide`, `omega`, `simp`, `rfl` and every other kernel-checked tactic are fine. A `decide` that
is too slow for the kernel is a sign to restate the lemma (prove it for a symbolic `k`, as
`and_not_two_pow_sub_one` does), not to switch to `native_decide`.

**Enforced by** `Oris/Gate.lean`, which runs `#audit_axioms` (`Oris/Audit.lean`) over every
declaration of the `Oris` namespace and of the vendored `RBTree` library on every `lake build`,
`private` declarations and Lean's auxiliary ones included. The gate was checked to reject a
`sorry`, a `native_decide` (public and `private`), a `bv_decide` that reaches its SAT checker, and
a hand-written axiom. (A `bv_decide` whose preprocessing closes the goal leaves an ordinary kernel
proof, which the gate rightly accepts.) If you change `Oris/Audit.lean`, re-run that check: a
scratch file with each of them, then `#audit_axioms`.

### The gate covers every module

`Oris/Gate.lean` audits exactly what `Oris.lean` imports. Every new module under `Oris/` must be
imported by `Oris.lean`; `scripts/check-imports.sh` fails otherwise (CI runs it). Every
declaration must live under the `Oris` namespace, so the audit sees it.

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
module doc's complete list of departures. A departure that is *not* about an unreachable state
(today, only `erase_fixup`'s cached `root`) must be called out as such, with what settles it.

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
| Mirror-image definitions | suffix `L` / `R` (the side `cur` is on) | `stage2L`, `stage2R` |
| Lemma about a definition | `<def>_<property>` | `insFix_toList`, `delFix_rotations`, `stage2L_balanced` |
| Mirror-image standalone theorems | suffix `_left` / `_right` | `hpha_sibling_not_sentinel_left` |
| Correctness theorem of an operation | `<def>_spec` | `insert_spec`, `erase_spec`, `normalizeSize_spec` |
| A fact HPHA asserts | `hpha_<fact>` | `hpha_far_child_red_left` |
| A fact about HPHA's own code | `hpha_<function>_...` | `hpha_normalize_SIZE_MAX`, `hphaMask_eq` |

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
| `Oris/RB/*.lean` | The red-black tree (`Fixup.lean`: the zipper level; `Heap.lean`: the pointer level, to come) |
| `Oris/Audit.lean`, `Oris/Gate.lean` | The axiom audit and the gate that runs it |
| `Tools/` | Executables (`XCheck.lean`, the cross-check consumer) |
| `scripts/` | Shell checks run by CI |
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
- A change to `tree.rs`'s, `bucket.rs`'s or `align.rs`'s size arithmetic must update
  `Oris/Arith.lean` in the same commit.
- A change to the trace format must change both the Rust producer and `Tools/XCheck.lean`.

## Toolchain

`lean-toolchain` and the Batteries pin in `lakefile.toml` move together, to a Batteries release
tag named after the toolchain. After a bump, the vendored library must still build unchanged (or
its patch is recorded in `RBTree/NOTICE.md`), and the whole gate must pass. No Mathlib: the
project needs only Batteries, and a heavy dependency would slow every CI run for nothing.
