# Claude Code Instructions — Lean proofs

## Coding conventions

Always apply the rules in `CONVENTIONS.md` (this directory). Kernel-only proofs, the
transcription rules, the listing of departures and statement honesty are mandatory. The repo-root
`CLAUDE.md` holds the shared **cross-port invariant**; a change to the tree logic or the size
arithmetic of the Rust port must be mirrored in the model here (`CONVENTIONS.md` § *Keeping the
model in step with the Rust*).

Every `.lean` file begins with `-- SPDX-License-Identifier: MIT OR Apache-2.0` as its first line
(vendored `RBTree/` files keep their original headers).

## Pre-commit checks

Run from `Lean/` (elan installs the pinned toolchain by itself):

1. `lake build` — compiles every proof and runs the axiom gate (`Oris/Gate.lean`). It must
   finish with no errors **and no warnings** (unused `simp` arguments and unused variables
   included), and print `standard axioms only` for both `Oris` and `RBTree`.
2. `./scripts/check-imports.sh` — every module under `Oris/` is imported by `Oris.lean`, so the
   gate audits it.
3. When `Oris/RB/`, `Tools/XCheck.lean` or `../Rust/src/rbtree.rs` changes, the cross-check
   (with `pipefail` on, so a failure anywhere in the pipe fails the command):

   ```
   cargo test --manifest-path ../Rust/Cargo.toml --lib \
     rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
     | grep '^XC ' | lake exe xcheck
   ```

   It must report `20000 operations compared, 0 mismatches` and exit 0.
4. Update `../CHANGELOG.md` — a bullet under `[Unreleased]` for any new or changed theorem a
   reader would cite.

## Toolchain

`lean-toolchain` pins `leanprover/lean4:v4.36.0-rc2`, and `lakefile.toml` pins Batteries to the
release tag of the same name. Bump both together (`CONVENTIONS.md` § *Toolchain*).
