# Claude Code Instructions — Lean proofs

## Coding conventions

Always apply the rules in `CONVENTIONS.md` (this directory). Kernel-only proofs, the
transcription rules, the listing of departures and statement honesty are mandatory. The repo-root
`CLAUDE.md` holds the shared **cross-port invariant**; a change to the tree logic or the size
arithmetic of the Rust port must be mirrored in the model here (`CONVENTIONS.md` § *Keeping the
model in step with the Rust*).

Every `.lean` file begins with `-- SPDX-License-Identifier: MIT OR Apache-2.0` as its first line
(the vendored `RBTree/` files and `RBTree.lean` keep their upstream headers, or lack of one).

## Pre-commit checks

Run from `Lean/`, in bash (on Windows, Git Bash; elan installs the pinned toolchain by itself):

1. `lake build --wfail` — compiles every proof; `--wfail` makes any warning (unused `simp`
   arguments and unused variables included) an error, as in CI.
2. `lake exe audit` (`Tools/Audit.lean`) — the axiom audit, run outside the build: every
   declaration of every Oris and RBTree module rests on the three standard axioms alone,
   `Oris.lean` imports every module under `Oris/`, every Oris declaration is in the `Oris`
   namespace, and no proof module uses a banned construct (`CONVENTIONS.md` § *Kernel-only
   proofs*). It must print `standard axioms only` and `clean`, and exit 0.
3. `lake env leanchecker --fresh Oris` — replays every declaration through the kernel from
   scratch (about a minute); it must exit 0.
4. When `Oris/RB/`, `Tools/XCheck.lean` or `../Rust/src/rbtree.rs` changes, the cross-check
   (with `pipefail` on, so a failure anywhere in the pipe fails the command):

   ```
   set -o pipefail
   cargo test --manifest-path ../Rust/Cargo.toml --lib \
     rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
     | grep '^XC' | lake exe xcheck
   ```

   It must report `20000 operations compared, 0 mismatches (zipper model 0, heap model 0)` and
   `0 of 9935 erases differ` for `erase_fixup`'s two root readings, list a non-zero count for
   every coverage item, and exit 0 (about 15 seconds after building).
5. Update `../CHANGELOG.md` — a bullet under `[Unreleased]` for any new or changed theorem a
   reader would cite.

## Toolchain

`lean-toolchain` pins `leanprover/lean4:v4.36.0-rc2`, and `lakefile.toml` pins Batteries to the
release tag of the same name. Bump both together (`CONVENTIONS.md` § *Toolchain*).
