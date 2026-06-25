# Claude Code Instructions — orisnik (Rust port)

## Coding conventions

Always apply the rules in `CONVENTIONS.md` (this directory). Every annotation pattern,
doc-comment rule, and `unsafe`/provenance rule is mandatory. The repo-root `CLAUDE.md` holds
the shared **cross-port invariant** — read it before changing size-class math, tree rotation,
coalescing order, or block-header layout.

Every `.rs` file begins with `// SPDX-License-Identifier: MIT OR Apache-2.0` as its first line.

## Pre-commit checks (once code lands)

1. `cargo fmt`
2. `cargo clippy --all-targets --all-features -- -D warnings`
3. `cargo test`
4. `cargo +nightly miri test` with `-Zmiri-strict-provenance` and `-Zmiri-tree-borrows` — the
   soundness gate for the allocator's `unsafe`, provenance, and aliasing code. See
   `CONVENTIONS.md` § *Miri: the verification gate*. A new or modified `unsafe` block is
   *pending* until a Miri-covered test exercises it.
5. Update `CHANGELOG.md` — a bullet under `[Unreleased]` for any user-visible change.

## MSRV and edition

The crate targets **edition 2024** with a minimum supported Rust version of **1.85** — one notch
above the 1.84 strict-provenance stabilization, to gain edition-2024 unsafe-attribute and
`unsafe extern` idioms. Keep `edition` and `rust-version` in `Cargo.toml` in sync with
`INSTALL.md`. The optional typed `Allocator` surface needs nightly (unstable `allocator_api`,
issue #32838 — still unstable as of 1.96) or the `allocator-api2` crate; keep it behind a cargo
feature so the default build stays on stable.
