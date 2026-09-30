// SPDX-License-Identifier: MIT OR Apache-2.0
//! `spomen` (спомен, "remembrance") — the `debug-allocator`-gated diagnostic subsystem
//! that ports HPHA's `DEBUG_ALLOCATOR` mode: guard-byte verification, allocation-record
//! tracking, callstack capture, leak detection on drop, and the `check()`/`report()`
//! diagnostics.
//!
//! Unlike `crate::guard`'s `MEMORY_GUARD_SIZE` (always compiled, since `bucket.rs`/
//! `tree.rs` must reference it unconditionally — see that module's doc), everything in
//! this module is compiled only with the `debug-allocator` feature enabled; a release
//! build without the feature links none of it. See `Rust/CONVENTIONS.md`'s
//! `debug_assert!` Invariants section and `ROADMAP.md`'s v0.2.0 milestone.
//!
//! Contents: guard-byte writing/checking ([`guard`]) and payload poisoning
//! ([`poison`]); the allocation-record store ([`record`], [`book`], [`store`]:
//! per-allocation records with callstack capture, indexed by address); and the hooks that
//! wire them into the allocator (`orisnik_debug.rs`), with fail-fast reporting of
//! detected corruption ([`failure`]); and the diagnostics: [`error`]'s `OrisError`, the
//! public `Orisnik::check`/`report`/`write_report`, and leak detection on `Drop`
//! (`orisnik_debug.rs`). This completes v0.2.0's debug allocator.

pub(crate) mod book;
pub(crate) mod error;
pub(crate) mod failure;
pub(crate) mod guard;
pub(crate) mod poison;
pub(crate) mod record;
pub(crate) mod store;
