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
//! Already landed: guard-byte writing/checking ([`guard`]) and payload poisoning
//! ([`poison`]), plus the allocation-record store ([`record`], [`book`], [`store`]:
//! per-allocation records with callstack capture, indexed by address). Still to come
//! across v0.2.0's remaining phases: wiring the store into the allocator's dispatch
//! layer, `OrisError`, and the `check()`/`report()` diagnostics.

pub(crate) mod guard;
pub(crate) mod poison;
// The allocation-record store is built and tested here but not yet called from the
// dispatch layer (`orisnik.rs`) — wiring it in is the next phase of v0.2.0 — so every
// item is dead outside its own tests until then.
#[allow(dead_code)]
pub(crate) mod book;
#[allow(dead_code)]
pub(crate) mod record;
#[allow(dead_code)]
pub(crate) mod store;
