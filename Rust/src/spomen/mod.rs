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
//! Populated across v0.2.0's phases: allocation-record tracking, callstack capture,
//! payload poisoning, `OrisError`, and the `check()`/`report()` diagnostics.

pub(crate) mod guard;
