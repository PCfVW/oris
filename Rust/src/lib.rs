// SPDX-License-Identifier: MIT OR Apache-2.0
//! # orisnik
//!
//! A Rust port of Dimitar Lazarov's HPHA (2007) — a single-threaded heap allocator
//! combining a size-class bucket allocator for small allocations with a red-black-tree
//! best-fit allocator for large ones. See [the brief](https://github.com/PCfVW/oris/blob/main/BRIEF.md)
//! for the design rationale and [the roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md)
//! for what ships in each version.
//!
//! Three surfaces share one core: the `oris_*` C-ABI (`oris_alloc`, `oris_free`, ...),
//! `unsafe impl GlobalAlloc` (opt in as a `#[global_allocator]`), and an optional
//! `unsafe impl core::alloc::Allocator` behind the `nightly` Cargo feature.
//!
//! An opt-in **debug allocator** ports HPHA's `DEBUG_ALLOCATOR` mode behind the
//! `debug-allocator` Cargo feature (unreleased; see `CHANGELOG.md`): trailing guard bytes,
//! payload poisoning, an allocation-record book with callstack capture, the `check()` and
//! `report()` methods on [`Orisnik`], the `OrisError` they return, and leak detection when
//! an instance is dropped. With the feature off it is compiled out entirely. The
//! [user guide](https://github.com/PCfVW/oris/blob/main/docs/debug-allocator.md) explains
//! what it catches and how to read its messages; run the example with
//! `cargo run --example catch_an_overrun --features debug-allocator`.
//!
//! ```no_run
//! use orisnik::Orisnik;
//!
//! #[global_allocator]
//! static ALLOCATOR: Orisnik = Orisnik::new();
//!
//! let v: Vec<u8> = Vec::with_capacity(4);
//! assert_eq!(v.capacity(), 4);
//! ```
//!
//! `Orisnik::new()` is a `const fn`, so the `static` above const-evaluates at compile
//! time — no `OnceLock`/`LazyLock` indirection needed. (`no_run` above: this doctest
//! is a real, separately-compiled binary that installs `Orisnik` as *its own*
//! process-wide allocator — safe in that isolated process, but Miri cannot interpret
//! the real `VirtualAlloc`/`mmap` calls this would then make, the same limitation
//! `os.rs`'s module doc describes for every other OS-touching test in this crate; the
//! actual runtime behaviour this illustrates is covered by `global_alloc.rs`'s own
//! Miri-ignored, OS-touching tests instead.)
//!
//! **Before installing [`Orisnik`] as a `#[global_allocator]`, read its own doc's
//! `# Thread safety` section**: this crate is single-threaded internally, and doing
//! so in a genuinely multithreaded program — including the default `cargo test`
//! harness — is undefined behaviour, not merely unsupported.

#![doc(html_root_url = "https://docs.rs/orisnik/0.1.1")]
#![deny(unsafe_op_in_unsafe_fn)]
// `feature(allocator_api)` is itself nightly-gated syntax — stable rustc hard-errors
// on any `#![feature(...)]` attribute, so this must stay behind `cfg_attr` even
// though the `nightly` Cargo feature already implies a nightly toolchain is in use.
// See `Rust/CONVENTIONS.md`'s Idiomatic Surfaces section and `INSTALL.md`.
//
// `#[allow(stable_features)]`: transitional, remove once Rust 1.100 ships to stable.
// As of nightly-1.101.0, the subset of `allocator_api` this crate actually uses
// (the `Allocator` trait, `AllocError`, `Vec`/`Box`'s `_in` constructors —
// rust-lang/rust#156882) has been promoted to stable-pending-1.100, so rustc now
// flags this `feature(...)` as a `stable_features` warning, which `-D warnings`
// (CI's nightly-feature Clippy job) turns into a hard error. Older nightlies and
// today's actual stable channel still require the attribute — the trait is not
// yet released — so it cannot simply be deleted; suppress the lint here instead of
// forking on rustc version. The `allocator_ext` name clippy suggests as a
// replacement covers unrelated leftovers (the Store API, a split `Deallocator`
// trait, `reallocate()` — rust-lang/rust#163177), none of which this crate uses.
#![allow(stable_features)]
#![cfg_attr(feature = "nightly", feature(allocator_api))]

mod align;
// `core::alloc::Allocator`/`AllocError` are themselves unstable items — this module
// only parses on a nightly toolchain with `feature(allocator_api)` enabled above,
// so the declaration itself must be feature-gated, not just its trait impl's use.
#[cfg(feature = "nightly")]
mod allocator_trait;
mod block;
mod bucket;
mod capi;
mod global_alloc;
// Always compiled — `bucket.rs` and `orisnik.rs` reference `guard::MEMORY_GUARD_SIZE`
// (directly, or through `guard::inflate`/`deflate`) unconditionally (it folds to 0
// without `debug-allocator`), unlike `spomen` below, which this feature excludes from
// the build entirely. See `Rust/CONVENTIONS.md`'s `debug_assert!` Invariants section.
mod guard;
mod home;
mod list;
mod orisnik;
mod os;
// Two independent consumers, neither the plain shipped library: `spomen`'s guard-byte
// ramp (see that module's doc), gated on the feature like `spomen` itself; and
// `orisnik.rs`'s own `#[cfg(test)]` stress workload, which needs it in every test
// build (that workload predates `debug-allocator` and is unrelated to it — this
// generator simply serves both).
#[cfg(any(test, feature = "debug-allocator"))]
mod rand;
mod rbtree;
// The port of HPHA's `DEBUG_ALLOCATOR` mode (guard-byte verification, allocation-record
// tracking, callstack capture, leak detection, `check()`/`report()`) — see `spomen`'s own
// module doc, `INSTALL.md`, and `ROADMAP.md`'s v0.2.0 milestone.
#[cfg(feature = "debug-allocator")]
mod spomen;
mod tag;
mod tree;

pub use capi::{
    oris_alloc, oris_alloc_aligned, oris_allocated, oris_calloc, oris_destroy, oris_free,
    oris_free_with_size, oris_free_with_size_aligned, oris_new, oris_purge, oris_realloc,
    oris_realloc_aligned, oris_resize, oris_size,
};
pub use orisnik::Orisnik;
// The error type of `Orisnik::check`, which exists only with `debug-allocator`.
#[cfg(feature = "debug-allocator")]
pub use spomen::error::OrisError;
