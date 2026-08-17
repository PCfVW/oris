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

#![doc(html_root_url = "https://docs.rs/orisnik/0.1.0")]
#![deny(unsafe_op_in_unsafe_fn)]
// `feature(allocator_api)` is itself nightly-gated syntax — stable rustc hard-errors
// on any `#![feature(...)]` attribute, so this must stay behind `cfg_attr` even
// though the `nightly` Cargo feature already implies a nightly toolchain is in use.
// See `Rust/CONVENTIONS.md`'s Idiomatic Surfaces section and `INSTALL.md`.
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
mod list;
mod orisnik;
mod os;
mod rbtree;
mod tag;
mod tree;

pub use capi::{
    oris_alloc, oris_alloc_aligned, oris_allocated, oris_calloc, oris_destroy, oris_free,
    oris_free_with_size, oris_free_with_size_aligned, oris_new, oris_purge, oris_realloc,
    oris_realloc_aligned, oris_resize, oris_size,
};
pub use orisnik::Orisnik;
