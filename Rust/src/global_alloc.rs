// SPDX-License-Identifier: MIT OR Apache-2.0
//! `unsafe impl GlobalAlloc for Orisnik` — the opt-in `#[global_allocator]` surface.
//! Every method converts `Layout`/`*mut u8` to/from [`Orisnik`]'s own
//! `Option<NonNull<u8>>` core API and forwards; no new allocator logic lives here.
//!
//! # Safety (single-threaded contract)
//! [`Orisnik`] carries `unsafe impl Sync` (documented on the type itself in
//! `orisnik.rs`) purely so an instance can occupy a `#[global_allocator]` static
//! slot — every `static` item requires `Sync` regardless of `#[global_allocator]`.
//! This crate is single-threaded internally for the whole of v0.1.0 (`Cell`-based
//! state throughout `Buckets`/`Tree`, no locking); HPHA's `MULTITHREADED` mode
//! (mutex-guarded) is out of scope until v2.x (`ROADMAP.md`). Installing an
//! `Orisnik` as `#[global_allocator]` in a genuinely multithreaded program is
//! undefined behaviour the moment two threads call into it concurrently — this
//! crate cannot check that at compile time, so it is a documented embedder
//! contract, not a compiler-enforced one.

use crate::block::DEFAULT_ALIGNMENT;
use crate::orisnik::Orisnik;
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::NonNull;

// SAFETY: every method below converts its `Layout`/`*mut u8` arguments into the
// `size`/`alignment`/`Option<NonNull<u8>>` shape `Orisnik`'s own core methods take,
// and forwards — each conversion states, at its own `unsafe` block, exactly which of
// `Orisnik`'s preconditions `GlobalAlloc`'s trait contract already establishes.
// `GlobalAlloc`'s contract (a `dealloc`/`realloc` call's `ptr` must denote a still-live
// block this instance produced) is exactly `Orisnik`'s own "still-live allocation
// this instance produced" contract, restated at this trait boundary. `dealloc`
// deliberately does not lean on `layout` for dispatch — see its own comment.
unsafe impl GlobalAlloc for Orisnik {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = if layout.align() <= DEFAULT_ALIGNMENT {
            self.alloc(layout.size())
        } else {
            self.alloc_aligned(layout.size(), layout.align())
        };
        ptr.map_or(core::ptr::null_mut(), NonNull::as_ptr)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        // Deliberately routes through `Orisnik::free` (the page-marker/block-header
        // dispatch), not the `free_with_size*` shortcuts: those require `orig_size`
        // to be the pointer's *original* allocation size, an invariant
        // `GlobalAlloc`'s own contract does not provide — `layout` here is only
        // guaranteed to match the block's *current* size, which can differ after a
        // `realloc` (a large-then-shrunk block stays tree-allocated even once its
        // current size would fit a bucket, and `free_with_size` has no way to tell
        // the two cases apart from size alone). `free`'s pointer-based dispatch is
        // correct regardless of any realloc history.
        // SAFETY: `ptr` is non-null (`GlobalAlloc`'s own contract: it was returned
        // by a prior successful `alloc`/`alloc_zeroed`/`realloc` on this instance).
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract, forwarded).
        unsafe { self.free(Some(ptr)) };
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: `ptr` is non-null and a still-live allocation this instance
        // produced with `layout` (this function's own contract, forwarded).
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        let new_ptr = if layout.align() <= DEFAULT_ALIGNMENT {
            // SAFETY: forwarded — same reasoning as `dealloc`'s unaligned branch.
            unsafe { self.realloc(Some(ptr), new_size) }
        } else {
            // SAFETY: forwarded — same reasoning, aligned path.
            unsafe { self.realloc_aligned(Some(ptr), new_size, layout.align()) }
        };
        new_ptr.map_or(core::ptr::null_mut(), NonNull::as_ptr)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = if layout.align() <= DEFAULT_ALIGNMENT {
            self.calloc(1, layout.size())
        } else {
            // HPHA's own `calloc` is DEFAULT_ALIGNMENT-only — no `tree`/`bucket`
            // method to port for an over-aligned zeroed request, so this allocates
            // aligned and zeroes explicitly instead (new idiomatic-surface code,
            // not a port; doesn't touch the cross-port invariant, which is scoped
            // to `Orisnik`'s own dispatch and the `bucket`/`tree` internals this
            // calls unchanged).
            let ptr = self.alloc_aligned(layout.size(), layout.align());
            if let Some(p) = ptr {
                // SAFETY: `p` was just allocated with room for exactly
                // `layout.size()` bytes, exclusively owned (freshly allocated, not
                // yet handed to any other caller).
                unsafe { p.as_ptr().write_bytes(0, layout.size()) };
            }
            ptr
        };
        ptr.map_or(core::ptr::null_mut(), NonNull::as_ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // These tests call the trait methods directly (`<Orisnik as GlobalAlloc>::...`)
    // on a local instance rather than installing it via `#[global_allocator]` — that
    // attribute sets a whole-binary, set-once singleton, which would route every
    // allocation in this crate's entire test suite (including unrelated modules'
    // `Vec`-backed test fixtures) through `Orisnik`, turning any latent bug here
    // into a suite-wide failure that is far harder to localize. Calling the trait
    // methods directly exercises exactly the same dispatch this module adds, without
    // that blast radius; every allocating call still reaches real `os::map` (no
    // OS-free seeding seam at this layer, same as `orisnik.rs`'s own tests), so
    // these are Miri-ignored for the same reason.

    #[test]
    #[cfg_attr(miri, ignore)]
    fn global_alloc_default_alignment_round_trip() {
        let orisnik = Orisnik::new();
        let layout = Layout::from_size_align(64, DEFAULT_ALIGNMENT).expect("valid layout");
        // SAFETY: `layout` has non-zero size.
        let ptr = unsafe { GlobalAlloc::alloc(&orisnik, layout) };
        assert!(!ptr.is_null());
        // SAFETY: `ptr` is a live allocation of at least `layout.size()` bytes.
        unsafe { ptr.write_bytes(0xAB, layout.size()) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced with `layout`.
        unsafe { GlobalAlloc::dealloc(&orisnik, ptr, layout) };
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn global_alloc_zeroed_and_over_aligned() {
        let orisnik = Orisnik::new();
        let layout = Layout::from_size_align(96, 256).expect("valid layout");
        // SAFETY: `layout` has non-zero size.
        let ptr = unsafe { GlobalAlloc::alloc_zeroed(&orisnik, layout) };
        assert!(!ptr.is_null());
        assert_eq!(ptr.addr() % 256, 0);
        // SAFETY: `ptr` is a live allocation of at least `layout.size()` bytes,
        // zeroed by `alloc_zeroed`.
        let zeroed = unsafe { core::slice::from_raw_parts(ptr, layout.size()) };
        assert!(zeroed.iter().all(|&b| b == 0));
        // SAFETY: `ptr` is a live allocation `orisnik` produced with `layout`.
        unsafe { GlobalAlloc::dealloc(&orisnik, ptr, layout) };
    }

    /// Simulates the grow-in-place-then-move pattern a `Vec`'s own capacity growth
    /// drives through `GlobalAlloc::realloc` — the scenario the plan's "smoke test
    /// via a `Vec`" refers to, exercised directly against the trait rather than by
    /// installing `Orisnik` process-wide (see the module doc above).
    #[test]
    #[cfg_attr(miri, ignore)]
    fn global_alloc_realloc_grows_like_a_vec_would() {
        let orisnik = Orisnik::new();
        let small = Layout::from_size_align(16, DEFAULT_ALIGNMENT).expect("valid layout");
        // SAFETY: `small` has non-zero size.
        let ptr = unsafe { GlobalAlloc::alloc(&orisnik, small) };
        assert!(!ptr.is_null());
        // SAFETY: `ptr` is a live allocation of at least 16 bytes.
        unsafe { ptr.write_bytes(0xCD, 16) };

        let big = Layout::from_size_align(4096, DEFAULT_ALIGNMENT).expect("valid layout");
        // SAFETY: `ptr` is a live allocation `orisnik` produced with `small`.
        let grown = unsafe { GlobalAlloc::realloc(&orisnik, ptr, small, big.size()) };
        assert!(!grown.is_null());
        // SAFETY: the first 16 bytes must have been preserved across the realloc.
        let preserved = unsafe { core::slice::from_raw_parts(grown, 16) };
        assert!(preserved.iter().all(|&b| b == 0xCD));

        // SAFETY: `grown` is a live allocation `orisnik` produced with `big`.
        unsafe { GlobalAlloc::dealloc(&orisnik, grown, big) };
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }
}
