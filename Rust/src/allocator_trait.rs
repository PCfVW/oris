// SPDX-License-Identifier: MIT OR Apache-2.0
//! `unsafe impl core::alloc::Allocator for Orisnik` — the typed-instance surface for
//! `Box::new_in`/`Vec::new_in`, gated behind the `nightly` Cargo feature (the native
//! `allocator_api`, still unstable — rust-lang/rust#32838). See
//! `Rust/CONVENTIONS.md`'s Idiomatic Surfaces section and `INSTALL.md`.
//!
//! Sharing one instance across several containers works through the standard
//! library's own blanket `impl<A: Allocator> Allocator for &A` — `Allocator`'s
//! methods only ever need `&self`, so no wrapper type is needed here (unlike
//! `GlobalAlloc`, which needs [`Orisnik`]'s `Sync` impl for its `static` slot, this
//! trait has no such requirement of its own).
//!
//! Unlike `GlobalAlloc`, `Allocator` explicitly permits zero-size [`Layout`]s and
//! expects them to succeed without claiming real memory (`allocate`'s own docs) —
//! HPHA has no equivalent (`allocator::alloc(0) == NULL` throughout), so the
//! zero-size handling below is new idiomatic-surface code, not a port; like
//! `global_alloc.rs`'s over-aligned `alloc_zeroed`, it doesn't touch the cross-port
//! invariant, which is scoped to `Orisnik`'s dispatch and the `bucket`/`tree`
//! internals this module calls unchanged for every non-zero-size request.

use crate::block::DEFAULT_ALIGNMENT;
use crate::orisnik::Orisnik;
use core::alloc::{AllocError, Allocator, Layout};
use core::ptr::NonNull;

/// A well-aligned, zero-size "block" for a zero-size [`Layout`] — never
/// dereferenced (`Layout::size() == 0`), so no real memory is needed behind it.
/// Ports nothing; matches the standard library's own `System` allocator's handling
/// of the same case.
#[must_use]
fn dangling_for(layout: Layout) -> NonNull<[u8]> {
    // PROVENANCE: a pointer with no provenance is exactly right for a block that is
    // never dereferenced — there is no real memory whose provenance it would need
    // to carry. `layout.align()` is always non-zero (a power of two, `Layout`'s own
    // invariant), so it doubles as a validly-aligned "address" here.
    let dangling = core::ptr::without_provenance_mut::<u8>(layout.align());
    // SAFETY: `layout.align()` is always non-zero.
    let dangling = unsafe { NonNull::new_unchecked(dangling) };
    NonNull::slice_from_raw_parts(dangling, 0)
}

// SAFETY: `allocate`/`allocate_zeroed`/`deallocate`/`grow`/`shrink` each convert
// their `Layout` arguments into the `size`/`alignment` shape `Orisnik`'s own core
// methods take (after handling the zero-size case `Orisnik` itself has no concept
// of, see the module doc) and forward; `Allocator`'s trait contract (a
// `deallocate`/`grow`/`shrink` call's `ptr`/`old_layout` must match a prior
// `allocate`/`allocate_zeroed`/`grow`/`shrink` call on the same instance) is exactly
// `Orisnik`'s own "still-live allocation this instance produced [with this
// size/alignment]" contract, restated at this trait boundary.
unsafe impl Allocator for Orisnik {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.size() == 0 {
            return Ok(dangling_for(layout));
        }
        let ptr = if layout.align() <= DEFAULT_ALIGNMENT {
            self.alloc(layout.size())
        } else {
            self.alloc_aligned(layout.size(), layout.align())
        };
        let ptr = ptr.ok_or(AllocError)?;
        Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.size() == 0 {
            return Ok(dangling_for(layout));
        }
        let ptr = if layout.align() <= DEFAULT_ALIGNMENT {
            self.calloc(1, layout.size())
        } else {
            let ptr = self.alloc_aligned(layout.size(), layout.align());
            if let Some(p) = ptr {
                // SAFETY: `p` was just allocated with room for exactly
                // `layout.size()` bytes, exclusively owned (freshly allocated, not
                // yet handed to any other caller).
                unsafe { p.as_ptr().write_bytes(0, layout.size()) };
            }
            ptr
        };
        let ptr = ptr.ok_or(AllocError)?;
        Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() == 0 {
            // No real block exists for a zero-size layout (see `allocate`); the
            // pointer never came from `Orisnik`'s own paths, so there is nothing to
            // free.
            return;
        }
        // Deliberately routes through `Orisnik::free` (the page-marker/block-header
        // dispatch), not the `free_with_size*` shortcuts: those require `orig_size`
        // to be the pointer's *original* allocation size, an invariant `Allocator`'s
        // own contract does not provide — `layout` here only matches the block's
        // *current* size, which a prior `grow`/`shrink` can have changed (a
        // large-then-shrunk block stays tree-allocated even once its current size
        // would fit a bucket, and `free_with_size` cannot tell the two cases apart
        // from size alone). `free`'s pointer-based dispatch is correct regardless of
        // any `grow`/`shrink` history.
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract).
        unsafe { self.free(Some(ptr)) };
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(new_layout.size() >= old_layout.size());
        debug_assert_eq!(new_layout.align(), old_layout.align());
        if old_layout.size() == 0 {
            // No real old block exists (see `allocate`'s zero-size case) — this is
            // a fresh allocation, not a grow.
            return self.allocate(new_layout);
        }
        if new_layout.size() == 0 {
            // SAFETY: `ptr` is a live allocation this instance produced with
            // `old_layout` (this function's own contract).
            unsafe { self.deallocate(ptr, old_layout) };
            return Ok(dangling_for(new_layout));
        }
        let new_ptr = if new_layout.align() <= DEFAULT_ALIGNMENT {
            // SAFETY: `ptr` is a live allocation this instance produced with
            // `old_layout` (this function's own contract).
            unsafe { self.realloc(Some(ptr), new_layout.size()) }
        } else {
            // SAFETY: same contract as above, aligned path.
            unsafe { self.realloc_aligned(Some(ptr), new_layout.size(), new_layout.align()) }
        };
        let new_ptr = new_ptr.ok_or(AllocError)?;
        Ok(NonNull::slice_from_raw_parts(new_ptr, new_layout.size()))
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(new_layout.size() <= old_layout.size());
        debug_assert_eq!(new_layout.align(), old_layout.align());
        if old_layout.size() == 0 {
            // No real old block exists; `new_layout.size() <= old_layout.size()
            // == 0` forces `new_layout.size() == 0` too.
            return Ok(dangling_for(new_layout));
        }
        if new_layout.size() == 0 {
            // SAFETY: `ptr` is a live allocation this instance produced with
            // `old_layout` (this function's own contract).
            unsafe { self.deallocate(ptr, old_layout) };
            return Ok(dangling_for(new_layout));
        }
        let new_ptr = if new_layout.align() <= DEFAULT_ALIGNMENT {
            // SAFETY: `ptr` is a live allocation this instance produced with
            // `old_layout` (this function's own contract).
            unsafe { self.realloc(Some(ptr), new_layout.size()) }
        } else {
            // SAFETY: same contract as above, aligned path.
            unsafe { self.realloc_aligned(Some(ptr), new_layout.size(), new_layout.align()) }
        };
        let new_ptr = new_ptr.ok_or(AllocError)?;
        Ok(NonNull::slice_from_raw_parts(new_ptr, new_layout.size()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every allocating call below goes through `os::map`, which under Miri is served
    // by `os::test_vm`'s heap-backed stand-in (see that module's doc); a native
    // `cargo test` still reaches the real `VirtualAlloc`/`mmap`. That is what lets
    // these tests run under the soundness gate at all — before v0.1.1 they were all
    // `#[cfg_attr(miri, ignore)]`. Each therefore ends by returning its pages with
    // `purge()`: the allocator holds them until asked (matching HPHA), which the
    // stand-in correctly reports to Miri as still-live memory.
    // `Layout::size() == 0` is exercised separately below without touching the OS at
    // all, since `allocate`'s own zero-size branch never calls into `Orisnik`.

    /// `NonNull<[u8]>::as_non_null_ptr`/`as_mut_ptr` are gated behind the separate
    /// unstable `slice_ptr_get` feature (not implied by `allocator_api`) — this
    /// crate only enables the latter (`lib.rs`'s `cfg_attr`), so tests recover the
    /// data pointer through the always-stable raw-pointer route instead.
    #[must_use]
    fn thin_ptr(block: NonNull<[u8]>) -> NonNull<u8> {
        NonNull::new(block.as_ptr().cast::<u8>()).expect("slice pointer is never null")
    }

    #[test]
    fn zero_size_layout_returns_dangling_without_touching_the_os() {
        let orisnik = Orisnik::new();
        let layout = Layout::from_size_align(0, 64).expect("valid layout");
        let block = orisnik.allocate(layout).expect("zero-size must succeed");
        assert_eq!(block.len(), 0);
        assert_eq!(thin_ptr(block).addr().get() % 64, 0);
        assert_eq!(orisnik.allocated(), 0, "must not have touched the OS");
        // SAFETY: `layout.size() == 0` — `deallocate`'s own contract treats this as
        // a no-op, matching `allocate` never having claimed real memory for it.
        unsafe { orisnik.deallocate(thin_ptr(block), layout) };
    }

    #[test]
    fn allocator_trait_grow_and_shrink_round_trip() {
        let orisnik = Orisnik::new();
        let small = Layout::from_size_align(16, DEFAULT_ALIGNMENT).expect("valid layout");
        let block = orisnik.allocate(small).expect("OS map failed");
        let ptr = thin_ptr(block);
        // SAFETY: `ptr` is a live allocation of at least 16 bytes.
        unsafe { ptr.as_ptr().write_bytes(0xEF, 16) };

        let big = Layout::from_size_align(4096, DEFAULT_ALIGNMENT).expect("valid layout");
        // SAFETY: `ptr` is a live allocation `orisnik` produced with `small`;
        // `big.size() >= small.size()` and both share `DEFAULT_ALIGNMENT`.
        let grown = unsafe { orisnik.grow(ptr, small, big) }.expect("growth never fails here");
        let grown_ptr = thin_ptr(grown);
        // SAFETY: the first 16 bytes must have been preserved across the grow.
        let preserved = unsafe { core::slice::from_raw_parts(grown_ptr.as_ptr(), 16) };
        assert!(preserved.iter().all(|&b| b == 0xEF));

        // SAFETY: `grown_ptr` is a live allocation `orisnik` produced with `big`;
        // `small.size() <= big.size()` and both share `DEFAULT_ALIGNMENT`.
        let shrunk =
            unsafe { orisnik.shrink(grown_ptr, big, small) }.expect("shrink never fails here");
        let shrunk_ptr = thin_ptr(shrunk);
        assert_eq!(
            shrunk_ptr, grown_ptr,
            "shrinking in place must not move the block"
        );

        // SAFETY: `shrunk_ptr` is a live allocation `orisnik` produced with `small`.
        unsafe { orisnik.deallocate(shrunk_ptr, small) };
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }

    #[test]
    fn vec_new_in_round_trips_through_orisnik() {
        let orisnik = Orisnik::new();
        let mut v: std::vec::Vec<u32, &Orisnik> = std::vec::Vec::new_in(&orisnik);
        for i in 0..2000u32 {
            v.push(i);
        }
        assert_eq!(v.len(), 2000);
        assert_eq!(v.get(1999), Some(&1999));
        drop(v);
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }
}
