// SPDX-License-Identifier: MIT OR Apache-2.0
//! The top-level allocator: dispatches every request between the bucket path (small
//! allocations) and the tree path (everything else), and owns nothing else.
//!
//! Ports the non-debug, single-threaded slice of `allocator`'s public surface —
//! `DEBUG_ALLOCATOR` (guard bytes, allocation records, `check()`/`report()`) and
//! `MULTITHREADED` (mutex-guarded buckets/tree) are both out of scope for v0.1.0, see
//! `ROADMAP.md`. With `MEMORY_GUARD_SIZE` fixed at 0 (the non-debug value), every
//! `+ MEMORY_GUARD_SIZE` / `- MEMORY_GUARD_SIZE` in HPHA's own arithmetic cancels out
//! and is simply omitted here; every `debug_*` call in HPHA's non-debug build is a
//! no-op and is likewise omitted rather than ported as a stub.
//!
//! `oris_*` ([`crate::capi`]), `GlobalAlloc` ([`crate::global_alloc`]), and the
//! optional `Allocator` trait ([`crate::allocator_trait`]) are thin shells over the
//! methods on this type — see `Rust/CONVENTIONS.md`'s Idiomatic Surfaces section.

use crate::align::round_up;
use crate::block::{self, DEFAULT_ALIGNMENT};
use crate::bucket::{self, Buckets, MAX_SMALL_ALLOCATION};
use crate::tree::Tree;
use core::ptr::NonNull;

/// The top-level allocator instance: dispatches every request between the bucket
/// path (`Buckets`, sizes at most `MAX_SMALL_ALLOCATION`) and the tree path
/// (`Tree`, everything larger), deciding which one owns any given pointer the same
/// way HPHA does — `Buckets::ptr_in_bucket`'s page-marker check, re-derived on every
/// call rather than cached anywhere. Ports `allocator`.
///
/// # Invariants
/// - Every live pointer this instance has handed out belongs to exactly one of
///   `buckets`/`tree`, decided once at allocation time by
///   `bucket::is_small_allocation` and re-derived on every later call via
///   `Buckets::ptr_in_bucket` — never by a separate stored discriminant.
/// - `buckets` and `tree` are otherwise fully independent: neither reads nor mutates
///   the other's state, matching HPHA's own `allocator` (whose `bucket_*`/`tree_*`
///   methods never call each other except through this dispatch layer).
pub struct Orisnik {
    /// The small-allocation path — every request `<= MAX_SMALL_ALLOCATION` (after
    /// [`bucket::clamp_small_allocation`]) lands here.
    buckets: Buckets,
    /// The large-allocation path — every request the bucket path doesn't serve.
    tree: Tree,
}

// SAFETY: `Orisnik`'s interior mutability (`Cell` throughout `Buckets`/`Tree`, no
// locking) is sound only under the single-threaded exclusivity this crate's whole
// v0.1.0 scope assumes (see the module doc and `ROADMAP.md`'s `MULTITHREADED`
// deferral to v2.x). Asserting `Sync` here is what lets an `Orisnik` occupy a
// `#[global_allocator]` static slot (`static` items require `Sync` unconditionally)
// and is the one place in this crate that single-threaded exclusivity is a
// caller/embedder contract rather than something the type system enforces: sharing
// a live `&Orisnik` across more than one OS thread and calling its methods
// concurrently from more than one of them is undefined behaviour, not merely
// unsupported. See `Rust/CONVENTIONS.md`'s `UnsafeCell`/interior-mutability note.
unsafe impl Sync for Orisnik {}

impl Orisnik {
    /// Builds a fresh, empty allocator instance — no OS memory is claimed until the
    /// first allocation. Ports `allocator::allocator` (the default constructor).
    ///
    /// `const fn` so a `static ALLOCATOR: Orisnik = Orisnik::new();` — the standard
    /// `#[global_allocator]` pattern — const-evaluates at compile time, needing no
    /// `OnceLock`/`LazyLock` indirection.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            buckets: Buckets::new(),
            tree: Tree::new(),
        }
    }

    /// Allocates `size` bytes at `DEFAULT_ALIGNMENT`. `size == 0` returns `None`.
    /// Ports `allocator::alloc(size_t)`.
    #[must_use]
    pub fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
        if !bucket::is_small_allocation(size) {
            return self.tree.alloc(size);
        }
        if size == 0 {
            return None;
        }
        let size = bucket::clamp_small_allocation(size);
        self.buckets
            .alloc_direct(bucket::bucket_spacing_function(size))
    }

    /// Allocates `size` bytes aligned to `alignment`. `size == 0` returns `None`;
    /// `alignment <= DEFAULT_ALIGNMENT` behaves exactly like [`Orisnik::alloc`].
    /// Ports `allocator::alloc(size_t, size_t)`.
    ///
    /// `alignment` must be a power of two — checked with `debug_assert!` rather than
    /// HPHA's always-on `assert`, matching this crate's hot-path-never-panics rule
    /// (`Rust/CONVENTIONS.md`'s Allocation Outcomes section).
    #[must_use]
    pub fn alloc_aligned(&self, size: usize, alignment: usize) -> Option<NonNull<u8>> {
        debug_assert!(alignment.is_power_of_two());
        if alignment <= DEFAULT_ALIGNMENT {
            return self.alloc(size);
        }
        if !bucket::is_small_allocation(size) || alignment > MAX_SMALL_ALLOCATION {
            return self.tree.alloc_aligned(size, alignment);
        }
        if size == 0 {
            return None;
        }
        let size = bucket::clamp_small_allocation(size);
        self.buckets
            .alloc_direct(bucket::bucket_spacing_function(round_up(size, alignment)))
    }

    /// Allocates `count * size` bytes at `DEFAULT_ALIGNMENT` and zeroes them. Ports
    /// `allocator::calloc`.
    #[must_use]
    pub fn calloc(&self, count: usize, size: usize) -> Option<NonNull<u8>> {
        // `wrapping_mul` mirrors HPHA's own unchecked `count * size`, including its
        // overflow-wraps-not-panics behaviour: the same (possibly wrapped) value is
        // used both as the allocation size and the zero-fill length below, so an
        // overflow changes what is allocated, never how much of it gets zeroed.
        let total = count.wrapping_mul(size);
        let ptr = self.alloc(total)?;
        // SAFETY: `ptr` was just allocated with room for exactly `total` bytes,
        // exclusively owned (freshly allocated, not yet handed to any other caller).
        unsafe { ptr.as_ptr().write_bytes(0, total) };
        Some(ptr)
    }

    /// Grows, shrinks, or moves `ptr` to hold `size` bytes at `DEFAULT_ALIGNMENT`.
    /// `ptr == None` acts as [`Orisnik::alloc`]; `size == 0` acts as
    /// [`Orisnik::free`] and returns `None`. Ports `allocator::realloc(void*, size_t)`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced.
    #[must_use]
    pub unsafe fn realloc(&self, ptr: Option<NonNull<u8>>, size: usize) -> Option<NonNull<u8>> {
        let Some(ptr) = ptr else {
            return self.alloc(size);
        };
        if size == 0 {
            // SAFETY: forwarded from this function's own contract.
            unsafe { self.free(Some(ptr)) };
            return None;
        }
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract), exactly what `ptr_in_bucket` requires.
        if unsafe { self.buckets.ptr_in_bucket(ptr) } {
            let size = bucket::clamp_small_allocation(size);
            if bucket::is_small_allocation(size) {
                // SAFETY: `ptr` is a live bucket-path allocation (just confirmed).
                return unsafe { self.buckets.realloc(ptr, size) };
            }
            let new_ptr = self.tree.alloc(size)?;
            // SAFETY: `ptr` is a live bucket-path allocation.
            let page = unsafe { bucket::ptr_get_page(ptr.as_ptr()) };
            // SAFETY: `page` is live.
            let elem_size = unsafe { bucket::Page::elem_size(page) };
            // SAFETY: `new_ptr` was just allocated with room for at least
            // `size > MAX_SMALL_ALLOCATION >= elem_size` bytes (`is_small_allocation`
            // was just checked `false` above, so `size > MAX_SMALL_ALLOCATION`, the
            // same bound every bucket `elem_size` is `<=`); `ptr` is valid for
            // `elem_size` bytes (its slot's own size); freshly, independently
            // allocated, so the two ranges never overlap.
            unsafe {
                new_ptr
                    .as_ptr()
                    .copy_from_nonoverlapping(ptr.as_ptr(), elem_size);
            };
            // SAFETY: `ptr` is a live bucket-path allocation, not used again after
            // this call.
            unsafe { self.buckets.free(ptr) };
            return Some(new_ptr);
        }
        // SAFETY: `ptr` is a live tree-path allocation this instance produced (not a
        // bucket pointer, per the `ptr_in_bucket` check above).
        unsafe { self.tree.realloc(ptr, size) }
    }

    /// Grows, shrinks, or moves `ptr` to hold `size` bytes aligned to `alignment`.
    /// `alignment <= DEFAULT_ALIGNMENT` behaves exactly like [`Orisnik::realloc`];
    /// `ptr == None` acts as [`Orisnik::alloc_aligned`]; `size == 0` acts as
    /// [`Orisnik::free`] and returns `None`. Ports
    /// `allocator::realloc(void*, size_t, size_t)`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced.
    #[must_use]
    pub unsafe fn realloc_aligned(
        &self,
        ptr: Option<NonNull<u8>>,
        size: usize,
        alignment: usize,
    ) -> Option<NonNull<u8>> {
        debug_assert!(alignment.is_power_of_two());
        if alignment <= DEFAULT_ALIGNMENT {
            // SAFETY: forwarded from this function's own contract.
            return unsafe { self.realloc(ptr, size) };
        }
        let Some(ptr) = ptr else {
            return self.alloc_aligned(size, alignment);
        };
        if size == 0 {
            // SAFETY: forwarded from this function's own contract.
            unsafe { self.free(Some(ptr)) };
            return None;
        }
        if ptr.addr().get() & (alignment - 1) != 0 {
            // `ptr` doesn't already satisfy `alignment` — the in-place paths below
            // all rely on it already doing so (bucket slots inherit their page's
            // alignment; the tree path shifts only within a block's own span), so
            // there is no way to reach the requested alignment without moving.
            let new_ptr = self.alloc_aligned(size, alignment)?;
            // SAFETY: `ptr` is a live allocation this instance produced (this
            // function's own contract), exactly what `size` requires.
            let count = unsafe { self.size(Some(ptr)) }.min(size);
            // SAFETY: `new_ptr` was just allocated with room for at least
            // `size >= count` bytes; `ptr` is valid for at least `count` bytes
            // (`count <= self.size(ptr)`); freshly, independently allocated, so the
            // two ranges never overlap.
            unsafe {
                new_ptr
                    .as_ptr()
                    .copy_from_nonoverlapping(ptr.as_ptr(), count);
            };
            // SAFETY: `ptr` is a live allocation this instance produced, not used
            // again after this call.
            unsafe { self.free(Some(ptr)) };
            return Some(new_ptr);
        }
        // SAFETY: `ptr` is a live allocation this instance produced.
        if unsafe { self.buckets.ptr_in_bucket(ptr) } {
            let size = bucket::clamp_small_allocation(size);
            if bucket::is_small_allocation(size) && alignment <= MAX_SMALL_ALLOCATION {
                // Growing in place within the bucket path here delegates to
                // `Buckets::realloc`, which is not itself alignment-aware — exactly
                // mirroring HPHA's own `bucket_realloc` call. Soundness relies on
                // the *original* allocation's bucket having been chosen by
                // `Orisnik::alloc_aligned` (whose `round_up(size, alignment)` makes
                // every slot in that bucket's pages a multiple of `alignment` from
                // a `PAGE_SIZE`-aligned base, hence itself `alignment`-aligned) —
                // this call does not re-establish that guarantee if it must move to
                // a larger bucket, an inherited HPHA quirk, not a new one.
                // SAFETY: `ptr` is a live bucket-path allocation.
                return unsafe { self.buckets.realloc(ptr, size) };
            }
            let new_ptr = self.tree.alloc_aligned(size, alignment)?;
            // SAFETY: `ptr` is a live bucket-path allocation.
            let page = unsafe { bucket::ptr_get_page(ptr.as_ptr()) };
            // SAFETY: `page` is live.
            let elem_size = unsafe { bucket::Page::elem_size(page) };
            // Deliberate deviation from HPHA: the upstream C++ copies `elem_size`
            // bytes unconditionally here. That is sound in *its* only reachable
            // case (`size` too big for any bucket, so `size > elem_size` always),
            // but this branch can also be reached with `size` small and merely
            // `alignment > MAX_SMALL_ALLOCATION` — and then `elem_size` (up to
            // `MAX_SMALL_ALLOCATION`) can exceed `size`, while `tree_alloc_aligned`
            // only guarantees `new_ptr` has room for `size` bytes. Copying the full
            // `elem_size` in that case would overflow `new_ptr`'s real capacity, a
            // genuine heap corruption bug in the 2007 original, not a behaviour this
            // port preserves — capping at `size` is a correctness fix, not a
            // cross-port deviation the invariant cares about (it only changes what
            // stale bytes beyond the caller's own requested `size` end up copied,
            // never any tree/bucket state transition).
            // SAFETY: `new_ptr` was just allocated with room for at least `size`
            // bytes; `ptr` is valid for `elem_size` bytes (its slot's own size), and
            // `elem_size.min(size) <= size` stays within both; freshly,
            // independently allocated, so the two ranges never overlap regardless.
            unsafe {
                new_ptr
                    .as_ptr()
                    .copy_from_nonoverlapping(ptr.as_ptr(), elem_size.min(size));
            };
            // SAFETY: `ptr` is a live bucket-path allocation, not used again after
            // this call.
            unsafe { self.buckets.free(ptr) };
            return Some(new_ptr);
        }
        // SAFETY: `ptr` is a live tree-path allocation this instance produced.
        unsafe { self.tree.realloc_aligned(ptr, size, alignment) }
    }

    /// Grows or shrinks `ptr` in place to the extent possible, without moving it,
    /// returning the resulting size either way. `ptr == None` returns 0. Ports
    /// `allocator::resize`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced.
    #[must_use]
    pub unsafe fn resize(&self, ptr: Option<NonNull<u8>>, size: usize) -> usize {
        let Some(ptr) = ptr else {
            return 0;
        };
        debug_assert!(size > 0);
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract).
        if unsafe { self.buckets.ptr_in_bucket(ptr) } {
            // SAFETY: `ptr` is a live bucket-path allocation.
            let page = unsafe { bucket::ptr_get_page(ptr.as_ptr()) };
            // SAFETY: `page` is live.
            return unsafe { bucket::Page::elem_size(page) };
        }
        // SAFETY: `ptr` is a live tree-path allocation this instance produced.
        unsafe { self.tree.resize(ptr, size) }
    }

    /// Queries the usable size of `ptr`'s allocation. `ptr == None` returns 0. Ports
    /// `allocator::size`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced.
    #[must_use]
    pub unsafe fn size(&self, ptr: Option<NonNull<u8>>) -> usize {
        let Some(ptr) = ptr else {
            return 0;
        };
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract).
        if unsafe { self.buckets.ptr_in_bucket(ptr) } {
            // SAFETY: `ptr` is a live bucket-path allocation.
            let page = unsafe { bucket::ptr_get_page(ptr.as_ptr()) };
            // SAFETY: `page` is live.
            return unsafe { bucket::Page::elem_size(page) };
        }
        // SAFETY: `ptr` is a live tree-path allocation this instance produced.
        let bl = unsafe { block::ptr_get_block_header(ptr.as_ptr()) };
        // SAFETY: `bl` is live.
        unsafe { block::BlockHeader::size(bl) }
    }

    /// Frees `ptr`. `ptr == None` is a no-op. Ports `allocator::free(void*)`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced.
    pub unsafe fn free(&self, ptr: Option<NonNull<u8>>) {
        let Some(ptr) = ptr else {
            return;
        };
        // SAFETY: `ptr` is a live allocation this instance produced (this
        // function's own contract).
        if unsafe { self.buckets.ptr_in_bucket(ptr) } {
            // SAFETY: `ptr` is a live bucket-path allocation.
            unsafe { self.buckets.free(ptr) };
            return;
        }
        // SAFETY: `ptr` is a live tree-path allocation this instance produced.
        unsafe { self.tree.free(ptr) };
    }

    /// Frees `ptr`, given its original request size — skips the page-marker
    /// dispatch [`Orisnik::free`] needs, at the cost of the caller supplying
    /// `orig_size` exactly. `ptr == None` is a no-op. Ports
    /// `allocator::free(void*, size_t)`.
    ///
    /// `orig_size` must be `ptr`'s size **at the moment it was allocated** —
    /// bucket-vs-tree routing is decided once, then, and never changes for that
    /// pointer's lifetime, even across a later [`Orisnik::realloc`]/
    /// [`Orisnik::resize`] that shrinks it (a large allocation later shrunk to a
    /// small size *stays* tree-allocated; `bucket::is_small_allocation(orig_size)`
    /// below has no way to tell that apart from a pointer that was always small).
    /// Passing a *current*, post-realloc size here is a caller bug this function
    /// cannot detect, since it has no pointer-derived ground truth to check against
    /// — unlike [`Orisnik::free`]. Prefer `free` whenever `ptr`'s allocation history
    /// isn't certain to be realloc-free.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced with
    /// `orig_size` at `DEFAULT_ALIGNMENT`, `orig_size` being that allocation's
    /// original request size, not a size from any later `realloc`/`resize` call.
    pub unsafe fn free_with_size(&self, ptr: Option<NonNull<u8>>, orig_size: usize) {
        let Some(ptr) = ptr else {
            return;
        };
        if bucket::is_small_allocation(orig_size) {
            // SAFETY: `ptr` is a live bucket-path allocation from bucket
            // `bucket_spacing_function(orig_size)` — this function's own contract
            // (`ptr` was allocated with this exact `orig_size` at
            // `DEFAULT_ALIGNMENT`) is exactly how `Orisnik::alloc` picks a bucket.
            unsafe {
                self.buckets
                    .free_direct(ptr, bucket::bucket_spacing_function(orig_size));
            };
            return;
        }
        // SAFETY: `ptr` is a live tree-path allocation (`orig_size` is not small,
        // this function's own contract, matching how `Orisnik::alloc` would have
        // routed it).
        unsafe { self.tree.free(ptr) };
    }

    /// Frees `ptr`, given its original request size and alignment. `ptr == None` is
    /// a no-op. Ports `allocator::free(void*, size_t, size_t)`.
    ///
    /// `orig_size`/`old_alignment` must be `ptr`'s size/alignment **at the moment it
    /// was allocated** — see [`Orisnik::free_with_size`]'s doc for why a later
    /// `realloc`/`resize`'s *current* size is not a safe substitute here, and prefer
    /// [`Orisnik::free`] whenever `ptr`'s allocation history isn't certain to be
    /// realloc-free.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced with
    /// `orig_size`/`old_alignment`, both being that allocation's original request
    /// values, not values from any later `realloc`/`resize` call.
    pub unsafe fn free_with_size_aligned(
        &self,
        ptr: Option<NonNull<u8>>,
        orig_size: usize,
        old_alignment: usize,
    ) {
        let Some(ptr) = ptr else {
            return;
        };
        if bucket::is_small_allocation(orig_size) && old_alignment <= MAX_SMALL_ALLOCATION {
            // SAFETY: `ptr` is a live bucket-path allocation from bucket
            // `bucket_spacing_function(round_up(orig_size, old_alignment))` — this
            // function's own contract is exactly how `Orisnik::alloc_aligned`'s
            // bucket branch picks a bucket.
            unsafe {
                self.buckets.free_direct(
                    ptr,
                    bucket::bucket_spacing_function(round_up(orig_size, old_alignment)),
                );
            };
            return;
        }
        // SAFETY: `ptr` is a live tree-path allocation, matching how
        // `Orisnik::alloc_aligned` would have routed it.
        unsafe { self.tree.free(ptr) };
    }

    /// Returns every fully-unused page/arena to the OS. Never called automatically —
    /// call periodically if reclaiming idle memory matters. Ports `allocator::purge`.
    pub fn purge(&self) {
        self.tree.purge();
        self.buckets.purge();
    }

    /// Total bytes currently claimed from the OS across both paths. Ports
    /// `allocator::allocated`.
    #[must_use]
    pub fn allocated(&self) -> usize {
        self.buckets.allocated() + self.tree.allocated()
    }
}

// Regression guard, not a runtime check: this only compiles if `Orisnik::new` (and
// transitively `Buckets::new`/`Tree::new`) stays `const fn` — the property the
// standard `#[global_allocator] static ALLOCATOR: Orisnik = Orisnik::new();` pattern
// needs. A future change that accidentally makes any of those non-const fails the
// build right here instead of surfacing as a confusing error in downstream code.
// `static`, not `const`: `Orisnik` is interior-mutable (`Cell` throughout
// `Buckets`/`Tree`), and a `const` of an interior-mutable type is a separate,
// real footgun (clippy's `declare_interior_mutable_const`) unrelated to what this
// guard checks — `static` is also the exact form the pattern above actually uses.
static _ORISNIK_NEW_IS_CONST: Orisnik = Orisnik::new();

impl Default for Orisnik {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every test below allocates through a fresh `Orisnik`, which (unlike
    // `bucket.rs`'s `FakePage`/`tree.rs`'s `FakeArena`) has no seam to seed its
    // `Buckets`/`Tree` from heap-backed memory — `Orisnik::new` always starts empty,
    // so any allocation reaches real `os::map`. Miri cannot interpret that (see
    // `os.rs`'s module doc); Miri-ignored here for the same reason `bucket.rs`'s
    // `Buckets`-level tests and `tree.rs`'s OS-touching test are, and verified
    // instead by native `cargo test` on all three OSes (`rust-ci.yml`). The
    // no-OS-touch zero-size/null-pointer edge cases below stay Miri-covered.

    #[test]
    fn alloc_zero_returns_none() {
        let orisnik = Orisnik::new();
        assert!(orisnik.alloc(0).is_none());
        assert!(orisnik.alloc_aligned(0, 64).is_none());
        assert_eq!(orisnik.allocated(), 0, "must not have touched the OS");
    }

    #[test]
    fn realloc_none_ptr_acts_as_alloc_of_zero() {
        let orisnik = Orisnik::new();
        // SAFETY: `None` trivially satisfies `realloc`'s "still-live allocation"
        // contract — there is no pointer to be live.
        assert!(unsafe { orisnik.realloc(None, 0) }.is_none());
    }

    #[test]
    fn size_and_resize_of_null_are_zero() {
        let orisnik = Orisnik::new();
        // SAFETY: `None` trivially satisfies both functions' contracts.
        assert_eq!(unsafe { orisnik.size(None) }, 0);
        // SAFETY: same as above.
        assert_eq!(unsafe { orisnik.resize(None, 8) }, 0);
    }

    #[test]
    fn free_of_null_is_a_no_op() {
        let orisnik = Orisnik::new();
        // SAFETY: `None` trivially satisfies `free`'s contract.
        unsafe { orisnik.free(None) };
        assert_eq!(orisnik.allocated(), 0);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn alloc_bucket_path_roundtrip() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.as_ptr().write_bytes(0xAB, 64) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        assert_eq!(unsafe { orisnik.size(Some(ptr)) }, 64);
        // SAFETY: `ptr` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(ptr)) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn alloc_tree_path_roundtrip() {
        let orisnik = Orisnik::new();
        let size = MAX_SMALL_ALLOCATION + 4096;
        let ptr = orisnik.alloc(size).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation of at least `size` bytes.
        unsafe { ptr.as_ptr().write_bytes(0xCD, size) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        assert!(unsafe { orisnik.size(Some(ptr)) } >= size);
        // SAFETY: `ptr` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(ptr)) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn alloc_aligned_respects_alignment_on_both_paths() {
        let orisnik = Orisnik::new();
        for &(size, alignment) in &[
            (48usize, 64usize),              // bucket path
            (MAX_SMALL_ALLOCATION + 8, 128), // tree path
        ] {
            let ptr = orisnik
                .alloc_aligned(size, alignment)
                .expect("OS map failed");
            assert_eq!(ptr.addr().get() % alignment, 0);
            // SAFETY: `ptr` is a live allocation `orisnik` produced.
            unsafe { orisnik.free(Some(ptr)) };
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn realloc_moves_bucket_allocation_across_size_classes() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc(8).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation of at least 8 bytes.
        unsafe { ptr.as_ptr().write_bytes(0xEF, 8) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        let grown = unsafe { orisnik.realloc(Some(ptr), 200) };
        let grown = grown.expect("growth within buckets never fails");
        // SAFETY: the first 8 bytes must have been preserved across the grow.
        let preserved = unsafe { core::slice::from_raw_parts(grown.as_ptr(), 8) };
        assert!(preserved.iter().all(|&b| b == 0xEF));
        // SAFETY: `grown` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(grown)) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn realloc_moves_bucket_allocation_to_the_tree_path() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.as_ptr().write_bytes(0x11, 64) };
        let big = MAX_SMALL_ALLOCATION + 4096;
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        let moved = unsafe { orisnik.realloc(Some(ptr), big) }
            .expect("growth onto the tree path never fails");
        // SAFETY: the first 64 bytes must have been preserved across the move.
        let preserved = unsafe { core::slice::from_raw_parts(moved.as_ptr(), 64) };
        assert!(preserved.iter().all(|&b| b == 0x11));
        // SAFETY: `moved` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(moved)) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn realloc_zero_size_frees_and_returns_none() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        assert!(unsafe { orisnik.realloc(Some(ptr), 0) }.is_none());
        // `free`/`realloc(_, 0)` never returns memory to the OS on its own — matching
        // HPHA, only an explicit `purge()` reclaims fully-unused pages/arenas.
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0, "the freed page must be reclaimable");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn resize_grows_tree_allocation_in_place() {
        let orisnik = Orisnik::new();
        let size = MAX_SMALL_ALLOCATION + 4096;
        let ptr = orisnik.alloc(size).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        let new_size = unsafe { orisnik.resize(Some(ptr), size + 64) };
        assert!(new_size >= size + 64);
        // SAFETY: `resize` grew `ptr` in place to at least `new_size` bytes.
        unsafe { ptr.as_ptr().write_bytes(0x22, new_size) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(ptr)) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn free_with_size_matches_plain_free() {
        let orisnik = Orisnik::new();
        let a = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `a` is a live allocation `orisnik` produced with 64 bytes at the
        // default alignment.
        unsafe { orisnik.free_with_size(Some(a), 64) };

        let b = orisnik.alloc_aligned(48, 128).expect("OS map failed");
        // SAFETY: `b` is a live allocation `orisnik` produced with 48 bytes at
        // alignment 128.
        unsafe { orisnik.free_with_size_aligned(Some(b), 48, 128) };

        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn allocated_tracks_both_paths_and_purge_reclaims_them() {
        let orisnik = Orisnik::new();
        let small = orisnik.alloc(32).expect("OS map failed");
        let large = orisnik
            .alloc(MAX_SMALL_ALLOCATION + 4096)
            .expect("OS map failed");
        assert!(orisnik.allocated() > 0);
        // SAFETY: `small`/`large` are live allocations `orisnik` produced.
        unsafe { orisnik.free(Some(small)) };
        // SAFETY: same as above.
        unsafe { orisnik.free(Some(large)) };
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "every fully-unused page/arena must be reclaimed"
        );
    }
}
