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
use core::cell::Cell;
use core::ptr::NonNull;

/// HPHA's own alignment precondition, ported verbatim: `(alignment & (alignment-1)) == 0`.
///
/// This is **not** `usize::is_power_of_two`, and the difference is load-bearing. Zero
/// is not a power of two, but it *does* satisfy HPHA's expression — `0 & (0-1)`, with
/// the subtraction wrapping to `SIZE_MAX`, is `0` — so upstream accepts
/// `alloc(size, 0)` / `realloc(ptr, size, 0)` and routes both to the unaligned path
/// via the `alignment <= DEFAULT_ALIGNMENT` test immediately below the assert.
/// Lazarov's own `main.cpp` benchmark relies on this, calling
/// `realloc(ptr, 0, 0)` to release each block in its aligned-realloc case.
///
/// v0.1.0 used `is_power_of_two` here, which rejected zero and aborted any
/// debug/`ReleaseSafe` build on that call — a deviation introduced by the port, not
/// inherited from HPHA. Restoring the original expression restores the original
/// behaviour; it is a fidelity fix, not a new extension.
#[must_use]
pub(crate) const fn is_hpha_alignment(alignment: usize) -> bool {
    alignment & alignment.wrapping_sub(1) == 0
}

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
///
/// # Address stability
/// **An `Orisnik` must not be moved once it has served its first request.** Three
/// pieces of its state bind to the instance's own address the moment it is first
/// used: the self-linked sentinel of each `Bucket`'s page list, the self-linked
/// sentinel of the tree's free-block index (both lazily initialized — see
/// `list.rs`'s "Lazy sentinel initialization" section), and the per-bucket page
/// marker that `Buckets::ptr_in_bucket` re-derives on every `free`/`realloc`/`size`
/// call to decide whether a pointer belongs to the bucket or the tree path.
///
/// Moving the value — `let b = a;`, pushing it into a `Vec`, returning it by value
/// from a builder — leaves all three pointing at the old address. The sentinels then
/// dangle, and every marker mismatches, so `ptr_in_bucket` starts answering `false`
/// for genuine bucket pointers and `free` hands them to the tree path, which reads a
/// block header out of a bucket slot's neighbouring bytes. This is the same implicit
/// constraint HPHA's C++ `allocator` already carries (it defines no move
/// constructor); Rust simply makes moving a value the default, so it is stated here.
///
/// Construct in final position and borrow from there — a `static` (the
/// `#[global_allocator]` pattern below), a `let` binding that is never moved out of,
/// or a `Box`/`&'static` if it must outlive a scope. Debug builds carry a tripwire
/// (`Orisnik::debug_assert_not_moved`, private) that panics with a named diagnostic on
/// the first operation after a move instead of corrupting silently; release builds do
/// not, so this remains a contract, not an enforced invariant. A `Pin`-based API
/// that would enforce it is deferred to v0.2.0 (see `ROADMAP.md`).
///
/// # Thread safety
/// **`Orisnik` is single-threaded internally** (`Cell`-based state throughout
/// `buckets`/`tree`, no locking — HPHA's `MULTITHREADED` mode is out of scope until
/// v2.x, see `ROADMAP.md`) and carries `unsafe impl Sync` for one reason only: every
/// `static` item, including the standard `#[global_allocator] static ALLOCATOR: Orisnik
/// = Orisnik::new();` pattern shown below, requires its type to be `Sync`
/// unconditionally, regardless of whether `#[global_allocator]` itself implies any
/// concurrency guarantee.
///
/// **Installing an `Orisnik` as `#[global_allocator]` in a genuinely multithreaded
/// program is undefined behaviour** the moment two threads call into it concurrently —
/// this includes the default `cargo test` harness, which runs tests on a thread pool.
/// This crate cannot check single-threaded exclusivity at compile time, so it is a
/// documented embedder contract, not a compiler-enforced one: callers opting into the
/// `GlobalAlloc` impl or the `nightly`-gated `Allocator` trait impl must guarantee,
/// themselves, that no more than one OS thread ever calls into a given `Orisnik`
/// instance.
pub struct Orisnik {
    /// The small-allocation path — every request `<= MAX_SMALL_ALLOCATION` (after
    /// [`bucket::clamp_small_allocation`]) lands here.
    buckets: Buckets,
    /// The large-allocation path — every request the bucket path doesn't serve.
    tree: Tree,
    /// This instance's own address, latched on the first operation and compared on
    /// every later one by [`Orisnik::debug_assert_not_moved`] — the tripwire for the
    /// non-move contract in this type's `# Address stability` doc section. `0` means
    /// "not yet latched", the same lazy-init encoding `list.rs`'s sentinel uses for
    /// its null `prev`. Read and written only under `debug_assert!`, so release
    /// builds pay one word of storage and no instructions.
    origin: Cell<usize>,
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
            origin: Cell::new(0),
        }
    }

    /// Latches this instance's address on first use and, on every later call,
    /// asserts it has not changed — the runtime tripwire for the non-move contract
    /// documented in this type's `# Address stability` section.
    ///
    /// Compiled out in release (`debug_assert!`), matching
    /// `Rust/CONVENTIONS.md`'s rule that a structural invariant checked on every
    /// operation is a `debug_assert!`, never an always-on `assert!` that would tax
    /// each release-build allocation.
    fn debug_assert_not_moved(&self) {
        // EXPLICIT: the whole body is debug-only bookkeeping; guarding it keeps
        // release builds from even loading `origin`, and keeps `&self`-through-`Cell`
        // mutation off the hot path entirely.
        #[cfg(debug_assertions)]
        {
            // PROVENANCE: the address is read for its bit pattern only, to compare
            // against a previously latched one — never turned back into a pointer.
            let here = core::ptr::from_ref(self).addr();
            let latched = self.origin.get();
            if latched == 0 {
                self.origin.set(here);
            } else {
                debug_assert_eq!(
                    latched, here,
                    "this Orisnik has been moved since its first use — its intrusive \
                     list/tree sentinels and every bucket page marker still refer to \
                     the old address, so bucket/tree dispatch is now silently wrong. \
                     See the type's `# Address stability` doc section."
                );
            }
        }
    }

    /// Allocates `size` bytes at `DEFAULT_ALIGNMENT`. `size == 0` returns `None`.
    /// Ports `allocator::alloc(size_t)`.
    #[must_use]
    pub fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
        self.debug_assert_not_moved();
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
    /// `alignment` must be a power of two, **or zero** — see
    /// `is_hpha_alignment`, which ports HPHA's own predicate exactly. Checked with
    /// `debug_assert!` rather than HPHA's always-on `assert`, matching this crate's
    /// hot-path-never-panics rule (`Rust/CONVENTIONS.md`'s Allocation Outcomes
    /// section). Zero behaves as "no alignment requested" and routes to
    /// [`Orisnik::alloc`], exactly as it does upstream.
    #[must_use]
    pub fn alloc_aligned(&self, size: usize, alignment: usize) -> Option<NonNull<u8>> {
        debug_assert!(is_hpha_alignment(alignment));
        self.debug_assert_not_moved();
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

    /// Allocates `count * size` bytes at `DEFAULT_ALIGNMENT` and zeroes them.
    /// `count * size == 0`, or a product that would overflow `usize`, returns `None`.
    /// Ports `allocator::calloc`.
    #[must_use]
    pub fn calloc(&self, count: usize, size: usize) -> Option<NonNull<u8>> {
        self.debug_assert_not_moved();
        // HPHA computes `count * size` unchecked and passes the same value to both
        // `alloc` and `memset`. That pairing is precisely what makes an overflow
        // fatal rather than merely wrong: the wrapped product under-allocates, while
        // the *unwrapped* length the caller believes in still governs how much gets
        // zeroed — so `calloc(2, SIZE_MAX)` acquires a few bytes and then memsets
        // exabytes. `checked_mul` declines instead. As with `tree::MAX_ALLOCATION`
        // (see its doc), this changes behaviour only for products HPHA could never
        // have served correctly, and touches no state transition the cross-port
        // invariant counts.
        let total = count.checked_mul(size)?;
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
        self.debug_assert_not_moved();
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
        debug_assert!(is_hpha_alignment(alignment));
        self.debug_assert_not_moved();
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
        self.debug_assert_not_moved();
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
        self.debug_assert_not_moved();
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
        self.debug_assert_not_moved();
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
    /// One caller bug in this family *is* detectable and is handled rather than
    /// propagated: `orig_size == 0` with a non-null `ptr` cannot describe any real
    /// allocation (`alloc(0)` returns `None`), so it falls back to `free`'s
    /// pointer-based dispatch instead of underflowing the size-class index. See
    /// `Orisnik::free_zero_orig_size`.
    ///
    /// # Safety
    /// `ptr`, if `Some`, must be a still-live allocation this instance produced with
    /// `orig_size` at `DEFAULT_ALIGNMENT`, `orig_size` being that allocation's
    /// original request size, not a size from any later `realloc`/`resize` call.
    pub unsafe fn free_with_size(&self, ptr: Option<NonNull<u8>>, orig_size: usize) {
        self.debug_assert_not_moved();
        let Some(ptr) = ptr else {
            return;
        };
        if orig_size == 0 {
            // SAFETY: `ptr` is a live allocation this instance produced (this
            // function's own contract), which is exactly `Orisnik::free`'s.
            unsafe { self.free_zero_orig_size(ptr) };
            return;
        }
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
        self.debug_assert_not_moved();
        debug_assert!(is_hpha_alignment(old_alignment));
        let Some(ptr) = ptr else {
            return;
        };
        if orig_size == 0 {
            // SAFETY: `ptr` is a live allocation this instance produced (this
            // function's own contract), which is exactly `Orisnik::free`'s.
            unsafe { self.free_zero_orig_size(ptr) };
            return;
        }
        // HPHA computes `round_up(origSize, oldAlignment)` below unconditionally,
        // which is well-defined for every alignment `alloc_aligned` could have used
        // *except* 0 — and 0 is one upstream accepts (see `is_hpha_alignment`),
        // routing it to the unaligned path at allocation time while leaving its own
        // `free(ptr, size, 0)` to compute `round_up(size, 0)`, i.e. garbage. Mapping
        // it to `DEFAULT_ALIGNMENT` restores the symmetry rather than inventing a
        // rule: `alloc_aligned(s, 0)` delegates to `alloc(s)`, which picks bucket
        // `bucket_spacing_function(clamp_small_allocation(s))`, and that is exactly
        // the bucket `bucket_spacing_function(round_up(s, DEFAULT_ALIGNMENT))` names
        // for every `s` in `1..=MAX_SMALL_ALLOCATION` (both ports carry a test
        // pinning the two expressions together across that whole range).
        let old_alignment = if old_alignment == 0 {
            DEFAULT_ALIGNMENT
        } else {
            old_alignment
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

    /// The `orig_size == 0` path shared by [`Orisnik::free_with_size`] and
    /// [`Orisnik::free_with_size_aligned`]: a caller bug, handled safely.
    ///
    /// No live pointer can ever have been allocated with size 0 — [`Orisnik::alloc`]
    /// and [`Orisnik::alloc_aligned`] both return `None` for a zero size, so the
    /// only pointer a zero `orig_size` could honestly accompany is the null one,
    /// which both callers have already returned on. A non-null `ptr` here therefore
    /// violates their documented contract that `orig_size` is the allocation's own
    /// original request size.
    ///
    /// HPHA does not check, and the arithmetic that follows has no defined result:
    /// `bucket_spacing_function(0)` is `((0 + 7) >> 3) - 1`, which underflows to
    /// `usize::MAX` and indexes a 32-element array. Rust's bounds check contains
    /// that to a panic; `orisnitsa`'s `ReleaseFast` build has no bounds check and
    /// corrupts memory silently, which is the reason this is worth a branch rather
    /// than a comment.
    ///
    /// Dispatching through [`Orisnik::free`] is the one answer that is *correct*
    /// rather than merely safe: `free` re-derives bucket-vs-tree ownership from the
    /// pointer itself, so it frees the block properly no matter which path it came
    /// from — the same reasoning `global_alloc.rs`'s `dealloc` already relies on.
    ///
    /// Deliberately **not** a `debug_assert!`. The recovery is not a guess to be
    /// warned about — it releases the block correctly, so there is no residual
    /// damage for a checked build to catch that a release build would miss.
    /// Asserting would also
    /// reintroduce exactly the failure shape v0.1.1's F5 fix removed: a degenerate
    /// argument that aborts in `debug`/`ReleaseSafe` while working in release, which
    /// is the worst of both (it never protects a release caller, and it breaks the
    /// checked builds that would otherwise exercise the path).
    ///
    /// # Safety
    /// `ptr` must be a still-live allocation this instance produced.
    unsafe fn free_zero_orig_size(&self, ptr: NonNull<u8>) {
        // SAFETY: forwarded from this function's own contract, which is exactly
        // `Orisnik::free`'s.
        unsafe { self.free(Some(ptr)) };
    }

    /// Returns every fully-unused page/arena to the OS. Never called automatically —
    /// call periodically if reclaiming idle memory matters. Ports `allocator::purge`.
    pub fn purge(&self) {
        self.debug_assert_not_moved();
        self.tree.purge();
        self.buckets.purge();
    }

    /// Total bytes currently claimed from the OS across both paths. Ports
    /// `allocator::allocated`.
    #[must_use]
    pub fn allocated(&self) -> usize {
        self.debug_assert_not_moved();
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

    // Every allocating call below goes through `os::map`, which under Miri is served
    // by `os::test_vm`'s heap-backed stand-in (see that module's doc); a native
    // `cargo test` still reaches the real `VirtualAlloc`/`mmap`. That is what lets
    // these tests run under the soundness gate at all — before v0.1.1 they were all
    // `#[cfg_attr(miri, ignore)]`. Each therefore ends by returning its pages with
    // `purge()`: the allocator holds them until asked (matching HPHA), which the
    // stand-in correctly reports to Miri as still-live memory.

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
    fn alloc_bucket_path_roundtrip() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.as_ptr().write_bytes(0xAB, 64) };
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        assert_eq!(unsafe { orisnik.size(Some(ptr)) }, 64);
        // SAFETY: `ptr` is a live allocation `orisnik` produced, not used again.
        unsafe { orisnik.free(Some(ptr)) };
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    #[test]
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

    // ---- v0.1.1 regression tests (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----

    /// F1. Every one of these overflows an intermediate `+` in the tree path's size
    /// arithmetic. Before v0.1.1 they wrapped: a release build returned a pointer to
    /// a *zero-byte* block for a `usize::MAX` request, and a debug build panicked in
    /// `align::round_up`. No OS call is reached on any of them, so this stays
    /// Miri-covered.
    #[test]
    fn oversized_requests_are_declined_not_wrapped() {
        let orisnik = Orisnik::new();
        for &size in &[
            usize::MAX,
            usize::MAX - 1,
            usize::MAX - 8,
            crate::tree::MAX_ALLOCATION + 1,
        ] {
            assert!(
                orisnik.alloc(size).is_none(),
                "alloc({size}) must decline, not wrap"
            );
            assert!(
                orisnik.alloc_aligned(size, 64).is_none(),
                "alloc_aligned({size}, 64) must decline, not wrap"
            );
        }
        // The aligned path needs `size + alignment` of headroom, not just `size`:
        // both operands here are individually under `MAX_ALLOCATION`, but their sum
        // is not, so only `alloc_aligned`'s own guard can catch this one.
        assert!(orisnik.alloc_aligned(1 << 63, 1 << 63).is_none());
        assert_eq!(orisnik.allocated(), 0, "must not have touched the OS");
    }

    /// F1, `calloc` half. `count * size` wrapped before v0.1.1, and the *unwrapped*
    /// length still drove the zero-fill — so this exact call segfaulted in release.
    #[test]
    fn calloc_declines_a_product_that_would_overflow() {
        let orisnik = Orisnik::new();
        assert!(orisnik.calloc(2, usize::MAX).is_none());
        assert!(orisnik.calloc(usize::MAX, 2).is_none());
        assert!(orisnik.calloc(1 << 32, 1 << 32).is_none());
        assert_eq!(orisnik.allocated(), 0, "must not have touched the OS");
    }

    /// F5. HPHA's `assert((alignment & (alignment-1)) == 0)` passes for zero, so
    /// upstream accepts a zero alignment and routes it to the unaligned path;
    /// Lazarov's own `main.cpp` calls `realloc(ptr, 0, 0)`. v0.1.0's
    /// `is_power_of_two` rejected it and aborted every debug build on that call.
    #[test]
    fn zero_alignment_is_accepted_as_unaligned() {
        assert!(is_hpha_alignment(0), "HPHA's own predicate accepts zero");
        assert!(is_hpha_alignment(1));
        assert!(is_hpha_alignment(DEFAULT_ALIGNMENT));
        assert!(!is_hpha_alignment(3));
        assert!(!is_hpha_alignment(24));

        let orisnik = Orisnik::new();
        // Zero size still declines, exactly as the unaligned path does — this is the
        // `alloc` delegation working, not a special case.
        assert!(orisnik.alloc_aligned(0, 0).is_none());
        assert_eq!(orisnik.allocated(), 0, "must not have touched the OS");
    }

    /// F5, the `main.cpp` call itself: `realloc(ptr, 0, 0)` must free and report
    /// `None` rather than abort.
    #[test]
    fn realloc_aligned_to_zero_size_and_zero_alignment_frees() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc_aligned(64, 0).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        assert!(unsafe { orisnik.realloc_aligned(Some(ptr), 0, 0) }.is_none());
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0, "the freed page must be reclaimable");
    }

    /// F5's downstream pair: an `alloc_aligned(_, 0)` allocation must be freeable
    /// through `free_with_size_aligned(_, _, 0)`, which is what a C caller mirroring
    /// its own allocation call would write.
    #[test]
    fn free_with_size_aligned_accepts_zero_alignment() {
        let orisnik = Orisnik::new();
        for &size in &[1_usize, 8, 9, 64, 255, MAX_SMALL_ALLOCATION] {
            let ptr = orisnik.alloc_aligned(size, 0).expect("OS map failed");
            // SAFETY: `ptr` is a live allocation `orisnik` produced with `size` at a
            // zero (i.e. defaulted) alignment.
            unsafe { orisnik.free_with_size_aligned(Some(ptr), size, 0) };
        }
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }

    /// A zero `orig_size` on a non-null pointer is a caller bug (no allocation can
    /// have size 0 — `alloc(0)` is `None`), and before v0.1.1 it underflowed
    /// `bucket_spacing_function` to `usize::MAX` and indexed a 32-element array:
    /// a bounds-check panic here, and a *silent out-of-bounds write* in
    /// `orisnitsa`'s `ReleaseFast`. All three entry points must now recover through
    /// `free`'s pointer-based dispatch instead, in every build profile.
    #[test]
    fn zero_orig_size_free_recovers_through_pointer_dispatch() {
        let orisnik = Orisnik::new();

        // Bucket path.
        let a = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: `a` is a live allocation `orisnik` produced; `orig_size` is a lie,
        // which is precisely what this exercises.
        unsafe { orisnik.free_with_size(Some(a), 0) };

        let b = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: as above.
        unsafe { orisnik.free_with_size_aligned(Some(b), 0, 64) };

        let c = orisnik.alloc(64).expect("OS map failed");
        // SAFETY: as above, with the zero alignment F5 made reachable.
        unsafe { orisnik.free_with_size_aligned(Some(c), 0, 0) };

        // Tree path too — the recovery must not assume the bucket path.
        let d = orisnik
            .alloc(MAX_SMALL_ALLOCATION + 4096)
            .expect("OS map failed");
        // SAFETY: as above.
        unsafe { orisnik.free_with_size(Some(d), 0) };

        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "every block must have been genuinely freed, not leaked or corrupted"
        );
    }

    // ---- F9: a randomized stress workload (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----

    /// The Microsoft C runtime's `rand()`, reproduced exactly.
    ///
    /// `holdrand = holdrand * 214013 + 2531011; return (holdrand >> 16) & 0x7fff`.
    /// Taken from Eric Jacopin's "Vintage RNGs" chapter (*Game AI Pro 3*), and verified
    /// against the real CRT before being relied on here: 200 000 draws after each of
    /// `srand(0)`, `srand(1)`, `srand(42)`, `srand(1234)` and `srand(0xFFFF_FFFF)` are
    /// bit-identical to `rand()` as linked on Windows.
    ///
    /// Why this generator and not an arbitrary one: it is what Dimitar Lazarov's own
    /// `main.cpp` benchmark drives HPHA with (`srand(1234)`). Porting it means the
    /// stress sequence below is *the same sequence* his harness produces, so a future
    /// three-way C++/Rust/Zig comparison (`ROADMAP.md`'s v0.3.0 trace corpus) can be
    /// generated independently in each language instead of shipping recorded traces.
    /// `orisnitsa` carries the identical generator, so both ports see one stream.
    struct VintageRand(u32);

    impl VintageRand {
        const fn new(seed: u32) -> Self {
            Self(seed)
        }

        /// One `rand()` draw: `0..=0x7fff`.
        fn next(&mut self) -> u32 {
            self.0 = self.0.wrapping_mul(214_013).wrapping_add(2_531_011);
            (self.0 >> 16) & 0x7fff
        }

        /// `main.cpp`'s `rand_size()`: 2..=4096, heavily skewed toward the floor.
        ///
        /// The C++ computes `MIN + (MAX - MIN) * powf(r, 8.0f)` with `r` a float in
        /// `[0,1]`. This uses an integer analogue — three squarings in 15-bit fixed
        /// point — deliberately: `powf` is not bit-reproducible across language
        /// runtimes, and a stress workload whose *shape* both ports agree on exactly
        /// is worth more here than one that matches C++'s last mantissa bit. The
        /// distribution is the same: overwhelmingly bucket-path, with a long tail
        /// crossing into the tree.
        fn size(&mut self) -> usize {
            const MIN_SIZE: u64 = 2;
            const MAX_SIZE: u64 = 4096;
            let r = u64::from(self.next()); // 0..=0x7fff
            let r2 = (r * r) >> 15;
            let r4 = (r2 * r2) >> 15;
            let r8 = (r4 * r4) >> 15;
            let span = MAX_SIZE - MIN_SIZE;
            // CAST: u64 -> usize, the result is at most MAX_SIZE (4096).
            #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
            {
                (MIN_SIZE + ((r8 * span) >> 15)) as usize
            }
        }

        /// `main.cpp`'s `rand_alignment()`: one of 1, 2, 4, ..., 128.
        fn alignment(&mut self) -> usize {
            const MAX_ALIGNMENT_LOG2: u64 = 7;
            let r = u64::from(self.next());
            1_usize << ((MAX_ALIGNMENT_LOG2 * r) >> 15)
        }

        /// `main.cpp`'s `i + rand() % (N - i)` — picks a survivor to swap with.
        fn index_in(&mut self, remaining: usize) -> usize {
            // INDEX: caller guarantees `remaining > 0`; the result is `< remaining`.
            usize::try_from(self.next()).unwrap_or(0) % remaining
        }
    }

    #[test]
    fn vintage_rand_matches_the_microsoft_crt() {
        // Golden vector: the first draws of `random values from rand.txt` in the
        // Vintage RNGs corpus, produced by the real CRT after `srand(0)`.
        let mut r = VintageRand::new(0);
        for &expected in &[38_u32, 7719, 21238, 2437, 8855, 11797, 8365, 32285, 10450] {
            assert_eq!(r.next(), expected);
        }
        // And the seed Lazarov's own `main.cpp` uses.
        let mut r = VintageRand::new(1234);
        for &expected in &[4068_u32, 213, 12761, 8758, 23056, 7717, 15274, 24508] {
            assert_eq!(r.next(), expected);
        }
    }

    /// Pins the *exact* derived stream both ports must see, with no allocator
    /// involved — the cross-port invariant's requirement applied to the test
    /// workload itself.
    ///
    /// The golden vectors above pin `next()`; this pins everything derived from it,
    /// so a drift in `size`'s fixed-point arithmetic or `alignment`'s shift cannot
    /// slip through in one port while the other stays put. `orisnitsa` asserts the
    /// identical constants. Computed independently from the reference LCG, not
    /// captured from this implementation's own output.
    #[test]
    fn vintage_rand_derived_stream_is_pinned_across_ports() {
        // Size distribution over `main.cpp`'s own seed, at both workload scales.
        for &(n, want_bucket, want_tree) in
            &[(150_usize, 108_usize, 42_usize), (20_000, 14_123, 5_877)]
        {
            let mut rng = VintageRand::new(1234);
            let (mut bucket_path, mut tree_path) = (0_usize, 0_usize);
            for _ in 0..n {
                if bucket::is_small_allocation(rng.size()) {
                    bucket_path += 1;
                } else {
                    tree_path += 1;
                }
            }
            assert_eq!(
                (bucket_path, tree_path),
                (want_bucket, want_tree),
                "N = {n}"
            );
        }

        // The aligned pass draws a size and an alignment per iteration; the sum of
        // the alignments pins that interleaving too.
        let mut rng = VintageRand::new(1234);
        let mut alignment_sum = 0_usize;
        for _ in 0..20_000 {
            let _ = rng.size();
            alignment_sum += rng.alignment();
        }
        assert_eq!(alignment_sum, 363_773);
    }

    /// The shape of `main.cpp`'s `benchmark1()`, with the assertions it never had.
    ///
    /// Allocates `N` blocks at `rand_size()`-distributed sizes, then frees them in
    /// `main.cpp`'s own randomized order, then repeats with alignment. Every block is
    /// stamped with a byte pattern derived from its index and verified on free, so a
    /// block handed out twice, or overlapping another, fails loudly rather than
    /// silently corrupting.
    ///
    /// This is the coverage class the suite had none of before v0.1.1: every other
    /// test is a hand-written scenario of at most a few thousand allocations, and the
    /// only randomized test in the crate exercised the `RB-tree` rather than the
    /// allocator.
    ///
    /// `N` is scaled down under Miri rather than the test being skipped there. Miri
    /// interprets every memory access, and its cost here is very close to linear in
    /// `N` — measured at 22.9 s, 45.7 s, 83.7 s and 149.9 s for `N` = 100, 250, 500
    /// and 1000, i.e. `t(N) ~= 8.8 + 0.141*N` seconds. The full workload would
    /// therefore take about **47 minutes** under Miri, which is not a CI cost worth
    /// paying; `N = 150` costs about **30 seconds** and still exercises the property
    /// only this test has — a randomized *interleaving* of allocation and free across
    /// both size paths, under the soundness gate. The full-scale run stays on the
    /// native lane, where it costs milliseconds.
    #[test]
    fn randomized_alloc_free_stress_matches_the_hpha_benchmark_shape() {
        // See this function's doc for how these two numbers were chosen.
        const N: usize = if cfg!(miri) { 150 } else { 20_000 };

        for &use_alignment in &[false, true] {
            let orisnik = Orisnik::new();
            let mut rng = VintageRand::new(1234); // main.cpp's own seed
            // (pointer, size, stamp) — the stamp travels with the block because the
            // free loop below relocates entries, so a vec index does not identify one.
            let mut live: Vec<(NonNull<u8>, usize, u8)> = Vec::with_capacity(N);
            let (mut bucket_path, mut tree_path) = (0_usize, 0_usize);

            for i in 0..N {
                let size = rng.size();
                if bucket::is_small_allocation(size) {
                    bucket_path += 1;
                } else {
                    tree_path += 1;
                }
                let ptr = if use_alignment {
                    let alignment = rng.alignment();
                    let p = orisnik
                        .alloc_aligned(size, alignment)
                        .expect("OS map failed");
                    assert_eq!(
                        p.addr().get() % alignment,
                        0,
                        "alloc_aligned({size}, {alignment}) returned a misaligned block"
                    );
                    p
                } else {
                    orisnik.alloc(size).expect("OS map failed")
                };

                // CAST: usize -> u8, a deliberate index fingerprint, not a value.
                #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
                let stamp = (i % 251) as u8;
                // SAFETY: `ptr` is a live allocation of at least `size` bytes.
                unsafe { ptr.as_ptr().write_bytes(stamp, size) };
                live.push((ptr, size, stamp));
            }

            // `main.cpp`'s free order: swap a random survivor into position `i`.
            for i in 0..N {
                let j = i + rng.index_in(N - i);
                // INDEX: `j` is in `i..N` by construction (`i + rng.index_in(N - i)`).
                #[allow(clippy::indexing_slicing)]
                let (ptr, size, expected) = live[j];
                // SAFETY: `ptr` is still live — nothing has freed it yet.
                let bytes = unsafe { core::slice::from_raw_parts(ptr.as_ptr(), size) };
                assert!(
                    bytes.iter().all(|&b| b == expected),
                    "block {j} ({size} bytes) was corrupted before it was freed"
                );
                // SAFETY: `ptr` is a live allocation `orisnik` produced, freed once.
                unsafe { orisnik.free(Some(ptr)) };
                // INDEX: both `i` and `j` are `< N == live.len()`.
                #[allow(clippy::indexing_slicing)]
                {
                    live[j] = live[i];
                }
            }

            orisnik.purge();
            assert_eq!(
                orisnik.allocated(),
                0,
                "every page must be reclaimable once all {N} blocks are freed \
                 (use_alignment = {use_alignment})"
            );

            // The `r^8` skew is the point of `main.cpp`'s distribution: mostly small,
            // with a substantial tail crossing the 256-byte bucket/tree boundary.
            // Pinned so a future change to `VintageRand::size` cannot quietly turn
            // this into a single-path test. Measured shares are ~71% / ~29%.
            assert!(
                bucket_path > N / 2,
                "expected a bucket-path majority, got {bucket_path}/{N}"
            );
            assert!(
                tree_path > N / 10,
                "expected a substantial tree-path tail, got {tree_path}/{N}"
            );
        }
    }

    // ---- F7: out-of-memory paths (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----
    //
    // Every `?` on a `system_alloc`/`os::map` result in `Buckets` and `Tree` was
    // unexecuted by any test before v0.1.1: `os::map` had no failure seam, so the OOM
    // early-outs existed only on paper. `os::test_vm::fail_map_after` supplies one.
    // These stay Miri-covered — with the very first `map` refused, no OS call is ever
    // reached.

    #[test]
    fn alloc_reports_oom_on_both_paths_when_the_os_refuses() {
        let orisnik = Orisnik::new();
        let _guard = crate::os::test_vm::fail_map_after(0);
        assert!(orisnik.alloc(64).is_none(), "bucket path must report OOM");
        assert!(
            orisnik.alloc(MAX_SMALL_ALLOCATION + 4096).is_none(),
            "tree path must report OOM"
        );
        assert!(
            orisnik.alloc_aligned(48, 128).is_none(),
            "aligned bucket path must report OOM"
        );
        assert!(
            orisnik
                .alloc_aligned(MAX_SMALL_ALLOCATION + 4096, 128)
                .is_none(),
            "aligned tree path must report OOM"
        );
        assert!(orisnik.calloc(4, 16).is_none(), "calloc must report OOM");
        assert_eq!(orisnik.allocated(), 0, "a refused map claims no bytes");
    }

    #[test]
    fn the_allocator_recovers_once_the_os_stops_refusing() {
        let orisnik = Orisnik::new();
        {
            let _guard = crate::os::test_vm::fail_map_after(0);
            assert!(orisnik.alloc(64).is_none());
        }
        // `_guard` dropped: injection is off again, and the allocator must be in a
        // usable state rather than poisoned by the failed growth.
        let ptr = orisnik.alloc(64).expect("OS map succeeds again");
        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        unsafe { orisnik.free(Some(ptr)) };
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
    }

    /// A `realloc` that cannot grow must report failure **and leave the original
    /// allocation live** — the caller still owns it. Losing the old block on the OOM
    /// path would be a leak at best and a use-after-free at worst.
    #[test]
    fn realloc_that_hits_oom_keeps_the_original_allocation() {
        let orisnik = Orisnik::new();
        // One page for the bucket allocation, then refuse: growing onto the tree path
        // needs a second, larger mapping.
        let _guard = crate::os::test_vm::fail_map_after(1);
        let ptr = orisnik.alloc(64).expect("first map is budgeted");
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.as_ptr().write_bytes(0x5A, 64) };

        // SAFETY: `ptr` is a live allocation `orisnik` produced.
        let grown = unsafe { orisnik.realloc(Some(ptr), MAX_SMALL_ALLOCATION + 4096) };
        assert!(grown.is_none(), "realloc must report OOM");

        // The original must be untouched and still usable.
        // SAFETY: `ptr` is still live — that is the property under test.
        let preserved = unsafe { core::slice::from_raw_parts(ptr.as_ptr(), 64) };
        assert!(
            preserved.iter().all(|&b| b == 0x5A),
            "the original block's contents must survive a failed realloc"
        );
        // SAFETY: `ptr` is still a live allocation `orisnik` produced.
        assert_eq!(unsafe { orisnik.size(Some(ptr)) }, 64);
        // SAFETY: `ptr` is live and not used again.
        unsafe { orisnik.free(Some(ptr)) };
        orisnik.purge();
        assert_eq!(
            orisnik.allocated(),
            0,
            "purge must reclaim every page this test used"
        );
    }

    /// F5's correctness premise, pinned: `free_with_size_aligned`'s zero-alignment
    /// mapping to `DEFAULT_ALIGNMENT` is only sound because
    /// `bucket_spacing_function(round_up(s, DEFAULT_ALIGNMENT))` names the same
    /// bucket as the `bucket_spacing_function(clamp_small_allocation(s))` that
    /// `alloc` used. Checked over the whole bucket range rather than trusted.
    #[test]
    fn zero_alignment_free_picks_the_bucket_alloc_used() {
        for size in 1..=MAX_SMALL_ALLOCATION {
            let allocated_from =
                bucket::bucket_spacing_function(bucket::clamp_small_allocation(size));
            let freed_into = bucket::bucket_spacing_function(round_up(size, DEFAULT_ALIGNMENT));
            assert_eq!(
                allocated_from, freed_into,
                "size {size}: alloc chose bucket {allocated_from}, free would pick {freed_into}"
            );
        }
    }
}
