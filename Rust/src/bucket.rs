// SPDX-License-Identifier: MIT OR Apache-2.0
//! The small-allocation path: fixed-size-class buckets over OS pages.
//!
//! Ports `Cpp/hpha.h`/`hpha.cpp`'s `allocator::bucket`, `allocator::page`, the
//! `bucket_*` methods, and the `bucket_spacing_function*`/`is_small_allocation`/
//! `clamp_small_allocation` size-class math. Self-contained: no dependency on
//! `rbtree.rs`/`block.rs` (mirrors HPHA, where the bucket and tree allocators share
//! only the top-level `allocator` class, not each other's internals).
//!
//! # Layout
//! Each 64 KiB OS page holds a singly-linked free list of `elem_size`-sized slots,
//! with a [`Page`] bookkeeping struct at the very tail (`PAGE_SIZE - size_of::<Page>()`
//! into the mapping) — [`ptr_get_page`] recovers it from any payload pointer with one
//! alignment step. A [`Bucket`] owns the (possibly-empty, possibly-full) list of pages
//! serving one size class; [`Buckets`] owns all 32 size classes plus the running
//! allocated-byte counter (`allocator::mTotalAllocatedSizeBuckets`).
//!
//! # Testability vs. the OS boundary
//! `os.rs` documents why Miri cannot interpret `VirtualAlloc`/`mmap` at all. Rather
//! than let that block Miri coverage of *this* module's actual bug-prone logic
//! (free-list threading, page-full/page-empty transitions, marker checks), page
//! initialization is factored into [`init_page_at`] — given an already-acquired
//! `PAGE_SIZE`-aligned buffer, thread its free list and place a `Page` at the tail.
//! Production code reaches it only through [`Buckets::system_alloc`] (which calls
//! `os::map` first); tests call it directly against a heap-backed buffer, giving full
//! Miri coverage of the part that actually varies by allocation pattern.

use crate::list::{IntrusiveList, ListLink, ListNode};
use crate::os;
use core::cell::Cell;
use core::ptr::NonNull;

/// `log2` of the smallest bucket size class. Ports `MIN_ALLOCATION_LOG2`.
pub(crate) const MIN_ALLOCATION_LOG2: usize = 3;
/// The smallest bucket size class, in bytes. Ports `MIN_ALLOCATION`.
pub(crate) const MIN_ALLOCATION: usize = 1 << MIN_ALLOCATION_LOG2; // 8
/// `log2` of the largest small allocation. Ports `MAX_SMALL_ALLOCATION_LOG2`.
pub(crate) const MAX_SMALL_ALLOCATION_LOG2: usize = 8;
/// The largest allocation still served by the bucket path; anything larger goes to
/// the tree allocator. Ports `MAX_SMALL_ALLOCATION`.
pub(crate) const MAX_SMALL_ALLOCATION: usize = 1 << MAX_SMALL_ALLOCATION_LOG2; // 256
/// The number of bucket size classes, at [`MIN_ALLOCATION`]-byte spacing from
/// [`MIN_ALLOCATION`] to [`MAX_SMALL_ALLOCATION`]. Ports `NUM_BUCKETS`.
pub(crate) const NUM_BUCKETS: usize = MAX_SMALL_ALLOCATION / MIN_ALLOCATION; // 32

/// Whether `size` belongs on the bucket path (`false` routes to the tree allocator).
/// Ports `allocator::is_small_allocation` (with `MEMORY_GUARD_SIZE` — always 0 until
/// the v0.2.0 debug allocator — elided).
#[must_use]
pub(crate) const fn is_small_allocation(size: usize) -> bool {
    size <= MAX_SMALL_ALLOCATION
}

/// Raises `size` up to the smallest bucket size class if it's below it. Ports
/// `allocator::clamp_small_allocation`.
#[must_use]
pub(crate) const fn clamp_small_allocation(size: usize) -> usize {
    if size < MIN_ALLOCATION {
        MIN_ALLOCATION
    } else {
        size
    }
}

/// The bucket index serving `size` (rounding up to the next size class). Ports
/// `allocator::bucket_spacing_function`.
///
/// # Panics (debug only)
/// If `size` is 0 or exceeds [`MAX_SMALL_ALLOCATION`] — callers are expected to have
/// already applied [`clamp_small_allocation`]/[`is_small_allocation`].
#[must_use]
pub(crate) const fn bucket_spacing_function(size: usize) -> usize {
    debug_assert!(size > 0 && size <= MAX_SMALL_ALLOCATION);
    ((size + (MIN_ALLOCATION - 1)) >> MIN_ALLOCATION_LOG2) - 1
}

/// The bucket index serving `size`, when `size` is already known to be an exact
/// multiple of [`MIN_ALLOCATION`] (cheaper than [`bucket_spacing_function`] — no
/// rounding needed). Ports `allocator::bucket_spacing_function_aligned`.
#[must_use]
pub(crate) const fn bucket_spacing_function_aligned(size: usize) -> usize {
    debug_assert!(size > 0 && size % MIN_ALLOCATION == 0 && size <= MAX_SMALL_ALLOCATION);
    (size >> MIN_ALLOCATION_LOG2) - 1
}

/// The element size served by bucket `index`. Ports
/// `allocator::bucket_spacing_function_inverse`.
#[must_use]
pub(crate) const fn bucket_spacing_function_inverse(index: usize) -> usize {
    debug_assert!(index < NUM_BUCKETS);
    (index + 1) << MIN_ALLOCATION_LOG2
}

/// One free slot in a page's intra-page free list — a plain singly-linked list
/// (distinct from `list.rs`'s doubly-linked `ListLink`, and from `Page`'s own
/// [`ListLink`] membership in its `Bucket`'s page list). Ports `free_link`.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct FreeLink {
    /// The next free slot, or null at the end of the list. Byte offset 0.
    next: *mut FreeLink,
}

impl FreeLink {
    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn next(this: *mut FreeLink) -> *mut FreeLink {
        // SAFETY: caller guarantees `this` is live; reads one field.
        unsafe { (*this).next }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn set_next(this: *mut FreeLink, next: *mut FreeLink) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).next = next };
    }
}

/// The bookkeeping struct at the tail of every bucket-owned OS page. Ports
/// `allocator::page`.
///
/// # Invariants
/// - Lives at exactly `PAGE_SIZE - size_of::<Page>()` bytes into a `PAGE_SIZE`-aligned
///   mapping — [`ptr_get_page`] depends on this.
/// - `free_list` is null exactly when every slot in the page is allocated
///   ([`Page::is_full`]).
/// - `marker` lets [`crate::bucket::Buckets::ptr_in_bucket`] distinguish a bucket
///   pointer from a tree pointer without a discriminant bit — see [`Bucket::marker`].
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: on-heap ABI mirrored by orisnitsa's extern struct equivalent; frozen.
pub(crate) struct Page {
    /// This page's membership in its `Bucket`'s page list. Byte offset 0, 8-byte
    /// aligned there (required by [`ListNode`]; every `Page` position is itself
    /// 8-aligned, see [`ptr_get_page`]'s `// ALIGN:` reasoning).
    link: ListLink,
    /// Head of this page's intra-page free-slot list, or null if full. Byte offset
    /// 16 (64-bit), 8-byte aligned (immediately follows `link`, itself a multiple of
    /// 8 bytes).
    free_list: *mut FreeLink,
    /// This page's bucket index — `bucket_spacing_function_aligned(elem_size)`. Byte
    /// offset 24 (64-bit), 2-byte aligned (`u16`'s own alignment).
    bucket_index: u16,
    /// Number of currently-allocated slots in this page. Byte offset 26 (64-bit),
    /// 2-byte aligned.
    use_count: u16,
    /// `owning_bucket.marker() ^ (this page's own truncated address)`. See
    /// [`Bucket::marker`]. Byte offset 28 (64-bit), 4-byte aligned (`u32`'s own
    /// alignment; `bucket_index` + `use_count` together total 4 bytes, keeping this
    /// field's offset a multiple of 4 with no padding needed).
    marker: u32,
}

// link (2 words) + free_list (1 word) + {bucket_index, use_count, marker} packed
// into 1 word (2 + 2 + 4 = 8 bytes) = 4 words on 64-bit.
const _: () = assert!(size_of::<Page>() == 4 * size_of::<usize>());

impl Page {
    // SAFETY-bearing accessors (one raw dereference each, matching the rest of the
    // crate's intrusive-node modules).

    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn raw_free_list(this: *mut Page) -> *mut FreeLink {
        // SAFETY: caller guarantees `this` is live; reads one field.
        unsafe { (*this).free_list }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn raw_set_free_list(this: *mut Page, val: *mut FreeLink) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).free_list = val };
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    unsafe fn raw_use_count(this: *mut Page) -> u16 {
        // SAFETY: caller guarantees `this` is live; reads one field.
        unsafe { (*this).use_count }
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn raw_set_use_count(this: *mut Page, val: u16) {
        // SAFETY: caller guarantees `this` is live; writes one field.
        unsafe { (*this).use_count = val };
    }

    /// The element size this page's slots serve.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn elem_size(this: *mut Page) -> usize {
        // SAFETY: caller guarantees `this` is live; reads one field.
        let index = unsafe { (*this).bucket_index };
        bucket_spacing_function_inverse(usize::from(index))
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn bucket_index(this: *mut Page) -> usize {
        // SAFETY: caller guarantees `this` is live; reads one field.
        usize::from(unsafe { (*this).bucket_index })
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn is_empty(this: *mut Page) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { Page::raw_use_count(this) == 0 }
    }

    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn is_full(this: *mut Page) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { Page::raw_free_list(this) }.is_null()
    }

    /// # Safety
    /// `this` must be live.
    unsafe fn inc_use_count(this: *mut Page) {
        // SAFETY: `this` is live (this function's contract).
        let count = unsafe { Page::raw_use_count(this) };
        // SAFETY: `this` is live.
        unsafe { Page::raw_set_use_count(this, count + 1) };
    }

    /// # Safety
    /// `this` must be live, with `use_count > 0`.
    unsafe fn dec_use_count(this: *mut Page) {
        // SAFETY: `this` is live (this function's contract).
        let count = unsafe { Page::raw_use_count(this) };
        debug_assert!(count > 0);
        // SAFETY: `this` is live.
        unsafe { Page::raw_set_use_count(this, count - 1) };
    }

    /// Whether `marker` (a candidate owning bucket's marker) is consistent with this
    /// page's own stored, address-mixed marker. Ports `page::check_marker`.
    ///
    /// # Safety
    /// `this` must be live.
    #[must_use]
    pub(crate) unsafe fn check_marker(this: *mut Page, marker: u32) -> bool {
        // SAFETY: caller guarantees `this` is live; reads one field.
        let stored = unsafe { (*this).marker };
        // CAST: usize -> u32, truncating `this`'s own address — mirrors how the
        // marker was seeded in `init_page_at` below; only the low bits need to match.
        #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
        let addr = this.addr() as u32;
        stored == (marker ^ addr)
    }
}

// SAFETY: `link` is Page's first field (repr(C) guarantees offset 0).
unsafe impl ListNode for Page {}

/// Recovers the [`Page`] bookkeeping struct owning a bucket-path payload pointer.
/// Ports `allocator::ptr_get_page`.
///
/// # Safety
/// `ptr` must point into a page that a call to [`init_page_at`] (directly, or via
/// [`Buckets::system_alloc`]) previously initialized.
#[must_use]
pub(crate) unsafe fn ptr_get_page(ptr: *mut u8) -> *mut Page {
    // ALIGN: round down to the PAGE_SIZE-aligned mapping base (`os::map`'s guarantee,
    // relied on transitively via this function's own contract), then step forward to
    // the Page struct's fixed tail position.
    let page_base = crate::align::align_down(ptr, os::PAGE_SIZE);
    // SAFETY: `page_base` is the live mapping base `ptr` belongs to (this function's
    // contract); `PAGE_SIZE - size_of::<Page>()` stays within that same mapping.
    let page = unsafe { page_base.byte_add(os::PAGE_SIZE - size_of::<Page>()) };
    // ALIGN: `page_base` is PAGE_SIZE-aligned (hence 8-aligned) and
    // `PAGE_SIZE - size_of::<Page>()` is a multiple of 8 (PAGE_SIZE is, size_of::<Page>()
    // is), so `page` is 8-aligned — matches `align_of::<Page>()`.
    #[allow(clippy::cast_ptr_alignment)]
    page.cast::<Page>()
}

/// Acquires one `PAGE_SIZE` buffer (already obtained — from `os::map` in production,
/// or a test's own heap-backed stand-in) and threads it into `elem_size`-sized free
/// slots with a [`Page`] at the tail. Ports the free-list-building loop and the
/// placement-new in `allocator::bucket_grow`, factored out from OS acquisition so it
/// can be exercised under Miri (see the module doc).
///
/// # Safety
/// `mem` must be valid for exactly `PAGE_SIZE` bytes, `PAGE_SIZE`-aligned, and not
/// concurrently accessed. `elem_size` must be a bucket size class
/// (`bucket_spacing_function_inverse` of some index `< NUM_BUCKETS`).
#[must_use]
unsafe fn init_page_at(mem: *mut u8, elem_size: usize, marker: u32) -> NonNull<Page> {
    debug_assert_eq!(mem.addr() % os::PAGE_SIZE, 0);
    debug_assert!(elem_size > 0);
    // The largest multiple of elem_size that leaves room for a trailing Page.
    let usable = os::PAGE_SIZE - size_of::<Page>();
    let slot_count = usable / elem_size;
    debug_assert!(
        u16::try_from(slot_count).is_ok(),
        "use_count would overflow u16"
    );
    let n = slot_count * elem_size;
    let mut i = 0;
    // EXPLICIT: threads the free-list `next` pointer through consecutive slots;
    // `i` is the state (byte offset of the slot being linked), not expressible as an
    // iterator over raw, uninitialized-until-written memory.
    while i < n - elem_size {
        // SAFETY: `mem` is valid for PAGE_SIZE bytes (this function's contract);
        // `i < n - elem_size <= usable` stays within that range.
        let slot = unsafe { mem.byte_add(i) };
        // ALIGN: `mem` is PAGE_SIZE-aligned (this function's contract, `>= 8`);
        // `i` is a multiple of `elem_size`, itself always a multiple of
        // `MIN_ALLOCATION` (8) — `bucket_spacing_function_inverse` only ever
        // returns `(index + 1) << MIN_ALLOCATION_LOG2`. So `slot` is 8-aligned.
        #[allow(clippy::cast_ptr_alignment)]
        let slot = slot.cast::<FreeLink>();
        // SAFETY: `mem` is valid for PAGE_SIZE bytes; `i + elem_size < n <= usable`
        // stays within that range.
        let next_slot = unsafe { mem.byte_add(i + elem_size) };
        // ALIGN: same reasoning as `slot` above (`i + elem_size` is likewise a
        // multiple of 8).
        #[allow(clippy::cast_ptr_alignment)]
        let next_slot = next_slot.cast::<FreeLink>();
        // SAFETY: `slot` is within `mem`'s PAGE_SIZE-byte region (established above);
        // writes one field (this is the slot's first write, establishing it as a
        // live FreeLink — no prior value is ever read).
        unsafe { FreeLink::set_next(slot, next_slot) };
        i += elem_size;
    }
    // SAFETY: `mem` is valid for PAGE_SIZE bytes; `i < n <= usable` stays within range.
    let last_slot = unsafe { mem.byte_add(i) };
    // ALIGN: same reasoning as `slot` above (`i` is a multiple of 8).
    #[allow(clippy::cast_ptr_alignment)]
    let last_slot = last_slot.cast::<FreeLink>();
    // SAFETY: `last_slot` is within `mem`'s PAGE_SIZE-byte region; writes one field
    // (this slot's first write).
    unsafe { FreeLink::set_next(last_slot, core::ptr::null_mut()) };
    debug_assert!(i + elem_size + size_of::<Page>() <= os::PAGE_SIZE);

    // SAFETY: `mem` is PAGE_SIZE-aligned and valid for PAGE_SIZE bytes (this
    // function's contract), so `ptr_get_page` finds the correct, in-bounds tail slot.
    let page = unsafe { ptr_get_page(mem) };
    // CAST: usize -> u32, truncating the page's own address to mix into its stored
    // marker (see `Page::check_marker`); only the low bits need to round-trip.
    #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
    let page_addr = page.addr() as u32;
    // CAST: usize -> u16, `bucket_spacing_function_aligned` always returns a value
    // `< NUM_BUCKETS` (32), which fits comfortably in u16.
    #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
    let bucket_index = bucket_spacing_function_aligned(elem_size) as u16;
    // ALIGN: `mem` is PAGE_SIZE-aligned (this function's contract), hence 8-aligned.
    #[allow(clippy::cast_ptr_alignment)]
    let free_list = mem.cast::<FreeLink>();
    let fresh = Page {
        link: ListLink::UNLINKED,
        free_list,
        bucket_index,
        use_count: 0,
        marker: marker ^ page_addr,
    };
    // SAFETY: `page` is a live, in-bounds, correctly-aligned `*mut Page` (established
    // above); this is its first write (placement), so no prior value is dropped.
    unsafe { page.write(fresh) };
    // SAFETY: `page` is non-null (a real position within `mem`'s live allocation).
    unsafe { NonNull::new_unchecked(page) }
}

/// One size class's page list. Ports `allocator::bucket`.
pub(crate) struct Bucket {
    /// This size class's pages, auto-sorted so pages with free slots stay near the
    /// front ([`Bucket::alloc`]/[`Bucket::free`] re-sort on the full/empty transition).
    pages: IntrusiveList<Page>,
}

/// XOR-mixed into every page's stored marker; ports `allocator::bucket::MARKER`.
const MARKER_CONST: u32 = 0x628b_f2b6;

impl Bucket {
    /// Builds an empty bucket. Ports `bucket::bucket` (HPHA's default constructor).
    #[must_use]
    const fn new() -> Self {
        Self {
            pages: IntrusiveList::new(),
        }
    }

    /// A per-instance, deterministic page-ownership marker. HPHA seeds this from
    /// `rand()` at construction; this crate derives it from the bucket's own address
    /// instead (deterministic, no RNG dependency — see `Rust/CONVENTIONS.md`'s
    /// determinism rule). The value only feeds [`Page::check_marker`]'s sanity check
    /// (never state-transition logic), so this substitution doesn't touch the
    /// cross-port invariant. Ports `bucket::marker`.
    #[must_use]
    pub(crate) fn marker(&self) -> u32 {
        // PROVENANCE: address read for its bit pattern only, never turned back into
        // a pointer — no provenance is created or consumed here.
        // CAST: usize -> u32, truncating this bucket's own address (matches HPHA's
        // `(unsigned)((size_t)this)`).
        #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
        let addr = core::ptr::from_ref(self).addr() as u32;
        addr ^ MARKER_CONST
    }

    /// The first page with a free slot, if any page in this bucket has one. Ports
    /// `bucket::get_free_page`.
    #[must_use]
    fn get_free_page(&self) -> Option<NonNull<Page>> {
        let front = self.pages.front()?;
        // SAFETY: `front` is live (just returned by the list above).
        if unsafe { Page::is_full(front.as_ptr()) } {
            None
        } else {
            Some(front)
        }
    }

    /// Adds a freshly-grown page (with a full free list) to this bucket. Ports the
    /// `mBuckets[bi].add_free_page(p)` call in `allocator::bucket_alloc(_direct)`.
    fn add_free_page(&self, page: NonNull<Page>) {
        self.pages.push_front(page);
    }

    /// Allocates one slot from `page`, which must have a free slot. Ports
    /// `bucket::alloc`.
    ///
    /// # Safety
    /// `page` must be live, currently a member of this bucket's page list, and not full.
    #[must_use]
    unsafe fn alloc(&self, page: NonNull<Page>) -> NonNull<u8> {
        // SAFETY: caller guarantees `page` is live and not full.
        unsafe { Page::inc_use_count(page.as_ptr()) };
        // SAFETY: `page` is live; reads one field.
        let free = unsafe { Page::raw_free_list(page.as_ptr()) };
        debug_assert!(!free.is_null(), "caller guaranteed page was not full");
        // SAFETY: `free` is live (a page's free-list head is always a live slot when
        // the list is non-empty, which the caller's "not full" contract guarantees).
        let next = unsafe { FreeLink::next(free) };
        // SAFETY: `page` is live; writes one field.
        unsafe { Page::raw_set_free_list(page.as_ptr(), next) };
        if next.is_null() {
            // The page just became full: move it to the back so mostly-empty pages
            // stay near the front of the list, matching HPHA's own auto-sort.
            crate::list::unlink_node(page);
            self.pages.push_back(page);
        }
        // SAFETY: `free` is non-null (checked above) and was this page's live
        // free-list head, i.e. a valid, exclusively-owned slot of `page`'s elem_size.
        unsafe { NonNull::new_unchecked(free.cast::<u8>()) }
    }

    /// Returns `ptr` (a slot of `page`) to `page`'s free list. Ports `bucket::free`.
    ///
    /// # Safety
    /// `page` must be live and currently a member of this bucket's page list. `ptr`
    /// must be a slot this bucket previously handed out from `page` via
    /// [`Bucket::alloc`], not currently free.
    unsafe fn free(&self, page: NonNull<Page>, ptr: NonNull<u8>) {
        // SAFETY: `page` is live (this function's contract); reads one field.
        let free = unsafe { Page::raw_free_list(page.as_ptr()) };
        let link = ptr.cast::<FreeLink>();
        // SAFETY: `link` is `ptr`, a live, exclusively-owned slot per this function's
        // contract; writes one field (reclaiming it as a free-list node).
        unsafe { FreeLink::set_next(link.as_ptr(), free) };
        // SAFETY: `page` is live; writes one field.
        unsafe { Page::raw_set_free_list(page.as_ptr(), link.as_ptr()) };
        // SAFETY: `page` is live, with `use_count > 0` (it owned `ptr` as an
        // allocated slot per this function's contract).
        unsafe { Page::dec_use_count(page.as_ptr()) };
        if free.is_null() {
            // The page was previously full: move it to the front, matching HPHA's
            // own auto-sort (freshly-freed pages are the best candidates to reuse).
            crate::list::unlink_node(page);
            self.pages.push_front(page);
        }
    }
}

/// All 32 bucket size classes, plus the bucket path's running allocated-byte total.
/// Ports the bucket-related slice of `allocator` (`mBuckets`,
/// `mTotalAllocatedSizeBuckets`, and the free `bucket_*` methods).
pub(crate) struct Buckets {
    /// One [`Bucket`] per size class, indexed by [`bucket_spacing_function`] and its
    /// variants.
    buckets: [Bucket; NUM_BUCKETS],
    /// Total bytes currently mapped for the bucket path (whole `PAGE_SIZE` pages).
    /// Interior-mutable: every `Buckets` method takes `&self` (see `list.rs`'s
    /// `IntrusiveList` doc for why the allocator's subsystems are `&self`-shaped
    /// throughout, anticipating the `GlobalAlloc` boundary). A plain `Cell<usize>`
    /// suffices here — unlike the list/tree sentinels, this field never stores a
    /// pointer, so it has none of their Tree-Borrows persistence hazard.
    allocated_bytes: Cell<usize>,
}

impl Buckets {
    #[must_use]
    pub(crate) const fn new() -> Self {
        // `core::array::from_fn` isn't callable in a const context; the
        // `[const { .. }; N]` repeat-expression form is — it evaluates `Bucket::new()`
        // once per array slot at compile time, which is what lets `Orisnik::new`
        // (and therefore `Buckets::new`) stay `const fn`, needed for the standard
        // `#[global_allocator] static ALLOCATOR: Orisnik = Orisnik::new();` pattern
        // (a `static`'s initializer must be const-evaluable).
        Self {
            buckets: [const { Bucket::new() }; NUM_BUCKETS],
            allocated_bytes: Cell::new(0),
        }
    }

    /// Total bytes currently claimed from the OS by the bucket path (whole pages,
    /// not payload bytes). Ports the bucket half of `allocator::allocated`.
    #[must_use]
    pub(crate) fn allocated(&self) -> usize {
        self.allocated_bytes.get()
    }

    /// Maps one fresh `PAGE_SIZE` OS page. Ports `allocator::bucket_system_alloc`.
    #[must_use]
    fn system_alloc(&self) -> Option<NonNull<u8>> {
        let ptr = os::map(os::PAGE_SIZE)?;
        self.allocated_bytes
            .set(self.allocated_bytes.get() + os::PAGE_SIZE);
        Some(ptr)
    }

    /// Returns one `PAGE_SIZE` OS page. Ports `allocator::bucket_system_free`.
    ///
    /// # Safety
    /// `ptr` must be a still-live result of [`Buckets::system_alloc`] on `self`.
    unsafe fn system_free(&self, ptr: NonNull<u8>) {
        // SAFETY: forwarded from this function's own contract.
        unsafe { os::unmap(ptr, os::PAGE_SIZE) };
        self.allocated_bytes
            .set(self.allocated_bytes.get() - os::PAGE_SIZE);
    }

    /// Maps a fresh page and threads it for `elem_size`-sized slots, owned by bucket
    /// `bi`. Ports `allocator::bucket_grow`.
    #[must_use]
    fn grow(&self, bi: usize) -> Option<NonNull<Page>> {
        debug_assert!(bi < NUM_BUCKETS);
        let elem_size = bucket_spacing_function_inverse(bi);
        let mem = self.system_alloc()?;
        // INDEX: `bi < NUM_BUCKETS`, checked above.
        #[allow(clippy::indexing_slicing)]
        let marker = self.buckets[bi].marker();
        // SAFETY: `mem` is exactly PAGE_SIZE bytes, PAGE_SIZE-aligned (`os::map`'s
        // guarantee), and freshly mapped (exclusively ours, nothing else accesses it
        // concurrently — this crate is single-threaded in v0.1.0); `elem_size` is a
        // real bucket size class (`bi < NUM_BUCKETS`, checked above).
        let page = unsafe { init_page_at(mem.as_ptr(), elem_size, marker) };
        Some(page)
    }

    /// Allocates `size` bytes on the bucket path, computing the bucket index from
    /// `size` directly (used when a prior guard-byte/alignment adjustment already
    /// produced the final target size — see `bucket_realloc`'s HPHA counterpart).
    /// Ports `allocator::bucket_alloc`.
    #[must_use]
    pub(crate) fn alloc(&self, size: usize) -> Option<NonNull<u8>> {
        debug_assert!(size <= MAX_SMALL_ALLOCATION);
        let bi = bucket_spacing_function(size);
        self.alloc_direct(bi)
    }

    /// Allocates from a pre-computed bucket index. Ports `allocator::bucket_alloc_direct`.
    #[must_use]
    pub(crate) fn alloc_direct(&self, bi: usize) -> Option<NonNull<u8>> {
        debug_assert!(bi < NUM_BUCKETS);
        // INDEX: `bi < NUM_BUCKETS`, checked above.
        #[allow(clippy::indexing_slicing)]
        let bucket = &self.buckets[bi];
        let page = if let Some(p) = bucket.get_free_page() {
            p
        } else {
            let p = self.grow(bi)?;
            bucket.add_free_page(p);
            p
        };
        // SAFETY: `page` is live and was just confirmed to have a free slot
        // (`get_free_page`'s own check) or was freshly grown (always has free
        // slots); it is a member of `bucket`'s page list either way.
        Some(unsafe { bucket.alloc(page) })
    }

    /// Grows or shrinks a bucket-path allocation in place if the current slot's
    /// element size can already accommodate `size`; otherwise allocates a new,
    /// larger slot, copies, and frees the old one. Ports `allocator::bucket_realloc`.
    ///
    /// # Safety
    /// `ptr` must be a still-live bucket-path allocation this instance produced.
    #[must_use]
    pub(crate) unsafe fn realloc(&self, ptr: NonNull<u8>, size: usize) -> Option<NonNull<u8>> {
        // SAFETY: forwarded from this function's own contract.
        let page = unsafe { ptr_get_page(ptr.as_ptr()) };
        // SAFETY: `page` is live (recovered from a live pointer, this function's
        // contract).
        let elem_size = unsafe { Page::elem_size(page) };
        if size <= elem_size {
            return Some(ptr);
        }
        let new_ptr = self.alloc(size)?;
        // SAFETY: `ptr` is valid for `elem_size` bytes (its slot's own size, an
        // upper bound on the live payload within it); `new_ptr` was just allocated
        // with room for at least `size > elem_size` bytes — copying `elem_size`
        // bytes fits in both.
        unsafe {
            new_ptr
                .as_ptr()
                .copy_from_nonoverlapping(ptr.as_ptr(), elem_size);
        };
        // SAFETY: `ptr` is a live bucket-path allocation this instance produced
        // (this function's contract), not used again after this call.
        unsafe { self.free(ptr) };
        Some(new_ptr)
    }

    /// Frees a bucket-path allocation, recovering its bucket index from its page.
    /// Ports `allocator::bucket_free`.
    ///
    /// # Safety
    /// `ptr` must be a still-live bucket-path allocation this instance produced.
    pub(crate) unsafe fn free(&self, ptr: NonNull<u8>) {
        // SAFETY: forwarded from this function's own contract.
        let page = unsafe { ptr_get_page(ptr.as_ptr()) };
        // SAFETY: `page` is live.
        let bi = unsafe { Page::bucket_index(page) };
        debug_assert!(bi < NUM_BUCKETS);
        // SAFETY: `page` is live; a member of `self.buckets[bi]`'s page list (its own
        // recovered bucket index, this function's contract).
        let page = unsafe { NonNull::new_unchecked(page) };
        // INDEX: `bi < NUM_BUCKETS`, checked above.
        #[allow(clippy::indexing_slicing)]
        let bucket = &self.buckets[bi];
        // SAFETY: `page` is a member of this bucket's list; `ptr` is a live slot of
        // it this instance previously handed out (this function's contract).
        unsafe { bucket.free(page, ptr) };
    }

    /// Frees a bucket-path allocation given its original bucket index directly
    /// (skipping the page-marker recovery `free` needs) — used when the caller
    /// already knows the exact original size/alignment. Ports
    /// `allocator::bucket_free_direct`.
    ///
    /// # Safety
    /// `ptr` must be a still-live allocation this instance produced from bucket `bi`.
    pub(crate) unsafe fn free_direct(&self, ptr: NonNull<u8>, bi: usize) {
        debug_assert!(bi < NUM_BUCKETS);
        // SAFETY: forwarded from this function's own contract.
        let page = unsafe { ptr_get_page(ptr.as_ptr()) };
        // SAFETY: `page` is live; caller guarantees `bi` matches `ptr`'s actual
        // bucket (mirrors HPHA's own `assert(bi == p->bucket_index())`).
        debug_assert_eq!(unsafe { Page::bucket_index(page) }, bi);
        // SAFETY: `page` is live and non-null (a real position within a live mapping).
        let page = unsafe { NonNull::new_unchecked(page) };
        // INDEX: `bi < NUM_BUCKETS`, checked above.
        #[allow(clippy::indexing_slicing)]
        let bucket = &self.buckets[bi];
        // SAFETY: `page` is a member of this bucket's list (caller-guaranteed `bi`);
        // `ptr` is a live slot of it this instance previously handed out.
        unsafe { bucket.free(page, ptr) };
    }

    /// Whether `ptr` is a live bucket-path allocation from this instance — the
    /// page-marker sanity check the pointer-only `free`/`realloc`/`size` overloads
    /// rely on to dispatch between the bucket and tree paths. Ports
    /// `allocator::ptr_in_bucket`.
    ///
    /// The marker check alone has a documented, HPHA-inherited false-positive risk:
    /// for a non-bucket pointer, the position `ptr_get_page` computes is not really
    /// a `Page`, so `bucket_index`/`marker` are just whatever bytes happen to sit
    /// there — bytes that can, on rare occasion, coincidentally read as a small
    /// valid-looking index whose recomputed marker matches (this is not
    /// hypothetical: it is exactly how a same-page tree allocation can occasionally
    /// alias a bucket page's marker layout, since both live inside `PAGE_SIZE`-sized,
    /// `PAGE_SIZE`-aligned OS mappings). HPHA's own `ptr_in_bucket` acknowledges this
    /// in a comment and compensates with a debug-only exhaustive scan of the
    /// candidate bucket's real page list, `assert`-ing the fast path agrees; ported
    /// below as a `debug_assert_eq!` (an always-on `assert!` would violate this
    /// crate's hot-path-never-panics rule for a check the *release* build — like
    /// HPHA's own release build — intentionally still skips, relying on the marker
    /// check alone once it has been debug-verified in test/CI builds).
    ///
    /// # Safety
    /// `ptr` must be a pointer this instance is being asked to classify (i.e. either
    /// a genuine live allocation from this instance, bucket or tree path, or a
    /// caller bug being defended against — this function must not be called with an
    /// arbitrary, unrelated pointer, since `ptr_get_page` unconditionally reads
    /// memory at a computed offset from it).
    #[must_use]
    pub(crate) unsafe fn ptr_in_bucket(&self, ptr: NonNull<u8>) -> bool {
        // SAFETY: forwarded from this function's own contract.
        let page = unsafe { ptr_get_page(ptr.as_ptr()) };
        // SAFETY: `page` is live per this function's contract (every allocation this
        // instance could have produced has a live Page at this computed position,
        // whether or not `ptr` truly is a bucket allocation).
        let bi = unsafe { Page::bucket_index(page) };
        if bi >= NUM_BUCKETS {
            return false;
        }
        // INDEX: `bi < NUM_BUCKETS`, checked above.
        #[allow(clippy::indexing_slicing)]
        let bucket = &self.buckets[bi];
        let marker = bucket.marker();
        // SAFETY: `page` is live.
        let result = unsafe { Page::check_marker(page, marker) };
        debug_assert_eq!(
            result,
            bucket.pages.contains(page.cast::<ListLink>()),
            "ptr_in_bucket's marker check disagreed with an exhaustive page-list scan. \
             Two causes are possible. A false positive (marker says yes, scan says no) \
             is the known, HPHA-inherited one this function's own doc describes. A \
             false *negative* (marker says no, scan says yes) is not: it means every \
             marker in this bucket was seeded from a different address than the one \
             `Bucket::marker` reports now — i.e. the owning `Orisnik` has been moved \
             since its first use. See `Orisnik`'s `# Address stability` doc section."
        );
        result
    }

    /// Returns every page with zero live allocations back to the OS. Ports
    /// `allocator::bucket_purge`.
    ///
    /// The walk visits the *whole* page list, stopping only at the first **full**
    /// page — it does not stop at a merely partially-used one. That distinction is
    /// HPHA's, and it is load-bearing: `Bucket`'s auto-sort only re-orders a page on
    /// its full↔not-full transition (`Bucket::alloc` pushes to the back on becoming
    /// full, `Bucket::free` to the front on ceasing to be full), so the ordering
    /// *among* not-full pages is arbitrary and an empty page can sit behind a
    /// partially-used one. v0.1.0 broke out of the loop on the first non-empty page
    /// and so left those unreclaimed; see `docs/audits/2026-08-29-pre-v0.2.0-audit.md`.
    pub(crate) fn purge(&self) {
        for bucket in &self.buckets {
            let sentinel = bucket.pages.sentinel();
            // EXPLICIT: raw link-chase rather than a `front()` loop — the walk must
            // advance *past* pages it does not free (unlike v0.1.0's head-only
            // version), and it must latch each node's successor before unlinking it.
            // `cur` is the state; an iterator cannot express a traversal whose
            // current node is spliced out mid-walk.
            // SAFETY: `sentinel` is live and self-linked (`IntrusiveList::sentinel`'s
            // own guarantee); its `next` is therefore live.
            let mut cur = unsafe { crate::list::ListLink::next(sentinel) };
            while cur != sentinel {
                // SAFETY: `cur != sentinel`, so it is a real node's link, and every
                // node in this list is a `Page` whose `link` sits at offset 0.
                let page = unsafe { NonNull::new_unchecked(cur.cast::<Page>()) };
                // SAFETY: `page` is live (a linked member of this bucket's list).
                if unsafe { Page::is_full(page.as_ptr()) } {
                    // HPHA's own early-out: a full page means every page after it is
                    // at least as full, since `Bucket::alloc` moves pages to the back
                    // exactly when they fill up.
                    break;
                }
                // Latched before the unlink below, which rewrites `cur`'s own links.
                // SAFETY: `cur` is live and linked (established above).
                let next = unsafe { crate::list::ListLink::next(cur) };
                // SAFETY: `page` is live.
                if unsafe { Page::is_empty(page.as_ptr()) } {
                    crate::list::unlink_node(page);
                    // ALIGN: `page` is a live `Page`, always
                    // `PAGE_SIZE - size_of::<Page>()` bytes into its owning
                    // PAGE_SIZE-aligned mapping (the type's own invariant); rounding
                    // its address down recovers that mapping's base.
                    let mem = crate::align::align_down(page.as_ptr().cast::<u8>(), os::PAGE_SIZE);
                    // SAFETY: `mem` is the live mapping `page` belongs to (established
                    // above), non-null (a real page address).
                    let mem = unsafe { NonNull::new_unchecked(mem) };
                    // SAFETY: `mem` is live, not referenced again after this call (the
                    // page was just unlinked from every structure this module tracks
                    // it through, and `next` was latched before the unlink).
                    unsafe { self.system_free(mem) };
                }
                cur = next;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `PAGE_SIZE`-sized, `PAGE_SIZE`-aligned heap buffer standing in for a real OS
    /// page — lets `init_page_at` (the actual bucket logic) run under Miri, which
    /// cannot interpret the real `os::map`/`VirtualAlloc`/`mmap` (see the module doc).
    /// Uses `std::alloc` directly with an explicit `PAGE_SIZE`-aligned `Layout` —
    /// unlike a `Vec<T>`, this lets the test request the exact alignment it needs
    /// rather than relying on a scalar type's (much smaller) natural alignment.
    struct FakePage {
        // The buffer itself; freed in `Drop` below.
        ptr: NonNull<u8>,
    }

    impl FakePage {
        fn new() -> Self {
            let layout = std::alloc::Layout::from_size_align(os::PAGE_SIZE, os::PAGE_SIZE)
                .expect("PAGE_SIZE is a power of two and fits in isize");
            // SAFETY: `layout` has a non-zero size (PAGE_SIZE).
            let raw = unsafe { std::alloc::alloc_zeroed(layout) };
            let ptr = NonNull::new(raw).expect("std::alloc::alloc_zeroed failed");
            Self { ptr }
        }

        fn ptr(&mut self) -> *mut u8 {
            self.ptr.as_ptr()
        }
    }

    impl Drop for FakePage {
        fn drop(&mut self) {
            let layout = std::alloc::Layout::from_size_align(os::PAGE_SIZE, os::PAGE_SIZE)
                .expect("PAGE_SIZE is a power of two and fits in isize");
            // SAFETY: `self.ptr` was allocated by `std::alloc::alloc_zeroed` with
            // this exact `layout` in `FakePage::new`, and is freed at most once
            // (`Drop` runs exactly once per value).
            unsafe { std::alloc::dealloc(self.ptr.as_ptr(), layout) };
        }
    }

    #[test]
    fn bucket_spacing_round_trips_every_class() {
        for bi in 0..NUM_BUCKETS {
            let size = bucket_spacing_function_inverse(bi);
            assert_eq!(bucket_spacing_function_aligned(size), bi);
            assert_eq!(bucket_spacing_function(size), bi);
            // One byte over a class boundary rounds up into the next class (except
            // at the top, where it would exceed MAX_SMALL_ALLOCATION).
            if bi + 1 < NUM_BUCKETS {
                assert_eq!(bucket_spacing_function(size + 1), bi + 1);
            }
        }
        assert_eq!(bucket_spacing_function_inverse(0), MIN_ALLOCATION);
        assert_eq!(
            bucket_spacing_function_inverse(NUM_BUCKETS - 1),
            MAX_SMALL_ALLOCATION
        );
    }

    #[test]
    fn clamp_and_is_small_allocation() {
        assert_eq!(clamp_small_allocation(1), MIN_ALLOCATION);
        assert_eq!(clamp_small_allocation(MIN_ALLOCATION), MIN_ALLOCATION);
        assert_eq!(
            clamp_small_allocation(MIN_ALLOCATION + 1),
            MIN_ALLOCATION + 1
        );
        assert!(is_small_allocation(MAX_SMALL_ALLOCATION));
        assert!(!is_small_allocation(MAX_SMALL_ALLOCATION + 1));
    }

    #[test]
    fn init_page_at_threads_free_list_and_computes_slot_count() {
        let mut fp = FakePage::new();
        let elem_size = 32;
        // SAFETY: `fp`'s buffer is PAGE_SIZE bytes, PAGE_SIZE-aligned, and
        // exclusively owned by this test; `elem_size` is a real bucket size class.
        let page = unsafe { init_page_at(fp.ptr(), elem_size, 0xDEAD_BEEF) };
        // SAFETY: `page` is live (just initialized above).
        assert_eq!(unsafe { Page::elem_size(page.as_ptr()) }, elem_size);
        // SAFETY: `page` is live.
        assert!(unsafe { Page::is_empty(page.as_ptr()) });
        // SAFETY: `page` is live.
        assert!(!unsafe { Page::is_full(page.as_ptr()) });

        // Walk the free list to the end, counting slots, and confirm the marker
        // round-trips against the seed used above.
        // SAFETY: `page` is live.
        let mut cur = unsafe { Page::raw_free_list(page.as_ptr()) };
        let mut count = 0;
        while !cur.is_null() {
            count += 1;
            // SAFETY: `cur` is live (the free list is fully threaded by
            // `init_page_at`, every non-null link points at a live slot).
            cur = unsafe { FreeLink::next(cur) };
        }
        let expected = (os::PAGE_SIZE - size_of::<Page>()) / elem_size;
        assert_eq!(count, expected);
        // SAFETY: `page` is live.
        assert!(unsafe { Page::check_marker(page.as_ptr(), 0xDEAD_BEEF) });
        // SAFETY: `page` is live.
        assert!(!unsafe { Page::check_marker(page.as_ptr(), 0xCAFE_BABE) });
    }

    #[test]
    fn bucket_alloc_free_cycle_updates_free_list_and_use_count() {
        let mut fp = FakePage::new();
        let elem_size = 16;
        // SAFETY: `fp`'s buffer is PAGE_SIZE bytes, PAGE_SIZE-aligned, exclusively
        // owned by this test.
        let page = unsafe { init_page_at(fp.ptr(), elem_size, 0) };
        let bucket = Bucket::new();
        bucket.add_free_page(page);

        // SAFETY: `page` is live, a member of `bucket`'s list, and not full.
        let a = unsafe { bucket.alloc(page) };
        // SAFETY: `page` is live.
        assert_eq!(unsafe { Page::raw_use_count(page.as_ptr()) }, 1);
        // SAFETY: `page` is live, a member of `bucket`'s list, not full (only 1 of
        // many slots taken).
        let b = unsafe { bucket.alloc(page) };
        assert_ne!(a, b);
        // SAFETY: `page` is live.
        assert_eq!(unsafe { Page::raw_use_count(page.as_ptr()) }, 2);

        // SAFETY: `page` is live, a member of `bucket`'s list; `a` is a live slot
        // this bucket handed out from `page` above, not currently free.
        unsafe { bucket.free(page, a) };
        // SAFETY: `page` is live.
        assert_eq!(unsafe { Page::raw_use_count(page.as_ptr()) }, 1);

        // SAFETY: same contract as `a`'s free above.
        unsafe { bucket.free(page, b) };
        // SAFETY: `page` is live.
        assert!(unsafe { Page::is_empty(page.as_ptr()) });
    }

    #[test]
    fn bucket_alloc_sorts_full_page_behind_partial_page() {
        let mut fp_small = FakePage::new(); // small elem_size -> many slots
        let mut fp = FakePage::new();
        let elem_size = MAX_SMALL_ALLOCATION; // largest class -> fewest slots
        let big_elem_size = MIN_ALLOCATION;
        // SAFETY: each buffer is PAGE_SIZE bytes, PAGE_SIZE-aligned, exclusively
        // owned by this test.
        let full_page = unsafe { init_page_at(fp.ptr(), elem_size, 0) };
        // SAFETY: same as above.
        let roomy_page = unsafe { init_page_at(fp_small.ptr(), big_elem_size, 0) };
        let bucket = Bucket::new();
        bucket.add_free_page(full_page);
        bucket.add_free_page(roomy_page);
        assert_eq!(bucket.get_free_page(), Some(roomy_page));

        // Exhaust every slot in `full_page` (few slots, since elem_size is large).
        let slots = (os::PAGE_SIZE - size_of::<Page>()) / elem_size;
        for _ in 0..slots {
            // SAFETY: `full_page` is live, a member of `bucket`'s list; not full
            // until this loop's last iteration.
            let _ = unsafe { bucket.alloc(full_page) };
        }
        // `full_page` auto-sorted to the back; `roomy_page` is still servable.
        assert_eq!(bucket.get_free_page(), Some(roomy_page));
    }

    // The `Buckets`-level tests below (as opposed to the `Bucket`/`init_page_at`
    // tests above, which use `FakePage`) call `Buckets::new()` and allocate through
    // `os::map` — served under Miri by `os::test_vm`'s heap-backed stand-in, and by
    // the real `VirtualAlloc`/`mmap` in a native `cargo test`. See `os::test_vm`'s
    // own doc for why that split exists: Miri does not shim `VirtualAlloc`, and its
    // `mmap` shim does not support the trim-to-alignment technique `os::map`'s Unix
    // path uses, so before v0.1.1 these tests could not run under Miri at all.
    #[test]
    fn buckets_alloc_direct_grows_and_serves_from_same_page() {
        let buckets = Buckets::new();
        let bi = bucket_spacing_function(24); // -> the 24-byte class
        let a = buckets.alloc_direct(bi).expect("OS map failed");
        let b = buckets.alloc_direct(bi).expect("OS map failed");
        assert_ne!(a, b);
        // SAFETY: `a` is a live allocation `buckets` just produced from bucket `bi`.
        unsafe { buckets.free_direct(a, bi) };
        // SAFETY: `b` is a live allocation `buckets` just produced from bucket `bi`.
        unsafe { buckets.free_direct(b, bi) };
        buckets.purge();
        assert_eq!(buckets.allocated(), 0);
    }

    #[test]
    fn buckets_free_recovers_bucket_index_from_page() {
        let buckets = Buckets::new();
        let ptr = buckets.alloc(40).expect("OS map failed");
        // SAFETY: `ptr` is a live allocation `buckets` just produced.
        assert!(unsafe { buckets.ptr_in_bucket(ptr) });
        // SAFETY: `ptr` is a live bucket-path allocation `buckets` produced.
        unsafe { buckets.free(ptr) };
        buckets.purge();
        assert_eq!(buckets.allocated(), 0);
    }

    #[test]
    fn buckets_realloc_grows_in_place_within_same_class() {
        let buckets = Buckets::new();
        let ptr = buckets.alloc(8).expect("OS map failed");
        // SAFETY: `ptr` is a live bucket-path allocation `buckets` produced.
        let grown = unsafe { buckets.realloc(ptr, 8) }.expect("same-size realloc never fails");
        assert_eq!(
            ptr, grown,
            "growing within the same elem_size stays in place"
        );
        // SAFETY: `grown` is a live bucket-path allocation.
        unsafe { buckets.free(grown) };
        buckets.purge();
    }

    #[test]
    fn buckets_realloc_moves_to_larger_class_and_copies() {
        let buckets = Buckets::new();
        let ptr = buckets.alloc(8).expect("OS map failed");
        // SAFETY: `ptr` is live and valid for at least 8 bytes (its own elem_size).
        unsafe { ptr.as_ptr().write_bytes(0xAB, 8) };
        // SAFETY: `ptr` is a live bucket-path allocation `buckets` produced.
        let grown = unsafe { buckets.realloc(ptr, 200) }.expect("OS map failed");
        assert_ne!(ptr, grown, "200 bytes needs a different size class");
        // SAFETY: `grown` is valid for at least 8 bytes (copied from `ptr` above).
        let copied = unsafe { core::slice::from_raw_parts(grown.as_ptr(), 8) };
        assert!(
            copied.iter().all(|&b| b == 0xAB),
            "realloc must preserve payload bytes"
        );
        // SAFETY: `grown` is a live bucket-path allocation.
        unsafe { buckets.free(grown) };
        buckets.purge();
    }

    #[test]
    fn buckets_purge_returns_fully_empty_pages_only() {
        let buckets = Buckets::new();
        let bi = bucket_spacing_function(16);
        let a = buckets.alloc_direct(bi).expect("OS map failed");
        let b = buckets.alloc_direct(bi).expect("OS map failed");
        let before = buckets.allocated();
        assert!(before > 0);
        // SAFETY: `a` is a live allocation from bucket `bi`.
        unsafe { buckets.free_direct(a, bi) };
        buckets.purge();
        // `b` is still live in the same page, so purge must not have reclaimed it.
        assert_eq!(
            buckets.allocated(),
            before,
            "page with a live slot must survive purge"
        );
        // SAFETY: `b` is a live allocation from bucket `bi`.
        unsafe { buckets.free_direct(b, bi) };
        buckets.purge();
        assert_eq!(buckets.allocated(), 0, "fully-empty page must be reclaimed");
    }

    /// F1 regression (docs/audits/2026-08-29-pre-v0.2.0-audit.md): `purge` must walk
    /// the *whole* page list, stopping only at a full page — an empty page sitting
    /// behind a partially-used one is still reclaimable, and HPHA reclaims it.
    ///
    /// Builds exactly that list state: fill page A (which auto-sorts it to the back
    /// and spawns page B at the front), take one slot from B, then free one slot of
    /// A — A was full, so it returns to the front, giving `[A partial, B partial]`.
    /// Freeing B's only slot leaves `[A partial, B empty]` with no re-sort, since B
    /// was never full. v0.1.0 broke out of the loop on A and leaked B's whole page.
    #[test]
    fn buckets_purge_reclaims_an_empty_page_behind_a_partial_one() {
        let buckets = Buckets::new();
        let elem_size = MAX_SMALL_ALLOCATION; // largest class => fewest slots to fill
        let bi = bucket_spacing_function(elem_size);
        let slots = (os::PAGE_SIZE - size_of::<Page>()) / elem_size;

        // Page A, filled completely: on its last slot it auto-sorts to the back.
        let mut page_a: Vec<_> = Vec::with_capacity(slots);
        for _ in 0..slots {
            page_a.push(buckets.alloc_direct(bi).expect("OS map failed"));
        }
        // One more request finds A full, so it grows page B at the front.
        let b_slot = buckets.alloc_direct(bi).expect("OS map failed");
        assert_eq!(
            buckets.allocated(),
            2 * os::PAGE_SIZE,
            "expected exactly two pages"
        );

        // A was full, so freeing one slot re-sorts it to the front, ahead of B.
        let a_slot = page_a.pop().expect("page A has slots");
        // SAFETY: `a_slot` is a live allocation from bucket `bi`.
        unsafe { buckets.free_direct(a_slot, bi) };
        // B was never full, so this triggers no re-sort: B stays behind A.
        // SAFETY: `b_slot` is a live allocation from bucket `bi`.
        unsafe { buckets.free_direct(b_slot, bi) };

        buckets.purge();
        assert_eq!(
            buckets.allocated(),
            os::PAGE_SIZE,
            "the empty page behind a partially-used one must still be reclaimed"
        );

        for slot in page_a {
            // SAFETY: each is a still-live allocation from bucket `bi`.
            unsafe { buckets.free_direct(slot, bi) };
        }
        buckets.purge();
        assert_eq!(buckets.allocated(), 0);
    }
}
