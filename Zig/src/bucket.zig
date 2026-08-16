// SPDX-License-Identifier: MIT OR Apache-2.0
//! The small-allocation path: fixed-size-class buckets over OS pages.
//!
//! Ports `Cpp/hpha.h`/`hpha.cpp`'s `allocator::bucket`, `allocator::page`, the
//! `bucket_*` methods, and the `bucket_spacing_function*`/`is_small_allocation`/
//! `clamp_small_allocation` size-class math, mirroring `orisnik`'s `bucket.rs`.
//! Self-contained: no dependency on `rbtree.zig`/`block.zig` (mirrors HPHA, where
//! the bucket and tree allocators share only the top-level `allocator` class, not
//! each other's internals).
//!
//! # Layout
//! Each 64 KiB OS page holds a singly-linked free list of `elem_size`-sized slots,
//! with a `Page` bookkeeping struct at the very tail (`PAGE_SIZE - @sizeOf(Page)`
//! into the mapping) — `ptrGetPage` recovers it from any payload pointer with one
//! alignment step. A `Bucket` owns the (possibly-empty, possibly-full) list of pages
//! serving one size class; `Buckets` owns all 32 size classes plus the running
//! allocated-byte counter (`allocator::mTotalAllocatedSizeBuckets`).
//!
//! # `&self` vs `*Self`
//! `orisnik`'s `Buckets`/`Bucket` methods all take `&self` and wrap the running
//! byte counter in a `Cell<usize>`, purely to satisfy Rust's aliasing rules at the
//! `GlobalAlloc`/`Allocator` trait boundary (shared access to a `static`). Zig has
//! no such rule — every method here just takes `*Buckets`/`*Bucket` directly and
//! `allocated_bytes` is a plain `usize` field, the same simplification `list.zig`/
//! `rbtree.zig` already made for their own sentinels.
//!
//! # Field/accessor naming
//! `Page.bucket_index` (the raw stored `u16`) and `Page.bucketIndex()` (the widened
//! `usize` accessor) don't collide — Rust's same-named field-plus-method pair
//! (`bucket_index`/`bucket_index()`, disambiguated there by field-access vs.
//! associated-function syntax) instead falls out of this project's own casing
//! convention (`snake_case` fields, `camelCase` functions), which happens to
//! already produce two distinct Zig identifiers here. See `block.zig`'s module doc
//! for the general shape of this issue, where the field and its accessor genuinely
//! needed the same name and one had to change.

const std = @import("std");
const align_helpers = @import("align.zig");
const list = @import("list.zig");
const os = @import("os.zig");

/// `log2` of the smallest bucket size class. Ports `MIN_ALLOCATION_LOG2`.
pub const MIN_ALLOCATION_LOG2: usize = 3;
/// The smallest bucket size class, in bytes. Ports `MIN_ALLOCATION`.
pub const MIN_ALLOCATION: usize = 1 << MIN_ALLOCATION_LOG2; // 8
/// `log2` of the largest small allocation. Ports `MAX_SMALL_ALLOCATION_LOG2`.
pub const MAX_SMALL_ALLOCATION_LOG2: usize = 8;
/// The largest allocation still served by the bucket path; anything larger goes to
/// the tree allocator. Ports `MAX_SMALL_ALLOCATION`.
pub const MAX_SMALL_ALLOCATION: usize = 1 << MAX_SMALL_ALLOCATION_LOG2; // 256
/// The number of bucket size classes, at `MIN_ALLOCATION`-byte spacing from
/// `MIN_ALLOCATION` to `MAX_SMALL_ALLOCATION`. Ports `NUM_BUCKETS`.
pub const NUM_BUCKETS: usize = MAX_SMALL_ALLOCATION / MIN_ALLOCATION; // 32

/// Whether `size` belongs on the bucket path (`false` routes to the tree
/// allocator). Ports `allocator::is_small_allocation` (with `MEMORY_GUARD_SIZE` —
/// always 0 until the v0.2.0 debug allocator — elided).
pub fn isSmallAllocation(size: usize) bool {
    return size <= MAX_SMALL_ALLOCATION;
}

/// Raises `size` up to the smallest bucket size class if it's below it. Ports
/// `allocator::clamp_small_allocation`.
pub fn clampSmallAllocation(size: usize) usize {
    return if (size < MIN_ALLOCATION) MIN_ALLOCATION else size;
}

/// The bucket index serving `size` (rounding up to the next size class). Ports
/// `allocator::bucket_spacing_function`.
///
/// Asserts (debug only) that `size` is nonzero and within `MAX_SMALL_ALLOCATION` —
/// callers are expected to have already applied `clampSmallAllocation`/
/// `isSmallAllocation`.
pub fn bucketSpacingFunction(size: usize) usize {
    std.debug.assert(size > 0 and size <= MAX_SMALL_ALLOCATION);
    return ((size + (MIN_ALLOCATION - 1)) >> MIN_ALLOCATION_LOG2) - 1;
}

/// The bucket index serving `size`, when `size` is already known to be an exact
/// multiple of `MIN_ALLOCATION` (cheaper than `bucketSpacingFunction` — no
/// rounding needed). Ports `allocator::bucket_spacing_function_aligned`.
pub fn bucketSpacingFunctionAligned(size: usize) usize {
    std.debug.assert(size > 0 and size % MIN_ALLOCATION == 0 and size <= MAX_SMALL_ALLOCATION);
    return (size >> MIN_ALLOCATION_LOG2) - 1;
}

/// The element size served by bucket `index`. Ports
/// `allocator::bucket_spacing_function_inverse`.
pub fn bucketSpacingFunctionInverse(index: usize) usize {
    std.debug.assert(index < NUM_BUCKETS);
    return (index + 1) << MIN_ALLOCATION_LOG2;
}

/// One free slot in a page's intra-page free list — a plain singly-linked list
/// (distinct from `list.zig`'s doubly-linked `ListLink`, and from `Page`'s own
/// `ListLink` membership in its `Bucket`'s page list). Ports `free_link`.
pub const FreeLink = extern struct {
    /// The next free slot, or `null` at the end of the list. Byte offset 0.
    next: ?*FreeLink,
};

/// The bookkeeping struct at the tail of every bucket-owned OS page. Ports
/// `allocator::page`.
///
/// # Invariants
/// - Lives at exactly `PAGE_SIZE - @sizeOf(Page)` bytes into a `PAGE_SIZE`-aligned
///   mapping — `ptrGetPage` depends on this.
/// - `free_list` is `null` exactly when every slot in the page is allocated
///   (`isFull`).
/// - `marker` lets `Buckets.ptrInBucket` distinguish a bucket pointer from a tree
///   pointer without a discriminant bit — see `Bucket.marker`.
pub const Page = extern struct {
    /// This page's membership in its `Bucket`'s page list. Byte offset 0, 8-byte
    /// aligned there (required by `IntrusiveList`; every `Page` position is itself
    /// 8-aligned, see `ptrGetPage`'s `// ALIGN:` reasoning).
    link: list.ListLink = list.ListLink.UNLINKED,
    /// Head of this page's intra-page free-slot list, or `null` if full. Byte
    /// offset 16 (64-bit), 8-byte aligned (immediately follows `link`, itself a
    /// multiple of 8 bytes).
    free_list: ?*FreeLink,
    /// This page's bucket index — `bucketSpacingFunctionAligned(elemSize)`. Byte
    /// offset 24 (64-bit), 2-byte aligned (`u16`'s own alignment).
    bucket_index: u16,
    /// Number of currently-allocated slots in this page. Byte offset 26 (64-bit),
    /// 2-byte aligned.
    use_count: u16,
    /// `owningBucket.marker() ^ (this page's own truncated address)`. See
    /// `Bucket.marker`. Byte offset 28 (64-bit), 4-byte aligned (`u32`'s own
    /// alignment; `bucket_index` + `use_count` together total 4 bytes, keeping
    /// this field's offset a multiple of 4 with no padding needed).
    marker: u32,

    /// The element size this page's slots serve.
    pub fn elemSize(this: *Page) usize {
        return bucketSpacingFunctionInverse(this.bucket_index);
    }

    /// This page's bucket index, widened from the raw stored `u16`.
    pub fn bucketIndex(this: *Page) usize {
        return this.bucket_index;
    }

    /// Whether this page currently has zero allocated slots — a candidate for
    /// `Buckets.purge`.
    pub fn isEmpty(this: *Page) bool {
        return this.use_count == 0;
    }

    /// Whether every slot in this page is currently allocated (`free_list` is
    /// exhausted).
    pub fn isFull(this: *Page) bool {
        return this.free_list == null;
    }

    /// `this` must be live, with `use_count` not already at its `u16` maximum
    /// (guaranteed by `initPageAt`'s own `slot_count <= maxInt(u16)` assertion:
    /// `use_count` never exceeds the page's total slot count).
    fn incUseCount(this: *Page) void {
        this.use_count += 1;
    }

    /// `this` must be live, with `use_count > 0`.
    fn decUseCount(this: *Page) void {
        std.debug.assert(this.use_count > 0);
        this.use_count -= 1;
    }

    /// Whether `marker` (a candidate owning bucket's marker) is consistent with
    /// this page's own stored, address-mixed marker. Ports `page::check_marker`.
    pub fn checkMarker(this: *Page, marker: u32) bool {
        const stored = this.marker;
        // PROVENANCE: address read for its bit pattern only, never turned back
        // into a pointer — no provenance is created or consumed here.
        // CAST: usize -> u32, truncating `this`'s own address — mirrors how the
        // marker was seeded in `initPageAt` below; only the low bits need to match.
        const addr: u32 = @truncate(@intFromPtr(this));
        return stored == (marker ^ addr);
    }
};

comptime {
    // link (2 words) + free_list (1 word) + {bucket_index, use_count, marker}
    // packed into 1 word (2 + 2 + 4 = 8 bytes) = 4 words on 64-bit.
    std.debug.assert(@sizeOf(Page) == 4 * @sizeOf(usize));
}

/// Recovers the `Page` bookkeeping struct owning a bucket-path payload pointer.
/// Ports `allocator::ptr_get_page`.
///
/// `ptr` must point into a page that a call to `initPageAt` (directly, or via
/// `Buckets.grow`, which maps the page via `systemAlloc` and then calls
/// `initPageAt` on it) previously initialized.
pub fn ptrGetPage(ptr: [*]u8) *Page {
    // ALIGN: round down to the PAGE_SIZE-aligned mapping base (`os.map`'s
    // guarantee, relied on transitively via this function's own contract), then
    // step forward to the Page struct's fixed tail position.
    const page_base = align_helpers.alignDown(ptr, os.PAGE_SIZE);
    const page = page_base + (os.PAGE_SIZE - @sizeOf(Page));
    // ALIGN: `page_base` is PAGE_SIZE-aligned (hence 8-aligned) and
    // `PAGE_SIZE - @sizeOf(Page)` is a multiple of 8 (PAGE_SIZE is, @sizeOf(Page)
    // is), so `page` is 8-aligned — matches `@alignOf(Page)`.
    return @ptrCast(@alignCast(page));
}

/// Acquires one `PAGE_SIZE` buffer (already obtained — from `os.map` in
/// production, or a test's own heap-backed stand-in) and threads it into
/// `elem_size`-sized free slots with a `Page` at the tail. Ports the
/// free-list-building loop and the placement-new in `allocator::bucket_grow`.
///
/// `mem` must be valid for exactly `PAGE_SIZE` bytes, `PAGE_SIZE`-aligned, and not
/// concurrently accessed. `elem_size` must be a bucket size class
/// (`bucketSpacingFunctionInverse` of some index `< NUM_BUCKETS`).
fn initPageAt(mem: [*]u8, elem_size: usize, marker: u32) *Page {
    std.debug.assert(@intFromPtr(mem) % os.PAGE_SIZE == 0);
    std.debug.assert(elem_size > 0);
    // The largest multiple of elem_size that leaves room for a trailing Page.
    const usable = os.PAGE_SIZE - @sizeOf(Page);
    const slot_count = usable / elem_size;
    std.debug.assert(slot_count <= std.math.maxInt(u16)); // "use_count would overflow u16"
    const n = slot_count * elem_size;
    var i: usize = 0;
    // EXPLICIT: threads the free-list `next` pointer through consecutive slots;
    // `i` is the state (byte offset of the slot being linked), not expressible as
    // an iterator over raw, uninitialized-until-written memory.
    while (i < n - elem_size) {
        const slot = mem + i;
        // ALIGN: `mem` is PAGE_SIZE-aligned (this function's contract, >= 8); `i`
        // is a multiple of `elem_size`, itself always a multiple of
        // `MIN_ALLOCATION` (8) — `bucketSpacingFunctionInverse` only ever returns
        // `(index + 1) << MIN_ALLOCATION_LOG2`. So `slot` is 8-aligned.
        const slot_link: *FreeLink = @ptrCast(@alignCast(slot));
        const next_slot = mem + (i + elem_size);
        // ALIGN: same reasoning as `slot` above (`i + elem_size` is likewise a
        // multiple of 8).
        const next_link: *FreeLink = @ptrCast(@alignCast(next_slot));
        slot_link.next = next_link;
        i += elem_size;
    }
    const last_slot = mem + i;
    // ALIGN: same reasoning as `slot` above (`i` is a multiple of 8).
    const last_link: *FreeLink = @ptrCast(@alignCast(last_slot));
    last_link.next = null;
    std.debug.assert(i + elem_size + @sizeOf(Page) <= os.PAGE_SIZE);

    // ALIGN: `mem` is PAGE_SIZE-aligned and valid for PAGE_SIZE bytes (this
    // function's contract), so `ptrGetPage` finds the correct, in-bounds tail slot.
    const page = ptrGetPage(mem);
    // PROVENANCE: address read for its bit pattern only, never turned back into a
    // pointer — no provenance is created or consumed here.
    // CAST: usize -> u32, truncating the page's own address to mix into its
    // stored marker (see `Page.checkMarker`); only the low bits need to
    // round-trip.
    const page_addr: u32 = @truncate(@intFromPtr(page));
    // CAST: usize -> u16, checked — `bucketSpacingFunctionAligned` always returns
    // a value < NUM_BUCKETS (32), which fits comfortably in u16.
    const bucket_index: u16 = @intCast(bucketSpacingFunctionAligned(elem_size));
    // ALIGN: `mem` is PAGE_SIZE-aligned (this function's contract), hence 8-aligned.
    const free_list: *FreeLink = @ptrCast(@alignCast(mem));
    page.* = .{
        .link = list.ListLink.UNLINKED,
        .free_list = free_list,
        .bucket_index = bucket_index,
        .use_count = 0,
        .marker = marker ^ page_addr,
    };
    return page;
}

/// XOR-mixed into every page's stored marker; ports `allocator::bucket::MARKER`.
const MARKER_CONST: u32 = 0x628b_f2b6;

/// One size class's page list. Ports `allocator::bucket`.
pub const Bucket = struct {
    /// This size class's pages, auto-sorted so pages with free slots stay near the
    /// front (`alloc`/`free` re-sort on the full/empty transition).
    pages: list.IntrusiveList(Page) = .init(),

    /// Builds an empty bucket. Ports `bucket::bucket` (HPHA's default constructor).
    pub fn init() Bucket {
        return .{};
    }

    /// A per-instance, deterministic page-ownership marker. HPHA seeds this from
    /// `rand()` at construction; this port derives it from the bucket's own
    /// address instead (deterministic, no RNG dependency — matches `orisnik`'s own
    /// substitution and its determinism reasoning). The value only feeds
    /// `Page.checkMarker`'s sanity check (never state-transition logic), so this
    /// substitution doesn't touch the cross-port invariant. Ports `bucket::marker`.
    pub fn marker(self: *Bucket) u32 {
        // PROVENANCE: address read for its bit pattern only, never turned back
        // into a pointer — no provenance is created or consumed here.
        // CAST: usize -> u32, truncating this bucket's own address (matches
        // HPHA's `(unsigned)((size_t)this)`).
        const addr: u32 = @truncate(@intFromPtr(self));
        return addr ^ MARKER_CONST;
    }

    /// The first page with a free slot, if any page in this bucket has one. Ports
    /// `bucket::get_free_page`.
    fn getFreePage(self: *Bucket) ?*Page {
        const front = self.pages.front() orelse return null;
        if (front.isFull()) return null;
        return front;
    }

    /// Adds a freshly-grown page (with a full free list) to this bucket. Ports the
    /// `mBuckets[bi].add_free_page(p)` call in `allocator::bucket_alloc(_direct)`.
    fn addFreePage(self: *Bucket, page: *Page) void {
        self.pages.pushFront(page);
    }

    /// Allocates one slot from `page`, which must have a free slot. Ports
    /// `bucket::alloc`.
    ///
    /// `page` must be live, currently a member of this bucket's page list, and
    /// not full.
    fn alloc(self: *Bucket, page: *Page) [*]u8 {
        page.incUseCount();
        // Named `free_head`, not `free` (which `orisnik`'s `bucket.rs` counterpart
        // uses) — this struct has its own `free` method in scope, and Zig errors
        // on identifier shadowing.
        const free_head = page.free_list;
        std.debug.assert(free_head != null); // "caller guaranteed page was not full"
        const next = free_head.?.next;
        page.free_list = next;
        if (next == null) {
            // The page just became full: move it to the back so mostly-empty
            // pages stay near the front of the list, matching HPHA's own
            // auto-sort.
            list.unlinkNode(page);
            self.pages.pushBack(page);
        }
        return @ptrCast(free_head.?);
    }

    /// Returns `ptr` (a slot of `page`) to `page`'s free list. Ports `bucket::free`.
    ///
    /// `page` must be live and currently a member of this bucket's page list.
    /// `ptr` must be a slot this bucket previously handed out from `page` via
    /// `alloc`, not currently free.
    fn free(self: *Bucket, page: *Page, ptr: [*]u8) void {
        const free_head = page.free_list;
        const link: *FreeLink = @ptrCast(@alignCast(ptr));
        link.next = free_head;
        page.free_list = link;
        page.decUseCount();
        if (free_head == null) {
            // The page was previously full: move it to the front, matching
            // HPHA's own auto-sort (freshly-freed pages are the best candidates
            // to reuse).
            list.unlinkNode(page);
            self.pages.pushFront(page);
        }
    }
};

/// All 32 bucket size classes, plus the bucket path's running allocated-byte total.
/// Ports the bucket-related slice of `allocator` (`mBuckets`,
/// `mTotalAllocatedSizeBuckets`, and the free `bucket_*` methods).
pub const Buckets = struct {
    /// One `Bucket` per size class, indexed by `bucketSpacingFunction` and its
    /// variants. `Bucket.init()` is a pure value (no address-dependent state at
    /// construction — see `list.zig`'s lazy-sentinel-init doc), so this repeat
    /// expression is comptime-evaluable, keeping `Buckets.init()` itself
    /// `comptime`-constructible per `Zig/CONVENTIONS.md`'s `comptime`-over-runtime
    /// guidance.
    buckets: [NUM_BUCKETS]Bucket = [1]Bucket{.init()} ** NUM_BUCKETS,
    /// Total bytes currently mapped for the bucket path (whole `PAGE_SIZE` pages).
    /// A plain field, not `orisnik`'s `Cell<usize>` — see the module doc's "`&self`
    /// vs `*Self`" section.
    allocated_bytes: usize = 0,

    /// Builds a fresh set of empty buckets, none of them yet holding any pages.
    pub fn init() Buckets {
        return .{};
    }

    /// Total bytes currently claimed from the OS by the bucket path (whole pages,
    /// not payload bytes). Ports the bucket half of `allocator::allocated`.
    pub fn allocated(self: *Buckets) usize {
        return self.allocated_bytes;
    }

    /// Maps one fresh `PAGE_SIZE` OS page. Ports `allocator::bucket_system_alloc`.
    fn systemAlloc(self: *Buckets) ?[*]u8 {
        const ptr = os.map(os.PAGE_SIZE) orelse return null;
        self.allocated_bytes += os.PAGE_SIZE;
        return ptr;
    }

    /// Returns one `PAGE_SIZE` OS page. Ports `allocator::bucket_system_free`.
    ///
    /// `ptr` must be a still-live result of `systemAlloc` on `self`.
    fn systemFree(self: *Buckets, ptr: [*]u8) void {
        os.unmap(ptr, os.PAGE_SIZE);
        self.allocated_bytes -= os.PAGE_SIZE;
    }

    /// Maps a fresh page and threads it for `elem_size`-sized slots, owned by
    /// bucket `bi`. Ports `allocator::bucket_grow`.
    fn grow(self: *Buckets, bi: usize) ?*Page {
        std.debug.assert(bi < NUM_BUCKETS);
        const elem_size = bucketSpacingFunctionInverse(bi);
        const mem = self.systemAlloc() orelse return null;
        const mrk = self.buckets[bi].marker();
        // `mem` is exactly PAGE_SIZE bytes, PAGE_SIZE-aligned (`os.map`'s
        // guarantee), and freshly mapped (exclusively ours, nothing else accesses
        // it concurrently — this port is single-threaded in v0.1.0); `elem_size`
        // is a real bucket size class (`bi < NUM_BUCKETS`, checked above).
        return initPageAt(mem, elem_size, mrk);
    }

    /// Allocates `size` bytes on the bucket path, computing the bucket index from
    /// `size` directly (used when a prior guard-byte/alignment adjustment already
    /// produced the final target size — see `realloc`'s HPHA counterpart). Ports
    /// `allocator::bucket_alloc`.
    pub fn alloc(self: *Buckets, size: usize) ?[*]u8 {
        std.debug.assert(size <= MAX_SMALL_ALLOCATION);
        const bi = bucketSpacingFunction(size);
        return self.allocDirect(bi);
    }

    /// Allocates from a pre-computed bucket index. Ports
    /// `allocator::bucket_alloc_direct`.
    pub fn allocDirect(self: *Buckets, bi: usize) ?[*]u8 {
        std.debug.assert(bi < NUM_BUCKETS);
        const bucket = &self.buckets[bi];
        const page = bucket.getFreePage() orelse blk: {
            const p = self.grow(bi) orelse return null;
            bucket.addFreePage(p);
            break :blk p;
        };
        // `page` is live and was just confirmed to have a free slot
        // (`getFreePage`'s own check) or was freshly grown (always has free
        // slots); it is a member of `bucket`'s page list either way.
        return bucket.alloc(page);
    }

    /// Grows or shrinks a bucket-path allocation in place if the current slot's
    /// element size can already accommodate `size`; otherwise allocates a new,
    /// larger slot, copies, and frees the old one. Ports
    /// `allocator::bucket_realloc`.
    ///
    /// `ptr` must be a still-live bucket-path allocation this instance produced.
    pub fn realloc(self: *Buckets, ptr: [*]u8, size: usize) ?[*]u8 {
        const page = ptrGetPage(ptr);
        const elem_size = page.elemSize();
        if (size <= elem_size) return ptr;
        const new_ptr = self.alloc(size) orelse return null;
        // `ptr` is valid for `elem_size` bytes (its slot's own size, an upper
        // bound on the live payload within it); `new_ptr` was just allocated with
        // room for at least `size > elem_size` bytes — copying `elem_size` bytes
        // fits in both.
        @memcpy(new_ptr[0..elem_size], ptr[0..elem_size]);
        // `ptr` is a live bucket-path allocation this instance produced (this
        // function's contract), not used again after this call.
        self.free(ptr);
        return new_ptr;
    }

    /// Frees a bucket-path allocation, recovering its bucket index from its page.
    /// Ports `allocator::bucket_free`.
    ///
    /// `ptr` must be a still-live bucket-path allocation this instance produced.
    pub fn free(self: *Buckets, ptr: [*]u8) void {
        const page = ptrGetPage(ptr);
        const bi = page.bucketIndex();
        std.debug.assert(bi < NUM_BUCKETS);
        const bucket = &self.buckets[bi];
        bucket.free(page, ptr);
    }

    /// Frees a bucket-path allocation given its original bucket index directly
    /// (skipping the page-marker recovery `free` needs) — used when the caller
    /// already knows the exact original size/alignment. Ports
    /// `allocator::bucket_free_direct`.
    ///
    /// `ptr` must be a still-live allocation this instance produced from bucket `bi`.
    pub fn freeDirect(self: *Buckets, ptr: [*]u8, bi: usize) void {
        std.debug.assert(bi < NUM_BUCKETS);
        const page = ptrGetPage(ptr);
        // `page` is live; caller guarantees `bi` matches `ptr`'s actual bucket
        // (mirrors HPHA's own `assert(bi == p->bucket_index())`).
        std.debug.assert(page.bucketIndex() == bi);
        const bucket = &self.buckets[bi];
        bucket.free(page, ptr);
    }

    /// Whether `ptr` is a live bucket-path allocation from this instance — the
    /// page-marker sanity check the pointer-only `free`/`realloc`/`size`
    /// overloads rely on to dispatch between the bucket and tree paths. Ports
    /// `allocator::ptr_in_bucket`.
    ///
    /// The marker check alone has a documented, HPHA-inherited false-positive
    /// risk: for a non-bucket pointer, the position `ptrGetPage` computes is not
    /// really a `Page`, so `bucket_index`/`marker` are just whatever bytes happen
    /// to sit there — bytes that can, on rare occasion, coincidentally read as a
    /// small valid-looking index whose recomputed marker matches (not
    /// hypothetical: it is exactly how a same-page tree allocation can
    /// occasionally alias a bucket page's marker layout, since both live inside
    /// `PAGE_SIZE`-sized, `PAGE_SIZE`-aligned OS mappings). HPHA's own
    /// `ptr_in_bucket` acknowledges this in a comment and compensates with a
    /// debug-only exhaustive scan of the candidate bucket's real page list,
    /// asserting the fast path agrees; ported below as a `std.debug.assert` (an
    /// always-on check would violate this port's hot-path-never-panics rule for a
    /// check the *release* build — like HPHA's own release build — intentionally
    /// still skips, relying on the marker check alone once it has been
    /// debug-verified in test/CI builds).
    ///
    /// `ptr` must be a pointer this instance is being asked to classify (i.e.
    /// either a genuine live allocation from this instance, bucket or tree path,
    /// or a caller bug being defended against — this function must not be called
    /// with an arbitrary, unrelated pointer, since `ptrGetPage` unconditionally
    /// reads memory at a computed offset from it).
    pub fn ptrInBucket(self: *Buckets, ptr: [*]u8) bool {
        const page = ptrGetPage(ptr);
        // `page` is live per this function's contract (every allocation this
        // instance could have produced has a live Page at this computed
        // position, whether or not `ptr` truly is a bucket allocation).
        const bi = page.bucketIndex();
        if (bi >= NUM_BUCKETS) return false;
        const bucket = &self.buckets[bi];
        const mrk = bucket.marker();
        const result = page.checkMarker(mrk);
        std.debug.assert(result == bucket.pages.contains(&page.link)); // "ptrInBucket's marker check disagreed with an exhaustive page-list scan — see this function's own doc for the known, HPHA-inherited cause"
        return result;
    }

    /// Returns every page with zero live allocations back to the OS. Ports
    /// `allocator::bucket_purge`.
    pub fn purge(self: *Buckets) void {
        for (&self.buckets) |*bucket| {
            // EXPLICIT: page-list walk with early termination and in-loop
            // removal; `front` is the state (the list's current head), not
            // expressible as an iterator over a structure this port
            // deliberately doesn't build one for.
            while (bucket.pages.front()) |front| {
                if (front.isFull()) {
                    // HPHA early-outs on the first full-or-partial page it meets
                    // scanning from the front — pages are auto-sorted so a full
                    // page here means every page after it is at least as full.
                    break;
                }
                if (!front.isEmpty()) break;
                list.unlinkNode(front);
                // ALIGN: `front` is a live `Page`, always
                // `PAGE_SIZE - @sizeOf(Page)` bytes into its owning
                // PAGE_SIZE-aligned mapping (the type's own invariant); rounding
                // its address down recovers that mapping's base.
                const front_bytes: [*]u8 = @ptrCast(front);
                const mem = align_helpers.alignDown(front_bytes, os.PAGE_SIZE);
                // `mem` is the live mapping `front` belongs to (established
                // above), not referenced again after this call (the page was
                // just unlinked from every structure this module tracks it
                // through).
                self.systemFree(mem);
            }
        }
    }
};

const testing = std.testing;

// A `PAGE_SIZE`-sized, `PAGE_SIZE`-aligned heap buffer standing in for a real OS
// page — lets `initPageAt` (the actual bucket logic) run under `std.testing.allocator`
// leak detection without touching real `os.map`/`VirtualAlloc`/`mmap`.
const FakePage = struct {
    buf: []align(os.PAGE_SIZE) u8,

    fn init(allocator: std.mem.Allocator) !FakePage {
        const buf = try allocator.alignedAlloc(u8, comptime std.mem.Alignment.fromByteUnits(os.PAGE_SIZE), os.PAGE_SIZE);
        @memset(buf, 0);
        return .{ .buf = buf };
    }

    fn deinit(self: *FakePage, allocator: std.mem.Allocator) void {
        allocator.free(self.buf);
    }

    fn ptr(self: *FakePage) [*]u8 {
        return self.buf.ptr;
    }
};

test "bucket spacing round-trips every class" {
    for (0..NUM_BUCKETS) |bi| {
        const size = bucketSpacingFunctionInverse(bi);
        try testing.expectEqual(bi, bucketSpacingFunctionAligned(size));
        try testing.expectEqual(bi, bucketSpacingFunction(size));
        // One byte over a class boundary rounds up into the next class (except
        // at the top, where it would exceed MAX_SMALL_ALLOCATION).
        if (bi + 1 < NUM_BUCKETS) {
            try testing.expectEqual(bi + 1, bucketSpacingFunction(size + 1));
        }
    }
    try testing.expectEqual(MIN_ALLOCATION, bucketSpacingFunctionInverse(0));
    try testing.expectEqual(MAX_SMALL_ALLOCATION, bucketSpacingFunctionInverse(NUM_BUCKETS - 1));
}

test "clamp and is-small-allocation" {
    try testing.expectEqual(MIN_ALLOCATION, clampSmallAllocation(1));
    try testing.expectEqual(MIN_ALLOCATION, clampSmallAllocation(MIN_ALLOCATION));
    try testing.expectEqual(MIN_ALLOCATION + 1, clampSmallAllocation(MIN_ALLOCATION + 1));
    try testing.expect(isSmallAllocation(MAX_SMALL_ALLOCATION));
    try testing.expect(!isSmallAllocation(MAX_SMALL_ALLOCATION + 1));
}

test "initPageAt threads the free list and computes slot count" {
    const allocator = testing.allocator;
    var fp = try FakePage.init(allocator);
    defer fp.deinit(allocator);
    const elem_size = 32;
    const page = initPageAt(fp.ptr(), elem_size, 0xDEAD_BEEF);
    try testing.expectEqual(elem_size, page.elemSize());
    try testing.expect(page.isEmpty());
    try testing.expect(!page.isFull());

    // Walk the free list to the end, counting slots, and confirm the marker
    // round-trips against the seed used above.
    var cur = page.free_list;
    var count: usize = 0;
    while (cur) |c| : (cur = c.next) {
        count += 1;
    }
    const expected = (os.PAGE_SIZE - @sizeOf(Page)) / elem_size;
    try testing.expectEqual(expected, count);
    try testing.expect(page.checkMarker(0xDEAD_BEEF));
    try testing.expect(!page.checkMarker(0xCAFE_BABE));
}

test "bucket alloc/free cycle updates free list and use count" {
    const allocator = testing.allocator;
    var fp = try FakePage.init(allocator);
    defer fp.deinit(allocator);
    const elem_size = 16;
    const page = initPageAt(fp.ptr(), elem_size, 0);
    var bucket: Bucket = .init();
    bucket.addFreePage(page);

    const a = bucket.alloc(page);
    try testing.expectEqual(@as(u16, 1), page.use_count);
    const b = bucket.alloc(page);
    try testing.expect(a != b);
    try testing.expectEqual(@as(u16, 2), page.use_count);

    bucket.free(page, a);
    try testing.expectEqual(@as(u16, 1), page.use_count);

    bucket.free(page, b);
    try testing.expect(page.isEmpty());
}

test "bucket alloc sorts full page behind partial page" {
    const allocator = testing.allocator;
    var fp_small = try FakePage.init(allocator); // small elem_size -> many slots
    defer fp_small.deinit(allocator);
    var fp = try FakePage.init(allocator);
    defer fp.deinit(allocator);
    const elem_size = MAX_SMALL_ALLOCATION; // largest class -> fewest slots
    const big_elem_size = MIN_ALLOCATION;
    const full_page = initPageAt(fp.ptr(), elem_size, 0);
    const roomy_page = initPageAt(fp_small.ptr(), big_elem_size, 0);
    var bucket: Bucket = .init();
    bucket.addFreePage(full_page);
    bucket.addFreePage(roomy_page);
    try testing.expectEqual(roomy_page, bucket.getFreePage().?);

    // Exhaust every slot in `full_page` (few slots, since elem_size is large).
    const slots = (os.PAGE_SIZE - @sizeOf(Page)) / elem_size;
    for (0..slots) |_| {
        _ = bucket.alloc(full_page);
    }
    // `full_page` auto-sorted to the back; `roomy_page` is still servable.
    try testing.expectEqual(roomy_page, bucket.getFreePage().?);
}

// The five `Buckets`-level tests below (as opposed to the `Bucket`/`initPageAt`
// tests above, which use `FakePage`) call `Buckets.init()` and allocate through
// it, which reaches real `os.map` — exercised by native `zig build test` on all
// three CI OSes (zig-ci.yml), just like `os.zig`'s own tests.

test "Buckets.allocDirect grows and serves from the same page" {
    var buckets: Buckets = .init();
    const bi = bucketSpacingFunction(24); // -> the 24-byte class
    const a = buckets.allocDirect(bi) orelse return error.TestUnexpectedResult; // "OS map failed"
    const b = buckets.allocDirect(bi) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(a != b);
    buckets.freeDirect(a, bi);
    buckets.freeDirect(b, bi);
    buckets.purge();
    try testing.expectEqual(@as(usize, 0), buckets.allocated());
}

test "Buckets.free recovers the bucket index from the page" {
    var buckets: Buckets = .init();
    const ptr = buckets.alloc(40) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(buckets.ptrInBucket(ptr));
    buckets.free(ptr);
    buckets.purge();
    try testing.expectEqual(@as(usize, 0), buckets.allocated());
}

test "Buckets.realloc grows in place within the same class" {
    var buckets: Buckets = .init();
    const ptr = buckets.alloc(8) orelse return error.TestUnexpectedResult; // "OS map failed"
    const grown = buckets.realloc(ptr, 8) orelse return error.TestUnexpectedResult; // "same-size realloc never fails"
    try testing.expectEqual(ptr, grown); // growing within the same elem_size stays in place
    buckets.free(grown);
    buckets.purge();
}

test "Buckets.realloc moves to a larger class and copies" {
    var buckets: Buckets = .init();
    const ptr = buckets.alloc(8) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..8], 0xAB);
    const grown = buckets.realloc(ptr, 200) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(ptr != grown); // 200 bytes needs a different size class
    try testing.expect(std.mem.allEqual(u8, grown[0..8], 0xAB)); // realloc must preserve payload bytes
    buckets.free(grown);
    buckets.purge();
}

test "Buckets.purge returns fully empty pages only" {
    var buckets: Buckets = .init();
    const bi = bucketSpacingFunction(16);
    const a = buckets.allocDirect(bi) orelse return error.TestUnexpectedResult; // "OS map failed"
    const b = buckets.allocDirect(bi) orelse return error.TestUnexpectedResult; // "OS map failed"
    const before = buckets.allocated();
    try testing.expect(before > 0);
    buckets.freeDirect(a, bi);
    buckets.purge();
    // `b` is still live in the same page, so purge must not have reclaimed it.
    try testing.expectEqual(before, buckets.allocated()); // "page with a live slot must survive purge"
    buckets.freeDirect(b, bi);
    buckets.purge();
    try testing.expectEqual(@as(usize, 0), buckets.allocated()); // "fully-empty page must be reclaimed"
}
