// SPDX-License-Identifier: MIT OR Apache-2.0
//! The top-level allocator: dispatches every request between the bucket path
//! (small allocations) and the tree path (everything else), and owns nothing else.
//!
//! Ports the non-debug, single-threaded slice of `allocator`'s public surface,
//! mirroring `orisnik`'s `orisnik.rs` — `DEBUG_ALLOCATOR` (guard bytes, allocation
//! records, `check()`/`report()`) and `MULTITHREADED` (mutex-guarded buckets/tree)
//! are both out of scope for v0.1.0, see `ROADMAP.md`. With `MEMORY_GUARD_SIZE`
//! fixed at 0 (the non-debug value), every `+ MEMORY_GUARD_SIZE` /
//! `- MEMORY_GUARD_SIZE` in HPHA's own arithmetic cancels out and is simply omitted
//! here; every `debug_*` call in HPHA's non-debug build is a no-op and is likewise
//! omitted rather than ported as a stub.
//!
//! `oris_*` (`capi.zig`) and the `std.mem.Allocator` vtable (`allocator.zig`) are
//! thin shells over the methods on this type — see `Zig/CONVENTIONS.md`'s
//! `std.mem.Allocator` vtable section.
//!
//! # `&self` vs `*Self`, and no `Sync` marker
//! Same simplification as `bucket.zig`/`tree.zig`: `orisnik`'s `Orisnik` methods
//! all take `&self` (relying on `Cell`-based interior mutability throughout
//! `Buckets`/`Tree`) purely to satisfy Rust's aliasing rules, and carries an
//! `unsafe impl Sync` so an instance can occupy a `#[global_allocator]` `static`
//! slot (every Rust `static` requires `Sync`, checked by the type system). Zig has
//! neither constraint: every method here takes `*Orisnitsa` directly, and a
//! `var ALLOCATOR: Orisnitsa = .init();` needs no trait marker to be shared as
//! global state — the single-threaded-only caveat is a plain doc note here (this
//! whole port's v0.1.0 scope, matching `orisnik`'s own `ROADMAP.md`-deferred
//! `MULTITHREADED` support), not something either language's type system enforces.

const std = @import("std");
const align_helpers = @import("align.zig");
const block = @import("block.zig");
const bucket = @import("bucket.zig");
const tree_mod = @import("tree.zig");

/// The top-level allocator instance: dispatches every request between the bucket
/// path (`Buckets`, sizes at most `bucket.MAX_SMALL_ALLOCATION`) and the tree path
/// (`Tree`, everything larger), deciding which one owns any given pointer the same
/// way HPHA does — `Buckets.ptrInBucket`'s page-marker check, re-derived on every
/// call rather than cached anywhere. Ports `allocator`.
///
/// # Invariants
/// - Every live pointer this instance has handed out belongs to exactly one of
///   `buckets`/`tree`, decided once at allocation time by
///   `bucket.isSmallAllocation` and re-derived on every later call via
///   `Buckets.ptrInBucket` — never by a separate stored discriminant.
/// - `buckets` and `tree` are otherwise fully independent: neither reads nor
///   mutates the other's state, matching HPHA's own `allocator` (whose
///   `bucket_*`/`tree_*` methods never call each other except through this
///   dispatch layer).
///
/// **Single-threaded only** — see the module doc's "`&self` vs `*Self`" section.
pub const Orisnitsa = struct {
    /// The small-allocation path — every request `<= MAX_SMALL_ALLOCATION` (after
    /// `bucket.clampSmallAllocation`) lands here.
    buckets: bucket.Buckets = .init(),
    /// The large-allocation path — every request the bucket path doesn't serve.
    tree: tree_mod.Tree = .init(),

    /// Builds a fresh, empty allocator instance — no OS memory is claimed until
    /// the first allocation. Ports `allocator::allocator` (the default
    /// constructor). A pure value (no address-dependent state at construction —
    /// see `list.zig`'s lazy-sentinel-init doc), so `var ALLOCATOR: Orisnitsa =
    /// .init();` is `comptime`-constructible, the standard global-allocator
    /// pattern's own requirement.
    pub fn init() Orisnitsa {
        return .{};
    }

    /// Allocates `size` bytes at `block.DEFAULT_ALIGNMENT`. `size == 0` returns
    /// `null`. Ports `allocator::alloc(size_t)`.
    pub fn alloc(self: *Orisnitsa, size: usize) ?[*]u8 {
        if (!bucket.isSmallAllocation(size)) {
            return self.tree.alloc(size);
        }
        if (size == 0) return null;
        const sz = bucket.clampSmallAllocation(size);
        return self.buckets.allocDirect(bucket.bucketSpacingFunction(sz));
    }

    /// Allocates `size` bytes aligned to `alignment`. `size == 0` returns `null`;
    /// `alignment <= block.DEFAULT_ALIGNMENT` behaves exactly like `alloc`. Ports
    /// `allocator::alloc(size_t, size_t)`.
    ///
    /// `alignment` must be a power of two — checked with `std.debug.assert`
    /// rather than HPHA's always-on `assert`, matching this port's
    /// hot-path-never-panics rule (`Zig/CONVENTIONS.md`'s Allocation Outcomes
    /// section).
    pub fn allocAligned(self: *Orisnitsa, size: usize, alignment: usize) ?[*]u8 {
        std.debug.assert(std.math.isPowerOfTwo(alignment));
        if (alignment <= block.DEFAULT_ALIGNMENT) {
            return self.alloc(size);
        }
        if (!bucket.isSmallAllocation(size) or alignment > bucket.MAX_SMALL_ALLOCATION) {
            return self.tree.allocAligned(size, alignment);
        }
        if (size == 0) return null;
        const sz = bucket.clampSmallAllocation(size);
        return self.buckets.allocDirect(bucket.bucketSpacingFunction(align_helpers.roundUp(sz, alignment)));
    }

    /// Allocates `count * size` bytes at `block.DEFAULT_ALIGNMENT` and zeroes
    /// them. Ports `allocator::calloc`.
    pub fn calloc(self: *Orisnitsa, count: usize, size: usize) ?[*]u8 {
        // `*%` mirrors HPHA's own unchecked `count * size`, including its
        // overflow-wraps-not-panics behaviour: the same (possibly wrapped) value
        // is used both as the allocation size and the zero-fill length below, so
        // an overflow changes what is allocated, never how much of it gets
        // zeroed.
        const total = count *% size;
        const ptr = self.alloc(total) orelse return null;
        // `ptr` was just allocated with room for exactly `total` bytes,
        // exclusively owned (freshly allocated, not yet handed to any other
        // caller).
        @memset(ptr[0..total], 0);
        return ptr;
    }

    /// Grows, shrinks, or moves `ptr` to hold `size` bytes at
    /// `block.DEFAULT_ALIGNMENT`. `ptr == null` acts as `alloc`; `size == 0` acts
    /// as `free` and returns `null`. Ports `allocator::realloc(void*, size_t)`.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced.
    pub fn realloc(self: *Orisnitsa, ptr: ?[*]u8, size: usize) ?[*]u8 {
        const p = ptr orelse return self.alloc(size);
        if (size == 0) {
            self.free(p);
            return null;
        }
        // `p` is a live allocation this instance produced (this function's own
        // contract), exactly what `ptrInBucket` requires.
        if (self.buckets.ptrInBucket(p)) {
            const sz = bucket.clampSmallAllocation(size);
            if (bucket.isSmallAllocation(sz)) {
                return self.buckets.realloc(p, sz);
            }
            const new_ptr = self.tree.alloc(sz) orelse return null;
            const page = bucket.ptrGetPage(p);
            const elem_size = page.elemSize();
            // `new_ptr` was just allocated with room for at least
            // `sz > MAX_SMALL_ALLOCATION >= elem_size` bytes (`isSmallAllocation`
            // was just checked `false` above, so `sz > MAX_SMALL_ALLOCATION`, the
            // same bound every bucket `elem_size` is `<=`); `p` is valid for
            // `elem_size` bytes (its slot's own size); freshly, independently
            // allocated, so the two ranges never overlap.
            @memcpy(new_ptr[0..elem_size], p[0..elem_size]);
            self.buckets.free(p);
            return new_ptr;
        }
        // `p` is a live tree-path allocation this instance produced (not a
        // bucket pointer, per the `ptrInBucket` check above).
        return self.tree.realloc(p, size);
    }

    /// Grows, shrinks, or moves `ptr` to hold `size` bytes aligned to
    /// `alignment`. `alignment <= block.DEFAULT_ALIGNMENT` behaves exactly like
    /// `realloc`; `ptr == null` acts as `allocAligned`; `size == 0` acts as
    /// `free` and returns `null`. Ports `allocator::realloc(void*, size_t,
    /// size_t)`.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced.
    pub fn reallocAligned(self: *Orisnitsa, ptr: ?[*]u8, size: usize, alignment: usize) ?[*]u8 {
        std.debug.assert(std.math.isPowerOfTwo(alignment));
        if (alignment <= block.DEFAULT_ALIGNMENT) {
            return self.realloc(ptr, size);
        }
        const p = ptr orelse return self.allocAligned(size, alignment);
        if (size == 0) {
            self.free(p);
            return null;
        }
        if (@intFromPtr(p) & (alignment - 1) != 0) {
            // `p` doesn't already satisfy `alignment` — the in-place paths below
            // all rely on it already doing so (bucket slots inherit their page's
            // alignment; the tree path shifts only within a block's own span),
            // so there is no way to reach the requested alignment without
            // moving.
            const new_ptr = self.allocAligned(size, alignment) orelse return null;
            // `p` is a live allocation this instance produced (this function's
            // own contract), exactly what `size` requires.
            const count = @min(self.querySize(p), size);
            // `new_ptr` was just allocated with room for at least `size >=
            // count` bytes; `p` is valid for at least `count` bytes (`count <=
            // self.querySize(p)`); freshly, independently allocated, so the two
            // ranges never overlap.
            @memcpy(new_ptr[0..count], p[0..count]);
            self.free(p);
            return new_ptr;
        }
        // `p` is a live allocation this instance produced.
        if (self.buckets.ptrInBucket(p)) {
            const sz = bucket.clampSmallAllocation(size);
            if (bucket.isSmallAllocation(sz) and alignment <= bucket.MAX_SMALL_ALLOCATION) {
                // Growing in place within the bucket path here delegates to
                // `Buckets.realloc`, which is not itself alignment-aware —
                // exactly mirroring HPHA's own `bucket_realloc` call. Soundness
                // relies on the *original* allocation's bucket having been
                // chosen by `allocAligned` (whose `roundUp(size, alignment)`
                // makes every slot in that bucket's pages a multiple of
                // `alignment` from a `PAGE_SIZE`-aligned base, hence itself
                // `alignment`-aligned) — this call does not re-establish that
                // guarantee if it must move to a larger bucket, an inherited
                // HPHA quirk, not a new one.
                return self.buckets.realloc(p, sz);
            }
            const new_ptr = self.tree.allocAligned(sz, alignment) orelse return null;
            const page = bucket.ptrGetPage(p);
            const elem_size = page.elemSize();
            // Deliberate deviation from HPHA: the upstream C++ copies
            // `elem_size` bytes unconditionally here. That is sound in *its*
            // only reachable case (`size` too big for any bucket, so `size >
            // elem_size` always), but this branch can also be reached with
            // `size` small and merely `alignment > MAX_SMALL_ALLOCATION` — and
            // then `elem_size` (up to `MAX_SMALL_ALLOCATION`) can exceed `size`,
            // while `tree.allocAligned` only guarantees `new_ptr` has room for
            // `size` bytes. Copying the full `elem_size` in that case would
            // overflow `new_ptr`'s real capacity, a genuine heap corruption bug
            // in the 2007 original, not a behaviour this port preserves —
            // capping at `size` is a correctness fix, not a cross-port deviation
            // the invariant cares about (it only changes what stale bytes beyond
            // the caller's own requested `size` end up copied, never any
            // tree/bucket state transition). `new_ptr` was just allocated with
            // room for at least `sz` bytes; `p` is valid for `elem_size` bytes
            // (its slot's own size), and `@min(elem_size, sz) <= sz` stays
            // within both; freshly, independently allocated, so the two ranges
            // never overlap regardless.
            const copy_len = @min(elem_size, sz);
            @memcpy(new_ptr[0..copy_len], p[0..copy_len]);
            self.buckets.free(p);
            return new_ptr;
        }
        // `p` is a live tree-path allocation this instance produced.
        return self.tree.reallocAligned(p, size, alignment);
    }

    /// Grows or shrinks `ptr` in place to the extent possible, without moving
    /// it, returning the resulting size either way. `ptr == null` returns 0.
    /// Ports `allocator::resize`.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced.
    pub fn resize(self: *Orisnitsa, ptr: ?[*]u8, size: usize) usize {
        const p = ptr orelse return 0;
        std.debug.assert(size > 0);
        // `p` is a live allocation this instance produced (this function's own
        // contract).
        if (self.buckets.ptrInBucket(p)) {
            const page = bucket.ptrGetPage(p);
            return page.elemSize();
        }
        // `p` is a live tree-path allocation this instance produced.
        return self.tree.resize(p, size);
    }

    /// Queries the usable size of `ptr`'s allocation. `ptr == null` returns 0.
    /// Ports `allocator::size`. Named `querySize`, not `size` — every other
    /// method here already has its own `size: usize` parameter (matching
    /// `orisnik`'s own naming), and Zig's struct-member namespace makes a
    /// method's name visible throughout the whole struct body, so `size` as a
    /// method name here would collide with all of them.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced.
    pub fn querySize(self: *Orisnitsa, ptr: ?[*]u8) usize {
        const p = ptr orelse return 0;
        // `p` is a live allocation this instance produced (this function's own
        // contract).
        if (self.buckets.ptrInBucket(p)) {
            const page = bucket.ptrGetPage(p);
            return page.elemSize();
        }
        // `p` is a live tree-path allocation this instance produced.
        const bl = block.ptrGetBlockHeader(p);
        return bl.size();
    }

    /// Frees `ptr`. `ptr == null` is a no-op. Ports `allocator::free(void*)`.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced.
    pub fn free(self: *Orisnitsa, ptr: ?[*]u8) void {
        const p = ptr orelse return;
        // `p` is a live allocation this instance produced (this function's own
        // contract).
        if (self.buckets.ptrInBucket(p)) {
            self.buckets.free(p);
            return;
        }
        // `p` is a live tree-path allocation this instance produced.
        self.tree.free(p);
    }

    /// Frees `ptr`, given its original request size — skips the page-marker
    /// dispatch `free` needs, at the cost of the caller supplying `orig_size`
    /// exactly. `ptr == null` is a no-op. Ports `allocator::free(void*,
    /// size_t)`.
    ///
    /// `orig_size` must be `ptr`'s size **at the moment it was allocated** —
    /// bucket-vs-tree routing is decided once, then, and never changes for that
    /// pointer's lifetime, even across a later `realloc`/`resize` that shrinks
    /// it (a large allocation later shrunk to a small size *stays*
    /// tree-allocated; `bucket.isSmallAllocation(orig_size)` below has no way to
    /// tell that apart from a pointer that was always small). Passing a
    /// *current*, post-realloc size here is a caller bug this function cannot
    /// detect, since it has no pointer-derived ground truth to check against —
    /// unlike `free`. Prefer `free` whenever `ptr`'s allocation history isn't
    /// certain to be realloc-free.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced with `orig_size` at `block.DEFAULT_ALIGNMENT`, `orig_size` being
    /// that allocation's original request size, not a size from any later
    /// `realloc`/`resize` call.
    pub fn freeWithSize(self: *Orisnitsa, ptr: ?[*]u8, orig_size: usize) void {
        const p = ptr orelse return;
        if (bucket.isSmallAllocation(orig_size)) {
            // `p` is a live bucket-path allocation from bucket
            // `bucketSpacingFunction(orig_size)` — this function's own contract
            // (`p` was allocated with this exact `orig_size` at
            // `DEFAULT_ALIGNMENT`) is exactly how `alloc` picks a bucket.
            self.buckets.freeDirect(p, bucket.bucketSpacingFunction(orig_size));
            return;
        }
        // `p` is a live tree-path allocation (`orig_size` is not small, this
        // function's own contract, matching how `alloc` would have routed it).
        self.tree.free(p);
    }

    /// Frees `ptr`, given its original request size and alignment. `ptr ==
    /// null` is a no-op. Ports `allocator::free(void*, size_t, size_t)`.
    ///
    /// `orig_size`/`old_alignment` must be `ptr`'s size/alignment **at the
    /// moment it was allocated** — see `freeWithSize`'s doc for why a later
    /// `realloc`/`resize`'s *current* size is not a safe substitute here, and
    /// prefer `free` whenever `ptr`'s allocation history isn't certain to be
    /// realloc-free.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced with `orig_size`/`old_alignment`, both being that allocation's
    /// original request values, not values from any later `realloc`/`resize`
    /// call.
    pub fn freeWithSizeAligned(self: *Orisnitsa, ptr: ?[*]u8, orig_size: usize, old_alignment: usize) void {
        const p = ptr orelse return;
        if (bucket.isSmallAllocation(orig_size) and old_alignment <= bucket.MAX_SMALL_ALLOCATION) {
            // `p` is a live bucket-path allocation from bucket
            // `bucketSpacingFunction(roundUp(orig_size, old_alignment))` — this
            // function's own contract is exactly how `allocAligned`'s bucket
            // branch picks a bucket.
            self.buckets.freeDirect(p, bucket.bucketSpacingFunction(align_helpers.roundUp(orig_size, old_alignment)));
            return;
        }
        // `p` is a live tree-path allocation, matching how `allocAligned` would
        // have routed it.
        self.tree.free(p);
    }

    /// Returns every fully-unused page/arena to the OS. Never called
    /// automatically — call periodically if reclaiming idle memory matters.
    /// Ports `allocator::purge`.
    pub fn purge(self: *Orisnitsa) void {
        self.tree.purge();
        self.buckets.purge();
    }

    /// Total bytes currently claimed from the OS across both paths. Ports
    /// `allocator::allocated`.
    pub fn allocated(self: *Orisnitsa) usize {
        return self.buckets.allocated() + self.tree.allocated();
    }
};

const testing = std.testing;

// Every test below allocates through a fresh `Orisnitsa`, which (unlike
// `bucket.zig`'s `FakePage`/`tree.zig`'s `FakeArena`) has no seam to seed its
// `Buckets`/`Tree` from heap-backed memory — `Orisnitsa.init()` always starts
// empty, so any allocation reaches real `os.map`, exercised by native
// `zig build test` on all three CI OSes (zig-ci.yml). The no-OS-touch
// zero-size/null-pointer edge cases below need no such caveat.

test "alloc of zero returns null" {
    var orisnitsa: Orisnitsa = .init();
    try testing.expect(orisnitsa.alloc(0) == null);
    try testing.expect(orisnitsa.allocAligned(0, 64) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // must not have touched the OS
}

test "realloc of a null pointer acts as alloc of zero" {
    var orisnitsa: Orisnitsa = .init();
    try testing.expect(orisnitsa.realloc(null, 0) == null);
}

test "size and resize of null are zero" {
    var orisnitsa: Orisnitsa = .init();
    try testing.expectEqual(@as(usize, 0), orisnitsa.querySize(null));
    try testing.expectEqual(@as(usize, 0), orisnitsa.resize(null, 8));
}

test "free of null is a no-op" {
    var orisnitsa: Orisnitsa = .init();
    orisnitsa.free(null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "alloc bucket-path round-trip" {
    var orisnitsa: Orisnitsa = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..64], 0xAB);
    try testing.expectEqual(@as(usize, 64), orisnitsa.querySize(ptr));
    orisnitsa.free(ptr);
}

test "alloc tree-path round-trip" {
    var orisnitsa: Orisnitsa = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..size], 0xCD);
    try testing.expect(orisnitsa.querySize(ptr) >= size);
    orisnitsa.free(ptr);
}

test "allocAligned respects alignment on both paths" {
    var orisnitsa: Orisnitsa = .init();
    const cases = [_]struct { size: usize, alignment: usize }{
        .{ .size = 48, .alignment = 64 }, // bucket path
        .{ .size = bucket.MAX_SMALL_ALLOCATION + 8, .alignment = 128 }, // tree path
    };
    for (cases) |c| {
        const ptr = orisnitsa.allocAligned(c.size, c.alignment) orelse return error.TestUnexpectedResult; // "OS map failed"
        try testing.expectEqual(@as(usize, 0), @intFromPtr(ptr) % c.alignment);
        orisnitsa.free(ptr);
    }
}

test "realloc moves a bucket allocation across size classes" {
    var orisnitsa: Orisnitsa = .init();
    const ptr = orisnitsa.alloc(8) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..8], 0xEF);
    const grown = orisnitsa.realloc(ptr, 200) orelse return error.TestUnexpectedResult; // "growth within buckets never fails"
    // The first 8 bytes must have been preserved across the grow.
    try testing.expect(std.mem.allEqual(u8, grown[0..8], 0xEF));
    orisnitsa.free(grown);
}

test "realloc moves a bucket allocation to the tree path" {
    var orisnitsa: Orisnitsa = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..64], 0x11);
    const big = bucket.MAX_SMALL_ALLOCATION + 4096;
    const moved = orisnitsa.realloc(ptr, big) orelse return error.TestUnexpectedResult; // "growth onto the tree path never fails"
    // The first 64 bytes must have been preserved across the move.
    try testing.expect(std.mem.allEqual(u8, moved[0..64], 0x11));
    orisnitsa.free(moved);
}

test "realloc with size zero frees and returns null" {
    var orisnitsa: Orisnitsa = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.realloc(ptr, 0) == null);
    // `free`/`realloc(_, 0)` never returns memory to the OS on its own — matching
    // HPHA, only an explicit `purge()` reclaims fully-unused pages/arenas.
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "the freed page must be reclaimable"
}

test "resize grows a tree allocation in place" {
    var orisnitsa: Orisnitsa = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    const new_size = orisnitsa.resize(ptr, size + 64);
    try testing.expect(new_size >= size + 64);
    // `resize` grew `ptr` in place to at least `new_size` bytes.
    @memset(ptr[0..new_size], 0x22);
    orisnitsa.free(ptr);
}

test "freeWithSize matches plain free" {
    var orisnitsa: Orisnitsa = .init();
    const a = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSize(a, 64);

    const b = orisnitsa.allocAligned(48, 128) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSizeAligned(b, 48, 128);

    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "allocated tracks both paths and purge reclaims them" {
    var orisnitsa: Orisnitsa = .init();
    const small = orisnitsa.alloc(32) orelse return error.TestUnexpectedResult; // "OS map failed"
    const large = orisnitsa.alloc(bucket.MAX_SMALL_ALLOCATION + 4096) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.allocated() > 0);
    orisnitsa.free(small);
    orisnitsa.free(large);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "every fully-unused page/arena must be reclaimed"
}
