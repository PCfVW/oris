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
const os = @import("os.zig");
const tree_mod = @import("tree.zig");

/// HPHA's own alignment precondition, ported verbatim: `(alignment & (alignment-1)) == 0`.
///
/// This is **not** `std.math.isPowerOfTwo`, and the difference is load-bearing. Zero is
/// not a power of two, but it *does* satisfy HPHA's expression — `0 & (0 -% 1)`, with
/// the subtraction wrapping to `maxInt(usize)`, is `0` — so upstream accepts
/// `alloc(size, 0)` / `realloc(ptr, size, 0)` and routes both to the unaligned path via
/// the `alignment <= DEFAULT_ALIGNMENT` test immediately below the assert. Lazarov's own
/// `main.cpp` benchmark relies on this, calling `realloc(ptr, 0, 0)` to release each
/// block in its aligned-realloc case.
///
/// v0.1.0 used `isPowerOfTwo` here, which rejected zero and aborted any
/// `Debug`/`ReleaseSafe` build on that call — a deviation introduced by the port, not
/// inherited from HPHA. Restoring the original expression restores the original
/// behaviour; it is a fidelity fix, not a new extension. Mirrors `orisnik`'s
/// `orisnik::is_hpha_alignment` exactly.
pub fn isHphaAlignment(alignment: usize) bool {
    return alignment & (alignment -% 1) == 0;
}

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
/// # Address stability
/// **An `Orisnitsa` must not be moved once it has served its first request.** Three
/// pieces of its state bind to the instance's own address the moment it is first
/// used: the self-linked sentinel of each `Bucket`'s page list, the self-linked
/// sentinel of the tree's free-block index (both lazily initialized — see
/// `list.zig`'s lazy-sentinel-init doc), and the per-bucket page marker that
/// `Buckets.ptrInBucket` re-derives on every `free`/`realloc`/`querySize` call to
/// decide whether a pointer belongs to the bucket or the tree path.
///
/// Copying the value out of its original storage — `var b = a;`, returning it by
/// value from a helper, appending it to an `ArrayList` — leaves all three pointing at
/// the old address. The sentinels then dangle, and every marker mismatches, so
/// `ptrInBucket` starts answering `false` for genuine bucket pointers and `free`
/// hands them to the tree path, which reads a block header out of a bucket slot's
/// neighbouring bytes. This is the same implicit constraint HPHA's C++ `allocator`
/// already carries (it defines no move constructor).
///
/// Declare it in final position and pass `*Orisnitsa` from there — the
/// `var backing: Orisnitsa = .init();` + `orisnitsa.allocator(&backing)` pattern in
/// `root.zig`'s module doc does exactly this. `Debug`/`ReleaseSafe` builds carry a
/// tripwire (`debugAssertNotMoved`) that trips on the first operation after a move
/// instead of corrupting silently; `ReleaseFast` does not, so this remains a
/// contract, not an enforced invariant. Mirrors `orisnik`'s `Orisnik`
/// "Address stability" doc section.
///
/// **Single-threaded only** — see the module doc's "`&self` vs `*Self`" section.
pub const Orisnitsa = struct {
    /// The small-allocation path — every request `<= MAX_SMALL_ALLOCATION` (after
    /// `bucket.clampSmallAllocation`) lands here.
    buckets: bucket.Buckets = .init(),
    /// The large-allocation path — every request the bucket path doesn't serve.
    tree: tree_mod.Tree = .init(),
    /// This instance's own address, latched on the first operation and compared on
    /// every later one by `debugAssertNotMoved` — the tripwire for the non-move
    /// contract in this type's "Address stability" doc section. `0` means "not yet
    /// latched", the same lazy-init encoding `list.zig`'s sentinel uses for its null
    /// `prev`. Compared only under `std.debug.assert`, so `ReleaseFast` pays one word
    /// of storage and no instructions.
    origin: usize = 0,

    /// Builds a fresh, empty allocator instance — no OS memory is claimed until
    /// the first allocation. Ports `allocator::allocator` (the default
    /// constructor). A pure value (no address-dependent state at construction —
    /// see `list.zig`'s lazy-sentinel-init doc), so `var ALLOCATOR: Orisnitsa =
    /// .init();` is `comptime`-constructible, the standard global-allocator
    /// pattern's own requirement.
    pub fn init() Orisnitsa {
        return .{};
    }

    /// Latches this instance's address on first use and, on every later call,
    /// asserts it has not changed — the runtime tripwire for the non-move contract
    /// documented in this type's "Address stability" section.
    ///
    /// Elided in `ReleaseFast`/`ReleaseSmall` (`std.debug.assert`), matching
    /// `Zig/CONVENTIONS.md`'s rule that a structural invariant checked on every
    /// operation is an `assert`, never a bare `if (!cond) unreachable` kept in
    /// release.
    fn debugAssertNotMoved(self: *Orisnitsa) void {
        // PROVENANCE: the address is read for its bit pattern only, to compare
        // against a previously latched one — never turned back into a pointer.
        const here = @intFromPtr(self);
        if (self.origin == 0) {
            self.origin = here;
        } else {
            // "this Orisnitsa has been moved since its first use — its intrusive
            //  list/tree sentinels and every bucket page marker still refer to the
            //  old address, so bucket/tree dispatch is now silently wrong. See the
            //  type's Address stability doc section."
            std.debug.assert(self.origin == here);
        }
    }

    /// Allocates `size` bytes at `block.DEFAULT_ALIGNMENT`. `size == 0` returns
    /// `null`. Ports `allocator::alloc(size_t)`.
    pub fn alloc(self: *Orisnitsa, size: usize) ?[*]u8 {
        self.debugAssertNotMoved();
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
        std.debug.assert(isHphaAlignment(alignment));
        self.debugAssertNotMoved();
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
        self.debugAssertNotMoved();
        // HPHA computes `count * size` unchecked and passes the same value to both
        // `alloc` and `memset`. That pairing is precisely what makes an overflow
        // fatal rather than merely wrong: the wrapped product under-allocates, while
        // the *unwrapped* length the caller believes in still governs how much gets
        // zeroed — so `calloc(2, maxInt(usize))` acquires a few bytes and then
        // memsets exabytes. `@mulWithOverflow` declines instead. As with
        // `tree.MAX_ALLOCATION` (see its doc), this changes behaviour only for
        // products HPHA could never have served correctly, and touches no state
        // transition the cross-port invariant counts.
        // CAST: none — `@mulWithOverflow` returns the wrapped product plus a `u1`
        // overflow flag, both at `usize` width.
        const product = @mulWithOverflow(count, size);
        if (product[1] != 0) return null;
        const total = product[0];
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
        self.debugAssertNotMoved();
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
        std.debug.assert(isHphaAlignment(alignment));
        self.debugAssertNotMoved();
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
        self.debugAssertNotMoved();
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
        self.debugAssertNotMoved();
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
        self.debugAssertNotMoved();
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
    /// One caller bug in this family *is* detectable and is handled rather than
    /// propagated: `orig_size == 0` with a non-null `ptr` cannot describe any real
    /// allocation (`alloc(0)` returns `null`), so it falls back to `free`'s
    /// pointer-based dispatch instead of underflowing the size-class index. See
    /// `freeZeroOrigSize`.
    ///
    /// `ptr`, if non-null, must be a still-live allocation this instance
    /// produced with `orig_size` at `block.DEFAULT_ALIGNMENT`, `orig_size` being
    /// that allocation's original request size, not a size from any later
    /// `realloc`/`resize` call.
    pub fn freeWithSize(self: *Orisnitsa, ptr: ?[*]u8, orig_size: usize) void {
        self.debugAssertNotMoved();
        const p = ptr orelse return;
        if (orig_size == 0) {
            // `p` is a live allocation this instance produced (this function's own
            // contract), which is exactly `free`'s.
            self.freeZeroOrigSize(p);
            return;
        }
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
        std.debug.assert(isHphaAlignment(old_alignment));
        self.debugAssertNotMoved();
        const p = ptr orelse return;
        if (orig_size == 0) {
            // `p` is a live allocation this instance produced (this function's own
            // contract), which is exactly `free`'s.
            self.freeZeroOrigSize(p);
            return;
        }
        // HPHA computes `round_up(origSize, oldAlignment)` below unconditionally,
        // which is well-defined for every alignment `allocAligned` could have used
        // *except* 0 — and 0 is one upstream accepts (see `isHphaAlignment`), routing
        // it to the unaligned path at allocation time while leaving its own
        // `free(ptr, size, 0)` to compute `round_up(size, 0)`, i.e. garbage. Mapping
        // it to `DEFAULT_ALIGNMENT` restores the symmetry rather than inventing a
        // rule: `allocAligned(s, 0)` delegates to `alloc(s)`, which picks bucket
        // `bucketSpacingFunction(clampSmallAllocation(s))`, and that is exactly the
        // bucket `bucketSpacingFunction(roundUp(s, DEFAULT_ALIGNMENT))` names for
        // every `s` in `1..=MAX_SMALL_ALLOCATION` (both ports carry a test pinning
        // the two expressions together across that whole range).
        const alignment = if (old_alignment == 0) block.DEFAULT_ALIGNMENT else old_alignment;
        if (bucket.isSmallAllocation(orig_size) and alignment <= bucket.MAX_SMALL_ALLOCATION) {
            // `p` is a live bucket-path allocation from bucket
            // `bucketSpacingFunction(roundUp(orig_size, old_alignment))` — this
            // function's own contract is exactly how `allocAligned`'s bucket
            // branch picks a bucket.
            self.buckets.freeDirect(p, bucket.bucketSpacingFunction(align_helpers.roundUp(orig_size, alignment)));
            return;
        }
        // `p` is a live tree-path allocation, matching how `allocAligned` would
        // have routed it.
        self.tree.free(p);
    }

    /// The `orig_size == 0` path shared by `freeWithSize` and
    /// `freeWithSizeAligned`: a caller bug, handled safely.
    ///
    /// No live pointer can ever have been allocated with size 0 — `alloc` and
    /// `allocAligned` both return `null` for a zero size, so the only pointer a
    /// zero `orig_size` could honestly accompany is the null one, which both
    /// callers have already returned on. A non-null `ptr` here therefore violates
    /// their documented contract that `orig_size` is the allocation's own original
    /// request size.
    ///
    /// HPHA does not check, and the arithmetic that follows has no defined result:
    /// `bucketSpacingFunction(0)` is `((0 + 7) >> 3) - 1`, which underflows to
    /// `maxInt(usize)` and indexes a 32-element array. `Debug`/`ReleaseSafe` catch
    /// that; **`ReleaseFast` has no bounds check and corrupts memory silently**,
    /// which is the reason this is worth a branch rather than a comment. (`orisnik`
    /// is contained to a panic by Rust's always-on slice bounds check — this port is
    /// the one where the consequence is real, so the guard matters more here.)
    ///
    /// Dispatching through `free` is the one answer that is *correct* rather than
    /// merely safe: `free` re-derives bucket-vs-tree ownership from the pointer
    /// itself, so it releases the block properly no matter which path it came from —
    /// the same reasoning `allocator.zig`'s `freeImpl` already relies on.
    ///
    /// Deliberately **not** an `assert`. The recovery is not a guess to be warned
    /// about, and asserting would reintroduce exactly the failure shape v0.1.1's F5
    /// fix removed: a degenerate argument that traps in `Debug`/`ReleaseSafe` while
    /// working in `ReleaseFast`.
    ///
    /// `ptr` must be a still-live allocation this instance produced.
    fn freeZeroOrigSize(self: *Orisnitsa, ptr: [*]u8) void {
        self.free(ptr);
    }

    /// Returns every fully-unused page/arena to the OS. Never called
    /// automatically — call periodically if reclaiming idle memory matters.
    /// Ports `allocator::purge`.
    pub fn purge(self: *Orisnitsa) void {
        self.debugAssertNotMoved();
        self.tree.purge();
        self.buckets.purge();
    }

    /// Total bytes currently claimed from the OS across both paths. Ports
    /// `allocator::allocated`.
    pub fn allocated(self: *Orisnitsa) usize {
        self.debugAssertNotMoved();
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

// ---- v0.1.1 regression tests (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----

test "oversized requests are declined, not wrapped" {
    // F1. Every one of these overflows an intermediate `+` in the tree path's size
    // arithmetic. Before v0.1.1 they wrapped: `ReleaseFast` returned a pointer to a
    // *zero-byte* block for a `maxInt(usize)` request, and `Debug`/`ReleaseSafe`
    // tripped `std.mem.alignForward`'s own overflow check.
    var orisnitsa: Orisnitsa = .init();
    const max = std.math.maxInt(usize);
    for ([_]usize{ max, max - 1, max - 8, tree_mod.MAX_ALLOCATION + 1 }) |size| {
        try testing.expect(orisnitsa.alloc(size) == null);
        try testing.expect(orisnitsa.allocAligned(size, 64) == null);
    }
    // The aligned path needs `size + alignment` of headroom, not just `size`: both
    // operands here are individually under `MAX_ALLOCATION`, but their sum is not,
    // so only `allocAligned`'s own guard can catch this one.
    try testing.expect(orisnitsa.allocAligned(1 << 63, 1 << 63) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "must not have touched the OS"
}

test "calloc declines a product that would overflow" {
    // F1, `calloc` half. `count * size` wrapped before v0.1.1, and the *unwrapped*
    // length still drove the zero-fill — so the Rust equivalent of this exact call
    // segfaulted in release.
    var orisnitsa: Orisnitsa = .init();
    try testing.expect(orisnitsa.calloc(2, std.math.maxInt(usize)) == null);
    try testing.expect(orisnitsa.calloc(std.math.maxInt(usize), 2) == null);
    try testing.expect(orisnitsa.calloc(1 << 32, 1 << 32) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "must not have touched the OS"
}

test "zero alignment is accepted as unaligned" {
    // F5. HPHA's `assert((alignment & (alignment-1)) == 0)` passes for zero, so
    // upstream accepts a zero alignment and routes it to the unaligned path;
    // Lazarov's own `main.cpp` calls `realloc(ptr, 0, 0)`. v0.1.0's `isPowerOfTwo`
    // rejected it and aborted every safe build on that call.
    try testing.expect(isHphaAlignment(0)); // "HPHA's own predicate accepts zero"
    try testing.expect(isHphaAlignment(1));
    try testing.expect(isHphaAlignment(block.DEFAULT_ALIGNMENT));
    try testing.expect(!isHphaAlignment(3));
    try testing.expect(!isHphaAlignment(24));

    var orisnitsa: Orisnitsa = .init();
    // Zero size still declines, exactly as the unaligned path does — this is the
    // `alloc` delegation working, not a special case.
    try testing.expect(orisnitsa.allocAligned(0, 0) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "reallocAligned with zero size and zero alignment frees" {
    // F5, the `main.cpp` call itself: must free and report null rather than abort.
    var orisnitsa: Orisnitsa = .init();
    const ptr = orisnitsa.allocAligned(64, 0) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.reallocAligned(ptr, 0, 0) == null);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "the freed page must be reclaimable"
}

test "freeWithSizeAligned accepts zero alignment" {
    // F5's downstream pair: an `allocAligned(_, 0)` allocation must be freeable
    // through `freeWithSizeAligned(_, _, 0)`, which is what a C caller mirroring its
    // own allocation call would write.
    var orisnitsa: Orisnitsa = .init();
    for ([_]usize{ 1, 8, 9, 64, 255, bucket.MAX_SMALL_ALLOCATION }) |size| {
        const ptr = orisnitsa.allocAligned(size, 0) orelse return error.TestUnexpectedResult; // "OS map failed"
        orisnitsa.freeWithSizeAligned(ptr, size, 0);
    }
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "zero-alignment free picks the bucket alloc used" {
    // F5's correctness premise, pinned: `freeWithSizeAligned`'s zero-alignment
    // mapping to `DEFAULT_ALIGNMENT` is only sound because
    // `bucketSpacingFunction(roundUp(s, DEFAULT_ALIGNMENT))` names the same bucket as
    // the `bucketSpacingFunction(clampSmallAllocation(s))` that `alloc` used. Checked
    // over the whole bucket range rather than trusted.
    var size: usize = 1;
    while (size <= bucket.MAX_SMALL_ALLOCATION) : (size += 1) {
        const allocated_from = bucket.bucketSpacingFunction(bucket.clampSmallAllocation(size));
        const freed_into = bucket.bucketSpacingFunction(
            align_helpers.roundUp(size, block.DEFAULT_ALIGNMENT),
        );
        try testing.expectEqual(allocated_from, freed_into);
    }
}

test "zero orig_size free recovers through pointer dispatch" {
    // A zero `orig_size` on a non-null pointer is a caller bug (no allocation can
    // have size 0 — `alloc(0)` is null), and before v0.1.1 it underflowed
    // `bucketSpacingFunction` to `maxInt(usize)` and indexed a 32-element array:
    // caught in `Debug`/`ReleaseSafe`, but a *silent out-of-bounds write* in
    // `ReleaseFast`, which is the build users ship. All three entry points must now
    // recover through `free`'s pointer-based dispatch instead, in every mode — this
    // test runs in all three.
    var orisnitsa: Orisnitsa = .init();

    // Bucket path.
    const a = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSize(a, 0);

    const b = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSizeAligned(b, 0, 64);

    // With the zero alignment F5 made reachable.
    const c = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSizeAligned(c, 0, 0);

    // Tree path too — the recovery must not assume the bucket path.
    const d = orisnitsa.alloc(bucket.MAX_SMALL_ALLOCATION + 4096) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSize(d, 0);

    orisnitsa.purge();
    // "every block must have been genuinely freed, not leaked or corrupted"
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

// ---- F7: out-of-memory paths (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----
//
// Every `orelse return null` on a `systemAlloc`/`os.map` result in `Buckets` and
// `Tree` was unexecuted by any test before v0.1.1. `os.test_vm.failMapAfter` supplies
// the seam; see its doc for why `std.testing.checkAllAllocationFailures` cannot serve
// here. These run in all three optimization modes.

test "alloc reports OOM on both paths when the OS refuses" {
    var orisnitsa: Orisnitsa = .init();
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();

    try testing.expect(orisnitsa.alloc(64) == null); // "bucket path must report OOM"
    try testing.expect(orisnitsa.alloc(bucket.MAX_SMALL_ALLOCATION + 4096) == null); // "tree path"
    try testing.expect(orisnitsa.allocAligned(48, 128) == null); // "aligned bucket path"
    try testing.expect(orisnitsa.allocAligned(bucket.MAX_SMALL_ALLOCATION + 4096, 128) == null);
    try testing.expect(orisnitsa.calloc(4, 16) == null); // "calloc must report OOM"
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "a refused map claims no bytes"
}

test "the allocator recovers once the OS stops refusing" {
    var orisnitsa: Orisnitsa = .init();
    os.test_vm.failMapAfter(0);
    try testing.expect(orisnitsa.alloc(64) == null);
    os.test_vm.clearFailure();

    // The allocator must be usable rather than poisoned by the failed growth.
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map succeeds again"
    orisnitsa.free(ptr);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "realloc that hits OOM keeps the original allocation" {
    // A `realloc` that cannot grow must report failure **and leave the original
    // allocation live** — the caller still owns it. Losing the old block on the OOM
    // path would be a leak at best and a use-after-free at worst.
    var orisnitsa: Orisnitsa = .init();
    // One page for the bucket allocation, then refuse: growing onto the tree path
    // needs a second, larger mapping.
    os.test_vm.failMapAfter(1);
    defer os.test_vm.clearFailure();

    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "first map is budgeted"
    @memset(ptr[0..64], 0x5A);

    try testing.expect(orisnitsa.realloc(ptr, bucket.MAX_SMALL_ALLOCATION + 4096) == null);

    // The original must be untouched and still usable.
    try testing.expect(std.mem.allEqual(u8, ptr[0..64], 0x5A));
    try testing.expectEqual(@as(usize, 64), orisnitsa.querySize(ptr));
    orisnitsa.free(ptr);
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
/// `main.cpp` benchmark drives HPHA with (`srand(1234)`). Porting it means the stress
/// sequence below is *the same sequence* his harness produces, so a future three-way
/// C++/Rust/Zig comparison (`ROADMAP.md`'s v0.3.0 trace corpus) can be generated
/// independently in each language instead of shipping recorded traces. `orisnik`
/// carries the identical generator, so both ports see one stream.
const VintageRand = struct {
    state: u32,

    fn init(seed: u32) VintageRand {
        return .{ .state = seed };
    }

    /// One `rand()` draw: `0..=0x7fff`.
    fn next(self: *VintageRand) u32 {
        self.state = self.state *% 214_013 +% 2_531_011;
        return (self.state >> 16) & 0x7fff;
    }

    /// `main.cpp`'s `rand_size()`: 2..=4096, heavily skewed toward the floor.
    ///
    /// The C++ computes `MIN + (MAX - MIN) * powf(r, 8.0f)` with `r` a float in
    /// `[0,1]`. This uses an integer analogue — three squarings in 15-bit fixed
    /// point — deliberately: `powf` is not bit-reproducible across language runtimes,
    /// and a stress workload whose *shape* both ports agree on exactly is worth more
    /// here than one that matches C++'s last mantissa bit. The distribution is the
    /// same: overwhelmingly bucket-path, with a long tail crossing into the tree
    /// (measured: ~71% / ~29%).
    fn size(self: *VintageRand) usize {
        const MIN_SIZE: u64 = 2;
        const MAX_SIZE: u64 = 4096;
        const r: u64 = self.next();
        const r2 = (r * r) >> 15;
        const r4 = (r2 * r2) >> 15;
        const r8 = (r4 * r4) >> 15;
        // CAST: u64 -> usize, the result is at most MAX_SIZE (4096).
        return @intCast(MIN_SIZE + ((r8 * (MAX_SIZE - MIN_SIZE)) >> 15));
    }

    /// `main.cpp`'s `rand_alignment()`: one of 1, 2, 4, ..., 128.
    fn alignment(self: *VintageRand) usize {
        const MAX_ALIGNMENT_LOG2: u64 = 7;
        const r: u64 = self.next();
        // CAST: u64 -> u6, the shift is at most MAX_ALIGNMENT_LOG2 (7).
        const shift: u6 = @intCast((MAX_ALIGNMENT_LOG2 * r) >> 15);
        return @as(usize, 1) << shift;
    }

    /// `main.cpp`'s `i + rand() % (N - i)` — picks a survivor to swap with.
    fn indexIn(self: *VintageRand, remaining: usize) usize {
        return @as(usize, self.next()) % remaining;
    }
};

test "VintageRand matches the Microsoft CRT" {
    // Golden vector: the first draws of `random values from rand.txt` in the Vintage
    // RNGs corpus, produced by the real CRT after `srand(0)`.
    var r: VintageRand = .init(0);
    for ([_]u32{ 38, 7719, 21238, 2437, 8855, 11797, 8365, 32285, 10450 }) |expected| {
        try testing.expectEqual(expected, r.next());
    }
    // And the seed Lazarov's own `main.cpp` uses.
    var r2: VintageRand = .init(1234);
    for ([_]u32{ 4068, 213, 12761, 8758, 23056, 7717, 15274, 24508 }) |expected| {
        try testing.expectEqual(expected, r2.next());
    }
}

test "randomized alloc/free stress matches the HPHA benchmark shape" {
    // The shape of `main.cpp`'s `benchmark1()`, with the assertions it never had.
    // Every block is stamped with a byte pattern derived from its index and verified
    // on free, so a block handed out twice, or overlapping another, fails loudly
    // rather than silently corrupting.
    //
    // This is the coverage class the suite had none of before v0.1.1: every other
    // test is a hand-written scenario of at most a few thousand allocations, and the
    // only randomized test in the module exercised the `RB-tree` rather than the
    // allocator.
    const N: usize = 20_000;
    const Block = struct { ptr: [*]u8, size: usize, stamp: u8 };

    for ([_]bool{ false, true }) |use_alignment| {
        var orisnitsa: Orisnitsa = .init();
        var rng: VintageRand = .init(1234); // main.cpp's own seed
        // The stamp travels with the block: the free loop below relocates entries, so
        // a slot index does not identify one.
        const live = try testing.allocator.alloc(Block, N);
        defer testing.allocator.free(live);
        var bucket_path: usize = 0;
        var tree_path: usize = 0;

        for (0..N) |i| {
            const sz = rng.size();
            if (bucket.isSmallAllocation(sz)) bucket_path += 1 else tree_path += 1;
            const ptr = blk: {
                if (use_alignment) {
                    const a = rng.alignment();
                    const p = orisnitsa.allocAligned(sz, a) orelse return error.TestUnexpectedResult;
                    try testing.expectEqual(@as(usize, 0), @intFromPtr(p) % a);
                    break :blk p;
                }
                break :blk orisnitsa.alloc(sz) orelse return error.TestUnexpectedResult;
            };
            // CAST: usize -> u8, a deliberate index fingerprint, not a value.
            const stamp: u8 = @intCast(i % 251);
            @memset(ptr[0..sz], stamp);
            live[i] = .{ .ptr = ptr, .size = sz, .stamp = stamp };
        }

        // `main.cpp`'s free order: swap a random survivor into position `i`.
        for (0..N) |i| {
            const j = i + rng.indexIn(N - i);
            const b = live[j];
            try testing.expect(std.mem.allEqual(u8, b.ptr[0..b.size], b.stamp));
            orisnitsa.free(b.ptr);
            live[j] = live[i];
        }

        orisnitsa.purge();
        // "every page must be reclaimable once all N blocks are freed"
        try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());

        // The `r^8` skew is the point of `main.cpp`'s distribution: mostly small, with
        // a substantial tail crossing the 256-byte bucket/tree boundary. Pinned so a
        // future change to `VintageRand.size` cannot quietly make this single-path.
        try testing.expect(bucket_path > N / 2);
        try testing.expect(tree_path > N / 10);
    }
}
