// SPDX-License-Identifier: MIT OR Apache-2.0
//! The top-level allocator: dispatches every request between the bucket path
//! (small allocations) and the tree path (everything else), and owns nothing else.
//!
//! Ports the single-threaded slice of `allocator`'s public surface, mirroring
//! `orisnik`'s `orisnik.rs` — `MULTITHREADED` (mutex-guarded buckets/tree) is out
//! of scope until v2.x, see `ROADMAP.md`. `DEBUG_ALLOCATOR` (guard bytes,
//! allocation records, `check()`/`report()`) is v0.2.0's own milestone, landing
//! incrementally behind `config.debug` (`guard.zig`, `spomen_guard.zig`,
//! `spomen_poison.zig`): both paths' guard bytes and payload poisoning are wired
//! in here (`treeAlloc`/`treeAllocAligned`/`treeRealloc`/`treeReallocAligned`/
//! `treeResize`/`bucketAlloc`/`bucketAllocAligned`/`bucketRealloc`/
//! `bucketResize`, and `querySize`/`free`/`freeWithSize`/`freeWithSizeAligned`'s
//! deflate/poison calls); the rest of `spomen` (allocation records, callstack
//! capture, `check()`/`report()`) follows in later phases. With
//! `config.debug` false, `guard.memoryGuardSize(config)` is 0, so every
//! `+`/`- memoryGuardSize(config)` site below is dead code the compiler removes,
//! restoring v0.1.x's exact guard-free arithmetic — the same "cancels out and is
//! simply omitted" shape this doc described before this feature existed, now
//! realized by the compiler rather than by the source never mentioning guard
//! bytes at all.
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
//! neither constraint: every method here takes `*Self` directly, and a
//! `var ALLOCATOR: Orisnitsa(.{}) = .init();` needs no trait marker to be shared as
//! global state — the single-threaded-only caveat is a plain doc note here (this
//! whole port's v0.1.0 scope, matching `orisnik`'s own `ROADMAP.md`-deferred
//! `MULTITHREADED` support), not something either language's type system enforces.

const std = @import("std");
const align_helpers = @import("align.zig");
const block = @import("block.zig");
const bucket = @import("bucket.zig");
const os = @import("os.zig");
const spomen = @import("spomen.zig");
const guard = @import("guard.zig");
const spomen_guard = @import("spomen_guard.zig");
const spomen_poison = @import("spomen_poison.zig");
const rand = @import("rand.zig");
const tree_mod = @import("tree.zig");

const Config = spomen.Config;

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
/// Declare it in final position and pass a pointer to it from there — the
/// `var backing: orisnitsa.Orisnitsa = .init();` + `orisnitsa.allocator(&backing)`
/// pattern in `root.zig`'s module doc does exactly this. `Debug`/`ReleaseSafe` builds carry a
/// tripwire (`debugAssertNotMoved`) that trips on the first operation after a move
/// instead of corrupting silently; `ReleaseFast` does not, so this remains a
/// contract, not an enforced invariant. Mirrors `orisnik`'s `Orisnik`
/// "Address stability" doc section — including its cross-port conclusion that no
/// compile-time enforcement (Rust `Pin`, an always-on check, or a marker redesign)
/// closes this gap without either breaking a load-bearing usage pattern or taxing
/// every release-build call; see the pre-v0.2.0 audit's F4 entry. This tripwire is
/// the accepted, final mitigation.
///
/// **Single-threaded only** — see the module doc's "`&self` vs `*Self`" section.
///
/// Generic over the `spomen` debug-subsystem `Config` (see `Zig/CONVENTIONS.md`'s
/// "`comptime` Toggles" section): `Orisnitsa(config)`, not a plain `Orisnitsa`
/// value with a runtime `config` field, is what gives the future debug subsystem
/// (guard bytes, allocation-record tracking) a compiler-enforced
/// zero-cost-when-disabled guarantee, matching Zig's own
/// `std.heap.DebugAllocator(comptime config: Config) type`. `root.zig`'s exported
/// `Orisnitsa` is the default, non-debug instantiation `Orisnitsa(.{})`, keeping
/// today's public surface source-compatible.
pub fn Orisnitsa(comptime config: Config) type {
    return struct {
        const Self = @This();

        /// The small-allocation path — every request `<= MAX_SMALL_ALLOCATION` (after
        /// `bucket.clampSmallAllocation`) lands here.
        buckets: bucket.Buckets(config) = .init(),
        /// The large-allocation path — every request the bucket path doesn't serve.
        tree: tree_mod.Tree(config) = .init(),
        /// This instance's own address, latched on the first operation and compared on
        /// every later one by `debugAssertNotMoved` — the tripwire for the non-move
        /// contract in this type's "Address stability" doc section. `0` means "not yet
        /// latched", the same lazy-init encoding `list.zig`'s sentinel uses for its null
        /// `prev`. Compared only under `std.debug.assert`, so `ReleaseFast` pays one word
        /// of storage and no instructions.
        origin: usize = 0,
        /// The guard-byte ramp's seed stream (`spomen`; see `rand.zig`'s module
        /// doc). `if (config.debug) rand.VintageRand else void` — Zig's standard
        /// zero-size-when-disabled idiom (`Zig/CONVENTIONS.md`'s "`comptime`
        /// Toggles" section): the non-debug `Orisnitsa`'s layout is completely
        /// unaffected by this field's existence. Seeded from a fixed, documented
        /// constant rather than any time-/address-derived source: guard-byte
        /// *content* (unlike its size/placement) is not part of the cross-port
        /// state-transition invariant, but making it deterministic and shared
        /// costs nothing and lets both ports produce byte-identical ramps for an
        /// identical allocation sequence, which a real per-run seed (`std.time`,
        /// ASLR) would not.
        guard_rng: if (config.debug) rand.VintageRand else void =
            if (config.debug) rand.VintageRand.init(0) else {},

        /// Builds a fresh, empty allocator instance — no OS memory is claimed until
        /// the first allocation. Ports `allocator::allocator` (the default
        /// constructor). A pure value (no address-dependent state at construction —
        /// see `list.zig`'s lazy-sentinel-init doc), so `var ALLOCATOR: Orisnitsa(.{}) =
        /// .init();` is `comptime`-constructible, the standard global-allocator
        /// pattern's own requirement.
        pub fn init() Self {
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
        fn debugAssertNotMoved(self: *Self) void {
            // SAFETY: `self` is a live `*Self` (a valid Zig reference), so
            // `@intFromPtr` is well-defined; the integer is only compared, never
            // converted back to a pointer or dereferenced.
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

        /// Draws the next guard-byte ramp seed from this instance's own stream.
        /// Only reachable when `config.debug` — every call site below is itself
        /// inside an `if (config.debug)` branch, `comptime`-eliminated otherwise,
        /// so this body is never analyzed (and `self.guard_rng` never treated as
        /// anything but `rand.VintageRand`) for a non-debug instantiation.
        fn nextGuardSeed(self: *Self) u8 {
            // CAST: u32 -> u8, HPHA's own `write_guard` does the identical
            // truncation — `(unsigned char)rand()` — on `rand()`'s `0..=0x7fff`
            // result; only the low byte seeds the ramp.
            return @truncate(self.guard_rng.next());
        }

        /// The tree path's sole *fresh-allocation* choke point: `alloc` and
        /// `realloc`'s bucket→tree crossover both go through this rather than
        /// `self.tree.alloc` directly, so the guard-byte write (when
        /// `config.debug`) exists exactly once. `size` is the caller-visible
        /// request; the guard reservation is folded in and out here, invisibly to
        /// every caller of this method.
        fn treeAlloc(self: *Self, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            const ptr = self.tree.alloc(inflated) orelse return null;
            if (config.debug) {
                // SAFETY: `ptr` is valid for `size + memoryGuardSize(config)` bytes
                // (just allocated with that inflated size above), exclusively owned
                // (freshly allocated, not yet handed to any other caller).
                spomen_guard.writeGuard(config, ptr, size, self.nextGuardSeed());
                // Poisons the payload *after* the guard write, matching HPHA's
                // own `write_guard()`-then-`initial_fill()` order inside
                // `debug_record`'s constructor/`debug_record_map::add` — the two
                // ranges are disjoint ([0, size) vs
                // [size, size + memoryGuardSize(config))) so the order has no
                // functional effect, only fidelity value.
                // SAFETY: `ptr` is valid for `size` bytes (a subset of the span
                // just established above), exclusively owned.
                spomen_poison.fill(ptr, size);
            }
            return ptr;
        }

        /// `treeAlloc`'s aligned counterpart — the tree path's sole
        /// *fresh-allocation* choke point for an aligned request.
        fn treeAllocAligned(self: *Self, size: usize, alignment: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            const ptr = self.tree.allocAligned(inflated, alignment) orelse return null;
            if (config.debug) {
                // SAFETY: `ptr` is valid for `size + memoryGuardSize(config)` bytes,
                // aligned to `alignment`, exclusively owned (freshly allocated).
                spomen_guard.writeGuard(config, ptr, size, self.nextGuardSeed());
                // See `treeAlloc`'s identical poisoning comment.
                // SAFETY: `ptr` is valid for `size` bytes (established above),
                // exclusively owned.
                spomen_poison.fill(ptr, size);
            }
            return ptr;
        }

        /// `treeAlloc`'s realloc counterpart: the tree path's sole choke point for
        /// growing/shrinking/moving an *existing* tree-path allocation. `size` is
        /// the new caller-visible target; on success, the guard ramp is
        /// (re)written at the new position regardless of whether the block grew
        /// in place, merged with a neighbour, or moved via allocate-copy-free —
        /// `tree.Tree.realloc`'s contract guarantees the returned pointer is valid
        /// for at least the inflated size passed in, whichever path it took
        /// internally.
        ///
        /// `ptr` must be a still-live tree-path allocation this instance
        /// produced.
        fn treeRealloc(self: *Self, ptr: [*]u8, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            const new_ptr = self.tree.realloc(ptr, inflated) orelse return null;
            if (config.debug) {
                // SAFETY: `new_ptr` is valid for `size + memoryGuardSize(config)`
                // bytes (just (re)allocated with that inflated size above);
                // exclusively owned — even if this is the same address `ptr` was,
                // the trailing guard region past the new, still-live payload is
                // this instance's own to write.
                spomen_guard.writeGuard(config, new_ptr, size, self.nextGuardSeed());
            }
            return new_ptr;
        }

        /// `treeRealloc`'s aligned counterpart.
        ///
        /// `ptr` must be a still-live tree-path allocation this instance
        /// produced, itself already aligned to `alignment`.
        fn treeReallocAligned(self: *Self, ptr: [*]u8, size: usize, alignment: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            const new_ptr = self.tree.reallocAligned(ptr, inflated, alignment) orelse return null;
            if (config.debug) {
                // SAFETY: same reasoning as `treeRealloc`, aligned.
                spomen_guard.writeGuard(config, new_ptr, size, self.nextGuardSeed());
            }
            return new_ptr;
        }

        /// `treeAlloc`'s in-place-only counterpart: grows `ptr` without ever
        /// moving it, reporting the resulting caller-visible size either way. On
        /// growth, the guard ramp is rewritten at the new position — HPHA's own
        /// `debug_update` re-runs `write_guard` here too (`resize` changing size
        /// necessarily changes where the trailing guard region starts).
        ///
        /// `ptr` must be a still-live tree-path allocation this instance
        /// produced.
        fn treeResize(self: *Self, ptr: [*]u8, size: usize) usize {
            // `size` this close to `maxInt(usize)` is certainly also past
            // `tree_mod.MAX_ALLOCATION` (far smaller — see that constant's own
            // doc), so passing it through unmodified when `inflate` overflows
            // still reaches `Tree.resize`'s own `normalizeSize`-driven decline
            // and reports the block's current size unchanged, exactly as
            // desired — no separate handling needed.
            const inflated = guard.inflate(config, size) orelse size;
            const real_size = self.tree.resize(ptr, inflated);
            const new_size = guard.deflate(config, real_size);
            // Unconditional — ports HPHA's own `resize` body exactly, which
            // reassigns `size` to `tree_resize`'s (deflated) return value and
            // calls `debug_update(ptr, size)` *every* time, whether or not the
            // block actually grew (`hpha.h`'s `resize`). This is not merely
            // faithful, it is necessary: when growth lands exactly on the
            // caller's own target (`new_size == size`), the guard's *position*
            // still moved from the old size's end to the new one's — comparing
            // `new_size` against `size` cannot detect that, only comparing
            // against the block's size *before* this call could, and
            // `Tree.resize` doesn't hand that back separately from the
            // *not-grown* case either.
            if (config.debug) {
                // SAFETY: `ptr` is valid for `real_size == new_size +
                // memoryGuardSize(config)` bytes (just reported by `Tree.resize`
                // above), exclusively owned.
                spomen_guard.writeGuard(config, ptr, new_size, self.nextGuardSeed());
            }
            return new_size;
        }

        /// The bucket path's sole *fresh-allocation* choke point for a plain
        /// (unaligned) request. `size` is the caller-visible, already-clamped
        /// request — the guard reservation is folded into the bucket-index
        /// computation and stripped back off nowhere here (bucket "size" is a
        /// slot's fixed class, never reported through this method; `resize`/
        /// `querySize` deflate it on their own).
        fn bucketAlloc(self: *Self, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse size;
            const ptr = self.buckets.allocDirect(bucket.bucketSpacingFunction(inflated)) orelse return null;
            if (config.debug) {
                // SAFETY: `ptr` is a slot of at least `inflated == size +
                // memoryGuardSize(config)` bytes (just allocated from that
                // bucket), exclusively owned (freshly allocated, not yet handed
                // to any other caller).
                spomen_guard.writeGuard(config, ptr, size, self.nextGuardSeed());
                // See `treeAlloc`'s identical poisoning comment.
                // SAFETY: `ptr` is a slot of at least `size` bytes (established
                // above), exclusively owned.
                spomen_poison.fill(ptr, size);
            }
            return ptr;
        }

        /// `bucketAlloc`'s aligned counterpart. The guard reservation is folded
        /// in **before** rounding to `alignment` — `roundUp(size +
        /// memoryGuardSize(config), alignment)`, not `roundUp(size, alignment)
        /// + memoryGuardSize(config)` — matching HPHA's own `alloc(size_t,
        /// size_t)` exactly (`Cpp/hpha.h:1291`); the two only ever differ when
        /// `alignment` doesn't evenly divide `memoryGuardSize(config)`, but the
        /// order is what HPHA's real arithmetic is, not an equivalent-looking
        /// alternative.
        fn bucketAllocAligned(self: *Self, size: usize, alignment: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse size;
            const ptr = self.buckets.allocDirect(
                bucket.bucketSpacingFunction(align_helpers.roundUp(inflated, alignment)),
            ) orelse return null;
            if (config.debug) {
                // SAFETY: `ptr` is a slot of at least `roundUp(inflated, alignment)
                // >= size + memoryGuardSize(config)` bytes, aligned to
                // `alignment`, exclusively owned.
                spomen_guard.writeGuard(config, ptr, size, self.nextGuardSeed());
                // See `treeAlloc`'s identical poisoning comment.
                // SAFETY: `ptr` is a slot of at least `size` bytes (established
                // above), exclusively owned.
                spomen_poison.fill(ptr, size);
            }
            return ptr;
        }

        /// The bucket path's sole choke point for growing/shrinking an
        /// *existing* bucket-path allocation in place (never a move —
        /// `Buckets.realloc` only ever grows into a larger size class,
        /// `realloc`'s own cross-path logic handles the bucket->tree case
        /// separately). `size` is the caller's already-clamped target; on
        /// success, the guard ramp is (re)written at that target, exactly
        /// mirroring HPHA's `bucket_realloc(ptr, size + MEMORY_GUARD_SIZE);
        /// debug_replace(ptr, newPtr, size, ...)` (`Cpp/hpha.h`'s `realloc`).
        ///
        /// `ptr` must be a still-live bucket-path allocation this instance
        /// produced.
        fn bucketRealloc(self: *Self, ptr: [*]u8, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse size;
            const new_ptr = self.buckets.realloc(ptr, inflated) orelse return null;
            if (config.debug) {
                // SAFETY: `new_ptr` is a slot of at least `inflated == size +
                // memoryGuardSize(config)` bytes, exclusively owned.
                spomen_guard.writeGuard(config, new_ptr, size, self.nextGuardSeed());
            }
            return new_ptr;
        }

        /// The bucket path's `resize` counterpart. Bucket slots never actually
        /// grow — this only ever reports the slot's own fixed, deflated size —
        /// but the guard ramp is still (re)written unconditionally on every
        /// call, matching HPHA's own `resize` body exactly: `size =
        /// ptr_get_page(ptr)->elem_size() - MEMORY_GUARD_SIZE;
        /// debug_update(ptr, size);` runs every time, not only when something
        /// changed (`Cpp/hpha.h`'s `resize`) — the same unconditional shape
        /// `treeResize`'s own doc explains at length for the tree path.
        ///
        /// `ptr` must be a still-live bucket-path allocation this instance
        /// produced.
        fn bucketResize(self: *Self, ptr: [*]u8) usize {
            // SAFETY: `ptr` is a still-live bucket-path allocation this instance
            // produced (this function's own contract), exactly what
            // `ptrGetPage` requires; the recovered `page` is therefore live too.
            const page = bucket.ptrGetPage(ptr);
            const real_size = page.elemSize();
            const new_size = guard.deflate(config, real_size);
            if (config.debug) {
                // SAFETY: `ptr` is valid for `real_size == new_size +
                // memoryGuardSize(config)` bytes (the whole slot), exclusively
                // owned.
                spomen_guard.writeGuard(config, ptr, new_size, self.nextGuardSeed());
            }
            return new_size;
        }

        /// Allocates `size` bytes at `block.DEFAULT_ALIGNMENT`. `size == 0` returns
        /// `null`. Ports `allocator::alloc(size_t)`.
        pub fn alloc(self: *Self, size: usize) ?[*]u8 {
            self.debugAssertNotMoved();
            if (!bucket.isSmallAllocation(config, size)) {
                return self.treeAlloc(size);
            }
            if (size == 0) return null;
            const sz = bucket.clampSmallAllocation(size);
            return self.bucketAlloc(sz);
        }

        /// Allocates `size` bytes aligned to `alignment`. `size == 0` returns `null`;
        /// `alignment <= block.DEFAULT_ALIGNMENT` behaves exactly like `alloc`. Ports
        /// `allocator::alloc(size_t, size_t)`.
        ///
        /// `alignment` must be a power of two — checked with `std.debug.assert`
        /// rather than HPHA's always-on `assert`, matching this port's
        /// hot-path-never-panics rule (`Zig/CONVENTIONS.md`'s Allocation Outcomes
        /// section).
        pub fn allocAligned(self: *Self, size: usize, alignment: usize) ?[*]u8 {
            std.debug.assert(isHphaAlignment(alignment));
            self.debugAssertNotMoved();
            if (alignment <= block.DEFAULT_ALIGNMENT) {
                return self.alloc(size);
            }
            if (!bucket.isSmallAllocation(config, size) or alignment > bucket.MAX_SMALL_ALLOCATION) {
                return self.treeAllocAligned(size, alignment);
            }
            if (size == 0) return null;
            const sz = bucket.clampSmallAllocation(size);
            return self.bucketAllocAligned(sz, alignment);
        }

        /// Allocates `count * size` bytes at `block.DEFAULT_ALIGNMENT` and zeroes
        /// them. Ports `allocator::calloc`.
        pub fn calloc(self: *Self, count: usize, size: usize) ?[*]u8 {
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
            // SAFETY: `ptr` was just allocated with room for exactly `total` bytes,
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
        pub fn realloc(self: *Self, ptr: ?[*]u8, size: usize) ?[*]u8 {
            self.debugAssertNotMoved();
            const p = ptr orelse return self.alloc(size);
            if (size == 0) {
                self.free(p);
                return null;
            }
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract), exactly what `ptrInBucket` requires.
            if (self.buckets.ptrInBucket(p)) {
                const sz = bucket.clampSmallAllocation(size);
                if (bucket.isSmallAllocation(config, sz)) {
                    return self.bucketRealloc(p, sz);
                }
                const new_ptr = self.treeAlloc(sz) orelse return null;
                // SAFETY: `p` is a live bucket-path allocation (`ptrInBucket`
                // just confirmed, above), exactly what `ptrGetPage` requires, so
                // the recovered page header is live.
                const page = bucket.ptrGetPage(p);
                const elem_size = page.elemSize();
                // Copies the old slot's *payload* only — `elem_size -
                // memoryGuardSize(config)`, HPHA's own `memcpy` length here
                // (`Cpp/hpha.h`'s `realloc`). Copying the whole inflated slot would
                // land the old guard ramp's tail on top of the new block's own ramp
                // (already written by `treeAlloc`, at `[sz, sz +
                // memoryGuardSize(config))`) whenever `elem_size > sz`.
                const payload_len = guard.deflate(config, elem_size);
                // SAFETY: `new_ptr` is really `treeAlloc`'s own `sz +
                // memoryGuardSize(config)` bytes, which exceeds `payload_len`:
                // `isSmallAllocation` was just checked `false` above, i.e. `sz +
                // memoryGuardSize(config) > MAX_SMALL_ALLOCATION`, the same bound
                // every bucket `elem_size` is `<=`. `p` is valid for `elem_size >=
                // payload_len` bytes (its slot's own real size); freshly,
                // independently allocated, so the two ranges never overlap.
                @memcpy(new_ptr[0..payload_len], p[0..payload_len]);
                self.buckets.free(p);
                return new_ptr;
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced (not a
            // bucket pointer, per the `ptrInBucket` check above).
            return self.treeRealloc(p, size);
        }

        /// Grows, shrinks, or moves `ptr` to hold `size` bytes aligned to
        /// `alignment`. `alignment <= block.DEFAULT_ALIGNMENT` behaves exactly like
        /// `realloc`; `ptr == null` acts as `allocAligned`; `size == 0` acts as
        /// `free` and returns `null`. Ports `allocator::realloc(void*, size_t,
        /// size_t)`.
        ///
        /// `ptr`, if non-null, must be a still-live allocation this instance
        /// produced.
        pub fn reallocAligned(self: *Self, ptr: ?[*]u8, size: usize, alignment: usize) ?[*]u8 {
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
            // SAFETY: `p` is a valid `[*]u8` (non-null, from the `orelse` above);
            // `@intFromPtr` only reads its address for a mask test, never
            // re-derives a pointer, and `alignment - 1` is a valid mask because
            // `alignment` is a power of two (`isHphaAlignment`, asserted on entry).
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
                // SAFETY: `new_ptr` was just allocated with room for at least `size >=
                // count` bytes; `p` is valid for at least `count` bytes (`count <=
                // self.querySize(p)`); freshly, independently allocated, so the two
                // ranges never overlap.
                @memcpy(new_ptr[0..count], p[0..count]);
                self.free(p);
                return new_ptr;
            }
            // SAFETY: `p` is a live allocation this instance produced.
            if (self.buckets.ptrInBucket(p)) {
                const sz = bucket.clampSmallAllocation(size);
                if (bucket.isSmallAllocation(config, sz) and alignment <= bucket.MAX_SMALL_ALLOCATION) {
                    // Growing in place within the bucket path here delegates to
                    // `bucketRealloc`, which is not itself alignment-aware —
                    // exactly mirroring HPHA's own `bucket_realloc` call. Soundness
                    // relies on the *original* allocation's bucket having been
                    // chosen by `allocAligned` (whose `roundUp(size, alignment)`
                    // makes every slot in that bucket's pages a multiple of
                    // `alignment` from a `PAGE_SIZE`-aligned base, hence itself
                    // `alignment`-aligned) — this call does not re-establish that
                    // guarantee if it must move to a larger bucket, an inherited
                    // HPHA quirk, not a new one.
                    return self.bucketRealloc(p, sz);
                }
                const new_ptr = self.treeAllocAligned(sz, alignment) orelse return null;
                // SAFETY: `p` is a live bucket-path allocation (`ptrInBucket`
                // just confirmed, above), exactly what `ptrGetPage` requires, so
                // the recovered page header is live.
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
                // tree/bucket state transition). The payload length is `elem_size -
                // memoryGuardSize(config)` (HPHA's own `memcpy` length, see the
                // plain `realloc` crossover above), capped at `sz` as described.
                // SAFETY: `new_ptr` was just allocated with room for at least `sz`
                // bytes; `p` is valid for `elem_size` bytes (its slot's own size),
                // and `copy_len <= @min(elem_size, sz)` stays within both; freshly,
                // independently allocated, so the two ranges never overlap
                // regardless.
                const copy_len = @min(guard.deflate(config, elem_size), sz);
                @memcpy(new_ptr[0..copy_len], p[0..copy_len]);
                self.buckets.free(p);
                return new_ptr;
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
            return self.treeReallocAligned(p, size, alignment);
        }

        /// Grows or shrinks `ptr` in place to the extent possible, without moving
        /// it, returning the resulting size either way. `ptr == null` returns 0.
        /// Ports `allocator::resize`.
        ///
        /// `ptr`, if non-null, must be a still-live allocation this instance
        /// produced.
        pub fn resize(self: *Self, ptr: ?[*]u8, size: usize) usize {
            self.debugAssertNotMoved();
            const p = ptr orelse return 0;
            std.debug.assert(size > 0);
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract).
            if (self.buckets.ptrInBucket(p)) {
                return self.bucketResize(p);
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
            return self.treeResize(p, size);
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
        pub fn querySize(self: *Self, ptr: ?[*]u8) usize {
            self.debugAssertNotMoved();
            const p = ptr orelse return 0;
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract).
            if (self.buckets.ptrInBucket(p)) {
                const page = bucket.ptrGetPage(p);
                return guard.deflate(config, page.elemSize());
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
            const bl = block.ptrGetBlockHeader(p);
            return guard.deflate(config, bl.size());
        }

        /// Frees `ptr`. `ptr == null` is a no-op. Ports `allocator::free(void*)`.
        ///
        /// `ptr`, if non-null, must be a still-live allocation this instance
        /// produced.
        pub fn free(self: *Self, ptr: ?[*]u8) void {
            self.debugAssertNotMoved();
            const p = ptr orelse return;
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract).
            if (self.buckets.ptrInBucket(p)) {
                if (config.debug) {
                    // Poisons *before* the reclaim below, matching HPHA's own
                    // `debug_remove`-before-`bucket_free` order in
                    // `allocator::free` — no caller-supplied size is available
                    // on this entry point (unlike `freeWithSize`), so this uses
                    // the slot's own current, deflated usable size rather than
                    // any HPHA-tracked original request (which needs the
                    // allocation-record store, a later phase, to supply).
                    // SAFETY: `p` is a live bucket-path allocation this instance
                    // produced (this function's own contract, and `ptrInBucket`
                    // just confirmed), so `ptrGetPage` finds its live page.
                    const page = bucket.ptrGetPage(p);
                    const real_size = page.elemSize();
                    // SAFETY: the slot is `real_size` bytes, so poisoning its
                    // deflated (guard-excluded) span stays within it; exclusively
                    // owned by this call (about to be reclaimed).
                    spomen_poison.fill(p, guard.deflate(config, real_size));
                }
                self.buckets.free(p);
                return;
            }
            if (config.debug) {
                // Same reasoning as the bucket branch above: no record store yet,
                // so this poisons the block's own current, deflated usable size.
                // SAFETY: `p` is a live tree-path allocation this instance
                // produced (this function's own contract), so
                // `ptrGetBlockHeader` finds its live header.
                const bl = block.ptrGetBlockHeader(p);
                const real_size = bl.size();
                // SAFETY: `p` is valid for `real_size` bytes, so poisoning its
                // deflated span stays within it; exclusively owned by this call
                // (about to be reclaimed).
                spomen_poison.fill(p, guard.deflate(config, real_size));
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
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
        pub fn freeWithSize(self: *Self, ptr: ?[*]u8, orig_size: usize) void {
            self.debugAssertNotMoved();
            const p = ptr orelse return;
            if (orig_size == 0) {
                // `p` is a live allocation this instance produced (this function's own
                // contract), which is exactly `free`'s.
                self.freeZeroOrigSize(p);
                return;
            }
            if (config.debug) {
                // Poisons *before* the reclaim below (either branch), at the
                // caller-supplied `orig_size` — unlike `free`'s pointer-only
                // dispatch, this one already has the exact original request
                // size in hand, matching HPHA's own
                // `initial_fill(ptr, record->size())` (`record->size()` is
                // asserted equal to this function's own `origSize` parameter in
                // HPHA's `debug_record_map::remove(ptr, size)` overload)
                // without needing the allocation-record store this port
                // doesn't have yet.
                // SAFETY: `p` is a live allocation this instance produced with
                // `orig_size` bytes (this function's own contract).
                spomen_poison.fill(p, orig_size);
            }
            if (bucket.isSmallAllocation(config, orig_size)) {
                // Inflate before recomputing the bucket index — `alloc`'s own
                // `bucketAlloc` chose this pointer's bucket from
                // `guard.inflate(config, orig_size)`, not the bare `orig_size`;
                // recomputing without it would land on a *different* bucket
                // under `config.debug` and free into the wrong size class's
                // free list. Ports HPHA's own `bucket_spacing_function(origSize
                // + MEMORY_GUARD_SIZE)` here exactly (`Cpp/hpha.h`'s
                // `free(void*, size_t)`).
                const inflated = guard.inflate(config, orig_size) orelse orig_size;
                // SAFETY: `p` is a live bucket-path allocation from bucket
                // `bucketSpacingFunction(inflated)` — this function's own
                // contract (`p` was allocated with this exact `orig_size` at
                // `DEFAULT_ALIGNMENT`) is exactly how `alloc`/`bucketAlloc`
                // picked its bucket.
                self.buckets.freeDirect(p, bucket.bucketSpacingFunction(inflated));
                return;
            }
            // SAFETY: `p` is a live tree-path allocation (`orig_size` is not small, this
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
        pub fn freeWithSizeAligned(self: *Self, ptr: ?[*]u8, orig_size: usize, old_alignment: usize) void {
            std.debug.assert(isHphaAlignment(old_alignment));
            self.debugAssertNotMoved();
            const p = ptr orelse return;
            if (orig_size == 0) {
                // `p` is a live allocation this instance produced (this function's own
                // contract), which is exactly `free`'s.
                self.freeZeroOrigSize(p);
                return;
            }
            if (config.debug) {
                // See `freeWithSize`'s identical poisoning comment — same
                // reasoning, at the same `orig_size` (not the
                // alignment-rounded value HPHA's own bucket-index computation
                // uses; `initial_fill` is always called with the plain
                // `origSize`, alignment plays no part in it —
                // `Cpp/hpha.h`'s `free(void*, size_t, size_t)`).
                // SAFETY: `p` is a live allocation this instance produced with
                // `orig_size` bytes (this function's own contract).
                spomen_poison.fill(p, orig_size);
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
            if (bucket.isSmallAllocation(config, orig_size) and alignment <= bucket.MAX_SMALL_ALLOCATION) {
                // Inflate before rounding to `alignment` — `bucketAllocAligned`
                // chose this pointer's bucket from
                // `roundUp(guard.inflate(config, orig_size), alignment)`, not
                // `roundUp(orig_size, alignment)`; the order (inflate, then
                // round) matters, not just that both happen. Ports HPHA's own
                // `bucket_spacing_function(round_up(origSize +
                // MEMORY_GUARD_SIZE, oldAlignment))` exactly (`Cpp/hpha.h`'s
                // `free(void*, size_t, size_t)`).
                const inflated = guard.inflate(config, orig_size) orelse orig_size;
                // SAFETY: `p` is a live bucket-path allocation from bucket
                // `bucketSpacingFunction(roundUp(inflated, old_alignment))` —
                // this function's own contract is exactly how
                // `allocAligned`'s `bucketAllocAligned` picked its bucket.
                self.buckets.freeDirect(p, bucket.bucketSpacingFunction(align_helpers.roundUp(inflated, alignment)));
                return;
            }
            // SAFETY: `p` is a live tree-path allocation, matching how `allocAligned` would
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
        fn freeZeroOrigSize(self: *Self, ptr: [*]u8) void {
            self.free(ptr);
        }

        /// Returns every fully-unused page/arena to the OS. Never called
        /// automatically — call periodically if reclaiming idle memory matters.
        /// Ports `allocator::purge`.
        pub fn purge(self: *Self) void {
            self.debugAssertNotMoved();
            self.tree.purge();
            self.buckets.purge();
        }

        /// Total bytes currently claimed from the OS across both paths. Ports
        /// `allocator::allocated`.
        pub fn allocated(self: *Self) usize {
            self.debugAssertNotMoved();
            return self.buckets.allocated() + self.tree.allocated();
        }
    };
}

const testing = std.testing;

// Every test below allocates through a fresh `Orisnitsa`, which (unlike
// `bucket.zig`'s `FakePage`/`tree.zig`'s `FakeArena`) has no seam to seed its
// `Buckets`/`Tree` from heap-backed memory — `Orisnitsa.init()` always starts
// empty, so any allocation reaches real `os.map`, exercised by native
// `zig build test` on all three CI OSes (zig-ci.yml). The no-OS-touch
// zero-size/null-pointer edge cases below need no such caveat.

test "alloc of zero returns null" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    try testing.expect(orisnitsa.alloc(0) == null);
    try testing.expect(orisnitsa.allocAligned(0, 64) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // must not have touched the OS
}

test "realloc of a null pointer acts as alloc of zero" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    try testing.expect(orisnitsa.realloc(null, 0) == null);
}

test "size and resize of null are zero" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    try testing.expectEqual(@as(usize, 0), orisnitsa.querySize(null));
    try testing.expectEqual(@as(usize, 0), orisnitsa.resize(null, 8));
}

test "free of null is a no-op" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    orisnitsa.free(null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "alloc bucket-path round-trip" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..64], 0xAB);
    try testing.expectEqual(@as(usize, 64), orisnitsa.querySize(ptr));
    orisnitsa.free(ptr);
}

test "alloc tree-path round-trip" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..size], 0xCD);
    try testing.expect(orisnitsa.querySize(ptr) >= size);
    orisnitsa.free(ptr);
}

test "allocAligned respects alignment on both paths" {
    var orisnitsa: Orisnitsa(.{}) = .init();
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
    var orisnitsa: Orisnitsa(.{}) = .init();
    const ptr = orisnitsa.alloc(8) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..8], 0xEF);
    const grown = orisnitsa.realloc(ptr, 200) orelse return error.TestUnexpectedResult; // "growth within buckets never fails"
    // The first 8 bytes must have been preserved across the grow.
    try testing.expect(std.mem.allEqual(u8, grown[0..8], 0xEF));
    orisnitsa.free(grown);
}

test "realloc moves a bucket allocation to the tree path" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..64], 0x11);
    const big = bucket.MAX_SMALL_ALLOCATION + 4096;
    const moved = orisnitsa.realloc(ptr, big) orelse return error.TestUnexpectedResult; // "growth onto the tree path never fails"
    // The first 64 bytes must have been preserved across the move.
    try testing.expect(std.mem.allEqual(u8, moved[0..64], 0x11));
    orisnitsa.free(moved);
}

test "realloc with size zero frees and returns null" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.realloc(ptr, 0) == null);
    // `free`/`realloc(_, 0)` never returns memory to the OS on its own — matching
    // HPHA, only an explicit `purge()` reclaims fully-unused pages/arenas.
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "the freed page must be reclaimable"
}

test "resize grows a tree allocation in place" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    const new_size = orisnitsa.resize(ptr, size + 64);
    try testing.expect(new_size >= size + 64);
    // `resize` grew `ptr` in place to at least `new_size` bytes.
    @memset(ptr[0..new_size], 0x22);
    orisnitsa.free(ptr);
}

test "freeWithSize matches plain free" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const a = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSize(a, 64);

    const b = orisnitsa.allocAligned(48, 128) orelse return error.TestUnexpectedResult; // "OS map failed"
    orisnitsa.freeWithSizeAligned(b, 48, 128);

    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "allocated tracks both paths and purge reclaims them" {
    var orisnitsa: Orisnitsa(.{}) = .init();
    const small = orisnitsa.alloc(32) orelse return error.TestUnexpectedResult; // "OS map failed"
    const large = orisnitsa.alloc(bucket.MAX_SMALL_ALLOCATION + 4096) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.allocated() > 0);
    orisnitsa.free(small);
    orisnitsa.free(large);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "every fully-unused page/arena must be reclaimed"
}

test "Orisnitsa(.{ .debug = true }) round-trips identically to the default instantiation" {
    // Proves the generic parameterization actually compiles and works for a
    // non-default Config, not just Orisnitsa(.{}) — see Zig/CONVENTIONS.md's
    // "comptime Toggles" section. `size == 64` stays on the bucket path, which
    // now carries its own guard ramp too (`bucketAlloc`, see the Phase 2 tests
    // below) — but that reservation is invisible through this observable
    // surface (`querySize`, `free`, `purge`), so the round-trip below must
    // still match the default instantiation exactly, even though the two
    // internally claim different bucket size classes for this request.
    var orisnitsa: Orisnitsa(.{ .debug = true }) = .init();
    const ptr = orisnitsa.alloc(64) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..64], 0xAB);
    try testing.expectEqual(@as(usize, 64), orisnitsa.querySize(ptr));
    orisnitsa.free(ptr);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

// ---- v0.2.0 Phase 2: tree-path guard bytes (real dispatch, not just
// `spomen_guard`'s own unit tests) ----

const debug_config: Config = .{ .debug = true };

test "treeAlloc hides the guard reservation from the caller" {
    // `querySize(ptr)` must report exactly what was requested — the guard
    // reservation (16 bytes trailing, real block size `size +
    // memoryGuardSize(config)`) must be completely invisible from the caller's
    // side of `querySize`/`alloc`.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const requested = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expectEqual(requested, orisnitsa.querySize(ptr));
    // `ptr` is a live tree-path allocation of exactly `requested` bytes, just
    // reported above — exactly `checkGuard`'s own contract.
    try testing.expect(spomen_guard.checkGuard(debug_config, ptr, requested));
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "treeAlloc ramp corruption is actually detectable" {
    // A real tree-path `alloc` must have actually written a checkable ramp, not
    // left the trailing bytes as whatever the arena's own initial content was —
    // otherwise the test above could pass by accident on a freshly-mapped,
    // zero-filled page (a ramp of all-zero bytes is *not* a valid
    // `seed, seed+1, ...` sequence unless `seed == 0` *and* every byte truly
    // increments). This corrupts one byte and confirms detection, the same
    // property `spomen_guard`'s own tests pin at the primitive level, exercised
    // here through the real dispatch instead of a synthetic buffer.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const requested = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    // INDEX: `requested < requested + memoryGuardSize(debug_config)`, and
    // `memoryGuardSize(debug_config) > 0`, so this stays within `ptr`'s valid
    // span.
    ptr[requested] = 0;
    // `ptr` is a live tree-path allocation of exactly `requested` bytes.
    try testing.expect(!spomen_guard.checkGuard(debug_config, ptr, requested));
    // Freed via `free` (pointer-based dispatch), not `freeWithSize`, since the
    // corrupted guard byte is no longer this test's concern once the check
    // above has run.
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "treeRealloc rewrites the guard ramp at the new size" {
    // `realloc` growing a tree-path allocation must (re)write the guard ramp at
    // the *new* size, whichever internal path `Tree.realloc` took (in-place
    // growth, neighbour merge, or allocate-copy-free) — `treeRealloc`'s own doc
    // argues this from `Tree.realloc`'s contract; this exercises it for real.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const small = bucket.MAX_SMALL_ALLOCATION + 64;
    const big = bucket.MAX_SMALL_ALLOCATION + 8192;
    const ptr = orisnitsa.alloc(small) orelse return error.TestUnexpectedResult; // "OS map failed"
    const grown = orisnitsa.realloc(ptr, big) orelse return error.TestUnexpectedResult; // "growth never fails here"
    try testing.expectEqual(big, orisnitsa.querySize(grown));
    // `grown` is a live tree-path allocation of exactly `big` bytes.
    try testing.expect(spomen_guard.checkGuard(debug_config, grown, big));
    orisnitsa.free(grown);
    orisnitsa.purge();
}

test "treeResize rewrites the guard ramp on growth" {
    // `resize` growing a tree-path allocation in place must likewise (re)write
    // the guard ramp at the new size — HPHA's own `debug_update` does the same
    // on every `resize`, not only on `realloc`.
    //
    // This is the scenario that would have caught the naive "only rewrite when
    // new_size > size" bug `treeResize`'s own doc warns against: growing to
    // land *exactly* on the caller's requested target still moves the guard's
    // position (from the old, smaller size's end to the new one's), even though
    // `new_size == size` in that case. The sizes below are chosen so `resize`
    // splits off the merged neighbour's excess and returns exactly the
    // (16-byte-aligned) target rather than the whole merged block — mirroring
    // `orisnik`'s identical test setup, which pins the same real behaviour.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const small = bucket.MAX_SMALL_ALLOCATION + 64;
    const ptr = orisnitsa.alloc(small) orelse return error.TestUnexpectedResult; // "OS map failed"
    // Free the immediately-following block first so `resize` has room to grow
    // into (a lone allocation has no free neighbour to grow into).
    const next_door = orisnitsa.alloc(bucket.MAX_SMALL_ALLOCATION + 64) orelse return error.TestUnexpectedResult; // "OS map failed"
    // `next_door` is physically right after `ptr` — the tree path serves
    // sequential same-size requests from one freshly-grown arena in order.
    orisnitsa.free(next_door);
    const target = small + 128;
    const new_size = orisnitsa.resize(ptr, target);
    try testing.expect(new_size >= target); // "must have grown into the freed neighbour"
    // `ptr` is a live tree-path allocation of exactly `new_size` bytes
    // (`resize`'s own return value, just asserted above).
    try testing.expect(spomen_guard.checkGuard(debug_config, ptr, new_size));
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

// ---- v0.2.0 Phase 2: bucket-path guard bytes (real dispatch, not just
// `spomen_guard`'s own unit tests) ----

test "bucketAlloc hides the guard reservation from the caller" {
    // `querySize(ptr)` must report exactly what was requested (post-clamp) — the
    // guard reservation must be as invisible on the bucket path as it is on the
    // tree path. `MAX_SMALL_ALLOCATION - memoryGuardSize(config)` (the shifted
    // `isSmallAllocation` boundary — see that function's own doc) is the
    // largest request that still stays on the bucket path under this config.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const requested = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config);
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expectEqual(requested, orisnitsa.querySize(ptr));
    // `ptr` is a live bucket-path allocation of exactly `requested` bytes, just
    // reported above — exactly `checkGuard`'s own contract.
    try testing.expect(spomen_guard.checkGuard(debug_config, ptr, requested));
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "bucketAlloc ramp corruption is actually detectable" {
    // Same corruption-detection property as "treeAlloc ramp corruption is
    // actually detectable", exercised on the bucket path — the two guard
    // mechanisms share one primitive (`spomen_guard`) but wire into dispatch
    // through entirely separate code (`bucketAlloc` vs `treeAlloc`), so each
    // earns its own real-dispatch test.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const requested = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config);
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    // INDEX: `requested < requested + memoryGuardSize(debug_config)`, and the
    // slot is at least that large (its own bucket class), so this stays within
    // `ptr`'s valid span.
    ptr[requested] = 0;
    // `ptr` is a live bucket-path allocation of exactly `requested` bytes.
    try testing.expect(!spomen_guard.checkGuard(debug_config, ptr, requested));
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "bucketRealloc rewrites the guard ramp at the new size" {
    // `realloc` growing a bucket-path allocation in place (staying within the
    // same or a larger size class) must (re)write the guard ramp at the new
    // size — `bucketRealloc`'s own doc argues this from HPHA's
    // `bucket_realloc`/`debug_replace` pairing; this exercises it for real,
    // including the "moves to a larger class" path (`Buckets.realloc`'s own
    // internal alloc-copy-free).
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const small = 8;
    const big = 200;
    const ptr = orisnitsa.alloc(small) orelse return error.TestUnexpectedResult; // "OS map failed"
    const grown = orisnitsa.realloc(ptr, big) orelse return error.TestUnexpectedResult; // "growth never fails here"
    // `grown` is a live allocation `orisnitsa` produced.
    try testing.expectEqual(big, orisnitsa.querySize(grown));
    // `grown` is a live bucket-path allocation of exactly `big` bytes.
    try testing.expect(spomen_guard.checkGuard(debug_config, grown, big));
    orisnitsa.free(grown);
    orisnitsa.purge();
}

test "bucketResize rewrites the guard ramp at the same position" {
    // `resize` on a bucket-path allocation never actually grows the slot (its
    // class is fixed once chosen), but HPHA's own `resize` still (re)writes the
    // guard unconditionally every call — `bucketResize`'s own doc explains why;
    // this confirms the ramp survives a `resize` call intact (rewritten at the
    // same, unchanged position) rather than merely never having been disturbed.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const ptr = orisnitsa.alloc(8) orelse return error.TestUnexpectedResult; // "OS map failed"
    const reported = orisnitsa.querySize(ptr);
    const new_size = orisnitsa.resize(ptr, 8);
    try testing.expectEqual(reported, new_size); // "a bucket slot's class never changes size"
    // `ptr` is a live bucket-path allocation of exactly `new_size` bytes.
    try testing.expect(spomen_guard.checkGuard(debug_config, ptr, new_size));
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "freeWithSize recomputes the same guard-inflated bucket" {
    // The fix this phase's design depended on most: `freeWithSize` and
    // `freeWithSizeAligned` must recompute the *same*, guard-inflated bucket
    // index `bucketAlloc`/`bucketAllocAligned` originally chose — without
    // inflating before recomputing, these would free into the *wrong* size
    // class's free list, corrupting it silently (no bounds check catches a
    // free into a real but incorrect bucket). Exercises every small size once,
    // both the plain and aligned forms, matching "zero-alignment free picks
    // the bucket alloc used"'s exhaustive style for the analogous non-guard
    // invariant.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var size: usize = 1;
    while (size <= bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config)) : (size += 1) {
        const a = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
        // `a` is a live allocation `orisnitsa` produced with `size` at
        // `DEFAULT_ALIGNMENT` — exactly this function's own contract.
        orisnitsa.freeWithSize(a, size);

        const b = orisnitsa.allocAligned(size, block.DEFAULT_ALIGNMENT) orelse return error.TestUnexpectedResult; // "OS map failed"
        // `b` is a live allocation `orisnitsa` produced with `size` at
        // `DEFAULT_ALIGNMENT` — exactly this function's own contract.
        orisnitsa.freeWithSizeAligned(b, size, block.DEFAULT_ALIGNMENT);
    }
    orisnitsa.purge();
    // "every block must have been freed into its real bucket, not a
    //  differently-sized neighbour's"
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "bucket-to-tree realloc keeps the new guard ramp and the payload" {
    // A `realloc` promoting a bucket allocation onto the tree path must copy only
    // the old slot's *payload* (`elem_size - memoryGuardSize(config)`, HPHA's own
    // `memcpy` length in `Cpp/hpha.h`'s `realloc`), never its trailing guard ramp:
    // `treeAlloc` has already written the new block's own ramp at
    // `[size, size + memoryGuardSize(config))`, and copying the whole inflated slot
    // lands the old ramp's tail bytes on top of it whenever `elem_size > size` — the
    // window this test picks (a 256-byte slot promoted to a 250-byte request).
    // Latent until guard-checking is wired into dispatch, when it would surface as
    // a false corruption report.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const old = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config); // a full 256-byte slot
    const new = bucket.MAX_SMALL_ALLOCATION - 6; // 250: no longer fits a bucket once guarded
    const ptr = orisnitsa.alloc(old) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..old], 0x5A);
    const moved = orisnitsa.realloc(ptr, new) orelse return error.TestUnexpectedResult; // "OS map failed"
    // Usable size, not requested size: the tree rounds a block up to a
    // `BlockHeader`-size multiple, so this may exceed `new` (here 256 vs 250).
    try testing.expect(orisnitsa.querySize(moved) >= new);
    try testing.expect(spomen_guard.checkGuard(debug_config, moved, new)); // "old slot's guard bytes must not clobber the new block's ramp"
    try testing.expect(std.mem.allEqual(u8, moved[0..old], 0x5A)); // "the caller's `old` payload must survive the promotion"
    orisnitsa.free(moved);
    orisnitsa.purge();
}

test "bucket-to-tree realloc-aligned keeps the new guard ramp and the payload" {
    // `reallocAligned`'s twin of the test above.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const alignment = 16;
    const old = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config);
    const new = bucket.MAX_SMALL_ALLOCATION - 6;
    const ptr = orisnitsa.allocAligned(old, alignment) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..old], 0x5A);
    const moved = orisnitsa.reallocAligned(ptr, new, alignment) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(spomen_guard.checkGuard(debug_config, moved, new));
    try testing.expect(std.mem.allEqual(u8, moved[0..old], 0x5A));
    orisnitsa.free(moved);
    orisnitsa.purge();
}

// ---- v0.2.0 Phase 2: payload poisoning ----

test "treeAlloc poisons the fresh payload" {
    // A fresh tree-path allocation's payload must actually read as the poison
    // pattern before the caller writes anything — not merely "some function
    // called `spomen_poison.fill` somewhere," verified end to end through the
    // real dispatch.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    for (0..size) |i| {
        try testing.expectEqual(spomen_poison.byteAt(i), ptr[i]);
    }
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "bucketAlloc poisons the fresh payload" {
    // Same property as "treeAlloc poisons the fresh payload", on the bucket
    // path — wired through entirely separate dispatch (`bucketAlloc`, not
    // `treeAlloc`), so it earns its own real-dispatch test.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const size = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config);
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    for (0..size) |i| {
        try testing.expectEqual(spomen_poison.byteAt(i), ptr[i]);
    }
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "free poisons the payload before reclaim" {
    // `free` must poison the payload *before* the underlying reclaim — reading
    // it back afterward is, from the pointer's own point of view,
    // indistinguishable from a use-after-free read (which is exactly the
    // scenario this mechanism exists to make loud rather than silent): this
    // test is that scenario, deliberately, on memory this instance still owns
    // the mapping for (not yet `purge()`d), the same way HPHA's own
    // `debug_remove`-before-`bucket_free`/`tree_free` order intends the poison
    // to be observed. Zig has no Miri-equivalent aliasing gate, but the same
    // justification applies here as it does for `orisnik`'s identical test:
    // the OS mapping backing `ptr` is still live (this instance never unmapped
    // it), and this test is the sole observer of it, before and after the
    // `free` call.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const size = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult; // "OS map failed"
    @memset(ptr[0..size], 0xAB);
    orisnitsa.free(ptr);
    for (0..size) |i| {
        try testing.expectEqual(spomen_poison.byteAt(i), ptr[i]);
    }
    orisnitsa.purge();
}

test "calloc zero-fill overwrites the poison" {
    // `calloc` composes with allocation-time poisoning exactly as HPHA does:
    // `alloc` poisons, then `calloc`'s own unconditional zero-fill overwrites
    // it — no special-casing either way, so the caller sees zeros, never
    // poison.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    const count = 4;
    const size = 64;
    const ptr = orisnitsa.calloc(count, size) orelse return error.TestUnexpectedResult; // "OS map failed"
    for (ptr[0 .. count * size]) |b| {
        try testing.expectEqual(@as(u8, 0), b);
    }
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

// ---- v0.1.1 regression tests (docs/audits/2026-08-29-pre-v0.2.0-audit.md) ----

test "oversized requests are declined, not wrapped" {
    // F1. Every one of these overflows an intermediate `+` in the tree path's size
    // arithmetic. Before v0.1.1 they wrapped: `ReleaseFast` returned a pointer to a
    // *zero-byte* block for a `maxInt(usize)` request, and `Debug`/`ReleaseSafe`
    // tripped `std.mem.alignForward`'s own overflow check.
    var orisnitsa: Orisnitsa(.{}) = .init();
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
    var orisnitsa: Orisnitsa(.{}) = .init();
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

    var orisnitsa: Orisnitsa(.{}) = .init();
    // Zero size still declines, exactly as the unaligned path does — this is the
    // `alloc` delegation working, not a special case.
    try testing.expect(orisnitsa.allocAligned(0, 0) == null);
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "reallocAligned with zero size and zero alignment frees" {
    // F5, the `main.cpp` call itself: must free and report null rather than abort.
    var orisnitsa: Orisnitsa(.{}) = .init();
    const ptr = orisnitsa.allocAligned(64, 0) orelse return error.TestUnexpectedResult; // "OS map failed"
    try testing.expect(orisnitsa.reallocAligned(ptr, 0, 0) == null);
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated()); // "the freed page must be reclaimable"
}

test "freeWithSizeAligned accepts zero alignment" {
    // F5's downstream pair: an `allocAligned(_, 0)` allocation must be freeable
    // through `freeWithSizeAligned(_, _, 0)`, which is what a C caller mirroring its
    // own allocation call would write.
    var orisnitsa: Orisnitsa(.{}) = .init();
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
    var orisnitsa: Orisnitsa(.{}) = .init();

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
    var orisnitsa: Orisnitsa(.{}) = .init();
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
    var orisnitsa: Orisnitsa(.{}) = .init();
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
    var orisnitsa: Orisnitsa(.{}) = .init();
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

/// `rand.zig`'s `VintageRand`, promoted to production for the guard-byte ramp
/// (see this file's own `guard_rng` field) and originally introduced right here
/// as a test-only stress-workload helper — see `rand.zig`'s module doc for the
/// full history and golden-vector provenance. Aliased under its original local
/// name so the stress test below (and its two golden-vector tests, now living in
/// `rand.zig` itself) reads unchanged.
const VintageRand = rand.VintageRand;

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
    //
    // `N` is the full 20 000 in every optimization mode. `orisnik` scales its own
    // copy down under Miri (where interpretation costs ~47 min at this size); Zig's
    // safety-checked builds run at native speed, so there is nothing to trade off
    // here — the two ports differ in the *cost* of their verification gate, not in
    // the workload they intend.
    const N: usize = 20_000;
    const Block = struct { ptr: [*]u8, size: usize, stamp: u8 };

    for ([_]bool{ false, true }) |use_alignment| {
        var orisnitsa: Orisnitsa(.{}) = .init();
        var rng: VintageRand = .init(1234); // main.cpp's own seed
        // The stamp travels with the block: the free loop below relocates entries, so
        // a slot index does not identify one.
        const live = try testing.allocator.alloc(Block, N);
        defer testing.allocator.free(live);
        var bucket_path: usize = 0;
        var tree_path: usize = 0;

        for (0..N) |i| {
            const sz = rng.size();
            if (bucket.isSmallAllocation(.{}, sz)) bucket_path += 1 else tree_path += 1;
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
