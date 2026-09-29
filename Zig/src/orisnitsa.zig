// SPDX-License-Identifier: MIT OR Apache-2.0
//! The top-level allocator: dispatches every request between the bucket path
//! (small allocations) and the tree path (everything else), and owns nothing else.
//!
//! Ports the single-threaded slice of `allocator`'s public surface, mirroring
//! `orisnik`'s `orisnik.rs` — `MULTITHREADED` (mutex-guarded buckets/tree) is out
//! of scope until v2.x, see `ROADMAP.md`. `DEBUG_ALLOCATOR` (guard bytes,
//! allocation records, `check()`/`report()`) is v0.2.0's own milestone, landing
//! incrementally behind `config.debug` (`guard.zig`, `spomen_guard.zig`,
//! `spomen_poison.zig`, `spomen_record.zig`/`spomen_book.zig`/`spomen_store.zig`,
//! `spomen_failure.zig`). The `tree*`/`bucket*` methods below are pure size-class
//! shims (they only fold the guard reservation in and out); the debug *hooks*
//! (`debugAdd`/`debugRemove`/`debugReplace`/`debugUpdate`/`debugCheck`/`debugPurge`,
//! HPHA's `debug_*`) own the guard seed, the ramp, the allocation record and the
//! poisoning, and are called by the public methods at the points HPHA's own
//! `alloc`/`realloc`/`resize`/`free`/`purge` call them — except one extra, state-neutral
//! `debugCheck` in `reallocAligned`'s misaligned-move branch. `check()`, `report()` and leak
//! detection are here too: `deinit()` returns all idle memory in every build and, with
//! `config.debug`, audits and reports live blocks then fails on the leak. With `config.debug` false,
//! `guard.memoryGuardSize(config)` is 0, so every
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
const spomen_record = @import("spomen_record.zig");
const spomen_store = @import("spomen_store.zig");
const spomen_failure = @import("spomen_failure.zig");
const rand = @import("rand.zig");
const tree_mod = @import("tree.zig");

const Config = spomen.Config;
const Record = spomen_record.Record;
const Source = spomen_record.Source;
const Corruption = spomen_failure.Corruption;
const VerifyError = spomen_failure.VerifyError;
const OrisError = spomen_failure.OrisError;

/// How many times each debug hook has run — a plain-counter seam that lets tests prove
/// the hooks are actually wired into dispatch at HPHA's call sites. Zig cannot catch a
/// panic, so a deleted hook call would otherwise change nothing observable. The seam
/// counts hook *invocations* only; it never lets dispatch continue past a detected
/// corruption (see `Zig/CONVENTIONS.md`). `report()` does not use it: it exists for the wiring tests.
/// Counted at the point a hook does real work: `adds`/`replaces` skip a null pointer
/// (a failed allocation/realloc is not an add/replace).
pub const HookStats = struct {
    /// `debugAdd` calls that received a real (non-null) allocation.
    adds: usize = 0,
    /// `debugRemove` calls (every free path).
    removes: usize = 0,
    /// The subset of `removes` that carried a caller-supplied `orig_size`
    /// (`freeWithSize`/`freeWithSizeAligned`) — proves the size reaches the check.
    removes_with_size: usize = 0,
    /// `debugReplace` calls that received a non-null new pointer (a successful realloc).
    replaces: usize = 0,
    /// `debugUpdate` calls (every `resize`).
    updates: usize = 0,
    /// `debugCheck` calls (`realloc`/`reallocAligned`/`resize` before touching the block).
    checks: usize = 0,
    /// `debugPurge` calls.
    purges: usize = 0,
};

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
/// decide whether a pointer belongs to the bucket or the tree path. Under
/// `config.debug` the record store adds two more: its book's page-list sentinel and
/// its address index's tree sentinel (`spomen_book.zig`/`spomen_store.zig`).
///
/// Copying the value out of its original storage — `var b = a;`, returning it by
/// value from a helper, appending it to an `ArrayList` — leaves all of them pointing at
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
/// **`deinit` must be called**, in every build: it returns every idle bucket page and tree
/// arena to the OS (HPHA's destructor begins with `purge()`), and with `config.debug` it
/// also returns the record store's pages (which nothing else does — `purge` only returns
/// the *spare* ones) and audits for leaks: any allocation still live is reported to stderr
/// and then fails the teardown with a panic, after everything else has been released
/// (HPHA's destructor asserts). Pages that still hold a live block stay mapped. Without
/// `config.debug` nothing is checked or printed.
///
/// Generic over the `spomen` debug-subsystem `Config` (see `Zig/CONVENTIONS.md`'s
/// "`comptime` Toggles" section): `Orisnitsa(config)`, not a plain `Orisnitsa`
/// value with a runtime `config` field, is what gives the debug subsystem
/// (guard bytes, allocation records, hooks) a compiler-enforced
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
        /// Every live allocation's debug record, indexed by address (`spomen`; HPHA's
        /// `mDebugMap`). `void` (zero-size) unless `config.debug`. Owns OS pages: the
        /// owner must call `deinit`.
        records: if (config.debug) spomen_store.RecordStore else void =
            if (config.debug) spomen_store.RecordStore.init() else {},
        /// Bytes currently outstanding on the bucket path, each block counted as
        /// `requested size + memoryGuardSize(config)`. Ports
        /// `mTotalRequestedSizeBuckets`. `void` unless `config.debug`.
        requested_buckets: if (config.debug) usize else void = if (config.debug) 0 else {},
        /// `requested_buckets`'s tree-path twin. Ports `mTotalRequestedSizeTree`.
        requested_tree: if (config.debug) usize else void = if (config.debug) 0 else {},
        /// How many times each debug hook has run — the wiring seam (see `HookStats`).
        /// `void` unless `config.debug`.
        stats: if (config.debug) HookStats else void = if (config.debug) .{} else {},

        /// Builds a fresh, empty allocator instance — no OS memory is claimed until
        /// the first allocation. Ports `allocator::allocator` (the default
        /// constructor). A pure value (no address-dependent state at construction —
        /// see `list.zig`'s lazy-sentinel-init doc), so `var ALLOCATOR: Orisnitsa(.{}) =
        /// .init();` is `comptime`-constructible, the standard global-allocator
        /// pattern's own requirement.
        pub fn init() Self {
            return .{};
        }

        /// Tears the allocator down: returns every fully-idle bucket page and tree
        /// arena to the OS — in **every** build (HPHA's `~allocator` begins with
        /// `purge()`) — and, with `config.debug`, first audits and reports any
        /// allocation still live, then fails on a leak once everything else has been
        /// released (HPHA's destructor asserts). Pages that still hold a live block stay
        /// mapped. Zig has no `Drop`, so the owner must call this; the instance must not
        /// be used afterwards. Without `config.debug` nothing is checked or printed.
        ///
        /// Order (debug): (1) if `records.len() > 0`, print to stderr a summary line, the
        /// first problem the audit finds and the report (head, one line per live record,
        /// foot), before the record store is released — mirroring HPHA's check-then-report.
        /// Unlike the public `check` (address order), this audit and the report walk the
        /// records in *storage* order, so the "first problem" is the first in storage order
        /// (see `debugTeardownTo`); (2) `purge()`; (3) `records.deinit()`;
        /// (4) if anything leaked, `std.debug.panic`. Zig panics do not unwind, so there is
        /// no "already panicking" case to skip and no `disabled` latch. The non-panicking
        /// part is `deinitReturningLeaks`, which the tests call.
        pub fn deinit(self: *Self) void {
            const leaked = self.deinitReturningLeaks();
            if (config.debug and leaked > 0) spomen_failure.failOnLeak(leaked);
        }

        /// `deinit` without the final panic: audits and reports leaks (debug), releases
        /// all idle memory and the record store, and returns how many allocations were
        /// still live (always `0` without `config.debug`). Exists so a test can observe a
        /// leaking teardown, which `deinit` itself ends in a panic no Zig test can catch.
        fn deinitReturningLeaks(self: *Self) usize {
            const leaked = if (config.debug) self.debugTeardown() else 0;
            self.purge();
            if (config.debug) self.records.deinit();
            return leaked;
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

        // ---- size-class wrappers ---------------------------------------------------
        //
        // Every `tree*`/`bucket*` method below is the single place the guard
        // reservation (`guard.inflate`/`guard.deflate`, an identity when
        // `config.debug` is false) is folded into a size before it reaches `Tree`/
        // `Buckets`, which are guard-oblivious. They do *not* write guard bytes,
        // poison payloads or touch the record store: that is the `debug*` hooks'
        // job, called by the public methods below exactly where HPHA's `alloc`/
        // `realloc`/`resize`/`free` call `debug_add`/`debug_replace`/`debug_update`/
        // `debug_remove`. (Before v0.2.0 Phase 4 the guard write lived here; it moved
        // so the guard seed, the record and the poisoning all happen in one place,
        // in HPHA's order.)

        /// The tree path's fresh-allocation shim: inflates `size` by the guard
        /// reservation. `size` is the caller-visible request.
        fn treeAlloc(self: *Self, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            return self.tree.alloc(inflated);
        }

        /// `treeAlloc`'s aligned counterpart.
        fn treeAllocAligned(self: *Self, size: usize, alignment: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            return self.tree.allocAligned(inflated, alignment);
        }

        /// `treeAlloc`'s realloc counterpart: grows/shrinks/moves an *existing*
        /// tree-path allocation. `size` is the new caller-visible target;
        /// `tree.Tree.realloc`'s contract guarantees the returned pointer is valid
        /// for at least the inflated size, whichever path it took internally.
        ///
        /// `ptr` must be a still-live tree-path allocation this instance
        /// produced.
        fn treeRealloc(self: *Self, ptr: [*]u8, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            return self.tree.realloc(ptr, inflated);
        }

        /// `treeRealloc`'s aligned counterpart.
        ///
        /// `ptr` must be a still-live tree-path allocation this instance
        /// produced, itself already aligned to `alignment`.
        fn treeReallocAligned(self: *Self, ptr: [*]u8, size: usize, alignment: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse return null;
            return self.tree.reallocAligned(ptr, inflated, alignment);
        }

        /// The tree path's in-place-only counterpart: grows `ptr` without ever
        /// moving it and returns the resulting caller-visible (deflated) size,
        /// whether or not it grew.
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
            return guard.deflate(config, real_size);
        }

        /// The bucket path's fresh-allocation shim for a plain (unaligned)
        /// request. `size` is the caller-visible, already-clamped request; the
        /// guard reservation is folded into the bucket-index computation here but
        /// never stripped back off, because a bucket slot's size is its fixed
        /// class (`querySize`/`resize` deflate it). The `orelse size` fallback is
        /// unreachable: every caller has just established `isSmallAllocation`, so
        /// `inflate` cannot overflow (the other `bucket*` shims and the sized
        /// `freeWithSize*` paths rely on the same bound).
        fn bucketAlloc(self: *Self, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse size;
            return self.buckets.allocDirect(bucket.bucketSpacingFunction(inflated));
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
            return self.buckets.allocDirect(
                bucket.bucketSpacingFunction(align_helpers.roundUp(inflated, alignment)),
            );
        }

        /// The bucket path's shim for growing/shrinking an *existing* bucket-path
        /// allocation (never a move — `Buckets.realloc` only ever grows into a
        /// larger size class; `realloc`'s own cross-path logic handles the
        /// bucket->tree case). `size` is the caller's already-clamped target.
        ///
        /// `ptr` must be a still-live bucket-path allocation this instance
        /// produced.
        fn bucketRealloc(self: *Self, ptr: [*]u8, size: usize) ?[*]u8 {
            const inflated = guard.inflate(config, size) orelse size;
            return self.buckets.realloc(ptr, inflated);
        }

        /// The bucket path's `resize` counterpart. Bucket slots never actually
        /// grow — this only ever reports the slot's own fixed, deflated size.
        ///
        /// `ptr` must be a still-live bucket-path allocation this instance
        /// produced.
        fn bucketResize(_: *Self, ptr: [*]u8) usize {
            // SAFETY: `ptr` is a still-live bucket-path allocation this instance
            // produced (this function's own contract), exactly what
            // `ptrGetPage` requires; the recovered `page` is therefore live too.
            const page = bucket.ptrGetPage(ptr);
            return guard.deflate(config, page.elemSize());
        }

        // ---- debug hooks (`config.debug` only) -------------------------------------
        //
        // HPHA's `allocator::debug_add`/`debug_remove`/`debug_replace`/`debug_update`/
        // `debug_check`/`debug_purge` (`Cpp/hpha.cpp:863-950`), called by the public
        // methods below at the points HPHA's own `alloc`/`realloc`/`resize`/
        // `free`/`purge` call them (`Cpp/hpha.h:1264-1440`), except one deliberate,
        // state-neutral strengthening: `reallocAligned`'s misaligned-move branch runs
        // `debugCheck` *first*, before it reads the block's page marker/header (HPHA
        // verifies only later, inside `free`). Every call site is inside
        // an `if (config.debug)` branch, so for `Orisnitsa(.{})` none of these bodies is
        // ever analyzed and no `records`/counter field exists.
        //
        // Each hook owns one whole responsibility, so the guard seed, the record and
        // the poison can never disagree: `debugAdd` draws the guard seed, writes the
        // ramp, records the allocation (remembering the seed) and poisons the payload;
        // `debugRemove` verifies the block, poisons at the *recorded* size and retires
        // the record; `debugReplace`/`debugUpdate` rewrite the ramp with a fresh seed
        // and retarget the record.
        //
        // # Callstack frame
        // The entry points read `@returnAddress()` only under `config.debug` (it is
        // `0` otherwise, so `Orisnitsa(.{})` carries nothing). If an entry point is
        // inlined into user code the first captured frame is one level further up
        // (harmless); users of the `std.mem.Allocator` vtable or the C API see a first
        // frame inside that shim, since the shim is the entry point's caller.
        //
        // Hooks that record a callstack take `first_address`: the public method that
        // was called by the user passes its own `@returnAddress()`, so a trace starts
        // at the *caller* of `alloc`/`realloc`/`resize`/..., not somewhere inside the
        // allocator (see `Record.captureCallstack`).
        //
        // # No re-entrancy guard, no global-allocator rule
        // Unlike `orisnik` (whose `Backtrace` capture *allocates*, so an instance used
        // as the global allocator re-enters itself and needs a `busy` flag and a
        // no-callstack mode), nothing here can re-enter the allocator: the capture is
        // `std.debug.captureCurrentStackTrace`, a lock-free frame walk into a fixed
        // `[MAX_CALLSTACK_DEPTH]usize` buffer that allocates nothing, and the record
        // store maps its pages through `os.map`, never through an allocator. So there
        // is no `busy`/`disabled` state and no re-entrancy rule to follow. (This is
        // not a claim that a debug instance can be installed anywhere: `allocator.zig`
        // and `capi.zig` are fixed to `Orisnitsa(.{})`, so in this repo a debug
        // instance is reachable only through the type's own methods, never through the
        // `std.mem.Allocator` vtable or the C API.)
        //
        // # Failure
        // Detected corruption ends in `spomen_failure.fail` (`std.debug.panic`).
        // Zig tests cannot catch a panic, so detection is factored into the pure
        // `verify`, which returns an error value and is tested directly; the tests do
        // not (and there is deliberately no seam to) continue past a detected
        // corruption.

        /// Hook-invocation counters. See `HookStats`.
        pub fn hookStats(self: *const Self) HookStats {
            comptime std.debug.assert(config.debug);
            return self.stats;
        }

        /// Total bytes callers currently have outstanding, each block counted with
        /// its guard reservation (`requested size + memoryGuardSize(config)`) —
        /// HPHA's `requested()`, the sum of `mTotalRequestedSizeBuckets` and
        /// `mTotalRequestedSizeTree`. Only available when `config.debug`.
        pub fn requested(self: *const Self) usize {
            comptime std.debug.assert(config.debug);
            return self.requested_buckets + self.requested_tree;
        }

        /// The running total for `source`'s path.
        fn requestedFor(self: *Self, source: Source) *usize {
            return switch (source) {
                .buckets => &self.requested_buckets,
                .tree => &self.requested_tree,
            };
        }

        /// Reacts to detected corruption: builds the diagnostic (with the record's
        /// recorded callstack addresses, if the pointer had a record) and panics.
        /// Never returns.
        fn failWith(what: Corruption, ptr: [*]u8, record: ?*const Record) noreturn {
            @branchHint(.cold);
            var buf: [spomen_failure.MESSAGE_CAPACITY]u8 = undefined;
            spomen_failure.fail(spomen_failure.describe(&buf, what, ptr, record));
        }

        /// `failWith` for a `verify` error: recovers the record and the compared
        /// size from `ptr`/`orig_size`.
        fn failVerify(self: *Self, err: VerifyError, ptr: [*]u8, orig_size: ?usize) noreturn {
            @branchHint(.cold);
            const record = self.records.find(ptr);
            const what: Corruption = switch (err) {
                error.UnknownPointer => .unknown_pointer,
                // `orig_size` is non-null exactly when `verify` can return this.
                error.SizeMismatch => .{ .size_mismatch = comparableSize(record.?.source, orig_size.?) },
                error.GuardOverrun => .guard_overrun,
            };
            failWith(what, ptr, record);
        }

        /// `given`, as `verify` compares it against a record served by `source`: clamped
        /// to the minimum allocation on the bucket path (the record holds the clamped
        /// size), raw on the tree path (the record holds the raw size).
        fn comparableSize(source: Source, given: usize) usize {
            return switch (source) {
                .buckets => bucket.clampSmallAllocation(given),
                .tree => given,
            };
        }

        /// Checks `ptr` against its record without changing anything: a record must
        /// exist, `orig_size` (a sized free's caller-supplied size), if given, must
        /// agree with the recorded size, and the guard ramp must be intact. The
        /// detection half of `debugRemove`/`debugCheck`, kept a plain value so it is
        /// directly testable.
        ///
        /// `orig_size` is compared the way the record holds it (`comparableSize`): a
        /// *bucket*-path record holds the minimum-size-clamped size (`alloc(5)` records
        /// 8), so `orig_size` is clamped before the compare; a *tree*-path record holds
        /// the raw size (`allocAligned(5, 512)` and a tree-path `realloc(p, 5)` both
        /// record 5), so `orig_size` is compared raw. HPHA compares the raw value
        /// everywhere, so its own `free(p, 5)` of an `alloc(5)` would trip its assert on
        /// a perfectly legal call — a 2007 debug-mode bug this port does not reproduce
        /// (see `Cpp/ERRATA.md`) — while its raw compare was right for the tree path,
        /// which is why the clamp must not be applied there.
        ///
        /// The block at `ptr` must still be live if a record exists for it (the
        /// callers' contract: `ptr` is a live allocation this instance produced).
        fn verify(self: *Self, ptr: [*]u8, orig_size: ?usize) VerifyError!*Record {
            const record = self.records.find(ptr) orelse return error.UnknownPointer;
            if (orig_size) |given| {
                if (comparableSize(record.source, given) != record.size) return error.SizeMismatch;
            }
            // SAFETY: the record describes the live allocation at `ptr` (this
            // function's contract), valid for `size + memoryGuardSize(config)` bytes and
            // readable for its trailing guard, which is all `checkGuard` reads.
            if (!record.checkGuard(config)) return error.GuardOverrun;
            return record;
        }

        /// Records a fresh allocation: draws a guard seed, writes the ramp, records
        /// `ptr` (remembering the seed and capturing the callstack) and poisons the
        /// payload. If the record store cannot get memory the allocation is undone
        /// and `null` returned — a value, never a panic, exactly like HPHA's
        /// `debug_add`. `ptr == null` (the underlying allocation failed) passes
        /// straight through. Ports `debug_add`.
        ///
        /// `size` is the caller-visible size, already clamped on the bucket path.
        fn debugAdd(self: *Self, first_address: usize, ptr: ?[*]u8, size: usize, source: Source) ?[*]u8 {
            const p = ptr orelse return null;
            self.stats.adds += 1;
            // SAFETY: `p` is a live allocation this instance just produced, exactly
            // what `querySize` requires.
            std.debug.assert(size <= self.querySize(p));
            const seed = self.nextGuardSeed();
            // SAFETY: `p` is valid for `size + memoryGuardSize(config)` bytes
            // (allocated with that inflated size), exclusively owned (not yet handed
            // to any caller).
            spomen_guard.writeGuard(config, p, size, seed);
            const record = Record.initAt(first_address, p, size, source, seed);
            if (self.records.addRecord(record)) {
                const counter = self.requestedFor(source);
                counter.* += size + guard.memoryGuardSize(config);
                // SAFETY: `p` is valid for `size` bytes, exclusively owned; the guard
                // ramp lies past them, so the two ranges are disjoint.
                spomen_poison.fill(p, size);
                return p;
            }
            // The record store could not get a page: give the block back and report
            // failure as a value (HPHA: `bucket_free(ptr)`/`tree_free(ptr)`,
            // `return NULL`).
            switch (source) {
                // SAFETY: `p` is a live bucket-path allocation, not handed out.
                .buckets => self.buckets.free(p),
                // SAFETY: `p` is a live tree-path allocation, not handed out.
                .tree => self.tree.free(p),
            }
            return null;
        }

        /// Verifies `ptr` and retires its record, poisoning the payload at the
        /// *recorded* size first. Called before the reclaim. `orig_size` is a sized
        /// free's caller-supplied size. Panics on corruption (see the hooks' section
        /// comment). Ports `debug_remove` (both overloads).
        fn debugRemove(self: *Self, ptr: [*]u8, orig_size: ?usize) void {
            self.stats.removes += 1;
            if (orig_size != null) self.stats.removes_with_size += 1;
            const record = self.verify(ptr, orig_size) catch |err| self.failVerify(err, ptr, orig_size);
            // SAFETY: `ptr` is a live allocation valid for `record.size` bytes (its
            // recorded size), exclusively owned by this call (about to be reclaimed).
            spomen_poison.fill(ptr, record.size);
            const info = self.records.remove(ptr) orelse failWith(.unknown_pointer, ptr, null);
            const counter = self.requestedFor(info.source);
            counter.* -= info.size + guard.memoryGuardSize(config);
        }

        /// Verifies `ptr` — a record exists and its guard is intact — without
        /// changing anything. Called before a realloc/resize touches the block.
        /// Ports `debug_check`.
        fn debugCheck(self: *Self, ptr: [*]u8) void {
            self.stats.checks += 1;
            _ = self.verify(ptr, null) catch |err| self.failVerify(err, ptr, null);
        }

        /// Retargets `ptr`'s record to `new_ptr` after a successful realloc, writing
        /// a fresh guard ramp at the new block. `new_ptr == null` (the realloc
        /// failed) is a no-op: the original block and its record are untouched —
        /// `Cpp/ERRATA.md`'s E9 correction, and HPHA's own `if (!newPtr) return;`
        /// guard. Ports `debug_replace`.
        fn debugReplace(self: *Self, first_address: usize, ptr: [*]u8, new_ptr: ?[*]u8, size: usize, source: Source) void {
            const np = new_ptr orelse return;
            self.stats.replaces += 1;
            // SAFETY: `np` is a live allocation this instance just produced, exactly
            // what `querySize` requires.
            std.debug.assert(size <= self.querySize(np));
            const seed = self.nextGuardSeed();
            // SAFETY: `np` is valid for `size + memoryGuardSize(config)` bytes (the
            // realloc was made with that inflated size), exclusively owned.
            spomen_guard.writeGuard(config, np, size, seed);
            // Built before the store is touched, so the store never observes a
            // half-updated state.
            const fresh = Record.initAt(first_address, np, size, source, seed);
            const old = self.records.replace(ptr, fresh) orelse failWith(.unknown_pointer, ptr, null);
            const old_counter = self.requestedFor(old.source);
            old_counter.* -= old.size + guard.memoryGuardSize(config);
            const new_counter = self.requestedFor(source);
            new_counter.* += size + guard.memoryGuardSize(config);
        }

        /// Updates `ptr`'s record after an in-place `resize` to `size`, rewriting the
        /// guard ramp (its position moved with the size) with a fresh seed. Runs on
        /// *every* `resize`, whether or not the block grew, exactly like HPHA. Ports
        /// `debug_update`.
        fn debugUpdate(self: *Self, first_address: usize, ptr: [*]u8, size: usize) void {
            self.stats.updates += 1;
            // SAFETY: `ptr` is a live allocation this instance produced (the caller's
            // contract), exactly what `querySize` requires.
            std.debug.assert(size <= self.querySize(ptr));
            const seed = self.nextGuardSeed();
            // SAFETY: `ptr` is valid for `size + memoryGuardSize(config)` bytes
            // (`size` is the block's own deflated size); it is the caller's live block,
            // accessed single-threaded, so nothing else touches the guard region.
            spomen_guard.writeGuard(config, ptr, size, seed);
            const callstack = Record.captureCallstack(first_address);
            const info = self.records.update(ptr, size, seed, callstack) orelse failWith(.unknown_pointer, ptr, null);
            const counter = self.requestedFor(info.source);
            // `size` may be smaller or larger than the old size, so add before
            // subtracting.
            counter.* = counter.* + size - info.size;
        }

        /// Returns the record store's spare pages to the OS. Ports `debug_purge`.
        fn debugPurge(self: *Self) void {
            self.stats.purges += 1;
            self.records.purge();
        }

        // ---- check(), report() and leak detection ----------------------------------

        /// The problem with one live allocation, if any: its recorded size must fit the
        /// block and its guard ramp must be intact. Ports the per-record assertions of
        /// `allocator::check`.
        fn auditRecord(self: *Self, record: *Record) ?Corruption {
            // SAFETY: `record.ptr` is a live allocation this instance produced (it has a
            // record), exactly what `querySize` requires.
            const usable = self.querySize(record.ptr);
            if (record.size > usable) return .{ .oversized = usable };
            // SAFETY: `record.ptr` is valid for `record.size + memoryGuardSize(config)`
            // bytes (its recorded size fits the block, checked just above).
            if (!record.checkGuard(config)) return .guard_overrun;
            return null;
        }

        /// Audits every live allocation and returns the first problem found, without
        /// changing anything and without panicking. Ports `allocator::check` (which
        /// `assert`s each record's size against the block's size and its guard ramp): for
        /// every record, in *address* order, the recorded size must fit the block and the
        /// trailing guard ramp must still be intact. Stops at the first mismatch, like
        /// HPHA. Only available when `config.debug`.
        ///
        /// A hook-detected corruption panics; this is the way to *ask* instead, e.g. from a
        /// test or a periodic self-check. If `diagnostic` is non-null it receives the
        /// human-readable description of the problem (block address, sizes, and where the
        /// block was allocated, as raw return addresses); no allocation happens either way.
        ///
        /// Returns `error.Corruption` for the first record found overrun or inconsistent.
        /// (`error.Os` is reserved and never returned yet.)
        pub fn check(self: *Self, diagnostic: ?*spomen_failure.Diagnostic) OrisError!void {
            comptime std.debug.assert(config.debug);
            self.debugAssertNotMoved();
            // A reused `Diagnostic` must not keep a stale message after a clean audit.
            if (diagnostic) |d| d.len = 0;
            var cursor = self.records.first();
            // EXPLICIT: address-order tree walk; `cursor` is the state (the successor is
            // re-derived from the tree each step), not expressible as an iterator.
            while (cursor) |record| {
                // Latched first: nothing below changes the store, but this keeps the walk
                // robust should a future caller interleave allocations.
                cursor = self.records.next(record);
                if (self.auditRecord(record)) |problem| {
                    if (diagnostic) |d| d.set(problem, record.ptr, record);
                    return error.Corruption;
                }
            }
        }

        /// Writes a report of the allocator's state to `writer`: total requested and
        /// allocated bytes, then one entry per live allocation in *address* order (address,
        /// requested size, and where it was allocated as raw return addresses). Ports
        /// `allocator::report`, which `printf`s the same content to stdout. Only available
        /// when `config.debug`. It allocates nothing itself, and cannot re-enter the
        /// allocator: the store maps its pages through `os.map`, never an allocator.
        pub fn report(self: *Self, writer: *std.Io.Writer) std.Io.Writer.Error!void {
            comptime std.debug.assert(config.debug);
            try self.writeReportHead(writer);
            var cursor = self.records.first();
            // EXPLICIT: address-order tree walk; `cursor` is the state, as in `check`.
            while (cursor) |record| {
                cursor = self.records.next(record);
                try writeRecordLine(record, writer);
            }
            try writeReportFoot(writer);
        }

        /// `report`, written to standard error (best effort: a failed write has nowhere to
        /// be reported).
        pub fn reportToStderr(self: *Self) void {
            comptime std.debug.assert(config.debug);
            var buffer: [512]u8 = undefined;
            const stderr = std.debug.lockStderr(&buffer);
            defer std.debug.unlockStderr();
            const writer = &stderr.file_writer.interface;
            self.report(writer) catch {};
            writer.flush() catch {};
        }

        fn writeReportHead(self: *Self, writer: *std.Io.Writer) std.Io.Writer.Error!void {
            try writer.writeAll("REPORT =================================================\n");
            try writer.print("Total requested size={d} bytes\n", .{self.requested()});
            try writer.print("Total allocated size={d} bytes\n", .{self.allocated()});
            try writer.writeAll("Currently allocated blocks:\n");
        }

        fn writeReportFoot(writer: *std.Io.Writer) std.Io.Writer.Error!void {
            try writer.writeAll("===========================================================\n");
        }

        /// One live allocation's entry in the report: address, requested size, and the
        /// allocation callstack as raw return addresses (none if none was captured).
        fn writeRecordLine(record: *const Record, writer: *std.Io.Writer) std.Io.Writer.Error!void {
            // PROVENANCE: address read for its bit pattern only (it is printed).
            try writer.print("ptr=0x{x}, size={d}", .{ @intFromPtr(record.ptr), record.size });
            for (record.callstack) |frame| {
                if (frame == 0) break; // the unused tail is zero-filled
                try writer.print("\n  0x{x}", .{frame});
            }
            try writer.writeByte('\n');
        }

        /// The leak half of `deinit`, run first (before the record store is released): if
        /// any allocation is still live, audits it and prints the report to stderr — HPHA's
        /// `~allocator`'s `check(); report();`. Returns how many allocations leaked. The
        /// stderr wrapper around `debugTeardownTo`, which holds the logic (and is what the
        /// tests read).
        fn debugTeardown(self: *Self) usize {
            if (self.records.len() == 0) return 0;
            var buffer: [512]u8 = undefined;
            const stderr = std.debug.lockStderr(&buffer);
            defer std.debug.unlockStderr();
            const writer = &stderr.file_writer.interface;
            defer writer.flush() catch {};
            return self.debugTeardownTo(writer);
        }

        /// `debugTeardown`'s content, written to `writer`; returns the leak count and
        /// writes nothing when there is none. In order: a summary line
        /// (`orisnitsa: N allocation(s) were still live when the allocator was dropped`),
        /// then — if any block is overrun or has an oversized record — one
        /// `orisnitsa: <description>` line for the first such block, then the report head,
        /// one `ptr=0x…, size=N` entry per live record, and the foot.
        ///
        /// Both the audit and the listing walk the record book in *storage* order (the order
        /// the records sit in the book, which a removal from the middle perturbs), so the two
        /// ports' leak reports list blocks alike — `orisnik` needs that for an aliasing
        /// reason Zig does not have. The public `check`/`report` use address order.
        fn debugTeardownTo(self: *Self, writer: *std.Io.Writer) usize {
            const leaked = self.records.len();
            if (leaked == 0) return 0;
            const Probe = struct {
                orisnitsa: *Self,
                diagnostic: spomen_failure.Diagnostic = .{},
                found: bool = false,
                writer: *std.Io.Writer,

                fn audit(probe: *@This(), record: *Record) void {
                    if (probe.found) return;
                    if (probe.orisnitsa.auditRecord(record)) |problem| {
                        probe.found = true;
                        probe.diagnostic.set(problem, record.ptr, record);
                    }
                }

                fn line(probe: *@This(), record: *Record) void {
                    writeRecordLine(record, probe.writer) catch {};
                }
            };
            var probe: Probe = .{ .orisnitsa = self, .writer = writer };
            writer.print(
                "orisnitsa: {d} allocation(s) were still live when the allocator was dropped\n",
                .{leaked},
            ) catch {};
            self.records.forEachLive(&probe, Probe.audit);
            if (probe.found) writer.print("orisnitsa: {s}\n", .{probe.diagnostic.message()}) catch {};
            self.writeReportHead(writer) catch {};
            self.records.forEachLive(&probe, Probe.line);
            writeReportFoot(writer) catch {};
            return leaked;
        }

        /// Allocates `size` bytes at `block.DEFAULT_ALIGNMENT`. `size == 0` returns
        /// `null`. Ports `allocator::alloc(size_t)`.
        pub fn alloc(self: *Self, size: usize) ?[*]u8 {
            const first = if (config.debug) @returnAddress() else 0;
            return self.allocAt(first, size);
        }

        /// `alloc` with the recorded callstack starting at `first_address` (the
        /// public entry points pass their own `@returnAddress()`, so internal
        /// delegation — `allocAligned`, `calloc`, `realloc` — still yields a trace
        /// that starts at the user's call).
        fn allocAt(self: *Self, first_address: usize, size: usize) ?[*]u8 {
            self.debugAssertNotMoved();
            if (!bucket.isSmallAllocation(config, size)) {
                const raw = self.treeAlloc(size);
                if (config.debug) return self.debugAdd(first_address, raw, size, .tree);
                return raw;
            }
            if (size == 0) return null;
            const sz = bucket.clampSmallAllocation(size);
            const raw = self.bucketAlloc(sz);
            if (config.debug) return self.debugAdd(first_address, raw, sz, .buckets);
            return raw;
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
            const first = if (config.debug) @returnAddress() else 0;
            return self.allocAlignedAt(first, size, alignment);
        }

        /// `allocAligned` with the recorded callstack starting at `first_address`;
        /// see `allocAt`.
        fn allocAlignedAt(self: *Self, first_address: usize, size: usize, alignment: usize) ?[*]u8 {
            std.debug.assert(isHphaAlignment(alignment));
            self.debugAssertNotMoved();
            if (alignment <= block.DEFAULT_ALIGNMENT) {
                return self.allocAt(first_address, size);
            }
            if (!bucket.isSmallAllocation(config, size) or alignment > bucket.MAX_SMALL_ALLOCATION) {
                const raw = self.treeAllocAligned(size, alignment);
                if (config.debug) return self.debugAdd(first_address, raw, size, .tree);
                return raw;
            }
            if (size == 0) return null;
            const sz = bucket.clampSmallAllocation(size);
            const raw = self.bucketAllocAligned(sz, alignment);
            if (config.debug) return self.debugAdd(first_address, raw, sz, .buckets);
            return raw;
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
            const first = if (config.debug) @returnAddress() else 0;
            const ptr = self.allocAt(first, total) orelse return null;
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
            const first = if (config.debug) @returnAddress() else 0;
            return self.reallocAt(first, ptr, size);
        }

        /// `realloc` with the recorded callstack starting at `first_address`; see
        /// `allocAt`.
        fn reallocAt(self: *Self, first_address: usize, ptr: ?[*]u8, size: usize) ?[*]u8 {
            self.debugAssertNotMoved();
            const p = ptr orelse return self.allocAt(first_address, size);
            if (size == 0) {
                self.free(p);
                return null;
            }
            // HPHA verifies the block (record present, guard intact) before touching it.
            if (config.debug) self.debugCheck(p);
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract), exactly what `ptrInBucket` requires.
            if (self.buckets.ptrInBucket(p)) {
                const sz = bucket.clampSmallAllocation(size);
                if (bucket.isSmallAllocation(config, sz)) {
                    const new_ptr = self.bucketRealloc(p, sz);
                    if (config.debug) self.debugReplace(first_address, p, new_ptr, sz, .buckets);
                    return new_ptr;
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
                if (config.debug) self.debugReplace(first_address, p, new_ptr, sz, .tree);
                return new_ptr;
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced (not a
            // bucket pointer, per the `ptrInBucket` check above).
            const new_ptr = self.treeRealloc(p, size);
            if (config.debug) self.debugReplace(first_address, p, new_ptr, size, .tree);
            return new_ptr;
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
            const first = if (config.debug) @returnAddress() else 0;
            return self.reallocAlignedAt(first, ptr, size, alignment);
        }

        /// `reallocAligned` with the recorded callstack starting at `first_address`;
        /// see `allocAt`.
        fn reallocAlignedAt(self: *Self, first_address: usize, ptr: ?[*]u8, size: usize, alignment: usize) ?[*]u8 {
            std.debug.assert(isHphaAlignment(alignment));
            self.debugAssertNotMoved();
            if (alignment <= block.DEFAULT_ALIGNMENT) {
                return self.reallocAt(first_address, ptr, size);
            }
            const p = ptr orelse return self.allocAlignedAt(first_address, size, alignment);
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
                //
                // Verify the block before reading anything from it (`querySize`
                // below reads its page marker or block header). HPHA checks only
                // later, inside `free`; checking here is a deliberate,
                // state-neutral strengthening (it changes no bucket/tree/record
                // state), so it costs no cross-port parity and catches a foreign
                // pointer before any read. Mirrors `orisnik`'s `realloc_aligned`.
                if (config.debug) self.debugCheck(p);
                const new_ptr = self.allocAlignedAt(first_address, size, alignment) orelse return null;
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
            // HPHA verifies the block (record present, guard intact) before touching it.
            if (config.debug) self.debugCheck(p);
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
                    const new_ptr = self.bucketRealloc(p, sz);
                    if (config.debug) self.debugReplace(first_address, p, new_ptr, sz, .buckets);
                    return new_ptr;
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
                if (config.debug) self.debugReplace(first_address, p, new_ptr, sz, .tree);
                return new_ptr;
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
            const new_ptr = self.treeReallocAligned(p, size, alignment);
            if (config.debug) self.debugReplace(first_address, p, new_ptr, size, .tree);
            return new_ptr;
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
            if (config.debug) self.debugCheck(p);
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract).
            if (self.buckets.ptrInBucket(p)) {
                const new_size = self.bucketResize(p);
                if (config.debug) self.debugUpdate(@returnAddress(), p, new_size);
                return new_size;
            }
            // SAFETY: `p` is a live tree-path allocation this instance produced.
            const new_size = self.treeResize(p, size);
            if (config.debug) self.debugUpdate(@returnAddress(), p, new_size);
            return new_size;
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
        /// With `config.debug`, first verifies the block (a record exists — i.e. not a
        /// double free or a foreign pointer — and its guard ramp is intact), poisons the
        /// payload at its recorded size and retires the record, all *before* the
        /// reclaim; detected corruption panics (`spomen_failure.fail`).
        ///
        /// `ptr`, if non-null, must be a still-live allocation this instance
        /// produced.
        pub fn free(self: *Self, ptr: ?[*]u8) void {
            self.debugAssertNotMoved();
            const p = ptr orelse return;
            // With `config.debug`: verify the block (a record exists — i.e. not a
            // double free or a foreign pointer — and its guard ramp is intact),
            // poison the payload at its *recorded* size and retire the record, all
            // *before* the reclaim, exactly HPHA's `debug_remove(ptr)`-then-
            // `bucket_free`/`tree_free` order. Detected corruption panics.
            if (config.debug) self.debugRemove(p, null);
            // SAFETY: `p` is a live allocation this instance produced (this function's own
            // contract).
            if (self.buckets.ptrInBucket(p)) {
                self.buckets.free(p);
                return;
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
        /// With `config.debug`, `orig_size` must additionally equal the allocation's
        /// **current** requested size (the size its record holds — after any
        /// `realloc`/`resize`, and after the minimum-size clamp, so `free(p, 5)` of an
        /// `alloc(5)` is accepted): a mismatch is detected and panics. The bucket-vs-
        /// tree routing above still uses the *original* size, so after a size-changing
        /// `realloc`/`resize` prefer `free`, which needs neither.
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
            // With `config.debug`: verify, poison and retire the record *before* the
            // reclaim (either branch), checking `orig_size` against the recorded size
            // (see `verify`: compared after the minimum-size clamp).
            if (config.debug) self.debugRemove(p, orig_size);
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
        /// With `config.debug`, `orig_size` must also equal the allocation's current
        /// requested size, exactly as for `freeWithSize`.
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
            // See `freeWithSize`'s identical hook comment — same call, same
            // `orig_size` (alignment plays no part in the record check).
            if (config.debug) self.debugRemove(p, orig_size);
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
            if (config.debug) self.debugPurge();
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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

/// The deferred teardown of a debug-instance test. `deinit` ends a leaking teardown with a
/// panic, which would kill the whole test runner (exit code 3) and bury the assertion that
/// really failed. So this tears down quietly (`deinitReturningLeaks`) and only escalates a
/// leak to the panic when the test body otherwise *succeeded* (`failed` is set by an
/// `errdefer`, which runs first). Use:
/// `var failed = false; errdefer failed = true; defer finishDebug(&o, &failed);`.
fn finishDebug(o: *Orisnitsa(debug_config), failed: *const bool) void {
    const leaked = o.deinitReturningLeaks();
    if (leaked > 0 and !failed.*) spomen_failure.failOnLeak(leaked);
}

/// Rewrites `ptr`'s guard ramp with the seed its record remembers, undoing a
/// deliberate corruption so the block can be freed without tripping the debug check.
fn repairGuard(orisnitsa: *Orisnitsa(debug_config), ptr: [*]u8, size: usize) void {
    const record = orisnitsa.records.find(ptr) orelse @panic("test bug: block is not recorded");
    spomen_guard.writeGuard(debug_config, ptr, size, record.guard_byte);
}

test "treeAlloc hides the guard reservation from the caller" {
    // `querySize(ptr)` must report exactly what was requested — the guard
    // reservation (16 bytes trailing, real block size `size +
    // memoryGuardSize(config)`) must be completely invisible from the caller's
    // side of `querySize`/`alloc`.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const requested = bucket.MAX_SMALL_ALLOCATION + 4096;
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    // INDEX: `requested < requested + memoryGuardSize(debug_config)`, and
    // `memoryGuardSize(debug_config) > 0`, so this stays within `ptr`'s valid
    // span.
    ptr[requested] = 0;
    // `ptr` is a live tree-path allocation of exactly `requested` bytes.
    try testing.expect(!spomen_guard.checkGuard(debug_config, ptr, requested));
    // A free of a corrupted block now panics (and a Zig test cannot catch that), so
    // repair the ramp — rewrite it with the seed the record remembers — before the
    // final free. Detection itself is covered by `verify`'s tests below.
    repairGuard(&orisnitsa, ptr, requested);
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "treeRealloc rewrites the guard ramp at the new size" {
    // `realloc` growing a tree-path allocation must (re)write the guard ramp at
    // the *new* size, whichever internal path `Tree.realloc` took (in-place
    // growth, neighbour merge, or allocate-copy-free) — `treeRealloc`'s own doc
    // argues this from `Tree.realloc`'s contract; this exercises it for real.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const requested = bucket.MAX_SMALL_ALLOCATION - guard.memoryGuardSize(debug_config);
    const ptr = orisnitsa.alloc(requested) orelse return error.TestUnexpectedResult; // "OS map failed"
    // INDEX: `requested < requested + memoryGuardSize(debug_config)`, and the
    // slot is at least that large (its own bucket class), so this stays within
    // `ptr`'s valid span.
    ptr[requested] = 0;
    // `ptr` is a live bucket-path allocation of exactly `requested` bytes.
    try testing.expect(!spomen_guard.checkGuard(debug_config, ptr, requested));
    repairGuard(&orisnitsa, ptr, requested); // see the tree-path test: a corrupted free panics
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
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
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const count = 4;
    const size = 64;
    const ptr = orisnitsa.calloc(count, size) orelse return error.TestUnexpectedResult; // "OS map failed"
    for (ptr[0 .. count * size]) |b| {
        try testing.expectEqual(@as(u8, 0), b);
    }
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

// ---- v0.2.0 Phase 4: allocation records wired into dispatch ----
//
// Mirrors `orisnik`'s `orisnik_debug.rs` tests. Not applicable in Zig, and why:
// - the `busy` / `disabled` / nested-call tests and the "hooks switch off after a
//   detected corruption" test: Zig has no re-entrancy guard and no `disabled` latch
//   (the capture never allocates, and `fail` is a non-returning panic — see the
//   hooks' section comment);
// - the `GlobalAlloc` latch test and the global-allocator integration test: there is no
//   no-callstack mode and no global-allocator rule to exercise;
// - "overrunning the block is caught on free/realloc/resize", "double free and foreign
//   pointers are caught" and "a sized free with the wrong size is caught": those observe
//   a panic, which a Zig test cannot catch. Their *detection* logic is `verify`, tested
//   directly below for every corruption kind, and the message text is tested in
//   `spomen_failure.zig`. There is deliberately no seam that lets dispatch continue
//   past a detected corruption.

const guard_size = guard.memoryGuardSize(debug_config);

test "every allocation is recorded and free retires it" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const small = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    const large = orisnitsa.alloc(1000) orelse return error.TestUnexpectedResult;
    const aligned_small = orisnitsa.allocAligned(24, 32) orelse return error.TestUnexpectedResult;
    const aligned_large = orisnitsa.allocAligned(1000, 128) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 4), orisnitsa.records.len());
    for ([_][*]u8{ small, large, aligned_small, aligned_large }) |p| {
        try testing.expect(orisnitsa.records.find(p) != null);
        orisnitsa.free(p);
    }
    try testing.expectEqual(@as(usize, 0), orisnitsa.records.len());
    try testing.expectEqual(@as(usize, 0), orisnitsa.requested());
    orisnitsa.purge();
}

test "requested counts size plus guard and follows realloc and resize" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const first = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(24 + guard_size, orisnitsa.requested());
    const second = orisnitsa.alloc(1000) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(24 + 1000 + 2 * guard_size, orisnitsa.requested());
    // Bucket -> tree crossover: the old record's bytes leave the bucket total.
    const first_grown = orisnitsa.realloc(first, 500) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 0), orisnitsa.requested_buckets);
    try testing.expectEqual(500 + 1000 + 2 * guard_size, orisnitsa.requested());
    const new_size = orisnitsa.resize(second, 1200);
    // `resize` re-records the block at the size it actually ended up with.
    try testing.expectEqual(500 + new_size + 2 * guard_size, orisnitsa.requested());
    orisnitsa.free(first_grown);
    orisnitsa.free(second);
    try testing.expectEqual(@as(usize, 0), orisnitsa.requested());
    orisnitsa.purge();
}

test "a bucket resize re-records the slot's real usable size" {
    // `alloc(20)` lands in a 40-byte slot (20 + 16 guard, rounded up to the 8-byte
    // spacing), so `resize` reports 24 usable bytes and the record follows.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const ptr = orisnitsa.alloc(20) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(20 + guard_size, orisnitsa.requested());
    const new_size = orisnitsa.resize(ptr, 20);
    try testing.expectEqual(@as(usize, 24), new_size);
    try testing.expectEqual(new_size + guard_size, orisnitsa.requested());
    const record = orisnitsa.records.find(ptr) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(new_size, record.size);
    // The ramp was rewritten at the new position with the new seed: the block verifies.
    _ = try orisnitsa.verify(ptr, null);
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "sub-minimum requests are recorded clamped and a sized free accepts them" {
    // `alloc(5)` records 8 (clamped). HPHA would assert on `free(p, 5)` because it
    // compares the raw size; this port compares after the clamp, so the legal call
    // passes (an HPHA debug-mode bug deliberately not reproduced).
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const ptr = orisnitsa.alloc(5) orelse return error.TestUnexpectedResult;
    const record = orisnitsa.records.find(ptr) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(bucket.MIN_ALLOCATION, record.size);
    orisnitsa.freeWithSize(ptr, 5);
    try testing.expectEqual(@as(usize, 0), orisnitsa.records.len());
    orisnitsa.purge();
}

test "realloc rekeys the record across every path" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    // bucket -> bucket
    var ptr = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    ptr = orisnitsa.realloc(ptr, 100) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), orisnitsa.records.len());
    try testing.expect(orisnitsa.records.find(ptr) != null);
    // bucket -> tree
    ptr = orisnitsa.realloc(ptr, 2000) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), orisnitsa.records.len());
    try testing.expect(orisnitsa.records.find(ptr) != null);
    // tree -> tree, both directions
    ptr = orisnitsa.realloc(ptr, 9000) orelse return error.TestUnexpectedResult;
    ptr = orisnitsa.realloc(ptr, 300) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), orisnitsa.records.len());
    try testing.expect(orisnitsa.records.find(ptr) != null);
    // Aligned variants.
    ptr = orisnitsa.reallocAligned(ptr, 5000, 128) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), orisnitsa.records.len());
    try testing.expect(orisnitsa.records.find(ptr) != null);
    // The guard is valid at every step (a stale record would fail this free).
    orisnitsa.free(ptr);
    try testing.expectEqual(@as(usize, 0), orisnitsa.records.len());
    orisnitsa.purge();
}

test "a failed realloc leaves the original allocation and record intact" {
    // `Cpp/ERRATA.md` E9: the replace hook only ever runs on success.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const ptr = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    // The bucket -> tree crossover needs a fresh arena; refuse the OS.
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    try testing.expect(orisnitsa.realloc(ptr, 4000) == null);
    os.test_vm.clearFailure();
    try testing.expectEqual(@as(usize, 1), orisnitsa.records.len()); // original record survives
    try testing.expect(orisnitsa.records.find(ptr) != null);
    // `ptr` is still live and its guard intact, so this free must not panic.
    orisnitsa.free(ptr);
    try testing.expectEqual(@as(usize, 0), orisnitsa.records.len());
    orisnitsa.purge();
}

test "a record store out of memory frees the block and returns null" {
    // The first map serves the bucket page; the second (the record page) is refused.
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    os.test_vm.failMapAfter(1);
    defer os.test_vm.clearFailure();
    try testing.expect(orisnitsa.alloc(24) == null);
    os.test_vm.clearFailure();
    try testing.expectEqual(@as(usize, 0), orisnitsa.records.len());
    try testing.expectEqual(@as(usize, 0), orisnitsa.requested());
    // The block really was freed: with nothing live, a purge returns the page.
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
    // And the allocator recovers.
    const ptr = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    orisnitsa.free(ptr);
    orisnitsa.purge();
}

test "the same OOM on the tree path frees the block and returns null" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    os.test_vm.failMapAfter(1); // the arena maps; the record page is refused
    defer os.test_vm.clearFailure();
    try testing.expect(orisnitsa.alloc(5000) == null);
    os.test_vm.clearFailure();
    try testing.expectEqual(@as(usize, 0), orisnitsa.requested());
    orisnitsa.purge();
    try testing.expectEqual(@as(usize, 0), orisnitsa.allocated());
}

test "verify reports each corruption kind as a value" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);

    // Guard overrun, on both paths.
    for ([_]usize{ 24, 1000 }) |size| {
        const ptr = orisnitsa.alloc(size) orelse return error.TestUnexpectedResult;
        _ = try orisnitsa.verify(ptr, null); // intact
        // INDEX: `size < size + memoryGuardSize(debug_config)`, inside the block.
        ptr[size] ^= 0xFF;
        try testing.expectError(error.GuardOverrun, orisnitsa.verify(ptr, null));
        try testing.expectError(error.GuardOverrun, orisnitsa.verify(ptr, size));
        repairGuard(&orisnitsa, ptr, size);
        _ = try orisnitsa.verify(ptr, size);
        orisnitsa.free(ptr);
    }

    // Size mismatch: compared after the minimum-size clamp.
    const ptr = orisnitsa.alloc(100) orelse return error.TestUnexpectedResult;
    try testing.expectError(error.SizeMismatch, orisnitsa.verify(ptr, 64));
    _ = try orisnitsa.verify(ptr, 100);
    orisnitsa.free(ptr);
    const tiny = orisnitsa.alloc(5) orelse return error.TestUnexpectedResult;
    _ = try orisnitsa.verify(tiny, 5); // clamps to 8, which is what was recorded
    _ = try orisnitsa.verify(tiny, 8);
    try testing.expectError(error.SizeMismatch, orisnitsa.verify(tiny, 9));
    orisnitsa.free(tiny);

    // Unknown pointer: a double free (the record is gone) and a foreign pointer. Only
    // the address is compared; nothing is dereferenced.
    try testing.expectError(error.UnknownPointer, orisnitsa.verify(tiny, null));
    var local = [_]u8{0} ** 64;
    try testing.expectError(error.UnknownPointer, orisnitsa.verify(&local, null));
    orisnitsa.purge();
}

// A `noinline` caller that records its own return address, so a test can tell where the
// first captured frame must be *without* resolving any symbols. The hooks capture with
// the public entry point's own `@returnAddress()` as `first_address`, i.e. a call site
// inside this helper (the entry point's caller); the next frame is then this helper's
// return address into the test. If the optimizer inlines the entry point into the helper
// the first frame is this helper's return address itself. Either way `ret` must be one
// of the first two frames, and no frame inside the allocator may precede it. What this
// does NOT prove: that the frame *before* `ret` is exactly the helper's call instruction
// (that needs symbol resolution, `report()`'s later job).
const Entry = enum { alloc, calloc, alloc_aligned, realloc_aligned_move, resize };

noinline fn callThroughHelper(o: *Orisnitsa(debug_config), entry: Entry, p: ?[*]u8, ret: *usize) ?[*]u8 {
    ret.* = @returnAddress();
    switch (entry) {
        .alloc => return o.alloc(24),
        .calloc => return o.calloc(2, 12),
        .alloc_aligned => return o.allocAligned(24, 32),
        .realloc_aligned_move => return o.reallocAligned(p, 100, 256),
        .resize => {
            _ = o.resize(p, 24);
            return p;
        },
    }
}

/// Allocates 24-byte blocks until one is not 256-aligned (a bucket slot at a page base
/// is), frees the rest and returns it: a block that `reallocAligned(_, _, 256)` must
/// *move* rather than adjust in place.
fn allocMisaligned(o: *Orisnitsa(debug_config)) ![*]u8 {
    var got: [4][*]u8 = undefined;
    for (&got) |*s| s.* = o.alloc(24) orelse return error.TestUnexpectedResult;
    var pick: ?usize = null;
    for (got, 0..) |s, i| {
        if (pick == null and @intFromPtr(s) % 256 != 0) pick = i;
    }
    const chosen = pick orelse return error.TestUnexpectedResult;
    for (got, 0..) |s, i| {
        if (i != chosen) o.free(s);
    }
    return got[chosen];
}

fn expectStartsAt(record: *const Record, ret: usize) !void {
    try testing.expect(ret != 0);
    try testing.expect(record.callstack[0] == ret or record.callstack[1] == ret);
}

test "callstacks start at the caller on every entry point" {
    if (!std.options.allow_stack_tracing) return error.SkipZigTest;
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    var ret: usize = 0;
    for ([_]Entry{ .alloc, .calloc, .alloc_aligned }) |entry| {
        const p = callThroughHelper(&orisnitsa, entry, null, &ret) orelse return error.TestUnexpectedResult;
        try expectStartsAt(orisnitsa.records.find(p) orelse return error.TestUnexpectedResult, ret);
        orisnitsa.free(p);
    }
    // `resize` recaptures on update.
    const q = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    const record = orisnitsa.records.find(q) orelse return error.TestUnexpectedResult;
    record.callstack = [_]usize{0} ** spomen_record.MAX_CALLSTACK_DEPTH;
    _ = callThroughHelper(&orisnitsa, .resize, q, &ret);
    try expectStartsAt(record, ret);
    orisnitsa.free(q);
    // The misaligned-move path of `reallocAligned` records the *new* block from the
    // user's call, not from inside the internal `allocAlignedAt` delegation. The second
    // slot of a bucket page is not 256-aligned, so this really takes the move branch.
    const misaligned = try allocMisaligned(&orisnitsa);
    const moved = callThroughHelper(&orisnitsa, .realloc_aligned_move, misaligned, &ret) orelse return error.TestUnexpectedResult;
    try expectStartsAt(orisnitsa.records.find(moved) orelse return error.TestUnexpectedResult, ret);
    orisnitsa.free(moved);
    orisnitsa.purge();
}

test "purge returns the record store's spare pages" {
    var orisnitsa: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&orisnitsa, &failed);
    const ptr = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    orisnitsa.free(ptr);
    // The freed record leaves an empty-but-mapped book page behind ...
    try testing.expect(orisnitsa.records.book.cur != null);
    orisnitsa.stats = .{};
    orisnitsa.purge();
    // ... which `debugPurge` returns (deleting the hook call would leave `cur` set).
    try testing.expectEqual(@as(usize, 1), orisnitsa.stats.purges);
    try testing.expect(orisnitsa.records.book.cur == null);
    // Usable after the record book was fully purged.
    const again = orisnitsa.alloc(24) orelse return error.TestUnexpectedResult;
    orisnitsa.free(again);
    orisnitsa.purge();
}

fn expectStats(o: *Orisnitsa(debug_config), want: HookStats) !void {
    try testing.expectEqual(want, o.stats);
    o.stats = .{};
}

test "every public operation runs exactly its hooks (dispatch wiring)" {
    // Zig cannot catch the panic a missing hook would otherwise be observed through, so
    // the wiring is pinned by counting hook invocations after each operation, at the
    // call sites HPHA has (`Cpp/hpha.h:1264-1440`).
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);

    // alloc / calloc / allocAligned (all four routes): one add each, nothing else.
    const a = o.alloc(24) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    const b = o.alloc(5000) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    const c = o.calloc(2, 12) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    const d = o.allocAligned(24, 32) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    const e = o.allocAligned(5000, 128) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    // A failed allocation is not an add.
    os.test_vm.failMapAfter(0);
    try testing.expect(o.alloc(1 << 20) == null);
    os.test_vm.clearFailure();
    try expectStats(&o, .{});

    // free: one remove, no size carried.
    o.free(a);
    try expectStats(&o, .{ .removes = 1 });

    // realloc within the bucket path: one check, one replace, no add.
    const c2 = o.realloc(c, 100) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .checks = 1, .replaces = 1 });
    // bucket -> tree crossover: same hooks, and still no add/remove.
    const c3 = o.realloc(c2, 2000) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .checks = 1, .replaces = 1 });
    // tree -> tree.
    const b2 = o.realloc(b, 9000) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .checks = 1, .replaces = 1 });
    // reallocAligned in place (tree path, already aligned).
    const e2 = o.reallocAligned(e, 6000, 128) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .checks = 1, .replaces = 1 });

    // resize: one check, one update (both paths).
    _ = o.resize(c3, 2000);
    try expectStats(&o, .{ .checks = 1, .updates = 1 });
    _ = o.resize(d, 24);
    try expectStats(&o, .{ .checks = 1, .updates = 1 });

    // realloc(null, n) is an alloc; realloc(p, 0) is a free (and does not check).
    const f = o.realloc(null, 40) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .adds = 1 });
    try testing.expect(o.realloc(f, 0) == null);
    try expectStats(&o, .{ .removes = 1 });

    // The misaligned move of `reallocAligned`: a fresh aligned allocation and a free of
    // the old block — one add, one remove — preceded by one check, a deliberate
    // state-neutral strengthening over HPHA (which verifies only later, in `free`) so the
    // block is verified before `querySize` reads its page marker/header.
    const filler = o.alloc(24) orelse return error.TestUnexpectedResult;
    const odd = try allocMisaligned(&o);
    o.stats = .{};
    const moved = o.reallocAligned(odd, 100, 256) orelse return error.TestUnexpectedResult;
    try expectStats(&o, .{ .checks = 1, .adds = 1, .removes = 1 });

    // freeWithSize / freeWithSizeAligned: one remove *carrying the size*.
    o.freeWithSize(filler, 24);
    try expectStats(&o, .{ .removes = 1, .removes_with_size = 1 });
    o.freeWithSizeAligned(moved, 100, 256);
    try expectStats(&o, .{ .removes = 1, .removes_with_size = 1 });
    // A zero orig_size recovers through plain `free`: a remove without a size.
    const g = o.alloc(24) orelse return error.TestUnexpectedResult;
    o.stats = .{};
    o.freeWithSize(g, 0);
    try expectStats(&o, .{ .removes = 1 });

    o.free(d);
    o.free(c3);
    o.free(b2);
    o.free(e2);
    o.stats = .{};
    // purge: one purge hook.
    o.purge();
    try expectStats(&o, .{ .purges = 1 });
    try testing.expectEqual(@as(usize, 0), o.requested());
}

test "a failed realloc runs the check but never the replace hook" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    o.stats = .{};
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    try testing.expect(o.realloc(p, 4000) == null);
    os.test_vm.clearFailure();
    try expectStats(&o, .{ .checks = 1 });
    o.free(p);
    o.purge();
}

test "E9 on the tree path: a failed tree realloc keeps the original and its record" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const p = o.alloc(5000) orelse return error.TestUnexpectedResult;
    const q = o.allocAligned(5000, 128) orelse return error.TestUnexpectedResult;
    o.stats = .{};
    // Bigger than the arena the blocks live in, so the tree can neither grow them in
    // place nor find room, and must map a new arena — which the OS refuses. (`q` is
    // 128-aligned, so `reallocAligned` reaches the check instead of taking the
    // misaligned-move branch.)
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    try testing.expect(o.realloc(p, 1 << 20) == null);
    try testing.expect(o.reallocAligned(q, 1 << 20, 128) == null);
    os.test_vm.clearFailure();
    try expectStats(&o, .{ .checks = 2 }); // checked, but never replaced
    try testing.expectEqual(@as(usize, 2), o.records.len());
    for ([_][*]u8{ p, q }) |blk| {
        const record = o.records.find(blk) orelse return error.TestUnexpectedResult;
        try testing.expectEqual(@as(usize, 5000), record.size);
        _ = try o.verify(blk, 5000); // ramp still intact
    }
    o.free(p);
    o.free(q);
    try testing.expectEqual(@as(usize, 0), o.requested());
    o.purge();
}

test "the record-store OOM path also frees an aligned block" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    // Bucket path: the first map serves the page, the second (the record page) fails.
    os.test_vm.failMapAfter(1);
    defer os.test_vm.clearFailure();
    try testing.expect(o.allocAligned(24, 32) == null);
    os.test_vm.clearFailure();
    // Tree path, aligned.
    os.test_vm.failMapAfter(1);
    try testing.expect(o.allocAligned(5000, 128) == null);
    os.test_vm.clearFailure();
    try testing.expectEqual(@as(usize, 0), o.records.len());
    try testing.expectEqual(@as(usize, 0), o.requested());
    o.purge();
    try testing.expectEqual(@as(usize, 0), o.allocated());
}

test "verify compares a tree-path record raw and a bucket-path record clamped" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);

    // Tree path via a large alignment records the RAW size, even below the minimum:
    // clamping the caller's size there would falsely report a mismatch.
    const t5 = o.allocAligned(5, 4096) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 5), (o.records.find(t5) orelse return error.TestUnexpectedResult).size);
    _ = try o.verify(t5, 5);
    try testing.expectError(error.SizeMismatch, o.verify(t5, 8)); // clamped value is NOT the record
    const t3 = o.allocAligned(3, 512) orelse return error.TestUnexpectedResult;
    _ = try o.verify(t3, 3);
    try testing.expectError(error.SizeMismatch, o.verify(t3, 4));
    o.freeWithSizeAligned(t3, 3, 512); // the sized free must not falsely trip
    o.freeWithSizeAligned(t5, 5, 4096);

    // Bucket path records the clamped size: a sub-minimum request verifies both ways.
    const b3 = o.allocAligned(3, 16) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(bucket.MIN_ALLOCATION, (o.records.find(b3) orelse return error.TestUnexpectedResult).size);
    _ = try o.verify(b3, 3);
    _ = try o.verify(b3, 8);
    try testing.expectError(error.SizeMismatch, o.verify(b3, 9));
    o.freeWithSizeAligned(b3, 3, 16);

    // A tree-path realloc down to a sub-minimum size records 5 raw too.
    const big = o.alloc(5000) orelse return error.TestUnexpectedResult;
    const shrunk = o.realloc(big, 5) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 5), (o.records.find(shrunk) orelse return error.TestUnexpectedResult).size);
    _ = try o.verify(shrunk, 5);
    try testing.expectError(error.SizeMismatch, o.verify(shrunk, 8));
    o.free(shrunk);
    o.purge();
}

test "the default instantiation carries no debug state" {
    comptime {
        std.debug.assert(@FieldType(Orisnitsa(.{}), "records") == void);
        std.debug.assert(@FieldType(Orisnitsa(.{}), "requested_buckets") == void);
        std.debug.assert(@FieldType(Orisnitsa(.{}), "requested_tree") == void);
        std.debug.assert(@FieldType(Orisnitsa(.{}), "stats") == void);
        std.debug.assert(@FieldType(Orisnitsa(.{}), "guard_rng") == void);
        // Every remaining field is release state: nothing debug-only is left hiding.
        std.debug.assert(@sizeOf(Orisnitsa(.{})) ==
            @sizeOf(bucket.Buckets(.{})) + @sizeOf(tree_mod.Tree(.{})) + @sizeOf(usize));
    }
    var orisnitsa: Orisnitsa(.{}) = .init();
    orisnitsa.deinit(); // nothing to release, and nothing to report, for an unused default instance
}

fn recordedSize(o: *Orisnitsa(debug_config), p: [*]u8) !usize {
    return (o.records.find(p) orelse return error.TestUnexpectedResult).size;
}

fn expectTotals(o: *Orisnitsa(debug_config), buckets: usize, tree: usize) !void {
    try testing.expectEqual(buckets, o.requested_buckets);
    try testing.expectEqual(tree, o.requested_tree);
}

test "counters and sources follow every realloc path" {
    // Kills a deleted `debugReplace`, or one passed the wrong `Source`, on any realloc
    // path: the per-source totals and the recorded size/source change with each step.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);

    // bucket -> bucket
    var p = o.alloc(24) orelse return error.TestUnexpectedResult;
    p = o.realloc(p, 100) orelse return error.TestUnexpectedResult;
    try expectTotals(&o, 100 + guard_size, 0);
    _ = try o.verify(p, 100);
    try testing.expectError(error.SizeMismatch, o.verify(p, 3));
    o.free(p);

    // tree -> tree, growing and shrinking below the bucket threshold
    p = o.alloc(3000) orelse return error.TestUnexpectedResult;
    p = o.realloc(p, 9000) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 9000), try recordedSize(&o, p));
    try expectTotals(&o, 0, 9000 + guard_size);
    p = o.realloc(p, 5) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 5), try recordedSize(&o, p));
    try testing.expectEqual(Source.tree, (o.records.find(p) orelse return error.TestUnexpectedResult).source);
    _ = try o.verify(p, 5); // a tree record compares raw
    o.free(p);

    // aligned bucket in place
    p = o.allocAligned(24, 32) orelse return error.TestUnexpectedResult;
    p = o.reallocAligned(p, 60, 32) orelse return error.TestUnexpectedResult;
    try expectTotals(&o, 60 + guard_size, 0);
    try testing.expectEqual(Source.buckets, (o.records.find(p) orelse return error.TestUnexpectedResult).source);
    o.free(p);

    // aligned bucket -> tree crossover
    p = o.allocAligned(24, 32) orelse return error.TestUnexpectedResult;
    p = o.reallocAligned(p, 5000, 32) orelse return error.TestUnexpectedResult;
    try expectTotals(&o, 0, 5000 + guard_size);
    try testing.expectEqual(Source.tree, (o.records.find(p) orelse return error.TestUnexpectedResult).source);
    o.free(p);

    // aligned tree -> tree, growing and shrinking
    p = o.allocAligned(3000, 128) orelse return error.TestUnexpectedResult;
    p = o.reallocAligned(p, 9000, 128) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 9000), try recordedSize(&o, p));
    try expectTotals(&o, 0, 9000 + guard_size);
    p = o.reallocAligned(p, 5, 128) orelse return error.TestUnexpectedResult;
    _ = try o.verify(p, 5); // a tree record compares raw
    o.free(p);

    try testing.expectEqual(@as(usize, 0), o.requested());
    o.purge();
}

test "every realloc path recaptures the record's callstack" {
    // A sentinel can never be a real capture (a capture is return addresses or, without
    // stack tracing, all zero), so surviving it means `debugReplace` did not rebuild the
    // record's callstack.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const sentinel_cs = [_]usize{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const Step = struct { aligned: bool, from: usize, to: usize, alignment: usize };
    const steps = [_]Step{
        .{ .aligned = false, .from = 24, .to = 100, .alignment = 0 }, // bucket -> bucket
        .{ .aligned = false, .from = 24, .to = 5000, .alignment = 0 }, // crossover
        .{ .aligned = false, .from = 3000, .to = 9000, .alignment = 0 }, // tree -> tree
        .{ .aligned = true, .from = 24, .to = 60, .alignment = 32 }, // aligned bucket in place
        .{ .aligned = true, .from = 24, .to = 5000, .alignment = 32 }, // aligned crossover
        .{ .aligned = true, .from = 3000, .to = 9000, .alignment = 128 }, // aligned tree
    };
    for (steps) |s| {
        var p = (if (s.aligned) o.allocAligned(s.from, s.alignment) else o.alloc(s.from)) orelse return error.TestUnexpectedResult;
        (o.records.find(p) orelse return error.TestUnexpectedResult).callstack = sentinel_cs;
        p = (if (s.aligned) o.reallocAligned(p, s.to, s.alignment) else o.realloc(p, s.to)) orelse return error.TestUnexpectedResult;
        const record = o.records.find(p) orelse return error.TestUnexpectedResult;
        try testing.expect(!std.mem.eql(usize, &record.callstack, &sentinel_cs));
        o.free(p);
    }
    o.purge();
}

// ---- v0.2.0 Phase 5: deinit releases memory, check(), report(), leak detection ----
//
// Panics cannot be caught in a Zig test. `deinit`'s leak failure is therefore observed
// through `deinitReturningLeaks` (everything `deinit` does except the final panic), and
// `check()` is a plain error value. The leaking-teardown tests below print their leak
// report to stderr, which is the point of the feature and harmless in a test run.

/// Unmaps the bucket page a deliberately leaked block lives in, so the test process
/// leaves nothing behind. `leaked_block` must be a bucket slot whose owner has been torn
/// down (which leaves that page mapped).
fn releaseLeakedBucketPage(leaked_block: [*]u8) void {
    // ALIGN: bucket pages are `os.PAGE_SIZE`-aligned mappings and a slot lies inside its
    // page, so rounding down to `PAGE_SIZE` recovers the mapping's base.
    const base = align_helpers.alignDown(leaked_block, os.PAGE_SIZE);
    // SAFETY: `base`/`PAGE_SIZE` describe exactly the mapping the (torn-down) allocator
    // obtained from `os.map(PAGE_SIZE)` for this bucket page and left mapped because a
    // live block remained in it; nothing references the page afterwards.
    os.unmap(base, os.PAGE_SIZE);
}

/// Runs the "everything idle comes back" scenarios against a fresh instance of `config`
/// each, asserting after every one that `deinit` returned every mapping it opened
/// (bucket pages, tree arenas and, with `config.debug`, the record store's pages).
fn deinitReleasesEverything(comptime config: Config) !void {
    const O = Orisnitsa(config);
    const gsize = guard.memoryGuardSize(config);
    const before = os.test_vm.liveMappings();

    // An instance that was never used maps and releases nothing.
    {
        var o: O = .init();
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }

    // Bucket pages of many size classes.
    {
        var o: O = .init();
        var blocks: std.ArrayList([*]u8) = .empty;
        defer blocks.deinit(testing.allocator);
        var size: usize = 1;
        while (size <= bucket.MAX_SMALL_ALLOCATION - gsize) : (size += 7) {
            try blocks.append(testing.allocator, o.alloc(size) orelse return error.TestUnexpectedResult);
        }
        // Several distinct pages were mapped.
        try testing.expect(os.test_vm.liveMappings() > before + 2);
        for (blocks.items) |p| o.free(p);
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }

    // A block freed last is cached in the tree's MR slot, invisible to a tree walk: the
    // teardown must still find it.
    {
        var o: O = .init();
        const p = o.alloc(5000) orelse return error.TestUnexpectedResult;
        o.free(p);
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }

    // Several tree arenas, freed in a shuffled order so some sit in the tree and one in the
    // MR cache.
    {
        var o: O = .init();
        const sizes = [_]usize{ 66_000, 70_000, 9_000, 80_000, 40_000, 5_000 };
        var blocks: [sizes.len][*]u8 = undefined;
        for (sizes, 0..) |s, i| blocks[i] = o.alloc(s) orelse return error.TestUnexpectedResult;
        for ([_]usize{ 3, 0, 5, 2, 4, 1 }) |i| o.free(blocks[i]);
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }

    // A mixed workload after realloc churn.
    {
        var o: O = .init();
        var live: std.ArrayList([*]u8) = .empty;
        defer live.deinit(testing.allocator);
        for (1..40) |round| {
            const size = 8 + (round * 37) % 2500;
            try live.append(testing.allocator, o.alloc(size) orelse return error.TestUnexpectedResult);
            if (round % 3 == 0) o.free(live.orderedRemove(round % live.items.len));
            if (round % 5 == 0) {
                if (live.pop()) |last| {
                    try live.append(testing.allocator, o.realloc(last, size * 3) orelse return error.TestUnexpectedResult);
                }
            }
        }
        for (live.items) |p| o.free(p);
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }

    // The `oris_destroy` shape: the allocator lives on the heap (used in place, never
    // moved), torn down with idle arenas in the free tree and the MR cache.
    {
        const o = try testing.allocator.create(O);
        defer testing.allocator.destroy(o);
        o.* = .init();
        const small = o.alloc(5000) orelse return error.TestUnexpectedResult;
        const large = o.alloc(66_000) orelse return error.TestUnexpectedResult;
        const other = o.alloc(70_000) orelse return error.TestUnexpectedResult;
        o.free(large);
        o.free(other);
        o.free(small);
        o.deinit();
        try testing.expectEqual(before, os.test_vm.liveMappings());
    }
}

test "deinit returns every mapping (default instantiation)" {
    try deinitReleasesEverything(.{});
}

test "deinit returns every mapping (debug instantiation, record pages included)" {
    try deinitReleasesEverything(debug_config);
}

test "deinit with a live block keeps only its page (default instantiation)" {
    // Non-debug only: with `config.debug` the same situation is a *leak* and fails the
    // teardown (tested below).
    const before = os.test_vm.liveMappings();
    var o: Orisnitsa(.{}) = .init();
    const kept = o.alloc(24) orelse return error.TestUnexpectedResult;
    const idle = o.alloc(5000) orelse return error.TestUnexpectedResult;
    o.free(idle);
    const other_class = o.alloc(100) orelse return error.TestUnexpectedResult;
    o.free(other_class);
    o.deinit();
    // Exactly the live block's page remains ...
    try testing.expectEqual(before + 1, os.test_vm.liveMappings());
    // ... and it belongs to nobody now: release it by hand so the test leaks nothing.
    releaseLeakedBucketPage(kept);
    try testing.expectEqual(before, os.test_vm.liveMappings());
}

fn reportText(o: *Orisnitsa(debug_config), aw: *std.Io.Writer.Allocating) ![]const u8 {
    aw.clearRetainingCapacity();
    try o.report(&aw.writer);
    return aw.written();
}

fn flipGuardByte(ptr: [*]u8, size: usize) void {
    // SAFETY: `ptr` is a live allocation of `size` requested bytes plus the guard
    // reservation, so the byte at `size` is the first guard byte, inside the block; the
    // calling test owns it exclusively. INDEX: as above (`size < size + guard size`).
    ptr[size] ^= 0xFF;
}

test "check passes on a healthy heap of every kind" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    try o.check(null); // an empty heap is healthy
    const blocks = [_][*]u8{
        o.alloc(24) orelse return error.TestUnexpectedResult,
        o.alloc(1000) orelse return error.TestUnexpectedResult,
        o.allocAligned(24, 32) orelse return error.TestUnexpectedResult,
        o.allocAligned(3000, 128) orelse return error.TestUnexpectedResult,
        o.calloc(3, 40) orelse return error.TestUnexpectedResult,
    };
    try o.check(null);
    const grown = o.realloc(blocks[1], 4000) orelse return error.TestUnexpectedResult;
    try o.check(null); // still healthy after a realloc
    for ([_][*]u8{ blocks[0], grown, blocks[2], blocks[3], blocks[4] }) |p| o.free(p);
    try o.check(null);
    o.purge();
}

test "check reports a guard overrun as a value, and changes nothing" {
    for ([_]usize{ 24, 3000 }) |size| {
        var o: Orisnitsa(debug_config) = .init();
        var failed = false;
        errdefer failed = true;
        defer finishDebug(&o, &failed);
        const healthy = o.alloc(64) orelse return error.TestUnexpectedResult;
        const victim = o.alloc(size) orelse return error.TestUnexpectedResult;
        flipGuardByte(victim, size);
        var diagnostic: spomen_failure.Diagnostic = .{};
        try testing.expectError(error.Corruption, o.check(&diagnostic));
        const message = diagnostic.message();
        try testing.expect(std.mem.indexOf(u8, message, "guard bytes overwritten") != null);
        var want: [64]u8 = undefined;
        try testing.expect(std.mem.indexOf(u8, message, try std.fmt.bufPrint(&want, "requested {d} bytes", .{size})) != null);
        // Asking again without a diagnostic gives the same error; the store is untouched.
        try testing.expectError(error.Corruption, o.check(null));
        try testing.expectEqual(@as(usize, 2), o.records.len());
        // Repair the block (the same flip restores it) and the audit passes again.
        flipGuardByte(victim, size);
        try o.check(null);
        o.free(victim);
        o.free(healthy);
        o.purge();
    }
}

test "check reports a record larger than its block" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    const record = o.records.find(p) orelse return error.TestUnexpectedResult;
    record.size = 10_000; // forged: the point of the test
    var diagnostic: spomen_failure.Diagnostic = .{};
    try testing.expectError(error.Corruption, o.check(&diagnostic));
    try testing.expect(std.mem.indexOf(u8, diagnostic.message(), "recorded size exceeds") != null);
    try testing.expect(std.mem.indexOf(u8, diagnostic.message(), "recorded 10000 bytes") != null);
    record.size = 24; // restored
    try o.check(null);
    o.free(p);
    o.purge();
}

fn ptrLess(_: void, a: [*]u8, b: [*]u8) bool {
    return @intFromPtr(a) < @intFromPtr(b);
}

test "check stops at the first problem in address order" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var blocks = [_][*]u8{
        o.alloc(24) orelse return error.TestUnexpectedResult,
        o.alloc(24) orelse return error.TestUnexpectedResult,
        o.alloc(24) orelse return error.TestUnexpectedResult,
    };
    std.mem.sort([*]u8, &blocks, {}, ptrLess);
    flipGuardByte(blocks[2], 24);
    flipGuardByte(blocks[1], 24);
    var diagnostic: spomen_failure.Diagnostic = .{};
    try testing.expectError(error.Corruption, o.check(&diagnostic));
    var want: [32]u8 = undefined;
    const lower = try std.fmt.bufPrint(&want, "0x{x}", .{@intFromPtr(blocks[1])});
    try testing.expect(std.mem.indexOf(u8, diagnostic.message(), lower) != null); // the lower address first
    flipGuardByte(blocks[2], 24);
    flipGuardByte(blocks[1], 24);
    for (blocks) |p| o.free(p);
    o.purge();
}

test "report lists the totals and every live block in address order" {
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    var blocks = [_][*]u8{
        o.alloc(24) orelse return error.TestUnexpectedResult,
        o.alloc(1000) orelse return error.TestUnexpectedResult,
        o.alloc(100) orelse return error.TestUnexpectedResult,
    };
    const text = try reportText(&o, &aw);
    try testing.expect(std.mem.startsWith(u8, text, "REPORT ===="));
    try testing.expect(std.mem.indexOf(u8, text, "Currently allocated blocks:") != null);
    var line: [96]u8 = undefined;
    try testing.expect(std.mem.indexOf(u8, text, try std.fmt.bufPrint(&line, "Total requested size={d} bytes", .{o.requested()})) != null);
    try testing.expect(std.mem.indexOf(u8, text, try std.fmt.bufPrint(&line, "Total allocated size={d} bytes", .{o.allocated()})) != null);
    std.mem.sort([*]u8, &blocks, {}, ptrLess);
    var cursor: usize = 0;
    for (blocks) |p| {
        const record = o.records.find(p) orelse return error.TestUnexpectedResult;
        const want = try std.fmt.bufPrint(&line, "ptr=0x{x}, size={d}", .{ @intFromPtr(p), record.size });
        const at = std.mem.indexOfPos(u8, text, cursor, want) orelse {
            std.debug.print("{s} missing or out of order in:\n{s}\n", .{ want, text });
            return error.TestUnexpectedResult;
        };
        cursor = at + want.len;
    }
    try testing.expect(std.mem.endsWith(u8, std.mem.trimEnd(u8, text, "\n"), "==========="));
    for (blocks) |p| o.free(p);
    // A freed block leaves the report.
    try testing.expect(std.mem.indexOf(u8, try reportText(&o, &aw), "ptr=") == null);
    o.purge();
}

test "report shows where a block was allocated (raw return addresses)" {
    if (!std.options.allow_stack_tracing) return error.SkipZigTest;
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    const record = o.records.find(p) orelse return error.TestUnexpectedResult;
    var line: [32]u8 = undefined;
    const frame = try std.fmt.bufPrint(&line, "0x{x}", .{record.callstack[0]});
    try testing.expect(std.mem.indexOf(u8, try reportText(&o, &aw), frame) != null);
    o.free(p);
    o.purge();
}

test "a leak at deinit is audited and reported, and everything else is released" {
    // `deinit` ends a leaking teardown with a panic no Zig test can catch, so this drives
    // `deinitReturningLeaks`: the audit, the report and the release, minus the panic.
    const before = os.test_vm.liveMappings();
    var o: Orisnitsa(debug_config) = .init();
    const leaked = o.alloc(24) orelse return error.TestUnexpectedResult;
    const idle = o.alloc(5000) orelse return error.TestUnexpectedResult;
    o.free(idle);
    try testing.expectEqual(@as(usize, 1), o.deinitReturningLeaks());
    // Everything idle was returned (the tree arena, the record page); only the leaked
    // block's own bucket page remains.
    try testing.expectEqual(before + 1, os.test_vm.liveMappings());
    releaseLeakedBucketPage(leaked);
    try testing.expectEqual(before, os.test_vm.liveMappings());
}

test "a leak audit counts every live block and survives a corrupted one" {
    const before = os.test_vm.liveMappings();
    var o: Orisnitsa(debug_config) = .init();
    const a = o.alloc(24) orelse return error.TestUnexpectedResult;
    const b = o.alloc(24) orelse return error.TestUnexpectedResult;
    flipGuardByte(b, 24); // the audit prints this as the first problem instead of panicking
    try testing.expectEqual(@as(usize, 2), o.deinitReturningLeaks());
    // Both blocks live in one bucket page, which stays mapped; nothing else does.
    try testing.expectEqual(before + 1, os.test_vm.liveMappings());
    releaseLeakedBucketPage(a);
    try testing.expectEqual(before, os.test_vm.liveMappings());
}

test "a clean deinit returns zero leaks and leaves no mappings" {
    const before = os.test_vm.liveMappings();
    var o: Orisnitsa(debug_config) = .init();
    const first = o.alloc(24) orelse return error.TestUnexpectedResult;
    const second = o.alloc(5000) orelse return error.TestUnexpectedResult;
    o.free(first);
    o.free(second);
    try testing.expectEqual(@as(usize, 0), o.deinitReturningLeaks());
    try testing.expectEqual(before, os.test_vm.liveMappings());
}

// ---- Phase 5 review follow-ups: teardown output, orders, golden report ----

fn teardownText(o: *Orisnitsa(debug_config), aw: *std.Io.Writer.Allocating) !usize {
    aw.clearRetainingCapacity();
    return o.debugTeardownTo(&aw.writer);
}

/// Every live record's pointer in *storage* order (`forEachLive`).
fn storageOrder(o: *Orisnitsa(debug_config), out: [][*]u8) usize {
    const Log = struct {
        out: [][*]u8,
        count: usize = 0,
        fn visit(self: *@This(), record: *Record) void {
            self.out[self.count] = record.ptr;
            self.count += 1;
        }
    };
    var log: Log = .{ .out = out };
    o.records.forEachLive(&log, Log.visit);
    return log.count;
}

/// Every live record's pointer in *address* order (`first`/`next`).
fn addressOrder(o: *Orisnitsa(debug_config), out: [][*]u8) usize {
    var count: usize = 0;
    var cursor = o.records.first();
    // EXPLICIT: address-order tree walk; `cursor` is the state, not expressible as an
    // iterator.
    while (cursor) |record| : (cursor = o.records.next(record)) {
        out[count] = record.ptr;
        count += 1;
    }
    return count;
}

test "check clears a reused Diagnostic on success" {
    // Kills: dropping `d.len = 0` at the top of `check` (a stale message would survive).
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    flipGuardByte(p, 24);
    var diagnostic: spomen_failure.Diagnostic = .{};
    try testing.expectError(error.Corruption, o.check(&diagnostic));
    try testing.expect(diagnostic.message().len > 0);
    flipGuardByte(p, 24); // repaired
    try o.check(&diagnostic);
    try testing.expectEqual(@as(usize, 0), diagnostic.message().len);
    o.free(p);
    o.purge();
}

test "a clean heap's teardown prints nothing and reports zero leaks" {
    // Kills: deleting the `leaked == 0` early return in `debugTeardownTo` (every clean
    // debug deinit would print a report).
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    try testing.expectEqual(@as(usize, 0), try teardownText(&o, &aw)); // never used
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    o.free(p);
    try testing.expectEqual(@as(usize, 0), try teardownText(&o, &aw));
    try testing.expectEqual(@as(usize, 0), aw.written().len);
    o.purge();
}

test "the teardown output for one leak: summary, head, one entry, foot" {
    // Kills: a wrong/missing summary line, head, entry or foot; a spurious problem line
    // for a healthy leak.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), try teardownText(&o, &aw));
    const text = aw.written();
    try testing.expect(std.mem.startsWith(u8, text, "orisnitsa: 1 allocation(s) were still live when the allocator was dropped\nREPORT ===="));
    var want: [96]u8 = undefined;
    try testing.expect(std.mem.indexOf(u8, text, try std.fmt.bufPrint(&want, "Currently allocated blocks:\nptr=0x{x}, size=24", .{@intFromPtr(p)})) != null);
    try testing.expectEqual(@as(usize, 1), std.mem.count(u8, text, "ptr="));
    try testing.expect(std.mem.indexOf(u8, text, "orisnitsa: guard") == null); // healthy: no problem line
    try testing.expect(std.mem.endsWith(u8, text, "===========================================================\n"));
    o.free(p);
    o.purge();
}

test "the teardown prints the first problem before the report head" {
    // Kills: dropping the problem line, or printing it after the head.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    flipGuardByte(p, 24);
    try testing.expectEqual(@as(usize, 1), try teardownText(&o, &aw));
    const text = aw.written();
    const problem = std.mem.indexOf(u8, text, "orisnitsa: guard bytes overwritten") orelse return error.TestUnexpectedResult;
    const head = std.mem.indexOf(u8, text, "REPORT ====") orelse return error.TestUnexpectedResult;
    try testing.expect(problem < head);
    flipGuardByte(p, 24); // repaired
    o.free(p);
    o.purge();
}

test "the teardown lists two leaks in storage order" {
    // Kills: listing (or auditing) in address order instead of storage order.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    const first = o.alloc(24) orelse return error.TestUnexpectedResult;
    const second = o.alloc(1000) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 2), try teardownText(&o, &aw));
    var a: [64]u8 = undefined;
    var b: [64]u8 = undefined;
    const at_first = std.mem.indexOf(u8, aw.written(), try std.fmt.bufPrint(&a, "ptr=0x{x}, size=24", .{@intFromPtr(first)})) orelse return error.TestUnexpectedResult;
    const at_second = std.mem.indexOf(u8, aw.written(), try std.fmt.bufPrint(&b, "ptr=0x{x}, size=1000", .{@intFromPtr(second)})) orelse return error.TestUnexpectedResult;
    try testing.expect(at_first < at_second);
    o.free(first);
    o.free(second);
    o.purge();
}

test "address order and storage order differ, and each consumer uses its own" {
    // Kills: `check`/`report` walking storage order, or the teardown audit/listing walking
    // address order. A freed block's slot is reused by a later allocation (lower address)
    // that sits last in the book, and swap-remove moves the last record into the hole.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    const a = o.alloc(24) orelse return error.TestUnexpectedResult;
    const b = o.alloc(24) orelse return error.TestUnexpectedResult;
    const c = o.alloc(24) orelse return error.TestUnexpectedResult;
    const d = o.alloc(24) orelse return error.TestUnexpectedResult;
    o.free(a); // book: [d, b, c] after the swap-remove
    const e = o.alloc(24) orelse return error.TestUnexpectedResult; // reuses a's slot; book: [d, b, c, e]
    var storage: [4][*]u8 = undefined;
    var by_address: [4][*]u8 = undefined;
    try testing.expectEqual(@as(usize, 4), storageOrder(&o, &storage));
    try testing.expectEqual(@as(usize, 4), addressOrder(&o, &by_address));
    // The precondition the rest of the test needs: the two orders really differ.
    try testing.expect(!std.mem.eql([*]u8, &storage, &by_address));
    try testing.expect(storage[0] != by_address[0]);

    // Corrupt the storage-first and the address-first blocks.
    flipGuardByte(storage[0], 24);
    flipGuardByte(by_address[0], 24);
    var want: [32]u8 = undefined;

    // `check` reports the address-first one.
    var diagnostic: spomen_failure.Diagnostic = .{};
    try testing.expectError(error.Corruption, o.check(&diagnostic));
    try testing.expect(std.mem.indexOf(u8, diagnostic.message(), try std.fmt.bufPrint(&want, "0x{x}", .{@intFromPtr(by_address[0])})) != null);

    // The teardown audit reports the storage-first one, and lists in storage order.
    try testing.expectEqual(@as(usize, 4), try teardownText(&o, &aw));
    const problem_line_end = std.mem.indexOf(u8, aw.written(), "\nallocated at") orelse return error.TestUnexpectedResult;
    try testing.expect(std.mem.indexOf(u8, aw.written()[0..problem_line_end], try std.fmt.bufPrint(&want, "0x{x}", .{@intFromPtr(storage[0])})) != null);
    var cursor: usize = std.mem.indexOf(u8, aw.written(), "Currently allocated blocks:") orelse return error.TestUnexpectedResult;
    for (storage) |p| {
        const line = try std.fmt.bufPrint(&want, "ptr=0x{x},", .{@intFromPtr(p)});
        cursor = (std.mem.indexOfPos(u8, aw.written(), cursor, line) orelse return error.TestUnexpectedResult) + line.len;
    }

    // `report` lists address order.
    aw.clearRetainingCapacity();
    try o.report(&aw.writer);
    cursor = 0;
    for (by_address) |p| {
        const line = try std.fmt.bufPrint(&want, "ptr=0x{x},", .{@intFromPtr(p)});
        cursor = (std.mem.indexOfPos(u8, aw.written(), cursor, line) orelse return error.TestUnexpectedResult) + line.len;
    }

    flipGuardByte(storage[0], 24);
    flipGuardByte(by_address[0], 24);
    for ([_][*]u8{ b, c, d, e }) |p| o.free(p);
    o.purge();
}

test "report golden output" {
    // Kills: any change to the report's exact text — the newline after the head lines, the
    // frame indent, whether zero frames print, the newline after each entry and the foot.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    var blocks = [_][*]u8{
        o.alloc(24) orelse return error.TestUnexpectedResult,
        o.alloc(100) orelse return error.TestUnexpectedResult,
    };
    std.mem.sort([*]u8, &blocks, {}, ptrLess);
    (o.records.find(blocks[0]) orelse return error.TestUnexpectedResult).callstack = .{ 0x1000, 0x2000, 0, 0, 0, 0, 0, 0 };
    (o.records.find(blocks[1]) orelse return error.TestUnexpectedResult).callstack = .{ 0, 0, 0, 0, 0, 0, 0, 0 };
    const expected = try std.fmt.allocPrint(
        testing.allocator,
        "REPORT =================================================\n" ++
            "Total requested size={d} bytes\n" ++
            "Total allocated size={d} bytes\n" ++
            "Currently allocated blocks:\n" ++
            "ptr=0x{x}, size=24\n  0x1000\n  0x2000\n" ++
            "ptr=0x{x}, size=100\n" ++
            "===========================================================\n",
        .{ o.requested(), o.allocated(), @intFromPtr(blocks[0]), @intFromPtr(blocks[1]) },
    );
    defer testing.allocator.free(expected);
    var aw: std.Io.Writer.Allocating = .init(testing.allocator);
    defer aw.deinit();
    try o.report(&aw.writer);
    try testing.expectEqualStrings(expected, aw.written());
    // The sizes in the head are the real ones: (24 + 16) + (100 + 16).
    try testing.expectEqual(@as(usize, 24 + 100 + 2 * guard_size), o.requested());
    for (blocks) |p| o.free(p);
    o.purge();
}

test "reportToStderr runs" {
    // Kills: nothing behavioural (it writes to stderr) — but it makes the suite compile and
    // run `reportToStderr`, which no other test does.
    var o: Orisnitsa(debug_config) = .init();
    var failed = false;
    errdefer failed = true;
    defer finishDebug(&o, &failed);
    const p = o.alloc(24) orelse return error.TestUnexpectedResult;
    o.reportToStderr();
    o.free(p);
    o.purge();
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
