// SPDX-License-Identifier: MIT OR Apache-2.0
//! The allocation-record map: every live allocation's `Record`, indexed by address.
//! Ports `Cpp/hpha.h`'s `debug_record_map` (`add`, `remove`, `replace`, `update`, plus
//! the lookup its `check`/`find` use), mirroring `orisnik`'s `Rust/src/spomen/store.rs`.
//!
//! Records live densely in a `spomen_book.zig` `RecordBook` and are indexed by an
//! `IntrusiveMultiRbTree` keyed on the payload address, exactly as in HPHA ("a
//! multi-red-black tree is technically not needed since addresses are always unique
//! but for brevity we omit the inclusion of the `intrusive_red_black_tree` class" —
//! `hpha.h`). A live allocation's address is unique, so the tree never chains.
//!
//! # What this module does *not* do
//! It is pure bookkeeping. HPHA's `add`/`remove` also poison the payload and assert the
//! guard ramp; here those stay with the dispatch layer (`orisnitsa.zig`), which already
//! owns poisoning (`spomen_poison.zig`) and the guard-seed stream, and calls
//! `Record.checkGuard` (through its pure `verify`) before retiring a record. Keeping the store free of payload
//! access means it never dereferences a caller's allocation, so it is testable with
//! made-up addresses.
//!
//! # Removal from the middle
//! `RecordBook` only pops from the back, so `RecordStore.remove` follows HPHA: erase the
//! victim from the tree, erase the *last* record too, move the last record into the
//! victim's slot, and re-insert it — the tree's nodes are embedded in the records, so a
//! moved record must be unlinked before the move and re-linked after.
//!
//! Follows the same **non-move-after-first-use** contract as its tree and page list, and,
//! having no `Drop` to lean on, must be `deinit`ed by its owner.

const std = @import("std");
const rbtree = @import("rbtree.zig");
const spomen_book = @import("spomen_book.zig");
const spomen_record = @import("spomen_record.zig");

const Record = spomen_record.Record;
const Source = spomen_record.Source;
const RecordBook = spomen_book.RecordBook;

/// What `RecordStore.remove`/`replace`/`update` report about the record they displaced.
/// Ports `debug_info`.
pub const DebugInfo = struct {
    /// The size the caller had requested for the allocation, in bytes.
    size: usize,
    /// Which sub-allocator had served it.
    source: Source,
};

/// Address-indexed store of every live allocation's `Record`. Ports
/// `debug_record_map`.
pub const RecordStore = struct {
    /// Address-ordered index over the records held in `book`.
    tree: rbtree.IntrusiveMultiRbTree(Record) = .init(),
    /// Dense storage for the records themselves.
    book: RecordBook = .init(),

    /// An empty store. Nothing is mapped until the first `add`.
    pub fn init() RecordStore {
        return .{};
    }

    /// Returns every page to the OS (records are plain data, so nothing else needs
    /// releasing). Mirrors `orisnik`'s `Drop` for the book; the store must not be used
    /// afterwards.
    pub fn deinit(self: *RecordStore) void {
        self.book.deinit();
    }

    /// Number of live records.
    pub fn len(self: *const RecordStore) usize {
        return self.book.len;
    }

    /// The record for the allocation at `ptr`, if one is live. Ports the map's `find`.
    pub fn find(self: *RecordStore, ptr: [*]u8) ?*Record {
        // PROVENANCE: address read for its bit pattern only, never turned back into a
        // pointer — the tree is keyed on bare addresses.
        const key = @intFromPtr(ptr);
        const candidate = self.tree.lowerBound(key) orelse return null;
        // PROVENANCE: as above; comparison only.
        const found = @intFromPtr(candidate.ptr);
        return if (found == key) candidate else null;
    }

    /// Records a new allocation of `size` bytes at `ptr`, served by `source`, whose
    /// guard ramp was seeded with `guard_byte`. Returns `false` — recording nothing —
    /// if the OS refused a page for the record. Ports `debug_record_map::add`.
    ///
    /// `ptr` must not already be recorded (HPHA `assert`s this; so does this, in safe
    /// builds).
    pub fn add(self: *RecordStore, ptr: [*]u8, size: usize, source: Source, guard_byte: u8) bool {
        // Convenience for tests (dispatch builds its record itself and calls
        // `addRecord`). `@returnAddress()` is taken at THIS level so the captured trace
        // starts at `add`'s caller, not somewhere inside the store; `replace`/`update`
        // capture nothing — their callers pass a prebuilt record/callstack.
        return self.addRecord(Record.initAt(@returnAddress(), ptr, size, source, guard_byte));
    }

    /// Stores an already-built `record` (its tree linkage is (re)initialised here) and
    /// indexes it. Returns `false` — recording nothing — if the OS refused a page.
    /// `add` delegates here; it is also the seam that lets tests supply a
    /// deterministic callstack via `Record.withCallstack`. Mirrors `orisnik`'s
    /// `add_record`.
    ///
    /// `record.ptr` must not already be recorded (asserted in safe builds).
    pub fn addRecord(self: *RecordStore, record: Record) bool {
        std.debug.assert(self.find(record.ptr) == null); // address already recorded
        const slot = self.book.pushBack(record) orelse return false;
        slot.node = rbtree.NodeBase.UNLINKED;
        self.tree.insert(slot);
        return true;
    }

    /// Forgets the allocation at `ptr`, returning what was recorded, or `null` if it is
    /// not recorded (HPHA `assert`s: "most likely the pointer was already deleted or
    /// the pointer points to a static or a global variable"). Ports
    /// `debug_record_map::remove`.
    pub fn remove(self: *RecordStore, ptr: [*]u8) ?DebugInfo {
        const record = self.find(ptr) orelse return null;
        self.tree.erase(record);
        const last = self.book.back();
        const removed: Record = if (record == last) self.book.popBack() else blk: {
            self.tree.erase(last);
            var moved = self.book.popBack();
            // `moved` was unlinked from the tree above; its copied node fields are
            // stale, so start it from a clean node before it is re-linked.
            moved.node = rbtree.NodeBase.UNLINKED;
            // SAFETY: `record` is a live, initialized slot in the book (found above)
            // and not `last`, so the popped `moved` did not come from it; it is
            // exclusively accessed here.
            const old = record.*;
            record.* = moved;
            self.tree.insert(record);
            break :blk old;
        };
        return .{ .size = removed.size, .source = removed.source };
    }

    /// Retargets the record of the allocation at `ptr` to `fresh`, the record of its
    /// replacement (a successful `realloc`, which may or may not have moved it),
    /// returning what it recorded before. Returns `null` — storing nothing — if `ptr` is
    /// not recorded. Ports `debug_record_map::replace`.
    ///
    /// The caller builds `fresh` (with `Record.initAt`, choosing the callstack's first
    /// frame) *before* calling, so nothing in here captures anything or can observe a
    /// half-updated store. Mirrors `orisnik`'s `replace(ptr, fresh)`.
    ///
    /// Call this only once the new allocation has *succeeded* — see `Cpp/ERRATA.md`'s
    /// E9 correction: HPHA's own caller guards on `newPtr`, so a failed realloc never
    /// reaches here and the original record survives untouched.
    pub fn replace(self: *RecordStore, ptr: [*]u8, fresh: Record) ?DebugInfo {
        const record = self.find(ptr) orelse return null;
        // The address is the tree key, so the record leaves the tree while it changes.
        self.tree.erase(record);
        // SAFETY: `record` is a live, initialized slot in the book (found above),
        // exclusively accessed here; the old value is copied out before the slot holds a
        // fresh, initialized record.
        const old = record.*;
        record.* = fresh;
        self.tree.insert(record);
        return .{ .size = old.size, .source = old.source };
    }

    /// Updates the record of the allocation at `ptr` after an in-place resize: new
    /// requested `size`, the new guard seed and `callstack` (freshly captured by the
    /// caller with `Record.captureCallstack`, choosing its first frame; built *before*
    /// this call, see `replace`). Returns what it recorded before, or `null` if `ptr` is
    /// not recorded. Ports `debug_record_map::update`. The address — the tree key — is
    /// unchanged, so the tree is untouched.
    pub fn update(
        self: *RecordStore,
        ptr: [*]u8,
        size: usize,
        guard_byte: u8,
        callstack: [spomen_record.MAX_CALLSTACK_DEPTH]usize,
    ) ?DebugInfo {
        const record = self.find(ptr) orelse return null;
        // SAFETY: `record` is a live, initialized record (found above), exclusively
        // accessed here; only non-key fields are written.
        const info: DebugInfo = .{ .size = record.size, .source = record.source };
        record.size = size;
        record.guard_byte = guard_byte;
        record.callstack = callstack;
        return info;
    }

    /// The record with the lowest payload address, or `null` if the store is empty: the
    /// start of an address-ordered walk (HPHA's `debug_record_map::begin()`), used by
    /// `check()` and `report()`.
    pub fn first(self: *RecordStore) ?*Record {
        return self.tree.minimum();
    }

    /// The record after `record` in address order, or `null` if it is the last. The
    /// successor is re-derived from the tree on every call, so a walk tolerates records
    /// being *inserted* while it is in progress, as long as `record` itself is still live
    /// when this is called. It does **not** tolerate removals: `remove` swaps the last
    /// book record into the vacated slot, so a successor latched before a removal can go
    /// stale.
    pub fn next(self: *RecordStore, record: *Record) ?*Record {
        return self.tree.succ(record);
    }

    /// Calls `visit(context, record)` for every live record in *storage* order (the order
    /// the records sit in the book, which a removal from the middle perturbs — not address
    /// order), changing nothing and never touching the
    /// address index. The leak audit in `Orisnitsa.deinit` uses it, so both ports list
    /// leaked blocks in the same order (`orisnik` needs it for an aliasing reason Zig does
    /// not have); the public `report()` uses address order (`first`/`next`).
    pub fn forEachLive(
        self: *RecordStore,
        context: anytype,
        comptime visit: fn (@TypeOf(context), *Record) void,
    ) void {
        self.book.forEachLive(context, visit);
    }

    /// Returns the record book's spare pages to the OS. Ports
    /// `debug_record_map::purge`.
    pub fn purge(self: *RecordStore) void {
        self.book.purge();
    }
};

const testing = std.testing;
const os = @import("os.zig");
const VintageRand = @import("rand.zig").VintageRand;

/// A made-up address; the store only ever compares addresses, never dereferences the
/// allocation a record describes.
fn addr(n: usize) [*]u8 {
    // SAFETY: never dereferenced.
    // PROVENANCE: no allocation; a bare integer used only as an ordering key.
    return @ptrFromInt(0x1000 + n * 16);
}

/// A deterministic, non-zero callstack for record `n`, so bookkeeping tests can tell
/// callstacks apart without any symbol resolution.
fn sentinel(n: usize) [spomen_record.MAX_CALLSTACK_DEPTH]usize {
    var cs: [spomen_record.MAX_CALLSTACK_DEPTH]usize = undefined;
    for (&cs, 0..) |*e, k| e.* = 0xC000 + n * 16 + k;
    return cs;
}

/// Distinct per-index guard seed and source, so a mixed-up record is detectable.
fn tagSeed(n: usize) u8 {
    return @truncate(n *% 7 +% 3);
}

fn tagSource(n: usize) Source {
    return if (n % 2 == 0) .buckets else .tree;
}

/// The record with every field a pure function of `n` (`size == n`).
fn tagged(n: usize) Record {
    return Record.withCallstack(addr(n), n, tagSource(n), tagSeed(n), sentinel(n));
}

/// Fisher-Yates shuffle of `0..n`, driven by `VintageRand(seed)` — the same shuffle as
/// `orisnik`'s store tests.
fn shuffled(comptime n: usize, seed: u32) [n]usize {
    var rng = VintageRand.init(seed);
    var v: [n]usize = undefined;
    for (&v, 0..) |*e, i| e.* = i;
    var i: usize = n;
    while (i > 1) {
        i -= 1;
        const j: usize = rng.next() % (i + 1);
        std.mem.swap(usize, &v[i], &v[j]);
    }
    return v;
}

test "add/find/remove round trip" {
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.add(addr(1), 40, .tree, 7));
    try testing.expectEqual(@as(usize, 1), store.len());
    const rec = store.find(addr(1)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 40), rec.size);
    try testing.expect(store.find(addr(2)) == null);
    const info = store.remove(addr(1)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(DebugInfo{ .size = 40, .source = .tree }, info);
    try testing.expectEqual(@as(usize, 0), store.len());
    try testing.expect(store.find(addr(1)) == null);
    try testing.expect(store.remove(addr(1)) == null); // double remove is reported
}

test "forward, backward and shuffled removal keep the index consistent" {
    // The point is the swap-the-last-into-the-hole path and tree re-linking across many
    // removal orders (page boundaries are covered by the book's own tests).
    const n = 200;
    var forward: [n]usize = undefined;
    var backward: [n]usize = undefined;
    for (0..n) |i| {
        forward[i] = i;
        backward[i] = n - 1 - i;
    }
    const orders = [3][n]usize{ forward, backward, shuffled(n, 1234) };
    const insert_order = shuffled(n, 42);
    for (orders) |order| {
        var store: RecordStore = .init();
        defer store.deinit();
        for (insert_order) |i| try testing.expect(store.addRecord(tagged(i)));
        var model: std.AutoHashMap(usize, usize) = .init(testing.allocator);
        defer model.deinit();
        for (0..n) |i| try model.put(i, i);
        for (order) |i| {
            const info = store.remove(addr(i)) orelse return error.TestUnexpectedResult;
            const expected = model.fetchRemove(i) orelse return error.TestUnexpectedResult;
            try testing.expectEqual(expected.value, info.size);
            try testing.expectEqual(@as(usize, model.count()), store.len());
            var it = model.keyIterator();
            while (it.next()) |j| {
                const rec = store.find(addr(j.*)) orelse return error.TestUnexpectedResult; // survivor still indexed
                try testing.expectEqual(j.*, rec.size);
                try testing.expectEqual(addr(j.*), rec.ptr);
                try testing.expectEqual(tagSeed(j.*), rec.guard_byte);
                try testing.expectEqual(tagSource(j.*), rec.source);
                try testing.expectEqual(sentinel(j.*), rec.callstack);
            }
            try testing.expect(store.find(addr(i)) == null);
        }
        try testing.expectEqual(@as(usize, 0), store.len());
    }
}

test "replace rekeys without duplicating" {
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.add(addr(1), 10, .buckets, 1));
    try testing.expect(store.add(addr(2), 20, .buckets, 2));
    const info = store.replace(addr(1), Record.init(addr(9), 300, .tree, 9)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(DebugInfo{ .size = 10, .source = .buckets }, info);
    try testing.expectEqual(@as(usize, 2), store.len()); // rekeyed, not duplicated
    try testing.expect(store.find(addr(1)) == null);
    const moved = store.find(addr(9)) orelse return error.TestUnexpectedResult; // new key indexed
    try testing.expectEqual(@as(usize, 300), moved.size);
    try testing.expectEqual(Source.tree, moved.source);
    try testing.expect(store.find(addr(2)) != null);
    try testing.expect(store.replace(addr(1), Record.init(addr(5), 1, .tree, 0)) == null);
}

test "update changes size and seed in place" {
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.add(addr(3), 10, .tree, 1));
    const info = store.update(addr(3), 64, 5, sentinel(3)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(DebugInfo{ .size = 10, .source = .tree }, info);
    const rec = store.find(addr(3)) orelse return error.TestUnexpectedResult; // still indexed
    try testing.expectEqual(@as(usize, 64), rec.size);
    try testing.expectEqual(@as(u8, 5), rec.guard_byte);
    try testing.expect(store.update(addr(4), 1, 0, sentinel(4)) == null);
}

test "first/next walk the records in address order, whatever the insertion order, before and after a removal" {
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.first() == null);
    const n = 50;
    for (shuffled(n, 42)) |i| try testing.expect(store.addRecord(tagged(i)));
    var expected: usize = 0;
    var cursor = store.first();
    // EXPLICIT: address-order tree walk; `cursor` is the state, not expressible as an
    // iterator.
    while (cursor) |record| : (cursor = store.next(record)) {
        try testing.expectEqual(addr(expected), record.ptr);
        expected += 1;
    }
    try testing.expectEqual(@as(usize, n), expected);
    // A removal between two complete walks leaves the second one consistent.
    _ = store.remove(addr(10));
    try testing.expect(store.find(addr(10)) == null);
    var seen: usize = 0;
    cursor = store.first();
    // EXPLICIT: as above.
    while (cursor) |record| : (cursor = store.next(record)) seen += 1;
    try testing.expectEqual(@as(usize, n - 1), seen);
}

test "forEachLive visits in storage order, not address order" {
    var store: RecordStore = .init();
    defer store.deinit();
    const order = [_]usize{ 5, 1, 9, 3 };
    for (order) |i| try testing.expect(store.addRecord(tagged(i)));
    const Log = struct {
        sizes: [4]usize = undefined,
        count: usize = 0,
        fn visit(self: *@This(), record: *Record) void {
            self.sizes[self.count] = record.size;
            self.count += 1;
        }
    };
    var log: Log = .{};
    store.forEachLive(&log, Log.visit);
    try testing.expectEqual(@as(usize, 4), log.count);
    try testing.expectEqualSlices(usize, &order, &log.sizes);
}

test "a removal from the middle perturbs the storage order" {
    // Swap-remove moves the last book record into the hole, so `forEachLive` no longer
    // lists records in the order they were added. Kills a doc/behaviour claim that storage
    // order is insertion order.
    var store: RecordStore = .init();
    defer store.deinit();
    for ([_]usize{ 1, 2, 3, 4 }) |i| try testing.expect(store.addRecord(tagged(i)));
    _ = store.remove(addr(2));
    const Log = struct {
        sizes: [4]usize = undefined,
        count: usize = 0,
        fn visit(self: *@This(), record: *Record) void {
            self.sizes[self.count] = record.size;
            self.count += 1;
        }
    };
    var log: Log = .{};
    store.forEachLive(&log, Log.visit);
    try testing.expectEqual(@as(usize, 3), log.count);
    try testing.expectEqualSlices(usize, &[_]usize{ 1, 4, 3 }, log.sizes[0..3]);
}

test "add reports OS refusal and records nothing" {
    var store: RecordStore = .init();
    defer store.deinit();
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    try testing.expect(!store.add(addr(1), 8, .buckets, 0));
    try testing.expectEqual(@as(usize, 0), store.len());
    try testing.expect(store.find(addr(1)) == null);
    os.test_vm.clearFailure();
    try testing.expect(store.add(addr(1), 8, .buckets, 0)); // recovers after OOM
}

test "remove last slot and purge release pages" {
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.add(addr(1), 1, .buckets, 0));
    try testing.expect(store.remove(addr(1)) != null);
    store.purge();
    try testing.expect(store.add(addr(2), 2, .tree, 0)); // usable after a full purge
}

test "records capture the allocating callstack" {
    // See `spomen_record.zig`'s callstack test: no frames exist to assert on when std has
    // stack tracing disabled (e.g. ReleaseSmall).
    if (!std.options.allow_stack_tracing) return error.SkipZigTest;
    var store: RecordStore = .init();
    defer store.deinit();
    try testing.expect(store.add(addr(1), 8, .buckets, 0));
    const rec = store.find(addr(1)) orelse return error.TestUnexpectedResult;
    // Zig cannot cheaply resolve symbols inside a unit test (that is `report()`'s later
    // job), so unlike `orisnik`'s test — which searches the rendered trace for this
    // test's name — this asserts only that a real frame was captured.
    try testing.expect(rec.callstack[0] != 0);
    // `update` recaptures.
    rec.callstack = [_]usize{0} ** spomen_record.MAX_CALLSTACK_DEPTH;
    _ = store.update(addr(1), 8, 0, Record.captureCallstack(@returnAddress()));
    try testing.expect(rec.callstack[0] != 0);
}

test "swap-remove moves the last record intact and leaves neighbours alone" {
    var store: RecordStore = .init();
    defer store.deinit();
    for (0..5) |i| try testing.expect(store.addRecord(tagged(i)));
    // Record 0 sits in slot 0; removing it moves the last record (4) into that slot.
    const info = store.remove(addr(0)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(DebugInfo{ .size = 0, .source = tagSource(0) }, info);
    try testing.expectEqual(@as(usize, 4), store.len());
    for (1..5) |i| {
        const rec = store.find(addr(i)) orelse return error.TestUnexpectedResult;
        try testing.expectEqual(i, rec.size);
        try testing.expectEqual(addr(i), rec.ptr);
        try testing.expectEqual(tagSeed(i), rec.guard_byte);
        try testing.expectEqual(tagSource(i), rec.source);
        try testing.expectEqual(sentinel(i), rec.callstack); // callstack preserved by the move
    }
}

test "replace preserves neighbours and update recaptures only its own record" {
    var store: RecordStore = .init();
    defer store.deinit();
    for (0..4) |i| try testing.expect(store.addRecord(tagged(i)));
    _ = store.replace(addr(1), Record.init(addr(9), 300, .tree, 9)) orelse return error.TestUnexpectedResult;
    _ = store.update(addr(2), 64, 5, Record.captureCallstack(@returnAddress())) orelse return error.TestUnexpectedResult;
    for ([_]usize{ 0, 3 }) |i| { // untouched neighbours
        const rec = store.find(addr(i)) orelse return error.TestUnexpectedResult;
        try testing.expectEqual(i, rec.size);
        try testing.expectEqual(tagSeed(i), rec.guard_byte);
        try testing.expectEqual(tagSource(i), rec.source);
        try testing.expectEqual(sentinel(i), rec.callstack);
    }
    // `update` changed size/seed and recaptured: the deterministic sentinel is gone (a
    // fresh capture is never that value, even all-zero when tracing is unavailable).
    const upd = store.find(addr(2)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 64), upd.size);
    try testing.expectEqual(@as(u8, 5), upd.guard_byte);
    try testing.expectEqual(tagSource(2), upd.source);
    try testing.expect(!std.mem.eql(usize, &upd.callstack, &sentinel(2)));
    // `replace` builds a fresh record at the new key.
    const rep = store.find(addr(9)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 300), rep.size);
    try testing.expectEqual(@as(u8, 9), rep.guard_byte);
    try testing.expectEqual(addr(9), rep.ptr);
}
