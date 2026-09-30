// SPDX-License-Identifier: MIT OR Apache-2.0
//! The dense, page-chained storage behind the allocation-record map. Ports
//! `Cpp/hpha.h`'s `virtual_book<T>` (instantiated for `debug_record`), mirroring
//! `orisnik`'s `Rust/src/spomen/book.rs`.
//!
//! A `RecordBook` is an append-only-at-the-back sequence of `Record`s spread over
//! `PAGE_SIZE` OS pages. It supports exactly the operations HPHA's `debug_record_map`
//! uses: `pushBack`, `popBack`, `back`, and `purge`. Removing a record from the
//! *middle* is the map's job (swap the last record into the hole, then pop — see
//! `spomen_store.zig`); the book itself never reorders anything.
//!
//! # Layout
//! Same tail-of-page shape as `bucket.zig`'s `Page`: a `BookPage` link sits in the last
//! `@sizeOf(BookPage)` bytes of each mapping and `CAPACITY` `Record` slots are packed
//! from the page's start. Pages are chained on an `IntrusiveList`.
//!
//! # Invariants
//! - Every page before `cur` in the chain is full (`CAPACITY` live records); `cur` holds
//!   `next` live records in slots `0..next`; every page after `cur` is empty spare
//!   capacity kept for reuse until `purge`.
//! - `cur` is `null` exactly when the book owns no pages at all (which implies
//!   `len == 0`).
//! - `len` is the total number of live records across all pages.
//!
//! A book is self-referential (the page list's sentinel) and follows the same
//! **non-move-after-first-use** contract as `list.zig`'s `IntrusiveList`: do not move a
//! `RecordBook` after the first call to any of its methods.
//!
//! # No `Drop`
//! Zig has no destructors. `Record` is plain data (its callstack is a fixed array of
//! addresses, see `spomen_record.zig`), so `popBack` simply returns the record by value
//! and there is nothing to drop; but the *pages* are OS mappings that must be returned,
//! so the owner must call `deinit` (the mirror of `orisnik`'s `Drop`, HPHA's
//! `~virtual_book`: `clear(); purge();`).

const std = @import("std");
const list = @import("list.zig");
const os = @import("os.zig");
const spomen_record = @import("spomen_record.zig");

const Record = spomen_record.Record;

/// A book page's bookkeeping, placed at the very tail of its mapping.
pub const BookPage = extern struct {
    /// This page's membership in the book's page chain. Byte offset 0 (required by
    /// `IntrusiveList`); the whole struct is this link.
    link: list.ListLink = list.ListLink.UNLINKED,
};

/// Bytes each mapping reserves at its tail for the `BookPage`.
const TAIL: usize = @sizeOf(BookPage);
/// Record slots per page.
pub const CAPACITY: usize = (os.PAGE_SIZE - TAIL) / @sizeOf(Record);

comptime {
    // Layout lock — the whole page tail is the list link (matches `orisnik`'s
    // `#[repr(C)]` `BookPage`).
    std.debug.assert(@sizeOf(BookPage) == @sizeOf(list.ListLink));
    std.debug.assert(@offsetOf(BookPage, "link") == 0);
    std.debug.assert(CAPACITY >= 1); // a page must hold at least one record
    // `os.map` returns `PAGE_SIZE`-aligned memory, so a slot at `i * @sizeOf(Record)`
    // is aligned as long as the size is a multiple of the alignment (always true in
    // Zig) and the alignment divides `PAGE_SIZE`.
    std.debug.assert(os.PAGE_SIZE % @alignOf(Record) == 0);
    std.debug.assert(@sizeOf(Record) % @alignOf(Record) == 0);
    // The tail link must itself be aligned at its fixed position.
    std.debug.assert((os.PAGE_SIZE - TAIL) % @alignOf(BookPage) == 0);
}

/// The base of the mapping `page`'s tail slot lives in.
///
/// `page` must be the tail `BookPage` of a live `PAGE_SIZE` mapping.
fn baseOf(page: *BookPage) [*]u8 {
    // SAFETY: `@ptrCast` from `*BookPage` to a byte pointer only widens the view to
    // bytes; it keeps the same address and the pointee's provenance (`page` is a live
    // tail slot, caller's contract), and dereferences nothing.
    const at: [*]u8 = @ptrCast(page);
    // SAFETY: `page` is at `PAGE_SIZE - TAIL` bytes into its mapping (caller's
    // contract), so stepping back that far lands on the mapping's base, inside the
    // same allocation.
    return at - (os.PAGE_SIZE - TAIL);
}

/// Address of record slot `index` in `page`.
///
/// `page` must be the tail `BookPage` of a live `PAGE_SIZE` mapping and
/// `index < CAPACITY`.
fn slot(page: *BookPage, index: usize) *Record {
    const base = baseOf(page);
    std.debug.assert(index < CAPACITY);
    // SAFETY: `index < CAPACITY`, and `CAPACITY * @sizeOf(Record) <= PAGE_SIZE - TAIL`,
    // so this pointer step stays inside the mapping's record area (`base` is the
    // start of a live `PAGE_SIZE` mapping, `baseOf`'s contract).
    const at = base + index * @sizeOf(Record);
    // ALIGN: `base` is PAGE_SIZE-aligned (`os.map`'s guarantee) and
    // `index * @sizeOf(Record)` is a multiple of `@alignOf(Record)`, which divides
    // `PAGE_SIZE` (comptime-asserted above).
    // SAFETY: `at` is the start of slot `index`, wholly inside the live mapping's
    // record area; `@ptrCast` only retypes it as `*Record`. Whether the slot holds a
    // live record is each caller's obligation (`pushBack` writes a dead slot,
    // `back`/`popBack` read a live one).
    return @ptrCast(@alignCast(at));
}

/// Dense, page-chained record storage. See the module doc.
pub const RecordBook = struct {
    /// The chain of mapped pages, in fill order.
    pages: list.IntrusiveList(BookPage) = .init(),
    /// The page holding the next free slot (see the module invariants), or `null` when
    /// there are no pages.
    cur: ?*BookPage = null,
    /// Live records in `cur`, i.e. the index of its next free slot (`0..=CAPACITY`).
    next: usize = 0,
    /// Live records in the whole book.
    len: usize = 0,

    /// An empty book owning no pages. The page list's sentinel is lazily linked on
    /// first use (see `list.zig`'s module doc).
    pub fn init() RecordBook {
        return .{};
    }

    /// Drops every live record, then returns all pages to the OS. Ports
    /// `~virtual_book`: `clear(); purge();`. Zig has no `Drop`, so the owner must call
    /// this; the book must not be used afterwards.
    pub fn deinit(self: *RecordBook) void {
        // EXPLICIT: draining loop; the state is the shrinking `len`, not expressible
        // as an iterator over a book being mutated.
        while (!self.isEmpty()) _ = self.popBack();
        self.purge();
    }

    /// Whether the book holds no live records.
    pub fn isEmpty(self: *const RecordBook) bool {
        return self.len == 0;
    }

    /// The page after `page` in the chain, or `null` if `page` is the last.
    ///
    /// `page` must be a live page of this book.
    fn nextPage(self: *RecordBook, page: *BookPage) ?*BookPage {
        // `page` is live and linked (caller's contract), so its `next` is non-null.
        const nxt = page.link.next.?;
        if (nxt == self.pages.sentinel()) return null;
        // `nxt` is not the sentinel, so it is the `link` field of a live
        // `BookPage` (only `grow` links nodes, and only `BookPage`s).
        // SAFETY: as just established, `nxt` is the `link` field of a live `BookPage`,
        // so `@fieldParentPtr` recovers that `BookPage`.
        return @fieldParentPtr("link", nxt);
    }

    /// The page before `page` in the chain, or `null` if `page` is the first.
    ///
    /// `page` must be a live page of this book.
    fn prevPage(self: *RecordBook, page: *BookPage) ?*BookPage {
        // `page` is live and linked (caller's contract), so its `prev` is non-null.
        const prv = page.link.prev.?;
        if (prv == self.pages.sentinel()) return null;
        // `prv` is not the sentinel, so it is the `link` field of a live
        // `BookPage` (only `grow` links nodes, and only `BookPage`s).
        // SAFETY: as just established, `prv` is the `link` field of a live `BookPage`,
        // so `@fieldParentPtr` recovers that `BookPage`.
        return @fieldParentPtr("link", prv);
    }

    /// Maps and links one fresh page at the end of the chain, or `null` if the OS
    /// refused it.
    fn grow(self: *RecordBook) ?*BookPage {
        const mem = os.map(os.PAGE_SIZE) orelse return null;
        // SAFETY: `mem` is a live `PAGE_SIZE` mapping (just returned by `os.map`) and
        // `PAGE_SIZE - TAIL < PAGE_SIZE`, so the tail pointer stays inside it.
        const tail = mem + (os.PAGE_SIZE - TAIL);
        // ALIGN: `mem` is PAGE_SIZE-aligned and `PAGE_SIZE - TAIL` is a multiple of
        // `@alignOf(BookPage)` (comptime-asserted above).
        // SAFETY: `tail` is the start of the last `@sizeOf(BookPage)` bytes of the fresh
        // mapping, exclusively owned; `@ptrCast` retypes them as the (about to be
        // initialised) `BookPage`, and nothing reads it before the write below.
        const page: *BookPage = @ptrCast(@alignCast(tail));
        // SAFETY: `page` is inside the fresh mapping (above), exclusively owned; this is
        // the slot's first write, so no prior value is read.
        page.* = .{ .link = list.ListLink.UNLINKED };
        self.pages.pushBack(page);
        return page;
    }

    /// Appends `value` and returns the address it now lives at, or `null` if a new page
    /// was needed and the OS refused it (nothing is stored then). Ports
    /// `virtual_book::push_back`.
    pub fn pushBack(self: *RecordBook, value: Record) ?*Record {
        var page: *BookPage = undefined;
        var index: usize = 0;
        if (self.cur != null and self.next < CAPACITY) {
            page = self.cur.?;
            index = self.next;
        } else {
            // When `cur` is non-null it is a live page of this book.
            const candidate: ?*BookPage = if (self.cur) |cur| self.nextPage(cur) else null;
            page = candidate orelse (self.grow() orelse return null);
            self.cur = page;
            self.next = 0;
            index = 0;
        }
        // SAFETY: `page` is a live page of this book and `index < CAPACITY` (the
        // fill-in-place branch checked `next < CAPACITY`; the fresh/advanced branch uses
        // slot 0), so `slot` returns an in-bounds, aligned, currently dead slot.
        const at = slot(page, index);
        // SAFETY: `at` is the book's next free slot — inside a live mapping, aligned
        // (see `slot`), and holding no live record (slots `>= next` are dead), so this
        // overwrites nothing live.
        at.* = value;
        self.next = index + 1;
        self.len += 1;
        return at;
    }

    /// The most recently pushed live record's address. Ports `virtual_book::back`.
    ///
    /// The book must be non-empty (asserted in safe builds).
    pub fn back(self: *RecordBook) *Record {
        std.debug.assert(!self.isEmpty());
        if (self.next == 0) {
            // The book is non-empty with `next == 0`, so `cur` is live and a full page
            // precedes it (module invariants), hence `.?` cannot fail.
            const prev = self.prevPage(self.cur.?).?;
            // SAFETY: `prev` is a live, full page of this book and `CAPACITY - 1 <
            // CAPACITY`, so `slot` returns its last, live record.
            return slot(prev, CAPACITY - 1);
        }
        // SAFETY: `cur` is a live page of this book (non-empty book) and `next - 1 <
        // CAPACITY`, so `slot` returns the last, live record.
        return slot(self.cur.?, self.next - 1);
    }

    /// Removes the last record and returns it by value. Ports `virtual_book::pop_back`,
    /// which ran the destructor in place — a `Record` needs none here, and returning by
    /// value lets the record map *move* the last record into a vacated slot.
    ///
    /// The book must be non-empty (asserted in safe builds).
    pub fn popBack(self: *RecordBook) Record {
        std.debug.assert(!self.isEmpty());
        if (self.next == 0) {
            // Non-empty with `next == 0`, so `cur` is live and preceded by a full page
            // (module invariants).
            const prev = self.prevPage(self.cur.?);
            std.debug.assert(prev != null);
            self.cur = prev;
            self.next = CAPACITY;
        }
        const index = self.next - 1;
        self.next = index;
        self.len -= 1;
        // SAFETY: `cur` is a live page of this book and `index < CAPACITY`, so `slot`
        // returns an in-bounds, aligned slot (the one just vacated, read below).
        const at = slot(self.cur.?, index);
        // SAFETY: `at` held the last live record (module invariants); `next` was
        // decremented above so the slot is now dead and the book will never read it
        // again — the value moves to the caller.
        return at.*;
    }

    /// Calls `visit(context, record)` for every live record in *storage* order (the order
    /// the records sit in the book, which a removal from the middle perturbs — not address
    /// order), changing nothing. Walks the page chain from the
    /// first page up to and including `cur`, visiting `next` records in `cur` and
    /// `CAPACITY` in each page before it. Mirrors `orisnik`'s `for_each_live`.
    pub fn forEachLive(
        self: *RecordBook,
        context: anytype,
        comptime visit: fn (@TypeOf(context), *Record) void,
    ) void {
        const cur = self.cur orelse return;
        var page = self.pages.front() orelse return;
        // EXPLICIT: walks the page chain up to and including `cur`; `page` is the state.
        while (true) {
            const live = if (page == cur) self.next else CAPACITY;
            for (0..live) |index| {
                // SAFETY: `page` is a live page of this book and `index < CAPACITY`
                // (`live <= CAPACITY`), so `slot` returns a live record — every slot below
                // the fill mark is initialised.
                visit(context, slot(page, index));
            }
            if (page == cur) return;
            page = self.nextPage(page) orelse return;
        }
    }

    /// Returns unused pages to the OS: every spare page after `cur`, and — when the
    /// book is empty — every page. Ports `virtual_book::purge`.
    pub fn purge(self: *RecordBook) void {
        const cur = self.cur orelse return;
        const empty = self.isEmpty();
        var page: ?*BookPage = if (empty) blk: {
            std.debug.assert(self.prevPage(cur) == null); // an empty book's `cur` is its first page
            break :blk cur;
        } else self.nextPage(cur);
        // EXPLICIT: walks the chain tail while unlinking, so the loop state is the
        // current page pointer, not expressible as an iterator over a list being
        // mutated.
        while (page) |p| {
            const after = self.nextPage(p);
            list.unlinkNode(p);
            // `p` is the tail of a live mapping this book obtained from
            // `os.map(PAGE_SIZE)` and has just unlinked; nothing references it now.
            const base = baseOf(p);
            // SAFETY: `base`/`PAGE_SIZE` describe exactly the mapping `grow` obtained
            // from `os.map(PAGE_SIZE)`, not yet unmapped (the page was live until
            // unlinked just above).
            os.unmap(base, os.PAGE_SIZE);
            page = after;
        }
        if (empty) {
            self.cur = null;
            self.next = 0;
        }
    }
};

const testing = std.testing;

/// The pointer is only ever compared, never dereferenced, in these tests.
fn rec(tag: usize) Record {
    // SAFETY: made-up address, never dereferenced.
    // PROVENANCE: no allocation; a bare integer address used only as a comparison key.
    return Record.init(@ptrFromInt(8 + tag * 8), tag, .buckets, 0);
}

test "push/pop is LIFO and back tracks the top" {
    var book: RecordBook = .init();
    defer book.deinit();
    try testing.expect(book.isEmpty());
    for (0..5) |i| {
        const at = book.pushBack(rec(i)) orelse return error.TestUnexpectedResult;
        try testing.expectEqual(at, book.back());
    }
    try testing.expectEqual(@as(usize, 5), book.len);
    var i: usize = 5;
    while (i > 0) {
        i -= 1;
        try testing.expectEqual(i, book.popBack().size);
    }
    try testing.expect(book.isEmpty());
}

test "spans pages and reuses spare capacity before growing" {
    var book: RecordBook = .init();
    defer book.deinit();
    const n = CAPACITY * 2 + 3;
    for (0..n) |i| _ = book.pushBack(rec(i)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(n, book.len);
    // Pop back down across a page boundary, then refill: the spare page is reused, so
    // no further mapping is needed — proven by refusing every map from here on.
    var i: usize = n;
    while (i > CAPACITY) {
        i -= 1;
        try testing.expectEqual(i, book.popBack().size);
    }
    try testing.expectEqual(CAPACITY, book.len);
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    for (CAPACITY..n) |k| _ = book.pushBack(rec(k)) orelse return error.TestUnexpectedResult;
    os.test_vm.clearFailure();
    i = n;
    while (i > 0) {
        i -= 1;
        try testing.expectEqual(i, book.popBack().size);
    }
}

test "purge keeps live pages and frees spares" {
    var book: RecordBook = .init();
    defer book.deinit();
    for (0..CAPACITY + 1) |i| _ = book.pushBack(rec(i)) orelse return error.TestUnexpectedResult;
    // Drain the second page's only record: one spare page remains.
    try testing.expectEqual(CAPACITY, book.popBack().size);
    book.purge();
    try testing.expectEqual(CAPACITY, book.len);
    // Still fully usable after purging the spare.
    _ = book.pushBack(rec(CAPACITY)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 0), @intFromPtr(book.back()) % @alignOf(Record));
    // Fully drain and purge everything; the book must restart cleanly.
    while (!book.isEmpty()) _ = book.popBack();
    book.purge();
    try testing.expect(book.cur == null);
    _ = book.pushBack(rec(0)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 1), book.len);
}

test "deinit drains every record and returns every page" {
    // Zig has no drop glue to observe (see the module doc), so this checks the
    // mirror of `orisnik`'s drop test instead: `deinit` leaves an empty, page-less
    // book. The book is deinit'd in place, never moved (non-move contract).
    var book: RecordBook = .init();
    for (0..CAPACITY + 2) |i| _ = book.pushBack(rec(i)) orelse return error.TestUnexpectedResult;
    book.deinit();
    try testing.expect(book.isEmpty());
    try testing.expect(book.cur == null);
    try testing.expect(book.pages.isEmpty());
}

const VisitLog = struct {
    seen: [CAPACITY * 2 + 3]usize = undefined,
    count: usize = 0,

    fn visit(self: *VisitLog, record: *Record) void {
        self.seen[self.count] = record.size;
        self.count += 1;
    }
};

test "forEachLive visits every live record in storage order" {
    var book: RecordBook = .init();
    defer book.deinit();
    var empty_log: VisitLog = .{};
    book.forEachLive(&empty_log, VisitLog.visit);
    try testing.expectEqual(@as(usize, 0), empty_log.count);

    const n = CAPACITY * 2 + 3; // spans three pages
    for (0..n) |i| _ = book.pushBack(rec(i)) orelse return error.TestUnexpectedResult;
    var log: VisitLog = .{};
    book.forEachLive(&log, VisitLog.visit);
    try testing.expectEqual(n, log.count);
    for (0..n) |i| try testing.expectEqual(i, log.seen[i]);

    // Popped records and spare pages are not visited.
    for (0..5) |_| _ = book.popBack();
    var after: VisitLog = .{};
    book.forEachLive(&after, VisitLog.visit);
    try testing.expectEqual(n - 5, after.count);
    try testing.expectEqual(n - 6, after.seen[after.count - 1]);
}

test "push reports OS refusal as null" {
    var book: RecordBook = .init();
    defer book.deinit();
    os.test_vm.failMapAfter(0);
    defer os.test_vm.clearFailure();
    try testing.expect(book.pushBack(rec(0)) == null);
    try testing.expect(book.isEmpty());
}
