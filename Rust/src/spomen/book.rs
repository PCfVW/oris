// SPDX-License-Identifier: MIT OR Apache-2.0
//! The dense, page-chained storage behind the allocation-record map. Ports
//! `Cpp/hpha.h`'s `virtual_book<T>` (instantiated for `debug_record`).
//!
//! A [`RecordBook`] is an append-only-at-the-back sequence of [`Record`]s spread over
//! `PAGE_SIZE` OS pages. It supports exactly the operations HPHA's `debug_record_map`
//! uses: [`push_back`](RecordBook::push_back), [`pop_back`](RecordBook::pop_back),
//! [`back`](RecordBook::back), and [`purge`](RecordBook::purge). Removing a record from
//! the *middle* is the map's job (swap the last record into the hole, then pop — see
//! [`crate::spomen::store`]); the book itself never reorders anything.
//!
//! # Layout
//! Same tail-of-page shape as `bucket.rs`'s `Page`: a [`BookPage`] link sits in the last
//! `size_of::<BookPage>()` bytes of each mapping and `CAPACITY` [`Record`] slots are
//! packed from the page's start. Pages are chained on an [`IntrusiveList`].
//!
//! # Invariants
//! - Every page before `cur` in the chain is full (`CAPACITY` live records); `cur` holds
//!   `next` live records in slots `0..next`; every page after `cur` is empty spare
//!   capacity kept for reuse until [`RecordBook::purge`].
//! - `cur` is null exactly when the book owns no pages at all (which implies `len == 0`).
//! - `len` is the total number of live records across all pages.
//!
//! A book is self-referential (the page list's sentinel) and follows the same
//! non-move-after-first-use contract as every other intrusive container here.
//!
//! # Records own heap memory
//! [`Record`] carries a `Backtrace` and so has drop glue. The book moves records with
//! `ptr::write`/`ptr::read` and drops each exactly once: [`RecordBook::pop_back`] hands
//! ownership of the popped record to its caller, and `Drop` drains whatever is left.

use crate::home::Home;
use crate::list::{IntrusiveList, ListLink, ListNode, unlink_node};
use crate::os;
use crate::spomen::record::Record;
use core::cell::Cell;
use core::ptr::NonNull;

/// A book page's bookkeeping, placed at the very tail of its mapping.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: crate-internal; the whole struct is the list link.
pub(crate) struct BookPage {
    /// This page's membership in the book's page chain. Byte offset 0 (required by
    /// [`ListNode`]).
    link: ListLink,
}

// SAFETY: `link` is BookPage's first field (repr(C) guarantees offset 0).
unsafe impl ListNode for BookPage {}

/// Bytes each mapping reserves at its tail for the [`BookPage`].
const TAIL: usize = size_of::<BookPage>();
/// Record slots per page.
const CAPACITY: usize = (os::PAGE_SIZE - TAIL) / size_of::<Record>();

const _: () = assert!(CAPACITY >= 1, "a page must hold at least one record");
// `os::map` returns `PAGE_SIZE`-aligned memory, so a slot at `i * size_of::<Record>()`
// is aligned as long as the size is a multiple of the alignment (always true in Rust)
// and the alignment divides `PAGE_SIZE`.
const _: () = assert!(os::PAGE_SIZE % align_of::<Record>() == 0);
// The tail link must itself be aligned at its fixed position.
const _: () = assert!((os::PAGE_SIZE - TAIL) % align_of::<BookPage>() == 0);

/// Dense, page-chained record storage. See the module doc.
pub(crate) struct RecordBook {
    /// The chain of mapped pages, in fill order.
    pages: IntrusiveList<BookPage>,
    /// The page holding the next free slot (see the module invariants), or null when
    /// there are no pages.
    cur: Cell<*mut BookPage>,
    /// Live records in `cur`, i.e. the index of its next free slot (`0..=CAPACITY`).
    next: Cell<usize>,
    /// Live records in the whole book.
    len: Cell<usize>,
    /// Where this book stood when it first mapped a page; `Drop` leaks instead of walking a
    /// page chain whose sentinel a later move left stale (see [`Home`]).
    home: Home,
}

/// The base of the mapping `page`'s tail slot lives in.
///
/// # Safety
/// `page` must be the tail [`BookPage`] of a live `PAGE_SIZE` mapping.
unsafe fn base_of(page: *mut BookPage) -> *mut u8 {
    // SAFETY: `page` is at `PAGE_SIZE - TAIL` bytes into its mapping (caller's
    // contract), so stepping back that far stays inside the same mapping.
    unsafe { page.cast::<u8>().byte_sub(os::PAGE_SIZE - TAIL) }
}

/// Address of record slot `index` in `page`.
///
/// # Safety
/// `page` must be the tail [`BookPage`] of a live `PAGE_SIZE` mapping and
/// `index < CAPACITY`.
unsafe fn slot(page: *mut BookPage, index: usize) -> *mut Record {
    // SAFETY: forwarded from this function's contract.
    let base = unsafe { base_of(page) };
    debug_assert!(index < CAPACITY);
    // SAFETY: `index < CAPACITY`, and `CAPACITY * size_of::<Record>() <= PAGE_SIZE -
    // TAIL`, so the slot lies wholly inside the mapping's record area.
    let at = unsafe { base.byte_add(index * size_of::<Record>()) };
    // ALIGN: `base` is PAGE_SIZE-aligned (`os::map`'s guarantee) and
    // `index * size_of::<Record>()` is a multiple of `align_of::<Record>()`, which
    // divides `PAGE_SIZE` (const-asserted above).
    #[allow(clippy::cast_ptr_alignment)]
    at.cast::<Record>()
}

impl RecordBook {
    /// An empty book owning no pages. The page list's sentinel is lazily linked on
    /// first use (see `list.rs`'s module doc).
    pub(crate) const fn new() -> Self {
        Self {
            pages: IntrusiveList::new(),
            cur: Cell::new(core::ptr::null_mut()),
            next: Cell::new(0),
            len: Cell::new(0),
            home: Home::new(),
        }
    }

    /// Number of live records.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.len.get()
    }

    /// Whether the book holds no live records.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.len.get() == 0
    }

    /// The page after `page` in the chain, or null if `page` is the last.
    ///
    /// # Safety
    /// `page` must be a live page of this book.
    unsafe fn next_page(&self, page: *mut BookPage) -> *mut BookPage {
        let link = BookPage::link(
            // SAFETY: `page` is live, hence non-null.
            unsafe { NonNull::new_unchecked(page) },
        );
        // SAFETY: `link` belongs to a live, linked page (caller's contract).
        let next = unsafe { ListLink::next(link.as_ptr()) };
        if next == self.pages.sentinel() {
            return core::ptr::null_mut();
        }
        next.cast::<BookPage>()
    }

    /// The base address of every mapped page, in chain order — lets a test that deliberately
    /// makes `Drop` leak (a moved book) return the mappings itself.
    #[cfg(test)]
    pub(crate) fn page_bases(&self) -> Vec<NonNull<u8>> {
        let mut bases = Vec::new();
        let mut page = self
            .pages
            .front()
            .map_or(core::ptr::null_mut(), NonNull::as_ptr);
        // EXPLICIT: chain walk; the current page pointer is the state.
        while !page.is_null() {
            // SAFETY: `page` is a live page of this book (test-only walk, nothing unmapped).
            let base = unsafe { base_of(page) };
            bases.push(NonNull::new(base).expect("a mapping base is non-null"));
            // SAFETY: `page` is a live page of this book.
            page = unsafe { self.next_page(page) };
        }
        bases
    }

    /// The page before `page` in the chain, or null if `page` is the first.
    ///
    /// # Safety
    /// `page` must be a live page of this book.
    unsafe fn prev_page(&self, page: *mut BookPage) -> *mut BookPage {
        let link = BookPage::link(
            // SAFETY: `page` is live, hence non-null.
            unsafe { NonNull::new_unchecked(page) },
        );
        // SAFETY: `link` belongs to a live, linked page (caller's contract).
        let prev = unsafe { ListLink::prev(link.as_ptr()) };
        if prev == self.pages.sentinel() {
            return core::ptr::null_mut();
        }
        prev.cast::<BookPage>()
    }

    /// Maps and links one fresh page at the end of the chain.
    fn grow(&self) -> Option<*mut BookPage> {
        let mem = os::map(os::PAGE_SIZE)?;
        self.home.latch(self);
        // SAFETY: `mem` is a live `PAGE_SIZE` mapping (just returned by `os::map`), so
        // the tail offset is inside it.
        let tail = unsafe { mem.as_ptr().byte_add(os::PAGE_SIZE - TAIL) };
        // ALIGN: `mem` is PAGE_SIZE-aligned and `PAGE_SIZE - TAIL` is a multiple of
        // `align_of::<BookPage>()` (const-asserted above).
        #[allow(clippy::cast_ptr_alignment)]
        let page = tail.cast::<BookPage>();
        // SAFETY: `page` is inside the fresh mapping (above), exclusively owned; this
        // is the slot's first write, so no prior value is dropped or read.
        unsafe {
            page.write(BookPage {
                link: ListLink::UNLINKED,
            });
        }
        // SAFETY: `page` is non-null (derived from a `NonNull` mapping).
        let node = unsafe { NonNull::new_unchecked(page) };
        self.pages.push_back(node);
        Some(page)
    }

    /// Appends `value` and returns the address it now lives at, or `None` if a new page
    /// was needed and the OS refused it (`value` is then dropped). Ports
    /// `virtual_book::push_back`.
    pub(crate) fn push_back(&self, value: Record) -> Option<NonNull<Record>> {
        let cur = self.cur.get();
        let (page, index) = if !cur.is_null() && self.next.get() < CAPACITY {
            (cur, self.next.get())
        } else {
            let candidate = if cur.is_null() {
                core::ptr::null_mut()
            } else {
                // SAFETY: `cur` is a live page of this book (non-null branch).
                unsafe { self.next_page(cur) }
            };
            let page = if candidate.is_null() {
                self.grow()?
            } else {
                candidate
            };
            self.cur.set(page);
            self.next.set(0);
            (page, 0)
        };
        // SAFETY: `page` is a live page of this book and `index < CAPACITY` (the
        // fill-in-place branch checked `next < CAPACITY`; the fresh/advanced branch
        // uses slot 0).
        let at = unsafe { slot(page, index) };
        // SAFETY: `at` is the book's next free slot — inside a live mapping, aligned
        // (see `slot`), and holding no live record (slots `>= next` are dead), so this
        // is a first write with no prior value to drop.
        unsafe { at.write(value) };
        self.next.set(index + 1);
        self.len.set(self.len.get() + 1);
        // SAFETY: `at` is non-null (inside a mapping).
        Some(unsafe { NonNull::new_unchecked(at) })
    }

    /// The most recently pushed live record's address, or `None` if the book is empty.
    /// Ports `virtual_book::back` (which asserts non-empty; a checked `Option` keeps this
    /// safe fn sound in release builds too).
    #[must_use]
    pub(crate) fn back(&self) -> Option<NonNull<Record>> {
        if self.is_empty() {
            return None;
        }
        let (page, index) = if self.next.get() == 0 {
            // SAFETY: the book is non-empty with `next == 0`, so `cur` is live and a
            // full page precedes it (module invariants).
            let prev = unsafe { self.prev_page(self.cur.get()) };
            (prev, CAPACITY - 1)
        } else {
            (self.cur.get(), self.next.get() - 1)
        };
        // SAFETY: `page` is a live page of this book and `index < CAPACITY`.
        let at = unsafe { slot(page, index) };
        // SAFETY: `at` is non-null (inside a mapping).
        Some(unsafe { NonNull::new_unchecked(at) })
    }

    /// Calls `visit` for every live record, in the order they were stored (page by page),
    /// changing nothing. The walk follows the pages' own links and compares against the page
    /// list's sentinel by *address* only — it never dereferences a stored pointer to the
    /// sentinel, which is what makes it usable from `Orisnik`'s `Drop` (see
    /// [`crate::spomen::store::RecordStore::for_each_live`]).
    pub(crate) fn for_each_live(&self, mut visit: impl FnMut(NonNull<Record>)) {
        let cur = self.cur.get();
        if cur.is_null() {
            return;
        }
        let Some(first) = self.pages.front() else {
            return;
        };
        let mut page = first.as_ptr();
        // EXPLICIT: walks the page chain up to and including `cur`; `page` is the state.
        loop {
            let live = if page == cur {
                self.next.get()
            } else {
                CAPACITY
            };
            for index in 0..live {
                // SAFETY: `page` is a live page of this book and `index < CAPACITY`
                // (`live <= CAPACITY`).
                let at = unsafe { slot(page, index) };
                // SAFETY: `at` is non-null (inside a mapping).
                visit(unsafe { NonNull::new_unchecked(at) });
            }
            if page == cur {
                return;
            }
            // SAFETY: `page` is a live page of this book.
            page = unsafe { self.next_page(page) };
            if page.is_null() {
                return;
            }
        }
    }

    /// Removes the last record and returns it by value; the caller now owns it (and
    /// its callstack) and must drop it or move it into another slot. Ports
    /// `virtual_book::pop_back`, which ran the destructor in place — ownership
    /// transfer is the by-value equivalent, and lets the record map *move* the last
    /// record into a vacated slot instead of copying it. Returns `None` if the book is
    /// empty.
    pub(crate) fn pop_back(&self) -> Option<Record> {
        if self.is_empty() {
            return None;
        }
        if self.next.get() == 0 {
            // SAFETY: non-empty with `next == 0`, so `cur` is live and preceded by a
            // full page (module invariants).
            let prev = unsafe { self.prev_page(self.cur.get()) };
            debug_assert!(!prev.is_null());
            self.cur.set(prev);
            self.next.set(CAPACITY);
        }
        let index = self.next.get() - 1;
        self.next.set(index);
        self.len.set(self.len.get() - 1);
        // SAFETY: `cur` is a live page of this book and `index < CAPACITY`.
        let at = unsafe { slot(self.cur.get(), index) };
        // SAFETY: `at` held the last live record (module invariants); `next` was
        // decremented above so the slot is now dead and will never be read or dropped
        // again by the book — ownership moves to the caller.
        Some(unsafe { at.read() })
    }

    /// Returns unused pages to the OS: every spare page after `cur`, and — when the
    /// book is empty — every page. Ports `virtual_book::purge`.
    pub(crate) fn purge(&self) {
        let cur = self.cur.get();
        if cur.is_null() {
            return;
        }
        let empty = self.is_empty();
        let mut page = if empty {
            debug_assert!(
                // SAFETY: `cur` is a live page of this book.
                unsafe { self.prev_page(cur) }.is_null(),
                "an empty book's `cur` is its first page"
            );
            cur
        } else {
            // SAFETY: `cur` is a live page of this book.
            unsafe { self.next_page(cur) }
        };
        // EXPLICIT: walks the chain tail while unlinking, so the loop state is the
        // current page pointer, not expressible as an iterator over a list being
        // mutated.
        while !page.is_null() {
            // SAFETY: `page` is a live page of this book.
            let after = unsafe { self.next_page(page) };
            // SAFETY: `page` is non-null.
            let node = unsafe { NonNull::new_unchecked(page) };
            unlink_node(node);
            // SAFETY: `page` is the tail of a live mapping this book obtained from
            // `os::map(PAGE_SIZE)` and has just unlinked; nothing references it now.
            let base = unsafe { base_of(page) };
            // SAFETY: `base` is non-null (a mapping base).
            let base = unsafe { NonNull::new_unchecked(base) };
            // SAFETY: `base`/`PAGE_SIZE` describe exactly the mapping `grow` obtained
            // from `os::map(PAGE_SIZE)`, not yet unmapped (the page was live until
            // unlinked just above).
            unsafe { os::unmap(base, os::PAGE_SIZE) };
            page = after;
        }
        if empty {
            self.cur.set(core::ptr::null_mut());
            self.next.set(0);
        }
    }
}

impl Drop for RecordBook {
    /// Drops every live record (running each callstack's destructor), then returns all
    /// pages. Ports `~virtual_book`: `clear(); purge();`.
    ///
    /// Unlike [`RecordBook::purge`], the pages are *not* unlinked first. `drop` receives
    /// `&mut self`, whose protector covers the whole book — including the page list's
    /// sentinel — for the entire call, and the pages' links hold the sentinel's address
    /// through pointers derived *before* this call; unlinking would write to the sentinel
    /// through one of those older pointers, which Tree Borrows (rightly) rejects as a
    /// foreign write to a protected tag (found by Miri). The whole list dies with the
    /// book, so unlinking would be wasted work anyway; reads through the old pointers are
    /// permitted.
    fn drop(&mut self) {
        // A book that mapped pages and was then moved has a stale sentinel: walking it would
        // unmap garbage (and, during the unwind of `Orisnik`'s own move tripwire, turn one
        // panic into an abort). Leak instead, as before `Drop` existed.
        if !self.home.holds(self) {
            return;
        }
        while let Some(record) = self.pop_back() {
            drop(record);
        }
        let mut page = self
            .pages
            .front()
            .map_or(core::ptr::null_mut(), NonNull::as_ptr);
        // EXPLICIT: walks the chain while releasing it, so the loop state is the current
        // page pointer; its successor must be read before its mapping is returned.
        while !page.is_null() {
            // SAFETY: `page` is a live page of this book (not yet unmapped: pages are
            // released strictly front to back, each after its successor is read).
            let after = unsafe { self.next_page(page) };
            // SAFETY: `page` is the tail of a live mapping this book obtained from
            // `os::map(PAGE_SIZE)`; nothing references it after this loop.
            let base = unsafe { base_of(page) };
            // SAFETY: `base` is non-null (a mapping base).
            let base = unsafe { NonNull::new_unchecked(base) };
            // SAFETY: `base`/`PAGE_SIZE` describe exactly the mapping `grow` obtained
            // from `os::map(PAGE_SIZE)`, not yet unmapped.
            unsafe { os::unmap(base, os::PAGE_SIZE) };
            page = after;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spomen::record::Source;

    fn rec(tag: usize) -> Record {
        // The pointer is only ever compared, never dereferenced, in these tests.
        let ptr = NonNull::new(core::ptr::without_provenance_mut::<u8>(8 + tag * 8))
            .expect("non-zero address");
        Record::new(ptr, tag, Source::Buckets, 0)
    }

    #[test]
    fn push_pop_is_lifo_and_back_tracks_the_top() {
        let book = RecordBook::new();
        assert!(book.is_empty());
        for i in 0..5 {
            let at = book.push_back(rec(i)).expect("map");
            assert_eq!(Some(at), book.back());
        }
        assert_eq!(book.len(), 5);
        for i in (0..5).rev() {
            assert_eq!(book.pop_back().expect("non-empty").size, i);
        }
        assert!(book.is_empty());
    }

    #[test]
    fn spans_pages_and_reuses_spare_capacity_before_growing() {
        let book = RecordBook::new();
        let n = CAPACITY * 2 + 3;
        for i in 0..n {
            book.push_back(rec(i)).expect("map");
        }
        assert_eq!(book.len(), n);
        // Pop back down across a page boundary, then refill: spare page reused, so the
        // page count must not grow (a leak would show as an extra mapping).
        assert_eq!(page_count(&book), 3);
        for i in (CAPACITY..n).rev() {
            assert_eq!(book.pop_back().expect("non-empty").size, i);
        }
        assert_eq!(book.len(), CAPACITY);
        // The now-empty upper pages are kept as spare capacity, not returned.
        assert_eq!(page_count(&book), 3);
        for i in CAPACITY..n {
            book.push_back(rec(i)).expect("map");
        }
        assert_eq!(
            page_count(&book),
            3,
            "spare pages were reused, not re-mapped"
        );
        for i in (0..n).rev() {
            assert_eq!(book.pop_back().expect("non-empty").size, i);
        }
    }

    /// Pages currently chained in `book` (test-only observation of the page list).
    fn page_count(book: &RecordBook) -> usize {
        let sentinel = book.pages.sentinel();
        let mut count = 0;
        // SAFETY: `sentinel` is live and linked (`sentinel()`'s guarantee).
        let mut cur = unsafe { ListLink::next(sentinel) };
        while cur != sentinel {
            count += 1;
            // SAFETY: `cur` is a live, linked page link (reached from the sentinel).
            cur = unsafe { ListLink::next(cur) };
        }
        count
    }

    #[test]
    fn purge_keeps_live_pages_and_frees_spares() {
        let book = RecordBook::new();
        for i in 0..=CAPACITY {
            book.push_back(rec(i)).expect("map");
        }
        assert_eq!(page_count(&book), 2);
        // Popping the second page's only record leaves it empty *but still `cur`*, so
        // there is no spare page yet and `purge` frees nothing.
        assert_eq!(book.pop_back().expect("non-empty").size, CAPACITY);
        book.purge();
        assert_eq!(page_count(&book), 2, "nothing is spare while it is `cur`");
        // One more pop moves `cur` back to the first page, making the second a real
        // spare: `purge` must now unmap exactly that one and keep the live page.
        assert_eq!(book.pop_back().expect("non-empty").size, CAPACITY - 1);
        book.purge();
        assert_eq!(page_count(&book), 1, "the spare page was returned");
        assert_eq!(book.len(), CAPACITY - 1);
        // Still fully usable: refill across the boundary re-grows a page.
        book.push_back(rec(CAPACITY - 1)).expect("map");
        book.push_back(rec(CAPACITY)).expect("map");
        assert_eq!(page_count(&book), 2);
        assert_eq!(
            book.back().expect("non-empty").as_ptr().addr() % core::mem::align_of::<Record>(),
            0
        );
        // Fully drain and purge everything; the book must restart cleanly.
        while let Some(record) = book.pop_back() {
            drop(record);
        }
        book.purge();
        assert_eq!(page_count(&book), 0, "an empty book releases every page");
        book.push_back(rec(0)).expect("map");
        assert_eq!(book.len(), 1);
    }

    #[test]
    fn drop_runs_each_records_destructor_once() {
        // Miri (with leak checking) catches a double drop / leak of a record's
        // `Backtrace` here. The book is dropped by going out of scope, *not* by an
        // explicit `drop(book)`: that would move it, which the non-move-after-first-use
        // contract forbids (the page list's sentinel is self-referential).
        let book = RecordBook::new();
        for i in 0..CAPACITY + 2 {
            book.push_back(rec(i)).expect("map");
        }
    }

    #[test]
    fn push_reports_os_refusal_as_none() {
        let book = RecordBook::new();
        let _oom = os::test_vm::fail_map_after(0);
        assert!(book.push_back(rec(0)).is_none());
        assert!(book.is_empty());
    }

    /// `for_each_live` visits every live record exactly once, in storage order, at every
    /// page-boundary shape — including records that span several pages, and a `cur` page
    /// left with `next == 0` after a pop.
    #[test]
    fn for_each_live_visits_every_record_once_across_pages() {
        for count in [0, 1, CAPACITY - 1, CAPACITY, CAPACITY + 1, CAPACITY * 2 + 3] {
            let book = RecordBook::new();
            for index in 0..count {
                book.push_back(rec(index)).expect("map");
            }
            let mut seen = Vec::new();
            book.for_each_live(|record| {
                // SAFETY: `record` is a live record.
                seen.push(unsafe { (*record.as_ptr()).size });
            });
            assert_eq!(seen, (0..count).collect::<Vec<_>>(), "count {count}");
        }
        // Pop the only record of the second page: `cur` is now a page with `next == 0`.
        let book = RecordBook::new();
        for index in 0..=CAPACITY {
            book.push_back(rec(index)).expect("map");
        }
        drop(book.pop_back());
        let mut seen = Vec::new();
        book.for_each_live(|record| {
            // SAFETY: `record` is a live record.
            seen.push(unsafe { (*record.as_ptr()).size });
        });
        assert_eq!(seen, (0..CAPACITY).collect::<Vec<_>>());
    }
}
