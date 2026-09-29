// SPDX-License-Identifier: MIT OR Apache-2.0
//! The allocation-record map: every live allocation's [`Record`], indexed by address.
//! Ports `Cpp/hpha.h`'s `debug_record_map` (`add`, `remove`, `replace`, `update`, plus
//! the lookup its `check`/`find` use).
//!
//! Records live densely in a [`RecordBook`] and are indexed by an
//! [`IntrusiveMultiRbTree`] keyed on the payload address, exactly as in HPHA ("a
//! multi-red-black tree is technically not needed since addresses are always unique
//! but for brevity we omit the inclusion of the `intrusive_red_black_tree` class" —
//! `hpha.h`). A live allocation's address is unique, so the tree never chains.
//!
//! # What this module does *not* do
//! It is pure bookkeeping. HPHA's `add`/`remove` also poison the payload and assert the
//! guard ramp; here those stay with the dispatch layer (`orisnik.rs`), which already owns
//! poisoning (`spomen::poison`) and the guard-seed stream, and will call
//! [`Record::check_guard`] before retiring a record. Keeping the store free of payload
//! access means it never dereferences a caller's allocation, so it is testable with
//! made-up addresses.
//!
//! # Removal from the middle
//! [`RecordBook`] only pops from the back, so [`RecordStore::remove`] follows HPHA: erase
//! the victim from the tree, erase the *last* record too, move the last record into the
//! victim's slot, and re-insert it — the tree's nodes are embedded in the records, so a
//! moved record must be unlinked before the move and re-linked after.
//!
//! Follows the same non-move-after-first-use contract as its tree and page list.

use crate::rbtree::{IntrusiveMultiRbTree, NodeBase};
use crate::spomen::book::RecordBook;
use crate::spomen::record::{Record, Source};
use core::ptr::NonNull;

/// What [`RecordStore::remove`]/[`replace`](RecordStore::replace)/
/// [`update`](RecordStore::update) report about the record they displaced. Ports
/// `debug_info`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: crate-internal two-field result, mirrored by orisnitsa's struct.
pub(crate) struct DebugInfo {
    /// The size the caller had requested for the allocation.
    pub(crate) size: usize,
    /// Which sub-allocator had served it.
    pub(crate) source: Source,
}

/// Address-indexed store of every live allocation's [`Record`]. Ports
/// `debug_record_map`.
pub(crate) struct RecordStore {
    /// Address-ordered index over the records held in `book`.
    tree: IntrusiveMultiRbTree<Record>,
    /// Dense storage for the records themselves.
    book: RecordBook,
}

impl RecordStore {
    /// An empty store. Nothing is mapped until the first [`add`](RecordStore::add).
    pub(crate) const fn new() -> Self {
        Self {
            tree: IntrusiveMultiRbTree::new(),
            book: RecordBook::new(),
        }
    }

    /// Number of live records.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.book.len()
    }

    /// The record for the allocation at `ptr`, if one is live. Ports the map's
    /// `find`.
    #[must_use]
    pub(crate) fn find(&self, ptr: NonNull<u8>) -> Option<NonNull<Record>> {
        let key = ptr.as_ptr().addr();
        let candidate = self.tree.lower_bound(&key)?;
        // SAFETY: `candidate` is a live record in this store's tree.
        let found = unsafe { (*candidate.as_ptr()).ptr.as_ptr().addr() };
        (found == key).then_some(candidate)
    }

    /// Records a new allocation of `size` bytes at `ptr`, served by `source`, whose
    /// guard ramp was seeded with `guard_byte`. Returns `false` — recording nothing —
    /// if the OS refused a page for the record. Ports `debug_record_map::add`.
    ///
    /// `ptr` must not already be recorded (HPHA `assert`s this; so does this, in debug
    /// builds).
    #[must_use]
    pub(crate) fn add(
        &self,
        ptr: NonNull<u8>,
        size: usize,
        source: Source,
        guard_byte: u8,
    ) -> bool {
        self.add_record(Record::new(ptr, size, source, guard_byte))
    }

    /// [`RecordStore::add`] for an already-built [`Record`] (e.g. one carrying a specific
    /// callstack). Same contract and return value.
    #[must_use]
    pub(crate) fn add_record(&self, record: Record) -> bool {
        debug_assert!(self.find(record.ptr).is_none(), "address already recorded");
        let Some(slot) = self.book.push_back(record) else {
            return false;
        };
        self.tree.insert(slot);
        true
    }

    /// Forgets the allocation at `ptr`, returning what was recorded, or `None` if it is
    /// not recorded (HPHA `assert`s: "most likely the pointer was already deleted or
    /// the pointer points to a static or a global variable"). Ports
    /// `debug_record_map::remove`.
    pub(crate) fn remove(&self, ptr: NonNull<u8>) -> Option<DebugInfo> {
        let record = self.find(ptr)?;
        self.tree.erase(record);
        let last = self.book.back();
        let removed = if record == last {
            self.book.pop_back()
        } else {
            self.tree.erase(last);
            let mut moved = self.book.pop_back();
            // `moved` was unlinked from the tree above; its copied node fields are
            // stale, so start it from a clean node before it is re-linked.
            moved.node = NodeBase::UNLINKED;
            // SAFETY: `record` is a live, initialized slot in the book (found above)
            // and not `last`, so the popped `moved` did not come from it; it is
            // exclusively accessed here.
            let old = unsafe { core::ptr::replace(record.as_ptr(), moved) };
            self.tree.insert(record);
            old
        };
        Some(DebugInfo {
            size: removed.size,
            source: removed.source,
        })
    }

    /// Retargets the record of the allocation at `ptr` to a new allocation at
    /// `new_ptr` (a successful `realloc` that moved), returning what it recorded before.
    /// Returns `None` if `ptr` is not recorded. Ports `debug_record_map::replace`.
    ///
    /// Call this only once the new allocation has *succeeded* — see `Cpp/ERRATA.md`'s
    /// E9 correction: HPHA's own caller guards on `newPtr`, so a failed realloc never
    /// reaches here and the original record survives untouched.
    pub(crate) fn replace(
        &self,
        ptr: NonNull<u8>,
        new_ptr: NonNull<u8>,
        size: usize,
        source: Source,
        guard_byte: u8,
    ) -> Option<DebugInfo> {
        let record = self.find(ptr)?;
        // The address is the tree key, so the record leaves the tree while it changes.
        self.tree.erase(record);
        // SAFETY: `record` is a live, initialized slot in the book (found above),
        // exclusively accessed here; `replace` moves the old value out, so it is dropped
        // exactly once (below) and the slot holds a fresh, initialized record.
        let old = unsafe {
            core::ptr::replace(
                record.as_ptr(),
                Record::new(new_ptr, size, source, guard_byte),
            )
        };
        self.tree.insert(record);
        Some(DebugInfo {
            size: old.size,
            source: old.source,
        })
    }

    /// Updates the record of the allocation at `ptr` after an in-place resize: new
    /// requested `size`, a freshly captured callstack, and the new guard seed. Returns
    /// what it recorded before, or `None` if `ptr` is not recorded. Ports
    /// `debug_record_map::update`. The address — the tree key — is unchanged, so the
    /// tree is untouched.
    pub(crate) fn update(
        &self,
        ptr: NonNull<u8>,
        size: usize,
        guard_byte: u8,
    ) -> Option<DebugInfo> {
        let record = self.find(ptr)?;
        // SAFETY: `record` is a live, initialized record (found above), exclusively
        // accessed here; only non-key fields are written.
        let old_size = unsafe { (*record.as_ptr()).size };
        // SAFETY: as above; a plain field read.
        let source = unsafe { (*record.as_ptr()).source };
        // SAFETY: as above; a plain field write.
        unsafe { (*record.as_ptr()).size = size };
        // SAFETY: as above; a plain field write.
        unsafe { (*record.as_ptr()).guard_byte = guard_byte };
        // SAFETY: as above; assignment drops the old `Backtrace` exactly once and
        // stores the new one.
        unsafe { (*record.as_ptr()).callstack = crate::spomen::record::capture_callstack() };
        Some(DebugInfo {
            size: old_size,
            source,
        })
    }

    /// Returns the record book's spare pages to the OS. Ports
    /// `debug_record_map::purge`.
    pub(crate) fn purge(&self) {
        self.book.purge();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rand::VintageRand;
    use std::collections::BTreeMap;

    /// A made-up address; the store only ever compares addresses, never dereferences
    /// the allocation a record describes.
    fn addr(n: usize) -> NonNull<u8> {
        NonNull::new(core::ptr::without_provenance_mut::<u8>(0x1000 + n * 16))
            .expect("non-zero address")
    }

    fn shuffled(n: usize, seed: u32) -> Vec<usize> {
        let mut rng = VintageRand::new(seed);
        let mut v: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = usize::try_from(rng.next()).expect("fits") % (i + 1);
            v.swap(i, j);
        }
        v
    }

    #[test]
    fn add_find_remove_round_trip() {
        let store = RecordStore::new();
        assert!(store.add(addr(1), 40, Source::Tree, 7));
        assert_eq!(store.len(), 1);
        let rec = store.find(addr(1)).expect("recorded");
        // SAFETY: `rec` is a live record.
        assert_eq!(unsafe { (*rec.as_ptr()).size }, 40);
        assert!(store.find(addr(2)).is_none());
        let info = store.remove(addr(1)).expect("recorded");
        assert_eq!(
            info,
            DebugInfo {
                size: 40,
                source: Source::Tree
            }
        );
        assert_eq!(store.len(), 0);
        assert!(store.find(addr(1)).is_none());
        assert!(store.remove(addr(1)).is_none(), "double remove is reported");
    }

    #[test]
    fn forward_backward_and_shuffled_removal_keep_the_index_consistent() {
        // Small enough for Miri, large enough to span a page boundary is covered by
        // `book`'s own tests; here the point is the swap-the-last-into-the-hole path
        // and tree re-linking across many removal orders.
        let n = 200;
        let orders: [Vec<usize>; 3] = [(0..n).collect(), (0..n).rev().collect(), shuffled(n, 1234)];
        for order in &orders {
            let store = RecordStore::new();
            for &i in &shuffled(n, 42) {
                assert!(store.add(addr(i), i, Source::Buckets, 0));
            }
            let mut model: BTreeMap<usize, usize> = (0..n).map(|i| (i, i)).collect();
            for &i in order {
                let info = store.remove(addr(i)).expect("recorded");
                assert_eq!(Some(info.size), model.remove(&i));
                assert_eq!(store.len(), model.len());
                for &j in model.keys() {
                    let rec = store.find(addr(j)).expect("survivor still indexed");
                    // SAFETY: `rec` is a live record.
                    assert_eq!(unsafe { (*rec.as_ptr()).size }, j);
                }
                assert!(store.find(addr(i)).is_none());
            }
            assert_eq!(store.len(), 0);
        }
    }

    #[test]
    fn replace_rekeys_without_duplicating() {
        let store = RecordStore::new();
        assert!(store.add(addr(1), 10, Source::Buckets, 1));
        assert!(store.add(addr(2), 20, Source::Buckets, 2));
        let info = store
            .replace(addr(1), addr(9), 300, Source::Tree, 9)
            .expect("recorded");
        assert_eq!(
            info,
            DebugInfo {
                size: 10,
                source: Source::Buckets
            }
        );
        assert_eq!(store.len(), 2, "rekeyed, not duplicated");
        assert!(store.find(addr(1)).is_none());
        let moved = store.find(addr(9)).expect("new key indexed");
        // SAFETY: `moved` is a live record.
        let moved_size = unsafe { (*moved.as_ptr()).size };
        // SAFETY: `moved` is a live record.
        let moved_source = unsafe { (*moved.as_ptr()).source };
        assert_eq!((moved_size, moved_source), (300, Source::Tree));
        assert!(store.find(addr(2)).is_some());
        assert!(
            store
                .replace(addr(1), addr(5), 1, Source::Tree, 0)
                .is_none()
        );
    }

    #[test]
    fn update_changes_size_and_seed_in_place() {
        let store = RecordStore::new();
        assert!(store.add(addr(3), 10, Source::Tree, 1));
        let info = store.update(addr(3), 64, 5).expect("recorded");
        assert_eq!(
            info,
            DebugInfo {
                size: 10,
                source: Source::Tree
            }
        );
        let rec = store.find(addr(3)).expect("still indexed");
        // SAFETY: `rec` is a live record.
        let size = unsafe { (*rec.as_ptr()).size };
        // SAFETY: `rec` is a live record.
        let seed = unsafe { (*rec.as_ptr()).guard_byte };
        assert_eq!((size, seed), (64, 5));
        assert!(store.update(addr(4), 1, 0).is_none());
    }

    #[test]
    fn add_reports_os_refusal_and_records_nothing() {
        let store = RecordStore::new();
        let oom = crate::os::test_vm::fail_map_after(0);
        assert!(!store.add(addr(1), 8, Source::Buckets, 0));
        assert_eq!(store.len(), 0);
        assert!(store.find(addr(1)).is_none());
        drop(oom);
        assert!(
            store.add(addr(1), 8, Source::Buckets, 0),
            "recovers after OOM"
        );
    }

    #[test]
    fn remove_last_slot_and_purge_release_pages() {
        let store = RecordStore::new();
        assert!(store.add(addr(1), 1, Source::Buckets, 0));
        assert!(store.remove(addr(1)).is_some());
        store.purge();
        assert!(
            store.add(addr(2), 2, Source::Tree, 0),
            "usable after a full purge"
        );
    }

    /// Real (`force_capture`d, heap-owning) backtraces through every move the store
    /// performs: swap-remove, replace and update. Runs under Miri too — Miri supports the
    /// capture itself (only symbolication is unsupported), so this is where a double drop
    /// or leak of a `Captured` `Backtrace` would surface. Few records, since each real
    /// capture is slow under Miri.
    #[test]
    fn real_backtraces_survive_swap_remove_replace_and_update() {
        use crate::spomen::record::capture_callstack_with;
        use std::backtrace::BacktraceStatus;
        let store = RecordStore::new();
        for i in 0..4 {
            let rec =
                Record::with_callstack(addr(i), i, Source::Tree, 0, capture_callstack_with(true));
            assert!(store.add_record(rec));
        }
        let status = |n: usize| {
            let rec = store.find(addr(n)).expect("recorded");
            // SAFETY: `rec` is a live record.
            unsafe { (*rec.as_ptr()).callstack.status() }
        };
        // Removing a non-last record moves the last (captured) record into its slot.
        assert!(store.remove(addr(0)).is_some());
        assert_eq!(
            status(3),
            BacktraceStatus::Captured,
            "moved record keeps its trace"
        );
        assert_eq!(status(1), BacktraceStatus::Captured);
        // Replace drops the old trace and installs a fresh one.
        assert!(
            store
                .replace(addr(1), addr(9), 5, Source::Buckets, 1)
                .is_some()
        );
        // Update swaps the trace in place (with the ordinary capture policy, so under Miri
        // the new trace is the cheap disabled one).
        assert_eq!(status(2), BacktraceStatus::Captured, "unaffected neighbour");
        assert!(store.update(addr(2), 7, 2).is_some());
        if !cfg!(miri) {
            assert_eq!(status(2), BacktraceStatus::Captured, "recaptured");
        }
        // Removing the (now) last record pops without a move.
        assert!(store.remove(addr(3)).is_some());
        assert_eq!(store.len(), 2);
        // Whatever remains is dropped, exactly once, with the store.
    }

    /// Symbol names in a captured trace. Runs natively, and under Miri as an opt-in: Miri
    /// resolves frames itself (real names *are* available under it), but std's
    /// symbolication first asks the OS for the current directory, which Miri's default
    /// isolation aborts on. `-Zmiri-isolation-error=warn` downgrades just that call to a
    /// warning (isolation otherwise stays on), so the `ignore` below is an opt-in, not a
    /// capability gap:
    /// `MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-tree-borrows -Zmiri-isolation-error=warn"
    /// cargo +nightly miri test --features debug-allocator records_capture -- --ignored`.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "opt-in: needs -Zmiri-isolation-error=warn (symbolication reads the current directory)"
    )]
    fn records_capture_the_allocating_callstack() {
        use crate::spomen::record::capture_callstack_with;
        let store = RecordStore::new();
        // Force the real capture in both modes (under Miri the ordinary policy is the
        // cheap no-op), so this always checks a genuine trace.
        let rec =
            Record::with_callstack(addr(1), 8, Source::Buckets, 0, capture_callstack_with(true));
        assert!(store.add_record(rec));
        // Natively, also check the ordinary `add` path captures at its call site.
        if !cfg!(miri) {
            assert!(store.add(addr(2), 8, Source::Tree, 0));
        }
        for n in if cfg!(miri) { 1..2 } else { 1..3 } {
            let rec = store.find(addr(n)).expect("recorded");
            // SAFETY: `rec` is a live record.
            let trace = unsafe { (*rec.as_ptr()).callstack.to_string() };
            assert!(
                trace.contains("records_capture_the_allocating_callstack"),
                "callstack should name the capturing test, got:\n{trace}"
            );
        }
    }
}
