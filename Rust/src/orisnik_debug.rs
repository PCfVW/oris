// SPDX-License-Identifier: MIT OR Apache-2.0
//! The `debug-allocator` hooks — HPHA's `allocator::debug_add`/`debug_remove`/
//! `debug_replace`/`debug_update`/`debug_check`/`debug_purge` (`Cpp/hpha.cpp:863-950`),
//! called by [`Orisnik`]'s public methods at exactly the points HPHA's own `alloc`/
//! `realloc`/`resize`/`free`/`purge` call them (`Cpp/hpha.h:1264-1440`). With the feature
//! off, `orisnik.rs` supplies no-op versions instead, so no call site carries a `cfg`.
//!
//! Each hook owns one whole responsibility, so the guard seed, the record and the poison
//! can never disagree: `debug_add` draws the guard seed, writes the ramp, records the
//! allocation (remembering the seed) and poisons the payload; `debug_remove` verifies the
//! block, poisons at the *recorded* size and retires the record; `debug_replace`/
//! `debug_update` rewrite the ramp with a fresh seed and retarget the record.
//!
//! # Re-entrancy
//! No hook allocates from *this* instance today: an owned instance's `Backtrace` capture
//! allocates from the system allocator, an instance used through `GlobalAlloc` records no
//! callstack at all (see `spomen::record`'s "global allocator" section — that rule exists
//! to avoid a *deadlock*, not recursion), and the record store maps its pages with
//! `os::map`. The `busy` flag is kept anyway as the enforcement of the invariant "a hook
//! never observes or records its own allocations", because the next hooks will break it:
//! `report()`/`check()` format strings (allocating) while iterating the record tree, and
//! that iteration must not see records inserted by its own allocations.
//!
//! While a hook runs, nested `alloc`/`free`/`realloc` calls are served normally but skip
//! every hook — unrecorded and unchecked. That is self-consistent provided everything a
//! hook allocates is also freed inside a hook (then an unrecorded block is never freed by
//! a *non*-busy call). The exception is the panic path: [`Orisnik::fail`] allocates its
//! message and payload unrecorded and they outlive the hook, so it sets `disabled`, which
//! turns every later hook off for good. The invariant is exercised directly (a nested
//! call made while `busy`) in this module's tests.
//!
//! # Contract
//! Every hook here assumes its caller passes a live allocation of this instance (or, for
//! `debug_add`/`debug_replace`, the block it just produced). They are private to
//! `Orisnik`'s public methods, whose own `# Safety` sections establish exactly that; the
//! hooks are safe `fn`s rather than `unsafe fn`s only because no code outside those
//! methods can call them.
//!
//! # Zero cost off
//! Only compiled with `debug-allocator`; see `orisnik.rs` for the no-op stand-ins.

use super::{DebugSource, Orisnik};
use crate::bucket;
use crate::guard::MEMORY_GUARD_SIZE;
use crate::spomen::failure::{self, Corruption};
use crate::spomen::record::{Record, Source};
use core::cell::Cell;
use core::ptr::NonNull;

impl From<DebugSource> for Source {
    fn from(source: DebugSource) -> Self {
        match source {
            DebugSource::Buckets => Source::Buckets,
            DebugSource::Tree => Source::Tree,
        }
    }
}

/// Marks a hook as running for as long as it lives; clears the flag on drop, including
/// when a panic unwinds through the hook.
struct Busy<'a>(&'a Cell<bool>);

impl Drop for Busy<'_> {
    fn drop(&mut self) {
        self.0.set(false);
    }
}

/// A detected corruption plus the record it concerns, if the pointer had one.
type Failure = (Corruption, Option<NonNull<Record>>);

impl Orisnik {
    /// Total bytes callers currently have outstanding, each block counted with its guard
    /// reservation (`requested size + MEMORY_GUARD_SIZE`) — HPHA's `requested()`, the sum
    /// of `mTotalRequestedSizeBuckets` and `mTotalRequestedSizeTree`. Only under
    /// `debug-allocator`.
    #[must_use]
    pub fn requested(&self) -> usize {
        self.requested_buckets.get() + self.requested_tree.get()
    }

    /// Latches this instance as used through `GlobalAlloc`: from now on its records carry
    /// no callstack (see `spomen::record`'s "global allocator" section for the deadlock this
    /// avoids).
    pub(crate) fn mark_used_as_global(&self) {
        self.used_as_global.set(true);
    }

    /// The callstack a new or updated record should carry: a real capture, or `None` for an
    /// instance that is the global allocator.
    fn callstack(&self) -> Option<std::backtrace::Backtrace> {
        if self.used_as_global.get() {
            None
        } else {
            Some(crate::spomen::record::capture_callstack())
        }
    }

    /// Starts a hook, or returns `None` if hooks are off right now: already inside one
    /// (re-entrancy — see the module doc) or permanently disabled after a detected
    /// corruption.
    fn enter_hook(&self) -> Option<Busy<'_>> {
        if self.busy.get() || self.disabled.get() {
            return None;
        }
        self.busy.set(true);
        Some(Busy(&self.busy))
    }

    /// The running total for `source`'s path.
    fn requested_for(&self, source: Source) -> &Cell<usize> {
        match source {
            Source::Buckets => &self.requested_buckets,
            Source::Tree => &self.requested_tree,
        }
    }

    /// Reacts to detected corruption: disables the hooks for good (see the module doc),
    /// then panics with the diagnostic. Never returns.
    #[cold]
    fn fail(&self, what: Corruption, ptr: NonNull<u8>, record: Option<NonNull<Record>>) -> ! {
        self.disabled.set(true);
        // SAFETY: `record`, if `Some`, was just found in this store and nothing has
        // touched the store since, so it is live.
        let message = unsafe { failure::describe(what, ptr, record) };
        failure::fail(&message)
    }

    /// Checks `ptr` against its record without changing anything: a record must exist,
    /// `orig_size` (a sized free's caller-supplied size), if given, must agree with the
    /// recorded size, and the guard ramp must be intact. The detection half of
    /// `debug_remove`/`debug_check`, kept a plain value so it is directly testable.
    ///
    /// `orig_size` is compared the way the record holds it: after the minimum-size clamp for
    /// a bucket-path record (`alloc(5)` records 8), raw for a tree-path one (an aligned
    /// request past `MAX_SMALL_ALLOCATION` alignment is never clamped). HPHA compares the raw value, so its own
    /// `free(p, 5)` of an `alloc(5)` would trip its assert on a perfectly legal call — a
    /// 2007 debug-mode bug this port does not reproduce (see `Cpp/ERRATA.md`).
    ///
    /// The block at `ptr` must still be live if a record exists for it (the callers'
    /// contract: `ptr` is a live allocation this instance produced).
    fn verify(
        &self,
        ptr: NonNull<u8>,
        orig_size: Option<usize>,
    ) -> Result<NonNull<Record>, Failure> {
        let Some(record) = self.records.find(ptr) else {
            return Err((Corruption::UnknownPointer, None));
        };
        if let Some(given) = orig_size {
            // SAFETY: `record` was just found in the store, so it is live.
            let recorded = unsafe { (*record.as_ptr()).size };
            // SAFETY: as above; reads one field.
            let source = unsafe { (*record.as_ptr()).source };
            // The record holds what `debug_add` was given: the *clamped* size on the bucket
            // path, the raw size on the tree path (a sub-minimum aligned request beyond
            // `MAX_SMALL_ALLOCATION` alignment goes to the tree and is never clamped).
            let given = match source {
                Source::Buckets => bucket::clamp_small_allocation(given),
                Source::Tree => given,
            };
            if given != recorded {
                return Err((Corruption::SizeMismatch { given }, Some(record)));
            }
        }
        // SAFETY: `record` was just found in the store, so it is live.
        let record_ref = unsafe { &*record.as_ptr() };
        // SAFETY: the record describes the live allocation at `ptr`, valid for `size +
        // MEMORY_GUARD_SIZE` bytes (this function's contract).
        if !unsafe { record_ref.check_guard() } {
            return Err((Corruption::GuardOverrun, Some(record)));
        }
        Ok(record)
    }

    /// Records a fresh allocation: draws a guard seed, writes the ramp, records `ptr`
    /// (remembering the seed and capturing the callstack) and poisons the payload. If the
    /// record store cannot get memory the allocation is undone and `None` returned — a
    /// value, never a panic, exactly like HPHA's `debug_add`. `ptr == None` (the
    /// underlying allocation failed) passes straight through. Ports `debug_add`.
    ///
    /// `size` is the caller-visible size, already clamped on the bucket path.
    pub(super) fn debug_add(
        &self,
        ptr: Option<NonNull<u8>>,
        size: usize,
        source: DebugSource,
    ) -> Option<NonNull<u8>> {
        let ptr = ptr?;
        let Some(_busy) = self.enter_hook() else {
            return Some(ptr);
        };
        // SAFETY: `ptr` is a live allocation this instance just produced.
        debug_assert!(size <= unsafe { self.size(Some(ptr)) });
        let seed = self.next_guard_seed();
        // SAFETY: `ptr` is valid for `size + MEMORY_GUARD_SIZE` bytes (allocated with
        // that inflated size), exclusively owned (not yet handed to any caller).
        unsafe { crate::spomen::guard::write_guard(ptr, size, seed) };
        let record = Record::with_callstack(ptr, size, source.into(), seed, self.callstack());
        if self.records.add_record(record) {
            let counter = self.requested_for(source.into());
            counter.set(counter.get() + size + MEMORY_GUARD_SIZE);
            // SAFETY: `ptr` is valid for `size` bytes, exclusively owned; the guard
            // ramp lies past them, so the two ranges are disjoint.
            unsafe { crate::spomen::poison::fill(ptr, size) };
            return Some(ptr);
        }
        // The record store could not get a page: give the block back and report failure
        // as a value (HPHA: `bucket_free(ptr)`/`tree_free(ptr)`, `return NULL`).
        match source {
            DebugSource::Buckets => {
                // SAFETY: `ptr` is a live bucket-path allocation, not handed out.
                unsafe { self.buckets.free(ptr) };
            }
            DebugSource::Tree => {
                // SAFETY: `ptr` is a live tree-path allocation, not handed out.
                unsafe { self.tree.free(ptr) };
            }
        }
        None
    }

    /// Verifies `ptr` and retires its record, poisoning the payload at the *recorded*
    /// size first. Called before the reclaim. `orig_size` is a sized free's caller-supplied
    /// size. Panics on corruption (see the module doc of `spomen::failure`). Ports
    /// `debug_remove` (both overloads).
    pub(super) fn debug_remove(&self, ptr: NonNull<u8>, orig_size: Option<usize>) {
        let Some(_busy) = self.enter_hook() else {
            return;
        };
        let record = match self.verify(ptr, orig_size) {
            Ok(record) => record,
            Err((what, record)) => self.fail(what, ptr, record),
        };
        // SAFETY: `record` is live (just verified).
        let size = unsafe { (*record.as_ptr()).size };
        // SAFETY: `ptr` is a live allocation valid for `size` bytes (its recorded size).
        unsafe { crate::spomen::poison::fill(ptr, size) };
        let Some(info) = self.records.remove(ptr) else {
            self.fail(Corruption::UnknownPointer, ptr, None);
        };
        let counter = self.requested_for(info.source);
        counter.set(counter.get() - (info.size + MEMORY_GUARD_SIZE));
    }

    /// Verifies `ptr` — a record exists and its guard is intact — without changing
    /// anything. Called before a realloc/resize touches the block. Ports `debug_check`.
    pub(super) fn debug_check(&self, ptr: NonNull<u8>) {
        let Some(_busy) = self.enter_hook() else {
            return;
        };
        if let Err((what, record)) = self.verify(ptr, None) {
            self.fail(what, ptr, record);
        }
    }

    /// Retargets `ptr`'s record to `new_ptr` after a successful realloc, writing a fresh
    /// guard ramp at the new block. `new_ptr == None` (the realloc failed) is a no-op:
    /// the original block and its record are untouched — `Cpp/ERRATA.md`'s E9 correction,
    /// and HPHA's own `if (!newPtr) return;` guard. Ports `debug_replace`.
    pub(super) fn debug_replace(
        &self,
        ptr: NonNull<u8>,
        new_ptr: Option<NonNull<u8>>,
        size: usize,
        source: DebugSource,
    ) {
        let Some(new_ptr) = new_ptr else {
            return;
        };
        let Some(_busy) = self.enter_hook() else {
            return;
        };
        // SAFETY: `new_ptr` is a live allocation this instance just produced.
        debug_assert!(size <= unsafe { self.size(Some(new_ptr)) });
        let seed = self.next_guard_seed();
        // SAFETY: `new_ptr` is valid for `size + MEMORY_GUARD_SIZE` bytes (the realloc
        // was made with that inflated size), exclusively owned.
        unsafe { crate::spomen::guard::write_guard(new_ptr, size, seed) };
        // Built before the store is touched (capturing allocates — see the module doc).
        let fresh = Record::with_callstack(new_ptr, size, source.into(), seed, self.callstack());
        let Some(old) = self.records.replace(ptr, fresh) else {
            self.fail(Corruption::UnknownPointer, ptr, None);
        };
        let old_counter = self.requested_for(old.source);
        old_counter.set(old_counter.get() - (old.size + MEMORY_GUARD_SIZE));
        let new_counter = self.requested_for(source.into());
        new_counter.set(new_counter.get() + size + MEMORY_GUARD_SIZE);
    }

    /// Updates `ptr`'s record after an in-place `resize` to `size`, rewriting the guard
    /// ramp (its position moved with the size) with a fresh seed. Runs on *every*
    /// `resize`, whether or not the block grew, exactly like HPHA. Ports `debug_update`.
    pub(super) fn debug_update(&self, ptr: NonNull<u8>, size: usize) {
        let Some(_busy) = self.enter_hook() else {
            return;
        };
        // SAFETY: `ptr` is a live allocation this instance produced.
        debug_assert!(size <= unsafe { self.size(Some(ptr)) });
        let seed = self.next_guard_seed();
        // SAFETY: `ptr` is valid for `size + MEMORY_GUARD_SIZE` bytes (`size` is the
        // block's own deflated size), exclusively owned.
        unsafe { crate::spomen::guard::write_guard(ptr, size, seed) };
        let callstack = self.callstack();
        let Some(info) = self.records.update(ptr, size, seed, callstack) else {
            self.fail(Corruption::UnknownPointer, ptr, None);
        };
        let counter = self.requested_for(info.source);
        // `size` may be smaller or larger than the old size, so add before subtracting.
        counter.set(counter.get() + size - info.size);
    }

    /// Returns the record store's spare pages to the OS. Ports `debug_purge`.
    pub(super) fn debug_purge(&self) {
        let Some(_busy) = self.enter_hook() else {
            return;
        };
        self.records.purge();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::os::test_vm;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    // The helpers below wrap the allocator's `unsafe` entry points. Their shared contract:
    // the pointer passed in is a live allocation of the `Orisnik` passed in — every test
    // upholds it, except the ones that violate it *on purpose* to provoke a detection
    // (they say so where they do).

    fn alloc(orisnik: &Orisnik, size: usize) -> NonNull<u8> {
        orisnik.alloc(size).expect("allocation must succeed")
    }

    fn free(orisnik: &Orisnik, ptr: NonNull<u8>) {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.free(Some(ptr)) };
    }

    fn free_sized(orisnik: &Orisnik, ptr: NonNull<u8>, size: usize) {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.free_with_size(Some(ptr), size) };
    }

    fn realloc(orisnik: &Orisnik, ptr: NonNull<u8>, size: usize) -> Option<NonNull<u8>> {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.realloc(Some(ptr), size) }
    }

    fn resize(orisnik: &Orisnik, ptr: NonNull<u8>, size: usize) -> usize {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.resize(Some(ptr), size) }
    }

    /// Flips the first guard byte of the `size`-byte allocation at `ptr`.
    fn overrun(ptr: NonNull<u8>, size: usize) {
        // SAFETY: the allocation reserves `size + MEMORY_GUARD_SIZE` bytes, so the byte at
        // `ptr + size` is inside it; it is exclusively owned by the calling test.
        let guard = unsafe { ptr.as_ptr().add(size) };
        // SAFETY: `guard` is inside the allocation (above); read of one byte.
        let byte = unsafe { guard.read() };
        // SAFETY: as above; write of one byte.
        unsafe { guard.write(byte ^ 0xFF) };
    }

    /// The panic message of `action`, or `None` if it did not panic.
    fn panic_message(action: impl FnOnce()) -> Option<String> {
        let err = catch_unwind(AssertUnwindSafe(action)).err()?;
        err.downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&str>().map(|text| (*text).to_owned()))
    }

    #[test]
    fn every_allocation_is_recorded_and_free_retires_it() {
        let orisnik = Orisnik::new();
        let small = alloc(&orisnik, 24);
        let large = alloc(&orisnik, 1000);
        let aligned_small = orisnik.alloc_aligned(24, 32).expect("alloc");
        let aligned_large = orisnik.alloc_aligned(1000, 128).expect("alloc");
        assert_eq!(orisnik.records.len(), 4);
        for ptr in [small, large, aligned_small, aligned_large] {
            assert!(orisnik.records.find(ptr).is_some());
            free(&orisnik, ptr);
        }
        assert_eq!(orisnik.records.len(), 0);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn requested_counts_size_plus_guard_and_follows_realloc_and_resize() {
        let orisnik = Orisnik::new();
        let first = alloc(&orisnik, 24);
        assert_eq!(orisnik.requested(), 24 + MEMORY_GUARD_SIZE);
        let second = alloc(&orisnik, 1000);
        assert_eq!(orisnik.requested(), 24 + 1000 + 2 * MEMORY_GUARD_SIZE);
        // Bucket -> tree crossover: the old record's bytes leave the bucket total.
        let first = realloc(&orisnik, first, 500).expect("realloc");
        assert_eq!(orisnik.requested_buckets.get(), 0);
        assert_eq!(orisnik.requested(), 500 + 1000 + 2 * MEMORY_GUARD_SIZE);
        let new_size = resize(&orisnik, second, 1200);
        assert_eq!(
            orisnik.requested(),
            500 + new_size + 2 * MEMORY_GUARD_SIZE,
            "resize re-records the block at the size it actually ended up with"
        );
        free(&orisnik, first);
        free(&orisnik, second);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn sub_minimum_requests_are_recorded_clamped_and_sized_free_accepts_them() {
        // `alloc(5)` records 8 (clamped). HPHA would assert on `free(p, 5)`; this port
        // compares clamped, so the legal call passes.
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 5);
        let record = orisnik.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record.
        let recorded_size = unsafe { (*record.as_ptr()).size };
        assert_eq!(recorded_size, bucket::MIN_ALLOCATION);
        free_sized(&orisnik, ptr, 5);
        assert_eq!(orisnik.records.len(), 0);
        orisnik.purge();
    }

    #[test]
    fn realloc_rekeys_the_record_across_every_path() {
        let orisnik = Orisnik::new();
        // bucket -> bucket
        let ptr = alloc(&orisnik, 24);
        let ptr = realloc(&orisnik, ptr, 100).expect("realloc");
        assert_eq!(orisnik.records.len(), 1);
        assert!(orisnik.records.find(ptr).is_some());
        // bucket -> tree
        let ptr = realloc(&orisnik, ptr, 2000).expect("realloc");
        assert_eq!(orisnik.records.len(), 1);
        assert!(orisnik.records.find(ptr).is_some());
        // tree -> tree, both directions
        let ptr = realloc(&orisnik, ptr, 9000).expect("realloc");
        let ptr = realloc(&orisnik, ptr, 300).expect("realloc");
        assert_eq!(orisnik.records.len(), 1);
        assert!(orisnik.records.find(ptr).is_some());
        // The guard is valid at every step (a stale record would fail this free).
        free(&orisnik, ptr);
        assert_eq!(orisnik.records.len(), 0);
        orisnik.purge();
    }

    #[test]
    fn a_failed_realloc_leaves_the_original_allocation_and_record_intact() {
        // `Cpp/ERRATA.md` E9: the replace hook only ever runs on success.
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        // The bucket -> tree crossover needs a fresh arena; refuse the OS.
        let refusal = test_vm::fail_map_after(0);
        let refused = realloc(&orisnik, ptr, 4000);
        drop(refusal);
        assert!(refused.is_none());
        assert_eq!(orisnik.records.len(), 1, "original record survives");
        assert!(orisnik.records.find(ptr).is_some());
        // `ptr` is still live and its guard intact, so this free must not panic.
        free(&orisnik, ptr);
        assert_eq!(orisnik.records.len(), 0);
        orisnik.purge();
    }

    #[test]
    fn a_record_store_out_of_memory_frees_the_block_and_returns_none() {
        // First map serves the bucket page; the second (the record page) is refused.
        let orisnik = Orisnik::new();
        let refusal = test_vm::fail_map_after(1);
        assert!(orisnik.alloc(24).is_none());
        drop(refusal);
        assert_eq!(orisnik.records.len(), 0);
        assert_eq!(orisnik.requested(), 0);
        // The block really was freed: with nothing live, a purge returns the page.
        orisnik.purge();
        assert_eq!(orisnik.allocated(), 0);
        // And the allocator recovers.
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn overrunning_the_block_is_caught_on_free_realloc_and_resize() {
        for size in [24_usize, 1000] {
            for action in 0..3 {
                let orisnik = Orisnik::new();
                let ptr = alloc(&orisnik, size);
                overrun(ptr, size);
                let message = panic_message(|| match action {
                    0 => free(&orisnik, ptr),
                    1 => drop(realloc(&orisnik, ptr, size + 8)),
                    _ => drop(resize(&orisnik, ptr, size)),
                })
                .expect("the overrun must be detected");
                assert!(message.contains("guard bytes overwritten"), "{message}");
                assert!(
                    message.contains(&format!("requested {size} bytes")),
                    "{message}"
                );
                // The detection switched the hooks off and reclaimed nothing: release the
                // block for real so the test leaves no arena behind.
                free(&orisnik, ptr);
                orisnik.purge();
            }
        }
    }

    #[test]
    fn double_free_and_foreign_pointers_are_caught() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        // Deliberately violates the contract (second free); the hook must catch it
        // before anything is touched.
        let message = panic_message(|| free(&orisnik, ptr)).expect("double free detected");
        assert!(message.contains("already freed"), "{message}");
        orisnik.purge();

        let orisnik = Orisnik::new();
        let mut local = [0_u8; 64];
        let foreign = NonNull::new(local.as_mut_ptr()).expect("non-null");
        // Deliberately violates the contract; caught before any dereference.
        let message = panic_message(|| free(&orisnik, foreign)).expect("foreign detected");
        assert!(
            message.contains("not allocated by this allocator"),
            "{message}"
        );
    }

    #[test]
    fn a_sized_free_with_the_wrong_size_is_caught() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 100);
        // Deliberately wrong `orig_size`; caught before the reclaim uses it.
        let message = panic_message(|| free_sized(&orisnik, ptr, 64)).expect("mismatch detected");
        assert!(
            message.contains("allocated as 100 bytes, freed as 64"),
            "{message}"
        );
        // Reclaim for real (the detection switched the hooks off).
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn detected_corruption_switches_the_hooks_off_for_good() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        // Deliberate double free, caught.
        assert!(panic_message(|| free(&orisnik, ptr)).is_some());
        assert!(orisnik.disabled.get());
        assert!(
            !orisnik.busy.get(),
            "the busy marker unwinds with the panic"
        );
        // Hooks are off: a fresh allocation is served but unrecorded, and freeing it
        // does not panic (the panic payload was allocated unrecorded too).
        let fresh = alloc(&orisnik, 24);
        assert_eq!(orisnik.records.len(), 0);
        free(&orisnik, fresh);
        orisnik.purge();
    }

    #[test]
    fn nested_calls_during_a_hook_are_served_unrecorded_and_free_cleanly() {
        // The re-entrancy contract, deterministically: what a `Backtrace` allocating
        // from inside `debug_add` looks like to the allocator.
        let orisnik = Orisnik::new();
        let outer = alloc(&orisnik, 24);
        {
            let _busy = orisnik.enter_hook().expect("hooks are on");
            let inner_small = alloc(&orisnik, 40);
            let inner_large = alloc(&orisnik, 5000);
            assert_eq!(
                orisnik.records.len(),
                1,
                "nested allocations are not recorded"
            );
            // Freed while still busy, as a record's `Backtrace` is.
            free(&orisnik, inner_small);
            free(&orisnik, inner_large);
        }
        assert!(orisnik.enter_hook().is_some(), "the marker cleared on drop");
        free(&orisnik, outer);
        assert_eq!(orisnik.records.len(), 0);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn an_instance_used_through_globalalloc_records_no_callstack() {
        use core::alloc::{GlobalAlloc, Layout};
        let owned = Orisnik::new();
        let ptr = alloc(&owned, 24);
        let record = owned.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record.
        assert!(unsafe { (*record.as_ptr()).callstack.is_some() });
        free(&owned, ptr);

        let global = Orisnik::new();
        let layout = Layout::from_size_align(24, 8).expect("layout");
        // SAFETY: `layout` has non-zero size.
        let raw = unsafe { GlobalAlloc::alloc(&global, layout) };
        let ptr = NonNull::new(raw).expect("allocation must succeed");
        assert_eq!(global.records.len(), 1, "still recorded");
        let record = global.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record.
        assert!(unsafe { (*record.as_ptr()).callstack.is_none() });
        // SAFETY: `raw` came from `GlobalAlloc::alloc` above with this layout.
        unsafe { GlobalAlloc::dealloc(&global, raw, layout) };
        assert_eq!(global.records.len(), 0);
        owned.purge();
        global.purge();
    }

    #[test]
    fn free_poisons_the_payload_at_the_recorded_size() {
        let orisnik = Orisnik::new();
        // Tree path: memory stays mapped after the free, so the poison is observable.
        let size = 1000;
        let ptr = alloc(&orisnik, size);
        // SAFETY: `ptr` is valid for `size` bytes.
        unsafe { ptr.as_ptr().write_bytes(0x11, size) };
        free(&orisnik, ptr);
        // SAFETY: offset 64 is inside the block.
        let probe = unsafe { ptr.as_ptr().add(64) };
        // SAFETY: the arena is still mapped (no purge); reading the freed payload is the
        // point of this test, and nothing reuses it.
        let head = unsafe { probe.read() };
        assert_eq!(head, crate::spomen::poison::byte_at(64));
        orisnik.purge();
    }

    fn realloc_aligned(
        orisnik: &Orisnik,
        ptr: NonNull<u8>,
        size: usize,
        alignment: usize,
    ) -> Option<NonNull<u8>> {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.realloc_aligned(Some(ptr), size, alignment) }
    }

    fn free_sized_aligned(orisnik: &Orisnik, ptr: NonNull<u8>, size: usize, alignment: usize) {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.free_with_size_aligned(Some(ptr), size, alignment) };
    }

    fn recorded_size(orisnik: &Orisnik, ptr: NonNull<u8>) -> usize {
        let record = orisnik.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record.
        unsafe { (*record.as_ptr()).size }
    }

    #[test]
    fn sized_frees_compare_the_way_the_record_holds_the_size() {
        let orisnik = Orisnik::new();
        // Tree path, sub-minimum size: an aligned request past MAX_SMALL_ALLOCATION
        // alignment goes to the tree, which never clamps — the record holds the raw 5, so an
        // unconditional clamp on the free side would falsely report a mismatch.
        let tree_aligned = orisnik.alloc_aligned(5, 4096).expect("alloc");
        assert_eq!(recorded_size(&orisnik, tree_aligned), 5);
        free_sized_aligned(&orisnik, tree_aligned, 5, 4096);
        // Bucket path, aligned: clamped to 8 on the way in, so 3 must pass on the way out.
        let bucket_aligned = orisnik.alloc_aligned(3, 16).expect("alloc");
        assert_eq!(
            recorded_size(&orisnik, bucket_aligned),
            bucket::MIN_ALLOCATION
        );
        free_sized_aligned(&orisnik, bucket_aligned, 3, 16);
        // Plain bucket path (the E10 case itself) and plain tree path.
        let plain_small = alloc(&orisnik, 1);
        free_sized(&orisnik, plain_small, 1);
        let plain_large = alloc(&orisnik, 3000);
        free_sized(&orisnik, plain_large, 3000);
        assert_eq!(orisnik.records.len(), 0);
        // A wrong size is still caught on both sources.
        for size in [24_usize, 3000] {
            let ptr = alloc(&orisnik, size);
            let message = panic_message(|| free_sized(&orisnik, ptr, size + 1)).expect("caught");
            assert!(message.contains("freed as"), "{message}");
            // The detection disabled the hooks; reclaim for real.
            free(&orisnik, ptr);
            orisnik.disabled.set(false);
        }
        orisnik.purge();
    }

    #[test]
    fn a_guard_overrun_is_caught_on_sized_frees_too() {
        for aligned in [false, true] {
            let orisnik = Orisnik::new();
            let ptr = if aligned {
                orisnik.alloc_aligned(40, 32).expect("alloc")
            } else {
                alloc(&orisnik, 40)
            };
            overrun(ptr, 40);
            let message = panic_message(|| {
                if aligned {
                    free_sized_aligned(&orisnik, ptr, 40, 32);
                } else {
                    free_sized(&orisnik, ptr, 40);
                }
            })
            .expect("the overrun must be detected");
            assert!(message.contains("guard bytes overwritten"), "{message}");
            free(&orisnik, ptr);
            orisnik.purge();
        }
    }

    #[test]
    fn realloc_aligned_rekeys_the_record_across_every_path() {
        let orisnik = Orisnik::new();
        // Misaligned move: the second slot of a fresh bucket page is not 64-aligned, so
        // reaching 64 needs a move (a new aligned block, then the old one freed).
        let first = alloc(&orisnik, 24);
        let second = alloc(&orisnik, 24);
        assert_ne!(
            second.addr().get() % 64,
            0,
            "the test needs a misaligned block"
        );
        let moved = realloc_aligned(&orisnik, second, 100, 64).expect("realloc");
        assert_eq!(moved.addr().get() % 64, 0);
        assert_eq!(
            orisnik.records.len(),
            2,
            "old record retired, new one added"
        );
        assert!(orisnik.records.find(second).is_none());
        // Bucket in place (already 32-aligned), then bucket -> tree crossover, then tree.
        let ptr = orisnik.alloc_aligned(24, 32).expect("alloc");
        let ptr = realloc_aligned(&orisnik, ptr, 60, 32).expect("realloc");
        assert_eq!(orisnik.records.len(), 3);
        let ptr = realloc_aligned(&orisnik, ptr, 3000, 32).expect("realloc");
        assert!(orisnik.requested_tree.get() >= 3000);
        let ptr = realloc_aligned(&orisnik, ptr, 9000, 128).expect("realloc");
        assert_eq!(orisnik.records.len(), 3);
        assert!(orisnik.records.find(ptr).is_some());
        // Every guard is valid: a stale record would panic in one of these frees.
        free(&orisnik, ptr);
        free(&orisnik, moved);
        free(&orisnik, first);
        assert_eq!(orisnik.records.len(), 0);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn calloc_is_recorded_at_the_requested_total_and_zeroed() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.calloc(4, 25).expect("calloc");
        assert_eq!(recorded_size(&orisnik, ptr), 100);
        // SAFETY: `ptr` is valid for 100 bytes.
        let bytes = unsafe { core::slice::from_raw_parts(ptr.as_ptr(), 100) };
        assert!(bytes.iter().all(|byte| *byte == 0));
        free(&orisnik, ptr);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn resize_re_records_the_size_the_block_ends_up_with() {
        let orisnik = Orisnik::new();
        // Bucket path: the slot never changes size, whatever is asked.
        let small = alloc(&orisnik, 24);
        let usable = resize(&orisnik, small, 10);
        assert_eq!(recorded_size(&orisnik, small), usable);
        assert_eq!(orisnik.requested_buckets.get(), usable + MEMORY_GUARD_SIZE);
        // Tree path: a shrinking resize reports the block's current (rounded-up) size.
        let large = alloc(&orisnik, 1000);
        let after = resize(&orisnik, large, 500);
        assert!(after >= 500);
        assert_eq!(recorded_size(&orisnik, large), after);
        assert_eq!(orisnik.requested_tree.get(), after + MEMORY_GUARD_SIZE);
        free(&orisnik, small);
        free(&orisnik, large);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn purge_keeps_live_allocations_recorded() {
        let orisnik = Orisnik::new();
        let live: Vec<_> = (1..=3).map(|index| alloc(&orisnik, index * 100)).collect();
        let before = orisnik.requested();
        orisnik.purge();
        assert_eq!(orisnik.records.len(), 3);
        assert_eq!(orisnik.requested(), before);
        for ptr in live {
            free(&orisnik, ptr);
        }
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn globalalloc_entry_points_record_at_the_layout_sizes() {
        use core::alloc::{GlobalAlloc, Layout};
        let global = Orisnik::new();
        let layout = Layout::from_size_align(100, 8).expect("layout");
        // SAFETY: non-zero size.
        let zeroed = unsafe { GlobalAlloc::alloc_zeroed(&global, layout) };
        let ptr = NonNull::new(zeroed).expect("alloc_zeroed");
        assert_eq!(recorded_size(&global, ptr), 100);
        // SAFETY: `zeroed` came from this instance with `layout`; 300 is non-zero.
        let grown = unsafe { GlobalAlloc::realloc(&global, zeroed, layout, 300) };
        let ptr = NonNull::new(grown).expect("realloc");
        assert_eq!(global.records.len(), 1);
        assert_eq!(recorded_size(&global, ptr), 300);
        let grown_layout = Layout::from_size_align(300, 8).expect("layout");
        // SAFETY: `grown` came from this instance, currently sized as `grown_layout`.
        unsafe { GlobalAlloc::dealloc(&global, grown, grown_layout) };
        assert_eq!(global.records.len(), 0);
        assert_eq!(global.requested(), 0);
        global.purge();
    }
}
