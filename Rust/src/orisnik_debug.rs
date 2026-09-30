// SPDX-License-Identifier: MIT OR Apache-2.0
//! The `debug-allocator` hooks — HPHA's `allocator::debug_add`/`debug_remove`/
//! `debug_replace`/`debug_update`/`debug_check`/`debug_purge` (`Cpp/hpha.cpp:863-950`),
//! called by [`Orisnik`]'s public methods at the points HPHA's own `alloc`/
//! `realloc`/`resize`/`free`/`purge` call them (`Cpp/hpha.h:1264-1440`). The one deliberate
//! addition is a `debug_check` at the top of `realloc_aligned`'s misaligned-move branch (HPHA
//! verifies only later, inside `free`): that branch reads the block's page marker or header
//! before anything else, so a foreign pointer must be rejected first. It changes no state, so
//! it costs no parity; both ports carry it. With the feature
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
//! never observes or records its own allocations", because it is what makes `report()`
//! safe: formatting a report (a `Backtrace`'s symbol resolution, or a caller's sink) can
//! allocate while the record tree is being walked, and the walk must not see records inserted
//! by its own allocations. `report`/`write_report` therefore hold `busy`; `check` allocates
//! nothing during its walk and does not need to.
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
use crate::spomen::error::OrisError;
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

/// A `fmt::Write` sink over standard error: one unbuffered `write_all` per piece, so
/// printing a report needs no heap buffer and allocates nothing from this instance.
struct StderrSink;

impl core::fmt::Write for StderrSink {
    fn write_str(&mut self, text: &str) -> core::fmt::Result {
        use std::io::Write;
        std::io::stderr()
            .write_all(text.as_bytes())
            .map_err(|_| core::fmt::Error)
    }
}

impl Orisnik {
    /// Audits every live allocation and returns the first problem found, without changing
    /// anything and without panicking. Ports `allocator::check` (which `assert`s each
    /// record's size against the block's size and its guard ramp): for every record, in
    /// address order, the recorded size must fit the block and the trailing guard ramp must
    /// still be intact. Stops at the first mismatch, like HPHA.
    ///
    /// Available with the `debug-allocator` feature. A hook-detected corruption panics; this
    /// is the way to *ask* instead, e.g. from a test or a periodic self-check.
    ///
    /// Once a hook has detected corruption the hooks are off for good and the records may be
    /// stale (a caller who caught the panic can free the block, which no longer retires its
    /// record). Auditing them would read freed memory, so `check` then refuses and returns an
    /// error instead: the heap is, by definition, no longer trustworthy.
    ///
    /// # Errors
    /// Returns [`OrisError::Corruption`] if a live record is found overrun or inconsistent
    /// with its block (the message gives the block address, the sizes and — for an owned
    /// instance — where it was allocated), or if a corruption was detected earlier and the
    /// records can no longer be audited.
    pub fn check(&self) -> Result<(), OrisError> {
        if self.disabled.get() {
            return Err(OrisError::Corruption(
                "records can no longer be audited (a corruption was already detected)".to_owned(),
            ));
        }
        let mut cursor = self.records.first();
        // EXPLICIT: walks the store by successor pointer, latched before the body runs; the
        // cursor is the state, not expressible as an iterator over the record tree.
        while let Some(record) = cursor {
            // Latched first: nothing below changes the store, but this keeps the walk
            // robust should a future caller interleave allocations.
            cursor = self.records.next(record);
            if let Some(problem) = self.audit_record(record) {
                return Err(problem);
            }
        }
        Ok(())
    }

    /// The problem with one live allocation, if any: its recorded size must fit the block
    /// and its guard ramp must be intact.
    fn audit_record(&self, record: NonNull<Record>) -> Option<OrisError> {
        // SAFETY: `record` is live (the caller got it from the store).
        let ptr = unsafe { (*record.as_ptr()).ptr };
        // SAFETY: `record` is live; reads one field.
        let size = unsafe { (*record.as_ptr()).size };
        // SAFETY: `ptr` is a live allocation this instance produced (it has a record).
        let usable = unsafe { self.size(Some(ptr)) };
        let problem = if size > usable {
            Corruption::Oversized { usable }
        } else {
            // SAFETY: `record` is live (see above).
            let record_ref = unsafe { &*record.as_ptr() };
            // SAFETY: `ptr` is valid for `size + MEMORY_GUARD_SIZE` bytes (its recorded
            // size fits the block, checked just above).
            if unsafe { record_ref.check_guard() } {
                return None;
            }
            Corruption::GuardOverrun
        };
        // SAFETY: `record` is live (nothing has touched the store since).
        let message = unsafe { failure::describe(problem, ptr, Some(record)) };
        Some(OrisError::Corruption(message))
    }

    /// Prints a report of the allocator's state to standard error: total requested and
    /// allocated bytes, then one line per live allocation (address, requested size, and
    /// where it was allocated). Ports `allocator::report`, which `printf`s the same content
    /// to stdout. Available with the `debug-allocator` feature.
    ///
    /// This is the form to use when this `Orisnik` is the `#[global_allocator]`: it formats
    /// straight to stderr, so it allocates nothing that outlives the call. See
    /// [`Orisnik::write_report`] for the caveat on the other form.
    ///
    /// After a detected corruption the records may be stale, so the report may list blocks
    /// that have since been freed; it only reads recorded data, never the blocks themselves.
    ///
    /// Each callstack is a `std::backtrace::Backtrace`, which cannot skip frames, so it begins
    /// with the capture call and the allocator's own frames (about ten of them) before reaching
    /// the caller's; `orisnitsa` trims to the caller where it can. Diagnostic content only —
    /// outside the cross-port invariant (see `ROADMAP.md`'s scope note).
    pub fn report(&self) {
        let _busy = self.hold_busy();
        // A failed write to stderr has nowhere to be reported; the report is best-effort.
        let _ = self.write_report_unguarded(&mut StderrSink);
    }

    /// [`Orisnik::report`]'s content, written to `out` instead of stderr.
    ///
    /// **Caveat for a `#[global_allocator]`.** Whatever `out` allocates while the report is
    /// being written (a `String` growing, say) is allocated while the hooks are suspended,
    /// so it is *unrecorded* — and freeing it later, outside the report, would look like a
    /// double free. With an owned instance `out` allocates from the system allocator and
    /// none of this applies. When this instance is the global allocator, use
    /// [`Orisnik::report`].
    ///
    /// # Errors
    /// Returns `fmt::Error` when `out` does.
    pub fn write_report<W: core::fmt::Write + ?Sized>(&self, out: &mut W) -> core::fmt::Result {
        let _busy = self.hold_busy();
        self.write_report_unguarded(out)
    }

    /// Suspends the hooks for as long as the returned guard lives, if they are not already
    /// suspended: the report iterates the record tree while formatting, and formatting can
    /// allocate (a `Backtrace`'s symbol resolution), which must not insert into the tree
    /// mid-walk. Unlike [`Orisnik::enter_hook`] this also works when the hooks are
    /// `disabled`: reading the records is still meaningful after a detected corruption.
    fn hold_busy(&self) -> Option<Busy<'_>> {
        if self.busy.get() {
            return None;
        }
        self.busy.set(true);
        Some(Busy(&self.busy))
    }

    /// The report itself, in address order. The caller has suspended the hooks.
    fn write_report_unguarded<W: core::fmt::Write + ?Sized>(
        &self,
        out: &mut W,
    ) -> core::fmt::Result {
        self.write_report_head(out)?;
        let mut cursor = self.records.first();
        // EXPLICIT: same successor-pointer walk as `check`; the cursor is the state.
        while let Some(record) = cursor {
            cursor = self.records.next(record);
            Self::write_record_line(record, out)?;
        }
        Self::write_report_foot(out)
    }

    fn write_report_head<W: core::fmt::Write + ?Sized>(&self, out: &mut W) -> core::fmt::Result {
        writeln!(
            out,
            "REPORT ================================================="
        )?;
        writeln!(out, "Total requested size={} bytes", self.requested())?;
        writeln!(out, "Total allocated size={} bytes", self.allocated())?;
        writeln!(out, "Currently allocated blocks:")
    }

    fn write_report_foot<W: core::fmt::Write + ?Sized>(out: &mut W) -> core::fmt::Result {
        writeln!(
            out,
            "==========================================================="
        )
    }

    /// One live allocation's line in the report: address, requested size, and — if one was
    /// recorded — the allocation callstack.
    fn write_record_line<W: core::fmt::Write + ?Sized>(
        record: NonNull<Record>,
        out: &mut W,
    ) -> core::fmt::Result {
        // SAFETY: `record` is live (the caller got it from the store); only borrowed for
        // the duration of this formatting.
        let record_ref = unsafe { &*record.as_ptr() };
        // PROVENANCE: address read for its bit pattern only (it is printed).
        let address = record_ref.ptr.as_ptr().addr();
        write!(out, "ptr={address:#x}, size={}", record_ref.size)?;
        if let Some(trace) = &record_ref.callstack {
            // `Backtrace`'s `Display` ends in a newline of its own; trimmed so that a record
            // with a callstack is followed by no blank line, as in `orisnitsa`'s report.
            let text = trace.to_string();
            write!(out, "\n{}", text.trim_end())?;
        }
        writeln!(out)
    }

    /// The leak half of `Drop`, run first — before the record store is released, in HPHA's
    /// `check()`-then-`report()` order (releasing idle memory would not disturb a live block;
    /// only the records must outlive the audit): if any allocation is still live, audits it
    /// and prints the report to stderr — HPHA's `~allocator`'s `check(); report();`. Returns how many
    /// allocations leaked. After a detected corruption (the hooks are off, so the records may
    /// be stale) it audits nothing and returns `0`, but prints one line saying that the records
    /// were skipped.
    ///
    /// Two constraints shape it, both from Tree Borrows (see `list.rs`'s "`Drop` and
    /// `&mut self`" section):
    ///
    /// - It writes into `self` (the `busy` flag) **before** reading anything else: a write
    ///   *after* a foreign read of a protected tag is undefined.
    /// - It walks the record **book** (a plain array of pages, in storage order), never
    ///   the record tree: the tree's leaves point at its sentinel, and reading the sentinel
    ///   through those stored pointers — foreign to the retagged `Box` an `oris_destroy`ed
    ///   instance lives in — makes the box's deallocation undefined. The order of the leak
    ///   report therefore differs from [`Orisnik::report`]'s address order; the content is
    ///   the same.
    pub(super) fn debug_teardown(&self) -> usize {
        self.debug_teardown_to(&mut StderrSink)
    }

    /// [`Orisnik::debug_teardown`] with the destination explicit, so a test can read what
    /// `Drop` would print. Same constraints, same return value.
    fn debug_teardown_to<W: core::fmt::Write + ?Sized>(&self, sink: &mut W) -> usize {
        if self.disabled.get() {
            // The records may be stale, so nothing is audited, reported or failed on — but a
            // caught corruption panic must not make the leaks behind it vanish without a
            // word, so say what was skipped. (`len` reads a counter, not a record.)
            let unaudited = self.records.len();
            if unaudited > 0 {
                let _ = writeln!(
                    sink,
                    concat!(
                        "orisnik: dropped after a detected corruption with {} record(s) ",
                        "still on the books; they were not audited, so any leak among them is not reported"
                    ),
                    unaudited
                );
            }
            return 0;
        }
        self.busy.set(true);
        let leaked = self.records.len();
        if leaked == 0 {
            return 0;
        }
        let _ = writeln!(
            sink,
            "orisnik: {leaked} allocation(s) were still live when the allocator was dropped"
        );
        let mut first_problem = None;
        self.records.for_each_live(|record| {
            if first_problem.is_none() {
                first_problem = self.audit_record(record);
            }
        });
        if let Some(problem) = first_problem {
            let _ = writeln!(sink, "orisnik: {problem}");
        }
        let _ = self.write_report_head(&mut *sink);
        self.records.for_each_live(|record| {
            let _ = Self::write_record_line(record, &mut *sink);
        });
        let _ = Self::write_report_foot(&mut *sink);
        leaked
    }
}

/// The panic that ends `Drop` when `leaked` allocations were still live (HPHA's destructor
/// assert), skipped while the thread is already unwinding: a second panic would abort the
/// process and bury the first one.
pub(super) fn fail_on_leak(leaked: usize) {
    if leaked == 0 || std::thread::panicking() {
        return;
    }
    failure::fail(&format!(
        "memory leaked: {leaked} allocation(s) still live when the allocator was dropped \
         (see the report above)"
    ));
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

    fn usable_size(orisnik: &Orisnik, ptr: NonNull<u8>) -> usize {
        // SAFETY: see the helpers' shared contract above.
        unsafe { orisnik.size(Some(ptr)) }
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
        orisnik.purge();
        // A wrong size is still caught on both sources (a fresh instance each time: a
        // detection disables the hooks for good, and re-enabling them would leave a stale
        // record for the block reclaimed below).
        for size in [24_usize, 3000] {
            let wrong = Orisnik::new();
            let ptr = alloc(&wrong, size);
            let message = panic_message(|| free_sized(&wrong, ptr, size + 1)).expect("caught");
            assert!(message.contains("freed as"), "{message}");
            // The detection disabled the hooks; reclaim for real.
            free(&wrong, ptr);
            wrong.purge();
        }
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

    // ---- tests that pin each hook call site (found by a mutation audit) ----
    //
    // Each test below fails if the named call is deleted, or given the wrong source, size or
    // `orig_size`. The audit ran ~60 such mutants against the suite; these are the ones the
    // earlier tests let survive.

    fn has_callstack(orisnik: &Orisnik, ptr: NonNull<u8>) -> bool {
        let record = orisnik.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record.
        unsafe { (*record.as_ptr()).callstack.is_some() }
    }

    fn totals(orisnik: &Orisnik) -> (usize, usize) {
        (
            orisnik.requested_buckets.get(),
            orisnik.requested_tree.get(),
        )
    }

    #[test]
    fn counters_and_sources_follow_every_realloc_path() {
        let orisnik = Orisnik::new();
        // bucket -> bucket
        let ptr = alloc(&orisnik, 24);
        let ptr = realloc(&orisnik, ptr, 100).expect("realloc");
        assert_eq!(totals(&orisnik), (100 + MEMORY_GUARD_SIZE, 0));
        assert!(orisnik.verify(ptr, Some(100)).is_ok());
        assert!(orisnik.verify(ptr, Some(3)).is_err());
        free(&orisnik, ptr);
        // tree -> tree, growing and shrinking below the bucket threshold
        let ptr = alloc(&orisnik, 3000);
        let ptr = realloc(&orisnik, ptr, 9000).expect("realloc");
        assert_eq!(recorded_size(&orisnik, ptr), 9000);
        assert_eq!(totals(&orisnik), (0, 9000 + MEMORY_GUARD_SIZE));
        let ptr = realloc(&orisnik, ptr, 5).expect("realloc");
        assert_eq!(recorded_size(&orisnik, ptr), 5);
        assert!(
            orisnik.verify(ptr, Some(5)).is_ok(),
            "a tree record compares raw"
        );
        free(&orisnik, ptr);
        // aligned bucket in place
        let ptr = orisnik.alloc_aligned(24, 32).expect("alloc");
        let ptr = realloc_aligned(&orisnik, ptr, 60, 32).expect("realloc");
        assert_eq!(totals(&orisnik), (60 + MEMORY_GUARD_SIZE, 0));
        free(&orisnik, ptr);
        // aligned tree -> tree, growing and shrinking
        let ptr = orisnik.alloc_aligned(3000, 128).expect("alloc");
        let ptr = realloc_aligned(&orisnik, ptr, 9000, 128).expect("realloc");
        assert_eq!(recorded_size(&orisnik, ptr), 9000);
        assert_eq!(totals(&orisnik), (0, 9000 + MEMORY_GUARD_SIZE));
        let ptr = realloc_aligned(&orisnik, ptr, 5, 128).expect("realloc");
        assert!(
            orisnik.verify(ptr, Some(5)).is_ok(),
            "a tree record compares raw"
        );
        free(&orisnik, ptr);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn bucket_resize_re_records_the_usable_size() {
        // `alloc(20)` lands in a 24-byte usable slot, so the recorded size must *change*
        // (20 -> 24) for a missing `debug_update` to be visible; `alloc(24)` would hide it.
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 20);
        let usable = resize(&orisnik, ptr, 20);
        assert_eq!(usable, 24);
        assert_eq!(recorded_size(&orisnik, ptr), 24);
        assert_eq!(orisnik.requested_buckets.get(), 24 + MEMORY_GUARD_SIZE);
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn realloc_aligned_detects_an_overrun_in_place() {
        for (size, alignment) in [(40_usize, 32_usize), (3000, 128)] {
            let orisnik = Orisnik::new();
            let ptr = orisnik.alloc_aligned(size, alignment).expect("alloc");
            overrun(ptr, size);
            let message = panic_message(|| {
                let _ = realloc_aligned(&orisnik, ptr, size + 8, alignment);
            })
            .expect("detected");
            assert!(message.contains("guard bytes overwritten"), "{message}");
            free(&orisnik, ptr);
            orisnik.purge();
        }
    }

    #[test]
    fn a_misaligned_realloc_aligned_verifies_before_moving() {
        let orisnik = Orisnik::new();
        let first = alloc(&orisnik, 24);
        let second = alloc(&orisnik, 24);
        assert_ne!(
            second.addr().get() % 64,
            0,
            "the test needs a misaligned block"
        );
        overrun(second, 24);
        let message = panic_message(|| {
            let _ = realloc_aligned(&orisnik, second, 100, 64);
        })
        .expect("detected");
        assert!(message.contains("guard bytes overwritten"), "{message}");
        // Detection came before the alloc-copy-free: nothing new was allocated.
        assert_eq!(orisnik.records.len(), 2);
        free(&orisnik, second);
        free(&orisnik, first);
        orisnik.purge();
    }

    #[test]
    fn a_sized_aligned_free_detects_a_wrong_size() {
        let orisnik = Orisnik::new();
        let ptr = orisnik.alloc_aligned(40, 32).expect("alloc");
        let message =
            panic_message(|| free_sized_aligned(&orisnik, ptr, 41, 32)).expect("mismatch");
        assert!(
            message.contains("allocated as 40 bytes, freed as 41"),
            "{message}"
        );
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn purge_returns_the_record_page() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        orisnik.purge();
        // The purge released the (now empty) record page, so the next allocation needs a
        // fresh map for it; refusing the second map (the first serves the bucket page)
        // makes that observable.
        let refusal = test_vm::fail_map_after(1);
        assert!(orisnik.alloc(24).is_none());
        drop(refusal);
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn a_record_store_out_of_memory_frees_every_kind_of_block() {
        let orisnik = Orisnik::new();
        for kind in 0..4 {
            let refusal = test_vm::fail_map_after(1);
            let refused = match kind {
                0 => orisnik.alloc(5000),
                1 => orisnik.alloc_aligned(5000, 128),
                2 => orisnik.alloc(24),
                _ => orisnik.alloc_aligned(24, 32),
            };
            drop(refusal);
            assert!(refused.is_none(), "kind {kind}");
            assert_eq!(
                (orisnik.requested(), orisnik.records.len()),
                (0, 0),
                "kind {kind}"
            );
            orisnik.purge();
            assert_eq!(
                orisnik.allocated(),
                0,
                "kind {kind}: the block was not given back"
            );
        }
    }

    #[test]
    fn nested_realloc_and_resize_skip_every_hook() {
        let orisnik = Orisnik::new();
        let outer = alloc(&orisnik, 24);
        {
            let _busy = orisnik.enter_hook().expect("hooks are on");
            let nested = alloc(&orisnik, 40);
            let nested = realloc(&orisnik, nested, 60).expect("realloc");
            let nested = realloc(&orisnik, nested, 3000).expect("realloc");
            let _ = resize(&orisnik, nested, 3000);
            let nested = realloc(&orisnik, nested, 3200).expect("realloc");
            free(&orisnik, nested);
            assert_eq!(orisnik.records.len(), 1, "only the outer block is recorded");
        }
        free(&orisnik, outer);
        assert_eq!(orisnik.requested(), 0);
        orisnik.purge();
    }

    #[test]
    fn callstacks_follow_replace_and_update_and_the_global_latch() {
        use core::alloc::{GlobalAlloc, Layout};
        // An owned instance keeps a callstack through replace and update.
        let owned = Orisnik::new();
        let ptr = alloc(&owned, 24);
        let ptr = realloc(&owned, ptr, 100).expect("realloc");
        assert!(has_callstack(&owned, ptr));
        let _ = resize(&owned, ptr, 100);
        assert!(has_callstack(&owned, ptr));
        free(&owned, ptr);
        owned.purge();

        // An instance used through GlobalAlloc records none, whichever entry point latched it.
        let layout = Layout::from_size_align(24, 8).expect("layout");
        let via_realloc = Orisnik::new();
        let ptr = alloc(&via_realloc, 24);
        // SAFETY: `ptr` is live and was allocated with `layout`'s size.
        let grown = unsafe { GlobalAlloc::realloc(&via_realloc, ptr.as_ptr(), layout, 100) };
        let grown = NonNull::new(grown).expect("realloc");
        assert!(!has_callstack(&via_realloc, grown));
        free(&via_realloc, grown);
        via_realloc.purge();

        let via_zeroed = Orisnik::new();
        // SAFETY: non-zero size.
        let zeroed = unsafe { GlobalAlloc::alloc_zeroed(&via_zeroed, layout) };
        let zeroed = NonNull::new(zeroed).expect("alloc_zeroed");
        assert!(!has_callstack(&via_zeroed, zeroed));
        free(&via_zeroed, zeroed);
        via_zeroed.purge();
    }

    #[test]
    fn every_globalalloc_entry_point_latches_the_instance() {
        use core::alloc::{GlobalAlloc, Layout};
        let layout = Layout::from_size_align(24, 8).expect("layout");
        for entry in 0..4 {
            let orisnik = Orisnik::new();
            let ptr = alloc(&orisnik, 24);
            assert!(!orisnik.used_as_global.get());
            let raw = match entry {
                // SAFETY: non-zero size.
                0 => unsafe { GlobalAlloc::alloc(&orisnik, layout) },
                // SAFETY: non-zero size.
                1 => unsafe { GlobalAlloc::alloc_zeroed(&orisnik, layout) },
                // SAFETY: `ptr` is a live allocation of `orisnik` made with `layout`'s size; 48
                // is non-zero.
                2 => unsafe { GlobalAlloc::realloc(&orisnik, ptr.as_ptr(), layout, 48) },
                _ => {
                    // SAFETY: `ptr` is a live allocation of `orisnik` made with `layout`'s size.
                    unsafe { GlobalAlloc::dealloc(&orisnik, ptr.as_ptr(), layout) };
                    core::ptr::null_mut()
                }
            };
            assert!(orisnik.used_as_global.get(), "entry point {entry}");
            if let Some(extra) = NonNull::new(raw) {
                free(&orisnik, extra);
            }
            if entry < 2 {
                free(&orisnik, ptr);
            }
            orisnik.purge();
        }
    }

    // ---- `check()`, `report()` and leak detection at drop ---------------------------------

    fn report_text(orisnik: &Orisnik) -> String {
        let mut text = String::new();
        orisnik
            .write_report(&mut text)
            .expect("writing to a String");
        text
    }

    /// A page-sized leak left behind by a block the test deliberately never freed: release
    /// its bucket page by hand so the test process (and Miri's leak checker) stay clean.
    fn release_leaked_bucket_page(block: NonNull<u8>) {
        let base = crate::align::align_down(block.as_ptr(), crate::os::PAGE_SIZE);
        // SAFETY: `block` is a bucket slot, so `base` is the `PAGE_SIZE` mapping it lives in;
        // the owning allocator has been dropped and left the page mapped; nothing uses it.
        unsafe {
            crate::os::unmap(NonNull::new(base).expect("non-null"), crate::os::PAGE_SIZE);
        }
    }

    #[test]
    fn check_passes_on_a_healthy_heap_of_every_kind() {
        let orisnik = Orisnik::new();
        assert!(orisnik.check().is_ok(), "an empty heap is healthy");
        let blocks = [
            alloc(&orisnik, 24),
            alloc(&orisnik, 1000),
            orisnik.alloc_aligned(24, 32).expect("alloc"),
            orisnik.alloc_aligned(3000, 128).expect("alloc"),
            orisnik.calloc(3, 40).expect("calloc"),
        ];
        assert!(orisnik.check().is_ok());
        let grown = realloc(&orisnik, blocks[1], 4000).expect("realloc");
        assert!(orisnik.check().is_ok(), "still healthy after a realloc");
        for ptr in [blocks[0], grown, blocks[2], blocks[3], blocks[4]] {
            free(&orisnik, ptr);
        }
        assert!(orisnik.check().is_ok());
        orisnik.purge();
    }

    #[test]
    fn check_reports_a_guard_overrun_without_panicking_or_disabling_the_hooks() {
        for size in [24_usize, 3000] {
            let orisnik = Orisnik::new();
            let healthy = alloc(&orisnik, 64);
            let victim = alloc(&orisnik, size);
            overrun(victim, size);
            let Err(OrisError::Corruption(message)) = orisnik.check() else {
                panic!("the overrun must be reported");
            };
            assert!(message.contains("guard bytes overwritten"), "{message}");
            assert!(
                message.contains(&format!("requested {size} bytes")),
                "{message}"
            );
            assert!(!orisnik.disabled.get(), "asking is not a detection");
            // Repair the block (the same flip restores it) and the audit passes again.
            overrun(victim, size);
            assert!(orisnik.check().is_ok());
            free(&orisnik, victim);
            free(&orisnik, healthy);
            orisnik.purge();
        }
    }

    #[test]
    fn check_reports_a_record_larger_than_its_block() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        let record = orisnik.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record; forging its size is the point of the test.
        unsafe { (*record.as_ptr()).size = 10_000 };
        let Err(OrisError::Corruption(message)) = orisnik.check() else {
            panic!("the oversized record must be reported");
        };
        assert!(message.contains("recorded size exceeds"), "{message}");
        assert!(message.contains("recorded 10000 bytes"), "{message}");
        // One line for the head (no stray newline inside the message), and the real usable
        // size is the one reported.
        let usable = usable_size(&orisnik, ptr);
        assert!(
            message
                .lines()
                .next()
                .is_some_and(|head| head.ends_with(&format!("block holds {usable})"))),
            "{message}"
        );
        // SAFETY: as above; restoring the true size.
        unsafe { (*record.as_ptr()).size = 24 };
        assert!(orisnik.check().is_ok());
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn check_stops_at_the_first_problem_in_address_order() {
        let orisnik = Orisnik::new();
        let mut blocks = [
            alloc(&orisnik, 24),
            alloc(&orisnik, 24),
            alloc(&orisnik, 24),
        ];
        blocks.sort_by_key(|ptr| ptr.addr());
        overrun(blocks[2], 24);
        overrun(blocks[1], 24);
        let Err(OrisError::Corruption(message)) = orisnik.check() else {
            panic!("reported");
        };
        assert!(
            message.contains(&format!("{:#x}", blocks[1].addr().get())),
            "the lower address must be reported first: {message}"
        );
        overrun(blocks[2], 24);
        overrun(blocks[1], 24);
        for ptr in blocks {
            free(&orisnik, ptr);
        }
        orisnik.purge();
    }

    #[test]
    fn report_lists_the_totals_and_every_live_block_in_address_order() {
        let orisnik = Orisnik::new();
        let mut blocks = [
            alloc(&orisnik, 24),
            alloc(&orisnik, 1000),
            alloc(&orisnik, 100),
        ];
        let text = report_text(&orisnik);
        assert!(text.starts_with("REPORT ===="), "{text}");
        assert!(text.contains("Currently allocated blocks:"), "{text}");
        assert!(
            text.contains(&format!(
                "Total requested size={} bytes",
                orisnik.requested()
            )),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "Total allocated size={} bytes",
                orisnik.allocated()
            )),
            "{text}"
        );
        blocks.sort_by_key(|ptr| ptr.addr());
        let mut cursor = 0;
        for ptr in blocks {
            let line = format!(
                "ptr={:#x}, size={}",
                ptr.addr().get(),
                recorded_size(&orisnik, ptr)
            );
            let at = text[cursor..]
                .find(&line)
                .unwrap_or_else(|| panic!("{line} missing or out of order in:\n{text}"));
            cursor += at + line.len();
        }
        assert!(text.trim_end().ends_with("==========="), "{text}");
        for ptr in blocks {
            free(&orisnik, ptr);
        }
        let empty = report_text(&orisnik);
        assert!(
            !empty.contains("ptr="),
            "a freed block must leave the report: {empty}"
        );
        orisnik.purge();
    }

    #[test]
    fn report_shows_where_an_owned_instance_allocated_but_not_a_global_one() {
        use core::alloc::{GlobalAlloc, Layout};
        let owned = Orisnik::new();
        let ptr = alloc(&owned, 24);
        let text = report_text(&owned);
        assert!(
            !text.contains("\n\n"),
            "no blank line after a record's callstack: {text}"
        );
        if cfg!(miri) {
            // Miri records the cheap, disabled backtrace (see `capture_callstack`).
            assert!(text.contains("disabled backtrace"), "{text}");
        } else {
            assert!(
                text.contains("report_shows_where_an_owned_instance"),
                "the trace should name this test: {text}"
            );
        }
        free(&owned, ptr);
        owned.purge();

        // An instance used through `GlobalAlloc` records no callstack at all.
        let global = Orisnik::new();
        let layout = Layout::from_size_align(24, 8).expect("layout");
        // SAFETY: non-zero size.
        let raw = unsafe { GlobalAlloc::alloc(&global, layout) };
        let text = report_text(&global);
        assert!(text.contains("ptr="), "{text}");
        assert!(!text.contains("backtrace"), "{text}");
        assert!(!text.contains("report_shows_where"), "{text}");
        // SAFETY: `raw` came from `GlobalAlloc::alloc` above with this layout.
        unsafe { GlobalAlloc::dealloc(&global, raw, layout) };
        global.purge();
    }

    #[test]
    fn report_works_while_the_hooks_are_suspended_or_disabled() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        orisnik.disabled.set(true);
        assert!(report_text(&orisnik).contains("ptr="));
        orisnik.disabled.set(false);
        let outer = orisnik.enter_hook().expect("hooks are on");
        assert!(report_text(&orisnik).contains("ptr="));
        assert!(orisnik.busy.get(), "an outer hold survives the report");
        drop(outer);
        assert!(!orisnik.busy.get());
        free(&orisnik, ptr);
        orisnik.purge();
    }

    #[test]
    fn a_leak_at_drop_is_reported_then_panics_after_everything_else_is_released() {
        let before = test_vm::live_mappings();
        let orisnik = Box::new(Orisnik::new());
        let leaked = alloc(&orisnik, 24);
        let idle = alloc(&orisnik, 5000);
        free(&orisnik, idle);
        let message = panic_message(move || drop(orisnik)).expect("a leak must fail the drop");
        assert!(
            message.contains("memory leaked: 1 allocation(s)"),
            "{message}"
        );
        // Everything idle was returned before the panic (the tree arena, the record page);
        // only the leaked block's own bucket page remains.
        assert_eq!(test_vm::live_mappings(), before + 1);
        release_leaked_bucket_page(leaked);
        assert_eq!(test_vm::live_mappings(), before);
    }

    #[test]
    fn a_leak_during_unwinding_does_not_abort_the_process() {
        let before = test_vm::live_mappings();
        // A `Cell`: the closure below always panics, so a plain assignment inside it looks
        // never-read to the compiler even though the test reads it afterwards.
        let leaked = core::cell::Cell::new(None);
        let outer = panic_message(|| {
            let orisnik = Box::new(Orisnik::new());
            leaked.set(Some(alloc(&orisnik, 24)));
            // Dropped while this panic unwinds: a second panic would abort the test binary.
            panic!("outer failure");
        })
        .expect("the outer panic propagates");
        assert!(outer.contains("outer failure"), "{outer}");
        release_leaked_bucket_page(leaked.get().expect("allocated"));
        assert_eq!(test_vm::live_mappings(), before);
    }

    #[test]
    fn a_clean_drop_does_not_panic_and_leaves_no_mappings() {
        let before = test_vm::live_mappings();
        let orisnik = Box::new(Orisnik::new());
        let first = alloc(&orisnik, 24);
        let second = alloc(&orisnik, 5000);
        free(&orisnik, first);
        free(&orisnik, second);
        assert!(panic_message(move || drop(orisnik)).is_none());
        assert_eq!(test_vm::live_mappings(), before);
    }

    #[test]
    fn a_drop_after_a_detected_corruption_skips_the_leak_report() {
        let before = test_vm::live_mappings();
        let orisnik = Box::new(Orisnik::new());
        let leaked = alloc(&orisnik, 24);
        let victim = alloc(&orisnik, 24);
        free(&orisnik, victim);
        // Deliberate double free: detected, and the hooks are off from here on.
        assert!(panic_message(|| free(&orisnik, victim)).is_some());
        assert!(orisnik.disabled.get());
        // The records may be stale now, so the still-live block is not reported as a leak —
        // but the teardown says it skipped them, rather than staying silent.
        let mut text = String::new();
        assert_eq!(orisnik.debug_teardown_to(&mut text), 0);
        assert!(
            text.contains("dropped after a detected corruption with 1 record(s)"),
            "{text}"
        );
        assert!(
            !text.contains("REPORT"),
            "no report of possibly-stale records: {text}"
        );
        assert!(panic_message(move || drop(orisnik)).is_none());
        release_leaked_bucket_page(leaked);
        assert_eq!(test_vm::live_mappings(), before);
    }

    #[test]
    fn dropping_a_globalalloc_instance_reports_no_callstack_but_still_detects_the_leak() {
        use core::alloc::{GlobalAlloc, Layout};
        let before = test_vm::live_mappings();
        let orisnik = Box::new(Orisnik::new());
        let layout = Layout::from_size_align(24, 8).expect("layout");
        // SAFETY: non-zero size.
        let raw = unsafe { GlobalAlloc::alloc(&*orisnik, layout) };
        let leaked = NonNull::new(raw).expect("alloc");
        let message = panic_message(move || drop(orisnik)).expect("a leak must fail the drop");
        assert!(message.contains("memory leaked"), "{message}");
        release_leaked_bucket_page(leaked);
        assert_eq!(test_vm::live_mappings(), before);
    }

    // ---- check() after a corruption, sinks that allocate, and the drop-time report -------

    /// A `fmt::Write` sink that allocates from the instance being reported on.
    struct AllocatingSink<'a> {
        orisnik: &'a Orisnik,
        blocks: Vec<NonNull<u8>>,
    }

    impl core::fmt::Write for AllocatingSink<'_> {
        fn write_str(&mut self, _text: &str) -> core::fmt::Result {
            self.blocks.push(self.orisnik.alloc(24).expect("alloc"));
            Ok(())
        }
    }

    #[test]
    fn write_report_suspends_the_hooks_for_allocations_made_by_the_sink() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        let mut sink = AllocatingSink {
            orisnik: &orisnik,
            blocks: Vec::new(),
        };
        orisnik.write_report(&mut sink).expect("sink never fails");
        assert!(!sink.blocks.is_empty());
        assert_eq!(
            orisnik.records.len(),
            1,
            "the sink's blocks must be unrecorded"
        );
        assert!(!orisnik.busy.get());
        // Freed under a hold, exactly as the documented caveat requires.
        let hold = orisnik.enter_hook().expect("hooks are on");
        for block in sink.blocks {
            free(&orisnik, block);
        }
        drop(hold);
        free(&orisnik, ptr);
        orisnik.purge();
    }

    /// After a detected corruption the hooks are off and a caught panic can be followed by
    /// freeing the block *without* retiring its record; auditing that stale record would read
    /// freed (here: unmapped) memory. `check` must refuse instead.
    #[test]
    fn check_after_a_detected_corruption_refuses_rather_than_reading_freed_memory() {
        let orisnik = Orisnik::new();
        let stale = alloc(&orisnik, 24);
        let victim = alloc(&orisnik, 24);
        free(&orisnik, victim);
        assert!(panic_message(|| free(&orisnik, victim)).is_some());
        assert!(orisnik.disabled.get());
        free(&orisnik, stale); // hooks are off: freed, but its record stays
        orisnik.purge(); // and the page is unmapped
        let Err(OrisError::Corruption(message)) = orisnik.check() else {
            panic!("check must refuse after a detected corruption");
        };
        assert!(message.contains("already detected"), "{message}");
    }

    #[test]
    fn a_clean_teardown_prints_nothing() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        free(&orisnik, ptr);
        let mut text = String::new();
        assert_eq!(orisnik.debug_teardown_to(&mut text), 0);
        assert!(text.is_empty(), "nothing leaked, nothing printed: {text}");
        orisnik.purge();
    }

    /// What `Drop` prints for a leak: the count, the first audit problem, then the report
    /// with each live block, in the order they were allocated.
    #[test]
    fn the_leak_report_printed_at_drop_lists_the_audit_and_every_live_block() {
        let orisnik = Box::new(Orisnik::new());
        let first = alloc(&orisnik, 24);
        let second = alloc(&orisnik, 1000);
        overrun(second, 1000);
        let mut text = String::new();
        assert_eq!(orisnik.debug_teardown_to(&mut text), 2);
        assert!(
            text.starts_with(
                "orisnik: 2 allocation(s) were still live when the allocator was dropped"
            ),
            "{text}"
        );
        assert!(
            text.contains("orisnik: guard bytes overwritten"),
            "the audit line: {text}"
        );
        assert!(text.contains("REPORT ===="), "{text}");
        let first_line = format!("ptr={:#x}, size=24", first.addr().get());
        let second_line = format!("ptr={:#x}, size=1000", second.addr().get());
        let at_first = text.find(&first_line).expect("first block listed");
        let at_second = text.find(&second_line).expect("second block listed");
        assert!(at_first < at_second, "storage (allocation) order: {text}");
        assert!(text.trim_end().ends_with("==========="), "{text}");
        // Undo: repair the block, lift the suspension the teardown set, and drop cleanly.
        overrun(second, 1000);
        orisnik.busy.set(false);
        free(&orisnik, first);
        free(&orisnik, second);
        assert!(panic_message(move || drop(orisnik)).is_none());
    }

    // ---- pins found by mutation review: order, suspension, sinks, golden text ------------

    fn record_ptr(record: NonNull<Record>) -> NonNull<u8> {
        // SAFETY: `record` is live (handed out by the store).
        unsafe { (*record.as_ptr()).ptr }
    }

    /// The drop-time audit and listing walk the record book in *storage* order, the public
    /// `report()` in address order; a freed slot that is reused sorts first by address but
    /// last in storage, which is what tells the two apart.
    #[test]
    fn the_leak_audit_and_listing_follow_storage_order_not_address_order() {
        let orisnik = Box::new(Orisnik::new());
        let first = alloc(&orisnik, 24);
        let others = [
            alloc(&orisnik, 24),
            alloc(&orisnik, 24),
            alloc(&orisnik, 24),
        ];
        free(&orisnik, first);
        // Reuses `first`'s slot: lowest address, stored last.
        let reused = alloc(&orisnik, 24);
        let mut storage = Vec::new();
        orisnik
            .records
            .for_each_live(|record| storage.push(record_ptr(record)));
        let mut by_address = Vec::new();
        let mut cursor = orisnik.records.first();
        while let Some(record) = cursor {
            by_address.push(record_ptr(record));
            cursor = orisnik.records.next(record);
        }
        let storage_first = *storage.first().expect("four live records");
        let address_first = *by_address.first().expect("four live records");
        assert_ne!(
            storage_first, address_first,
            "precondition: the two orders differ"
        );
        overrun(storage_first, 24);
        overrun(address_first, 24);
        let mut text = String::new();
        assert_eq!(orisnik.debug_teardown_to(&mut text), 4);
        let audit = text.lines().nth(1).expect("the audit line");
        assert!(
            audit.contains(&format!("{:#x}", storage_first.addr().get())),
            "the audit names the storage-first block: {text}"
        );
        let mut at = text
            .find("Currently allocated blocks:")
            .expect("the listing");
        for block in &storage {
            let line = format!("ptr={:#x},", block.addr().get());
            let found = text
                .get(at..)
                .and_then(|rest| rest.find(&line))
                .unwrap_or_else(|| panic!("{line} out of storage order in {text}"));
            at += found + line.len();
        }
        // Undo: repair both blocks, lift the suspension, and drop cleanly.
        overrun(storage_first, 24);
        overrun(address_first, 24);
        orisnik.busy.set(false);
        for block in others.into_iter().chain([reused]) {
            free(&orisnik, block);
        }
        assert!(panic_message(move || drop(orisnik)).is_none());
    }

    /// The teardown formats its report while the instance is suspended (`busy`), so a sink
    /// that allocates from the instance adds no records of its own.
    #[test]
    fn the_teardown_suspends_the_hooks_for_a_sink_that_allocates() {
        let orisnik = Box::new(Orisnik::new());
        let ptr = alloc(&orisnik, 24);
        let mut sink = AllocatingSink {
            orisnik: &orisnik,
            blocks: Vec::new(),
        };
        assert_eq!(orisnik.debug_teardown_to(&mut sink), 1);
        assert!(!sink.blocks.is_empty());
        assert_eq!(
            orisnik.records.len(),
            1,
            "the sink's blocks must be unrecorded"
        );
        for block in sink.blocks {
            free(&orisnik, block);
        }
        orisnik.busy.set(false);
        free(&orisnik, ptr);
        assert!(panic_message(move || drop(orisnik)).is_none());
    }

    #[test]
    fn write_report_accepts_an_unsized_sink() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        let mut text = String::new();
        let sink: &mut dyn core::fmt::Write = &mut text;
        orisnik.write_report(sink).expect("a String sink");
        assert!(text.contains("ptr="), "{text}");
        free(&orisnik, ptr);
        orisnik.purge();
    }

    /// The exact report text (a global-latched instance records no callstack, so it is fully
    /// deterministic); Zig has the same golden test.
    #[test]
    fn report_golden_output() {
        let orisnik = Orisnik::new();
        orisnik.mark_used_as_global();
        let first = alloc(&orisnik, 24);
        let second = alloc(&orisnik, 100);
        let mut blocks = [(first, 24), (second, 100)];
        blocks.sort_by_key(|(ptr, _)| ptr.addr());
        let expected = format!(
            concat!(
                "REPORT =================================================\n",
                "Total requested size={} bytes\n",
                "Total allocated size={} bytes\n",
                "Currently allocated blocks:\n",
                "ptr={:#x}, size={}\n",
                "ptr={:#x}, size={}\n",
                "===========================================================\n",
            ),
            orisnik.requested(),
            orisnik.allocated(),
            blocks[0].0.addr().get(),
            blocks[0].1,
            blocks[1].0.addr().get(),
            blocks[1].1,
        );
        assert_eq!(report_text(&orisnik), expected);
        free(&orisnik, first);
        free(&orisnik, second);
        orisnik.purge();
    }

    /// A record only one byte larger than its block: the guard check fails too, so only the
    /// message tells the size check from it.
    #[test]
    fn check_flags_a_record_one_byte_larger_than_its_block() {
        let orisnik = Orisnik::new();
        let ptr = alloc(&orisnik, 24);
        let usable = usable_size(&orisnik, ptr);
        let record = orisnik.records.find(ptr).expect("recorded");
        // SAFETY: `record` is a live record; forging its size is the point of the test.
        unsafe { (*record.as_ptr()).size = usable + 1 };
        let Err(OrisError::Corruption(message)) = orisnik.check() else {
            panic!("the oversized record must be reported");
        };
        assert!(message.contains("recorded size exceeds"), "{message}");
        // SAFETY: as above; restoring the true size.
        unsafe { (*record.as_ptr()).size = 24 };
        assert!(orisnik.check().is_ok());
        free(&orisnik, ptr);
        orisnik.purge();
    }
}
