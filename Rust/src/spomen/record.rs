// SPDX-License-Identifier: MIT OR Apache-2.0
//! One allocation's debug record. Ports `Cpp/hpha.h`'s `allocator::debug_record` and
//! `debug_source`.
//!
//! A [`Record`] remembers everything the debug subsystem needs to know about one live
//! allocation: where it is, how big the *caller* asked for, which sub-allocator served
//! it, the seed of its trailing guard ramp, and where it was allocated from. Records are
//! kept in a [`crate::spomen::book::RecordBook`] and indexed by address in an
//! [`IntrusiveMultiRbTree`](crate::rbtree::IntrusiveMultiRbTree) via the embedded
//! [`NodeBase`], exactly as HPHA's `debug_record_map` does.
//!
//! # Callstack capture
//! HPHA's `record_stack` is a stub ("usually very system specific so here we just clear
//! all"). This port captures a real [`Backtrace`] instead — the idiomatic equivalent
//! `ROADMAP.md` allows ("contents must be equivalent, structure need not match"): the
//! capture is diagnostic content, never part of the cross-port state-transition
//! invariant. It uses [`Backtrace::force_capture`], not [`Backtrace::capture`]: the
//! latter is a no-op unless the *embedder's* `RUST_BACKTRACE` says otherwise, and a
//! debug allocator that silently records nothing would defeat its purpose.
//!
//! A `Backtrace` owns heap memory (it is not `Copy`, not plain old data), so a `Record`
//! has drop glue and the record book must move it with `ptr::read`/`ptr::write` and drop
//! it exactly once — see [`crate::spomen::book`].
//!
//! # `#[global_allocator]` and callstacks
//! [`Backtrace::force_capture`] **allocates**, and takes a process-wide, non-reentrant
//! lock inside std while it does. If an `Orisnik` with `debug-allocator` is itself the
//! `#[global_allocator]`, that is a **deadlock** waiting for application code that is
//! capturing a backtrace of its own (a panic hook with `RUST_BACKTRACE=1`, an explicit
//! `Backtrace::capture`): std holds its lock while it allocates; that allocation reaches
//! our hook; the hook tries to capture and blocks on the same lock, forever. No flag
//! inside the hook can see this, because the outer capture is not ours. (The
//! *recursion* one might expect — capturing inside `alloc` re-entering `alloc` — is not
//! the hazard: it is tamed by the dispatch layer's `busy` flag, see `orisnik_debug.rs`.)
//!
//! So an instance that has been used through the `GlobalAlloc` interface records **no
//! callstack** ([`Record::callstack`] is `None`): the record still tracks the pointer, the
//! requested size, the source and the guard seed, so guard-overrun, double-free and
//! size-mismatch detection all still work — only the "allocated at:" trace is absent.
//! Owned instances (the ordinary test/debug use, the `Allocator` trait, the C-ABI) are
//! unaffected: std's backtrace machinery allocates from the *system* allocator, not from
//! them. `orisnitsa` needs no such rule — its capture walks frames into a fixed buffer
//! with no lock and no allocation.
//!
//! The store methods also capture *before* touching any state, so nothing that runs while
//! a record is being built can observe a half-updated store.
//!
//! This module also makes `debug-allocator` require `std` (for `std::backtrace`); the
//! crate is not `no_std`, so nothing else changes.

use crate::rbtree::{NodeBase, RbNode};
use crate::spomen::guard::check_guard_seeded;
use core::cmp::Ordering;
use core::ptr::NonNull;
use std::backtrace::Backtrace;

/// Which sub-allocator served an allocation. Ports `debug_source`
/// (`DEBUG_SOURCE_BUCKETS = 0`, `DEBUG_SOURCE_TREE = 1`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
#[allow(clippy::exhaustive_enums)]
// EXHAUSTIVE: HPHA has exactly these two allocators; mirrored by orisnitsa's enum.
pub(crate) enum Source {
    /// The small-allocation path (`bucket.rs`).
    Buckets = 0,
    /// The large-allocation path (`tree.rs`).
    Tree = 1,
}

/// Everything the debug subsystem remembers about one live allocation. Ports
/// `debug_record`.
///
/// # Invariants
/// - [`NodeBase`] is the first field of a `#[repr(C)]` struct, so a `NonNull<Record>`
///   and its `NonNull<NodeBase>` are the same address ([`RbNode`]'s contract).
/// - `ptr` is only ever compared and (by [`Record::check_guard`]) read through; the
///   record does not own the allocation it describes.
/// - Records are ordered by `ptr`'s address, and every live allocation's address is
///   unique, so the tree never actually chains two records.
#[repr(C)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: crate-internal record; layout is not exposed and is free to grow.
pub(crate) struct Record {
    /// This record's tree linkage. Byte offset 0 (required by [`RbNode`]).
    pub(crate) node: NodeBase,
    /// The payload pointer the allocator handed to the caller.
    pub(crate) ptr: NonNull<u8>,
    /// The size the *caller* requested — not the (larger) usable size the block
    /// really has. The guard ramp trails at `ptr + size`.
    pub(crate) size: usize,
    /// Which sub-allocator served this allocation.
    pub(crate) source: Source,
    /// The first byte of this allocation's guard ramp — the seed
    /// [`crate::spomen::guard::write_guard`] was given.
    pub(crate) guard_byte: u8,
    /// Where this allocation was made from, or `None` when the allocator is in use as a
    /// `#[global_allocator]` and capturing would risk a deadlock (see the module doc's
    /// "global allocator" section).
    pub(crate) callstack: Option<Backtrace>,
}

// SAFETY: `node` is Record's first field (repr(C) guarantees offset 0).
unsafe impl RbNode for Record {
    /// A query key is a bare address: records are looked up by the pointer a caller
    /// hands back to `free`, never by a whole record.
    type Key = usize;

    unsafe fn cmp(this: NonNull<Self>, other: NonNull<Self>) -> Ordering {
        // PROVENANCE: addresses are read as ordering keys only; never turned back into
        // pointers.
        // SAFETY: caller guarantees `this` is live.
        let this_addr = unsafe { (*this.as_ptr()).ptr.as_ptr().addr() };
        // SAFETY: caller guarantees `other` is live.
        let other_addr = unsafe { (*other.as_ptr()).ptr.as_ptr().addr() };
        this_addr.cmp(&other_addr)
    }

    unsafe fn cmp_key(this: NonNull<Self>, key: &usize) -> Ordering {
        // SAFETY: caller guarantees `this` is live.
        let this_addr = unsafe { (*this.as_ptr()).ptr.as_ptr().addr() };
        this_addr.cmp(key)
    }
}

/// Captures the current callstack for a record. See the module doc for why this is
/// [`Backtrace::force_capture`].
///
/// Under Miri it degrades to [`Backtrace::capture`] (which honours `RUST_BACKTRACE` and is
/// a cheap no-op by default). Miri *can* capture, and can symbolicate with
/// `-Zmiri-isolation-error=warn`, but a real capture costs ~1.5 s there, so
/// record-heavy tests took minutes for nothing. Native builds always force the capture.
pub(crate) fn capture_callstack() -> Backtrace {
    capture_callstack_with(!cfg!(miri))
}

/// [`capture_callstack`] with the policy explicit: `force` selects
/// [`Backtrace::force_capture`] over [`Backtrace::capture`]. Exists so Miri tests can run
/// the *real* capture (which Miri does support — only symbolication is unsupported, it
/// needs the filesystem) a few times, to check that a heap-owning `Backtrace` survives
/// the record book's moves, without paying for it on every record.
pub(crate) fn capture_callstack_with(force: bool) -> Backtrace {
    if force {
        Backtrace::force_capture()
    } else {
        Backtrace::capture()
    }
}

impl Record {
    /// A fresh, unlinked record for the allocation at `ptr`, capturing the current
    /// callstack. Ports `debug_record(ptr, size, source)`'s `record_stack()` half; the
    /// `write_guard()` half stays with the caller, which owns the guard-seed stream
    /// (see [`crate::spomen::guard::write_guard`]) and passes the seed it used as
    /// `guard_byte`.
    #[must_use]
    pub(crate) fn new(ptr: NonNull<u8>, size: usize, source: Source, guard_byte: u8) -> Self {
        Self::with_callstack(ptr, size, source, guard_byte, Some(capture_callstack()))
    }

    /// [`Record::new`] with the callstack supplied by the caller.
    #[must_use]
    pub(crate) fn with_callstack(
        ptr: NonNull<u8>,
        size: usize,
        source: Source,
        guard_byte: u8,
        callstack: Option<Backtrace>,
    ) -> Self {
        Self {
            node: NodeBase::UNLINKED,
            ptr,
            size,
            source,
            guard_byte,
            callstack,
        }
    }

    /// Whether this allocation's trailing guard ramp is still exactly the one written
    /// for it. Ports `debug_record::check_guard`.
    ///
    /// # Safety
    /// The allocation this record describes must still be live and valid for
    /// `size + MEMORY_GUARD_SIZE` bytes, readable for at least the trailing
    /// [`crate::guard::MEMORY_GUARD_SIZE`] of them.
    #[must_use]
    pub(crate) unsafe fn check_guard(&self) -> bool {
        // SAFETY: forwarded from this function's own contract.
        unsafe { check_guard_seeded(self.ptr, self.size, self.guard_byte) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::guard::MEMORY_GUARD_SIZE;
    use crate::spomen::guard::write_guard;

    #[test]
    fn ordering_is_by_address() {
        let mut bytes = [0_u8; 4];
        let base = bytes.as_mut_ptr();
        let mk = |offset: usize| {
            // SAFETY: `offset < 4`, within `bytes`.
            let p = unsafe { base.add(offset) };
            Record::new(NonNull::new(p).expect("non-null"), 1, Source::Buckets, 0)
        };
        let (lo, hi) = (mk(0), mk(3));
        // SAFETY: both records are live locals.
        let ord = unsafe { Record::cmp(NonNull::from(&lo), NonNull::from(&hi)) };
        assert_eq!(ord, Ordering::Less);
        // SAFETY: `hi` is a live local.
        let vs_key = unsafe { Record::cmp_key(NonNull::from(&hi), &lo.ptr.as_ptr().addr()) };
        assert_eq!(vs_key, Ordering::Greater);
    }

    #[test]
    fn check_guard_uses_the_recorded_seed() {
        let requested = 10;
        let mut buf = vec![0_u8; requested + MEMORY_GUARD_SIZE];
        let ptr = NonNull::new(buf.as_mut_ptr()).expect("Vec's buffer is never null");
        // SAFETY: `buf` is `requested + MEMORY_GUARD_SIZE` bytes, exclusively owned.
        unsafe { write_guard(ptr, requested, 77) };
        let good = Record::new(ptr, requested, Source::Tree, 77);
        // SAFETY: `buf` is live, valid for `requested + MEMORY_GUARD_SIZE` bytes.
        assert!(unsafe { good.check_guard() });
        // Same (self-consistent) ramp, wrong remembered seed: must be rejected.
        let stale = Record::new(ptr, requested, Source::Tree, 78);
        // SAFETY: as above.
        assert!(!unsafe { stale.check_guard() });
    }
}
