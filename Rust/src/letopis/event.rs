// SPDX-License-Identifier: MIT OR Apache-2.0
//! The transition events the allocator's hooks emit, and the slot they are emitted into.
//!
//! An [`Event`] carries raw addresses: the hooks know nothing about normalization, which
//! is the replayer's job (`record.rs`). Every address is taken with `.addr()` — read for
//! its value only, never turned back into a pointer — so the hooks create and consume no
//! provenance.
//!
//! # How events reach the replayer
//! [`Buckets`](crate::bucket::Buckets) and [`Tree`](crate::tree::Tree) each own a
//! [`Tap`]: a `Cell` holding either nothing (the default; every emission is a no-op) or a
//! pointer to an [`EventLog`]. Only [`Orisnik::with_letopis`](crate::Orisnik) installs
//! one, for the duration of a closure, on an instance the replayer owns; the borrow of
//! the log outlives the installation by construction. The log appends to a `Vec`, which
//! allocates through the *global* allocator — never through the traced instance itself,
//! since the replayer only ever traces a local instance, not a `#[global_allocator]`.

use crate::rbtree::{EraseKind, InsertKind};
use core::cell::{Cell, RefCell};
use core::ptr::NonNull;

/// Which sub-allocator mapped memory: the `b`/`t` of a record's `map` event.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum MapKind {
    /// A bucket page (`Buckets::system_alloc`).
    Bucket,
    /// A tree arena (`Tree::system_alloc`).
    Tree,
}

/// One state transition, as the allocator performed it. Each variant is one event line of
/// the transition record (`examples/traces/GRAMMAR.md` §2.3); `examples/traces/EVENTS.md`
/// lists where each is emitted.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Event {
    /// Memory was mapped from the OS.
    Map {
        /// Which path mapped it.
        kind: MapKind,
        /// The mapping's base address.
        base: usize,
        /// Its length in bytes.
        bytes: usize,
    },
    /// A mapping was returned to the OS.
    Unmap {
        /// The mapping's base address.
        base: usize,
        /// Its length in bytes.
        bytes: usize,
    },
    /// A fresh page entered bucket `bucket`'s page list (`page+`).
    PageSpawn {
        /// The bucket index.
        bucket: usize,
        /// Any address inside the page (its `Page` footer).
        page: usize,
    },
    /// An empty page left bucket `bucket`'s page list (`page-`).
    PageRelease {
        /// The bucket index.
        bucket: usize,
        /// Any address inside the page.
        page: usize,
    },
    /// A page became full and moved to the back of its list (`page-full`).
    PageFull {
        /// The bucket index.
        bucket: usize,
        /// Any address inside the page.
        page: usize,
    },
    /// A full page got a slot back and moved to the front of its list (`page-refill`).
    PageRefill {
        /// The bucket index.
        bucket: usize,
        /// Any address inside the page.
        page: usize,
    },
    /// The block at `block` was cut to `size` payload bytes (`split`).
    Split {
        /// The block header's address.
        block: usize,
        /// The payload size the block keeps.
        size: usize,
    },
    /// The block at `block` moved `offset` bytes forward (`shift`).
    Shift {
        /// The block header's address before the move.
        block: usize,
        /// How far it moved.
        offset: usize,
    },
    /// The block at `block` was absorbed into its physical predecessor (`merge`).
    Merge {
        /// The absorbed block's header address.
        block: usize,
    },
    /// A free block entered the red-black tree (`tree+`).
    TreeInsert {
        /// The block header's address.
        block: usize,
        /// The block's payload size.
        size: usize,
        /// Which `do_insert` branch placed it.
        kind: InsertKind,
        /// Rotations the insertion cost.
        rotations: u32,
    },
    /// A free block left the red-black tree (`tree-`).
    TreeErase {
        /// The block header's address.
        block: usize,
        /// The block's payload size.
        size: usize,
        /// Which `do_erase` branch removed it.
        kind: EraseKind,
        /// Rotations the removal cost.
        rotations: u32,
    },
    /// A free block entered the small free list (`list+`).
    ListPush {
        /// The block header's address.
        block: usize,
        /// The block's payload size.
        size: usize,
    },
    /// A free block left the small free list (`list-`).
    ListErase {
        /// The block header's address.
        block: usize,
        /// The block's payload size.
        size: usize,
    },
    /// The most-recently-freed cache now holds `block` (or nothing) (`mr`).
    Mr {
        /// The cached block's header address, if any.
        block: Option<usize>,
    },
}

/// The events one traced instance has emitted, in order.
#[derive(Default)]
pub(crate) struct EventLog {
    /// Appended by [`Tap::emit`], drained by the replayer after each operation.
    events: RefCell<Vec<Event>>,
}

impl EventLog {
    /// An empty log.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Takes every event emitted since the last call, oldest first.
    #[must_use]
    pub(crate) fn drain(&self) -> Vec<Event> {
        self.events.take()
    }
}

/// Where a sub-allocator emits its events: empty by default, pointed at an [`EventLog`]
/// only while [`Orisnik::with_letopis`](crate::Orisnik) runs.
pub(crate) struct Tap(Cell<Option<NonNull<EventLog>>>);

impl Tap {
    /// An empty tap: every emission is dropped.
    #[must_use]
    pub(crate) const fn new() -> Self {
        Self(Cell::new(None))
    }

    /// Points this tap at `log`, or empties it.
    pub(crate) fn set(&self, log: Option<NonNull<EventLog>>) {
        self.0.set(log);
    }

    /// Appends `event` to the installed log, if any.
    pub(crate) fn emit(&self, event: Event) {
        if let Some(log) = self.0.get() {
            // SAFETY: a log is installed only by `Orisnik::with_letopis`, which borrows it
            // for longer than the installation lasts and uninstalls it before returning
            // (even on unwind), so `log` is live here. The shared reference is short-lived
            // and every write goes through the `RefCell`.
            let log = unsafe { log.as_ref() };
            log.events.borrow_mut().push(event);
        }
    }
}
