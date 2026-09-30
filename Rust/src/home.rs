// SPDX-License-Identifier: MIT OR Apache-2.0
//! The address a self-referential owner first mapped memory at, kept so `Drop` can tell
//! that it has been moved since.
//!
//! Every container here is bound to its own address (see `list.rs`'s module doc): its
//! sentinels are lazily self-linked at first use and never re-pointed. A value that was
//! *used, then moved, then dropped* therefore holds sentinels that name the old address,
//! and a teardown that chases them never reaches its own sentinel — in a release build,
//! where the `debug_assert!` tripwire is compiled out, that is an infinite loop (before
//! `Drop` existed such a value merely leaked).
//!
//! [`Home`] is the release-build answer: latched on the **cold** path only (whenever an
//! owner maps memory, an OS call anyway), so the hot alloc/free paths pay nothing, and
//! consulted only by `Drop`, which leaks instead of walking when the address changed.
//! "Never mapped anything" has nothing to walk and nothing to leak, so it is never a move.

use core::cell::Cell;

/// A latched address; `0` means "not yet latched".
pub(crate) struct Home(Cell<usize>);

impl Home {
    /// A latch that has recorded nothing yet.
    pub(crate) const fn new() -> Self {
        Self(Cell::new(0))
    }

    /// Records `owner`'s address the first time it is called; later calls are no-ops.
    pub(crate) fn latch<T>(&self, owner: &T) {
        if self.0.get() == 0 {
            // PROVENANCE: the address is stored for its bit pattern only, to compare against
            // a later one — never turned back into a pointer.
            self.0.set(core::ptr::from_ref(owner).addr());
        }
    }

    /// Whether `owner` is still where it was when [`Home::latch`] ran (or nothing was ever
    /// latched, in which case there is nothing that could be stale).
    #[must_use]
    pub(crate) fn holds<T>(&self, owner: &T) -> bool {
        let latched = self.0.get();
        latched == 0 || latched == core::ptr::from_ref(owner).addr()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unlatched_home_holds_anywhere() {
        let home = Home::new();
        let (a, b) = (0u8, 0u8);
        assert!(home.holds(&a) && home.holds(&b));
    }

    #[test]
    fn a_latched_home_holds_only_at_its_own_address() {
        let home = Home::new();
        let (a, b) = (0u8, 0u8);
        home.latch(&a);
        assert!(home.holds(&a));
        assert!(!home.holds(&b));
        home.latch(&b); // the first latch wins
        assert!(home.holds(&a));
        assert!(!home.holds(&b));
    }
}
