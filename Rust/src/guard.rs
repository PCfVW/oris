// SPDX-License-Identifier: MIT OR Apache-2.0
//! Fixed constants and size-arithmetic helpers for `DEBUG_ALLOCATOR`'s memory-guard
//! bytes — deliberately always compiled (unlike `spomen`, which the `debug-allocator`
//! feature excludes entirely), since `bucket.rs`/`tree.rs`/`orisnik.rs` must reference
//! `MEMORY_GUARD_SIZE` unconditionally for their size arithmetic to type-check in every
//! configuration. Ports `Cpp/hpha.h:936-942`'s `MEMORY_GUARD_SIZE` constant exactly,
//! including its value (16) and its being 0 outside a debug build.
//!
//! The guard *bytes themselves* — writing and checking the ramp — are `spomen`'s job
//! (`spomen::guard`), not this module's: this module only holds the size arithmetic
//! every allocation path needs regardless of whether guard bytes are ever actually
//! written, matching HPHA's own `MEMORY_GUARD_SIZE`-only (no `write_guard` stub)
//! presence in the non-debug build.

/// Extra bytes reserved after every allocation's payload to detect a write past the end
/// of the block. `16` when the `debug-allocator` feature is enabled, `0` otherwise —
/// every `+ MEMORY_GUARD_SIZE` / `- MEMORY_GUARD_SIZE` site in `bucket.rs`/`tree.rs`/
/// `orisnik.rs`, and any loop bounded by this constant, becomes dead code the compiler
/// removes when it is 0, restoring v0.1.x's exact guard-free behaviour. Mirrors HPHA's
/// own `MEMORY_GUARD_SIZE` (`Cpp/hpha.h:936-942`).
#[cfg(feature = "debug-allocator")]
pub(crate) const MEMORY_GUARD_SIZE: usize = 16;

/// See `MEMORY_GUARD_SIZE`'s `debug-allocator`-enabled doc above (this crate never
/// compiles both definitions at once).
#[cfg(not(feature = "debug-allocator"))]
pub(crate) const MEMORY_GUARD_SIZE: usize = 0;

/// The size to actually request from the bucket/tree allocator for a caller's
/// `requested` bytes, once guard-byte reservation is folded in — ports the
/// `size + MEMORY_GUARD_SIZE` HPHA computes inline at every `alloc`/`realloc`/`resize`
/// call site (`Cpp/hpha.h:1266-1440`). Identity when the `debug-allocator` feature is
/// off: the `if MEMORY_GUARD_SIZE == 0` branch below is `const`-evaluable, so the
/// checked addition is never even emitted, not merely folded away — matching this
/// crate's zero-cost-when-disabled requirement more strongly than relying on the
/// optimizer to prove `x + 0` never overflows.
///
/// `None` on overflow — an already-unserviceable request (within [`MEMORY_GUARD_SIZE`]
/// of `usize::MAX`) declined a few bytes earlier than [`crate::tree::MAX_ALLOCATION`]
/// alone would, the same "no real input changes" reasoning that bound's own doc gives.
#[must_use]
pub(crate) const fn inflate(requested: usize) -> Option<usize> {
    if MEMORY_GUARD_SIZE == 0 {
        Some(requested)
    } else {
        requested.checked_add(MEMORY_GUARD_SIZE)
    }
}

/// The reverse of [`inflate`]: recovers the caller-visible size from a real,
/// guard-inflated block/slot size. Identity when the feature is off.
///
/// `real` must be at least [`MEMORY_GUARD_SIZE`] — true of every block/slot size this
/// crate ever reports, since every one of them passed through [`inflate`] on the way
/// in (`debug_assert!`, not a public contract: this is an internal arithmetic inverse,
/// not a caller-facing precondition).
#[must_use]
pub(crate) const fn deflate(real: usize) -> usize {
    // Vacuously true (`MEMORY_GUARD_SIZE == 0`, `usize`'s own minimum) without the
    // feature — clippy's `absurd_extreme_comparisons` correctly flags asserting that
    // unconditionally, so the check only exists where it can actually catch something.
    #[cfg(feature = "debug-allocator")]
    debug_assert!(real >= MEMORY_GUARD_SIZE);
    real - MEMORY_GUARD_SIZE
}

#[cfg(test)]
mod tests {
    use super::{MEMORY_GUARD_SIZE, deflate, inflate};

    #[test]
    fn matches_hpha_when_enabled_and_is_zero_otherwise() {
        #[cfg(feature = "debug-allocator")]
        assert_eq!(MEMORY_GUARD_SIZE, 16);
        #[cfg(not(feature = "debug-allocator"))]
        assert_eq!(MEMORY_GUARD_SIZE, 0);
    }

    #[test]
    fn inflate_and_deflate_round_trip() {
        for size in [0_usize, 1, 64, 4096, usize::MAX / 2] {
            assert_eq!(deflate(inflate(size).expect("not near usize::MAX")), size);
        }
    }

    #[test]
    fn inflate_declines_only_within_guard_size_of_the_maximum() {
        // Exactly at the maximum: overflows unless there is nothing to add.
        assert_eq!(inflate(usize::MAX).is_some(), MEMORY_GUARD_SIZE == 0);
        // One `MEMORY_GUARD_SIZE` below it: always fits, by construction.
        assert_eq!(inflate(usize::MAX - MEMORY_GUARD_SIZE), Some(usize::MAX));
    }
}
