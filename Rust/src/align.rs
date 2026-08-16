// SPDX-License-Identifier: MIT OR Apache-2.0
//! Alignment and rounding helpers shared by every allocator subsystem.
//!
//! Ports `Cpp/hpha.h`'s `round_up`/`round_down`/`align_up`/`align_down`. Every `align`
//! parameter here must be a power of two — callers are responsible for validating that
//! (the public API validates `Layout::align` before any of these are reached); a
//! non-power-of-two `align` is a caller bug, checked with `debug_assert!` rather than
//! propagated as a runtime error.

/// Rounds `value` down to the nearest multiple of `align` (`align` must be a power of two).
#[must_use]
pub(crate) const fn round_down(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    value & !(align - 1)
}

/// Rounds `value` up to the nearest multiple of `align` (`align` must be a power of two).
#[must_use]
pub(crate) const fn round_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + (align - 1)) & !(align - 1)
}

/// Rounds a pointer's address down to the nearest multiple of `align`, preserving provenance.
#[must_use]
pub(crate) fn align_down<T>(ptr: *mut T, align: usize) -> *mut T {
    // ALIGN: round the address down to `align`, matching HPHA's align_down.
    // PROVENANCE: map_addr preserves ptr's provenance; only the address changes.
    ptr.map_addr(|addr| round_down(addr, align))
}

/// Rounds a pointer's address up to the nearest multiple of `align`, preserving provenance.
#[must_use]
pub(crate) fn align_up<T>(ptr: *mut T, align: usize) -> *mut T {
    // ALIGN: round the address up to `align`, matching HPHA's align_up.
    // PROVENANCE: map_addr preserves ptr's provenance; only the address changes.
    ptr.map_addr(|addr| round_up(addr, align))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_down_multiple_is_identity() {
        assert_eq!(round_down(64, 64), 64);
        assert_eq!(round_down(128, 64), 128);
    }

    #[test]
    fn round_down_clears_low_bits() {
        assert_eq!(round_down(65, 64), 64);
        assert_eq!(round_down(1, 64), 0);
        assert_eq!(round_down(63, 8), 56);
    }

    #[test]
    fn round_up_multiple_is_identity() {
        assert_eq!(round_up(64, 64), 64);
        assert_eq!(round_up(0, 64), 0);
    }

    #[test]
    fn round_up_crosses_to_next_multiple() {
        assert_eq!(round_up(65, 64), 128);
        assert_eq!(round_up(1, 8), 8);
        assert_eq!(round_up(9, 8), 16);
    }

    #[test]
    fn align_down_up_pointer_roundtrip() {
        // A provenance-free probe address: align_down/align_up never dereference,
        // they only do address arithmetic, so this is a sound way to test the math
        // in isolation without a real allocation behind the pointer.
        let ptr = core::ptr::without_provenance_mut::<u8>(0x1_2345);
        let down = align_down(ptr, 0x1000);
        let up = align_up(ptr, 0x1000);
        assert_eq!(down.addr(), 0x1_2000);
        assert_eq!(up.addr(), 0x1_3000);
    }

    #[test]
    fn align_down_up_already_aligned() {
        let ptr = core::ptr::without_provenance_mut::<u8>(0x1_0000);
        assert_eq!(align_down(ptr, 0x1000).addr(), 0x1_0000);
        assert_eq!(align_up(ptr, 0x1000).addr(), 0x1_0000);
    }
}
