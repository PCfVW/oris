// SPDX-License-Identifier: MIT OR Apache-2.0
//! Payload poisoning — filling a block's payload with a recognizable pattern on
//! allocation (catches reads of uninitialized memory) and on free (catches
//! use-after-free reads), so a bug reads *this*, not silently plausible-looking
//! leftover data.
//!
//! Ports `Cpp/hpha.cpp:762-767`'s `debug_record_map::initial_fill` exactly: a
//! repeating 4-byte pattern, `{0xFF, 0xC0, 0xC0, 0xFF}`, chosen (per HPHA's own
//! comment) because it reads as a quiet-NaN bit pattern in either endianness. This is
//! a **separate** mechanism from the guard ramp ([`crate::spomen::guard`]) — guard
//! bytes trail the payload to catch overflow, poisoning fills the payload itself.
//!
//! Wired into the tree/bucket `alloc`/`alloc_aligned` choke points (fill on success,
//! after the guard write — matching HPHA's `write_guard()`-then-`initial_fill()`
//! order inside `debug_record_map::add`) and into `free`/`free_with_size*` (fill
//! before the underlying reclaim — matching `debug_remove` running before
//! `bucket_free`/`tree_free` in `allocator::free`). Deliberately **not** wired into
//! `realloc`/`resize`: HPHA's own `update`/`replace` never poison, only `add`/`remove`
//! do (see `Cpp/hpha.cpp`'s `debug_record_map`, `update`/`replace` bodies).
//!
//! `calloc` composes with this for free: [`crate::orisnik::Orisnik::calloc`] calls
//! `alloc` (which poisons), then unconditionally zero-fills the exact same span —
//! the poison is immediately overwritten, exactly as it would be in HPHA (which
//! poisons inside `alloc` unconditionally too, with no `calloc`-specific bypass).

use core::ptr::NonNull;

/// The repeating fill pattern. Ports `debug_record_map::initial_fill`'s
/// `unsigned char sFiller[] = {0xFF,0xC0,0xC0,0xFF}`.
const PATTERN: [u8; 4] = [0xFF, 0xC0, 0xC0, 0xFF];

/// The pattern byte at position `i` of a [`fill`]ed span — the one place
/// [`PATTERN`] is actually indexed, so every caller (this module's own [`fill`],
/// plus tests elsewhere that check a poisoned payload) shares one provably-in-bounds
/// site instead of repeating the same `#[allow(clippy::indexing_slicing)]`.
#[must_use]
pub(crate) const fn byte_at(i: usize) -> u8 {
    // INDEX: `PATTERN.len() == 4`, and `i % 4 < 4` always.
    #[allow(clippy::indexing_slicing)]
    PATTERN[i % PATTERN.len()]
}

/// Fills `len` bytes starting at `ptr` with the repeating [`PATTERN`].
///
/// # Safety
/// `ptr` must be valid for `len` bytes, writable, and exclusively owned for that span
/// (no other live reference into it).
pub(crate) unsafe fn fill(ptr: NonNull<u8>, len: usize) {
    // EXPLICIT: a plain `for i in 0..len` loop over single-byte writes, not a
    // `chunks`/`copy_from_slice`-style bulk fill — `len` is not necessarily a
    // multiple of `PATTERN.len()`, and this is a direct, one-to-one port of HPHA's
    // own `for (s = 0; s < size; s++) p[s] = sFiller[s % 4];` loop, not a
    // functionally-equivalent rewrite.
    for i in 0..len {
        // SAFETY: `i < len`, so this stays within `ptr`'s valid span (caller's
        // contract).
        let byte_ptr = unsafe { ptr.as_ptr().add(i) };
        // SAFETY: `byte_ptr` is within `ptr`'s valid span (established above) and
        // writable for that span (caller's contract).
        unsafe { byte_ptr.write(byte_at(i)) };
    }
}

#[cfg(test)]
mod tests {
    use super::{PATTERN, byte_at, fill};
    use core::ptr::NonNull;

    #[test]
    fn fills_shorter_than_the_pattern() {
        let mut buf = [0_u8; 3];
        let ptr = NonNull::new(buf.as_mut_ptr()).expect("stack array is never null");
        // SAFETY: `buf` is 3 bytes, exclusively owned by this test.
        unsafe { fill(ptr, 3) };
        assert_eq!(buf, [PATTERN[0], PATTERN[1], PATTERN[2]]);
    }

    #[test]
    fn cycles_the_pattern_past_its_own_length() {
        let mut buf = [0_u8; 10];
        let ptr = NonNull::new(buf.as_mut_ptr()).expect("stack array is never null");
        // SAFETY: `buf` is 10 bytes, exclusively owned by this test.
        unsafe { fill(ptr, 10) };
        let expected: Vec<u8> = (0..10).map(byte_at).collect();
        assert_eq!(&buf, expected.as_slice());
    }

    #[test]
    fn zero_length_fill_touches_nothing() {
        let mut buf = [0xAB_u8; 4];
        let ptr = NonNull::new(buf.as_mut_ptr()).expect("stack array is never null");
        // SAFETY: `len == 0`, so this is a no-op regardless of `buf`'s real size.
        unsafe { fill(ptr, 0) };
        assert_eq!(buf, [0xAB; 4], "a zero-length fill must not write anything");
    }
}
