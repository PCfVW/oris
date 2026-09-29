// SPDX-License-Identifier: MIT OR Apache-2.0
//! Writing and checking the guard-byte ramp itself — `crate::guard` holds only the
//! always-compiled size arithmetic ([`crate::guard::MEMORY_GUARD_SIZE`]/`inflate`/
//! `deflate`); this module holds the actual bytes, and so is `spomen`-gated like the
//! rest of the debug subsystem.
//!
//! Ports `Cpp/hpha.cpp:745-760`'s `debug_record::write_guard`/`check_guard` exactly:
//! [`crate::guard::MEMORY_GUARD_SIZE`] bytes trailing at `ptr + requested_size`, filled
//! with a random-seeded incrementing ramp (`seed, seed+1, ..., seed+15`, wrapping mod
//! 256) rather than a fixed pattern.

use crate::guard::MEMORY_GUARD_SIZE;
use core::ptr::NonNull;

// This whole module is `spomen`-gated (only compiled under the `debug-allocator`
// feature — see `lib.rs`'s `#[cfg(feature = "debug-allocator")] mod spomen;`), so
// `crate::guard::MEMORY_GUARD_SIZE`'s *other* definition (0, for a build without the
// feature) never coexists with this file: every function below can assume the ramp is
// really `MEMORY_GUARD_SIZE` (16) bytes, never 0. This assertion documents that
// assumption and would catch it going stale (e.g. a future feature/value change) at
// compile time rather than as a silent one-byte out-of-bounds read in `check_guard`.
const _: () = assert!(MEMORY_GUARD_SIZE > 0);

/// Writes the guard ramp trailing at `ptr + requested_size`: `seed`, then each
/// subsequent byte one more than the last (wrapping). Ports `write_guard`'s
/// `for (i = 0; i < MEMORY_GUARD_SIZE; i++) guard[i] = guardByte++`.
///
/// `seed` is a caller-supplied byte (this crate draws it from [`crate::rand`]'s
/// `VintageRand`, promoted to production so both ports write byte-identical ramps for
/// the same allocation sequence — see that module's doc) rather than this function
/// reading a global RNG itself, keeping it a pure, directly testable primitive.
///
/// # Safety
/// `ptr` must be valid for `requested_size + MEMORY_GUARD_SIZE` bytes, writable for at
/// least the trailing [`MEMORY_GUARD_SIZE`] of them, and exclusively owned for that
/// span (no other live reference into it).
pub(crate) unsafe fn write_guard(ptr: NonNull<u8>, requested_size: usize, seed: u8) {
    // SAFETY: `requested_size` is within `ptr`'s valid span (caller's contract); the
    // offset stays inside `ptr`'s own allocation, so its provenance is preserved for
    // the writes below.
    let guard = unsafe { ptr.as_ptr().add(requested_size) };
    let mut byte = seed;
    // EXPLICIT: `byte` (the running ramp value) is state a `for i in 0..N` loop over
    // `write` calls carries most plainly as a local `mut`, not via an iterator adapter
    // — this is HPHA's own `guardByte++` loop, ported directly.
    for i in 0..MEMORY_GUARD_SIZE {
        // SAFETY: `i < MEMORY_GUARD_SIZE`, so this stays within `ptr`'s valid span
        // (caller's contract: valid for `requested_size + MEMORY_GUARD_SIZE` bytes).
        let byte_ptr = unsafe { guard.add(i) };
        // SAFETY: `byte_ptr` is within `ptr`'s valid span (established above) and
        // writable for that span (caller's contract).
        unsafe { byte_ptr.write(byte) };
        byte = byte.wrapping_add(1);
    }
}

/// Checks that the guard ramp trailing at `ptr + requested_size` is still a valid
/// consecutive sequence — each byte one more than the last, wrapping, exactly the
/// shape [`write_guard`] produces.
///
/// This is a **self-consistency** check only: it does not (yet) compare against the
/// allocation's originally-recorded seed byte, which needs `spomen`'s allocation-record
/// store (a later phase of this work) to supply — without it, nothing else remembers
/// what the first byte was supposed to be. It still catches the overwhelming majority
/// of real overflow corruption: an overrun almost never happens to also land on a
/// perfectly incrementing 16-byte sequence starting from whatever the corrupted first
/// guard byte now reads as. `hpha.cpp`'s own `check_guard` early-exits on the first
/// mismatch; this does too.
///
/// # Safety
/// `ptr` must be valid for `requested_size + MEMORY_GUARD_SIZE` bytes, readable for at
/// least the trailing [`MEMORY_GUARD_SIZE`] of them.
// Not yet called from any real dispatch path — wiring it into `free`/`realloc`'s
// pre-reclaim check needs the allocation-record store (a later phase) to supply the
// true original size a live pointer's usable size can exceed; see this function's own
// doc. Exercised directly by this module's own tests until then.
#[allow(dead_code)]
#[must_use]
pub(crate) unsafe fn check_guard(ptr: NonNull<u8>, requested_size: usize) -> bool {
    // SAFETY: `requested_size` is within `ptr`'s valid span (caller's contract).
    let guard = unsafe { ptr.as_ptr().add(requested_size) };
    // SAFETY: `guard` (offset 0) is within `ptr`'s valid span (caller's contract: valid
    // for at least `MEMORY_GUARD_SIZE` trailing bytes, and this module's own
    // `MEMORY_GUARD_SIZE > 0` assertion above guarantees that span is non-empty).
    let mut prev = unsafe { guard.read() };
    // EXPLICIT: `prev` (the last-seen ramp byte) is loop state a `for i in
    // 1..MEMORY_GUARD_SIZE` walk over reads carries most plainly as a local `mut`, one
    // comparison per iteration — mirrors `check_guard`'s own `guardByte++` walk.
    for i in 1..MEMORY_GUARD_SIZE {
        // SAFETY: `i < MEMORY_GUARD_SIZE`, so this stays within `ptr`'s valid span
        // (caller's contract).
        let byte_ptr = unsafe { guard.add(i) };
        // SAFETY: `byte_ptr` is within `ptr`'s valid span (established above) and
        // readable for that span (caller's contract).
        let cur = unsafe { byte_ptr.read() };
        if cur != prev.wrapping_add(1) {
            return false;
        }
        prev = cur;
    }
    true
}

/// Checks that the guard ramp trailing at `ptr + requested_size` is *exactly* the one
/// [`write_guard`] wrote for `seed` — the strict form of [`check_guard`], possible only
/// once something remembers the seed (`spomen`'s allocation record does, see
/// `spomen::record`). Ports `debug_record::check_guard`, which compares every byte
/// against `mGuardByte++` and early-exits on the first mismatch.
///
/// # Safety
/// `ptr` must be valid for `requested_size + MEMORY_GUARD_SIZE` bytes, readable for at
/// least the trailing [`MEMORY_GUARD_SIZE`] of them.
#[must_use]
pub(crate) unsafe fn check_guard_seeded(ptr: NonNull<u8>, requested_size: usize, seed: u8) -> bool {
    // SAFETY: `requested_size` is within `ptr`'s valid span (caller's contract).
    let guard = unsafe { ptr.as_ptr().add(requested_size) };
    let mut expected = seed;
    // EXPLICIT: `expected` (the running ramp value) is loop state, mirroring HPHA's own
    // `guardByte++` walk in `check_guard`.
    for i in 0..MEMORY_GUARD_SIZE {
        // SAFETY: `i < MEMORY_GUARD_SIZE`, so this stays within `ptr`'s valid span
        // (caller's contract).
        let byte_ptr = unsafe { guard.add(i) };
        // SAFETY: `byte_ptr` is within `ptr`'s valid span (established above) and
        // readable for that span (caller's contract).
        let cur = unsafe { byte_ptr.read() };
        if cur != expected {
            return false;
        }
        expected = expected.wrapping_add(1);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{check_guard, check_guard_seeded, write_guard};
    use core::ptr::NonNull;

    /// A stack buffer big enough for any payload this module's tests use plus a full
    /// guard ramp, so these tests need no OS allocation at all — pure Miri-friendly
    /// pointer arithmetic over owned memory.
    fn buffer(size: usize) -> (Vec<u8>, NonNull<u8>) {
        let mut v = vec![0_u8; size];
        let ptr = NonNull::new(v.as_mut_ptr()).expect("Vec's own buffer is never null");
        (v, ptr)
    }

    #[test]
    fn round_trips_when_untouched() {
        let requested = 40;
        let (_buf, ptr) = buffer(requested + crate::guard::MEMORY_GUARD_SIZE);
        // SAFETY: `_buf` is `requested + MEMORY_GUARD_SIZE` bytes, exclusively owned
        // (freshly allocated, not yet aliased).
        unsafe { write_guard(ptr, requested, 0x42) };
        // SAFETY: same buffer, still exclusively owned, only read.
        let intact = unsafe { check_guard(ptr, requested) };
        assert!(intact);
    }

    #[test]
    fn detects_a_single_corrupted_byte_anywhere_in_the_ramp() {
        let requested = 8;
        let guard_size = crate::guard::MEMORY_GUARD_SIZE;
        for corrupt_at in 0..guard_size {
            let (mut buf, ptr) = buffer(requested + guard_size);
            // SAFETY: `buf` is `requested + MEMORY_GUARD_SIZE` bytes, exclusively owned.
            unsafe { write_guard(ptr, requested, 0x99) };
            // Flip one guard byte — guaranteed to break the ramp's `+1` invariant at
            // this position regardless of what value was there (a value and its
            // wrapped-increment are always distinct).
            // INDEX: `requested + corrupt_at < requested + guard_size == buf.len()`
            // (`corrupt_at` ranges over `0..guard_size`, this loop's own bound).
            #[allow(clippy::indexing_slicing)]
            {
                buf[requested + corrupt_at] = buf[requested + corrupt_at].wrapping_add(1);
            }
            // SAFETY: still exclusively owned, only read.
            let intact = unsafe { check_guard(ptr, requested) };
            assert!(
                !intact,
                "corruption at guard byte {corrupt_at} went undetected"
            );
        }
    }

    #[test]
    fn wraps_at_255_like_hpha_does() {
        let requested = 4;
        let (_buf, ptr) = buffer(requested + crate::guard::MEMORY_GUARD_SIZE);
        // Seed near the top of `u8`'s range so the ramp must wrap during the write —
        // `check_guard`'s `wrapping_add` must agree with `write_guard`'s.
        // SAFETY: `_buf` is `requested + MEMORY_GUARD_SIZE` bytes, exclusively owned.
        unsafe { write_guard(ptr, requested, 250) };
        // SAFETY: same buffer, still exclusively owned, only read.
        let intact = unsafe { check_guard(ptr, requested) };
        assert!(intact);
    }

    #[test]
    fn seeded_check_accepts_only_the_written_seed() {
        let requested = 12;
        let (_buf, ptr) = buffer(requested + crate::guard::MEMORY_GUARD_SIZE);
        // SAFETY: `_buf` is `requested + MEMORY_GUARD_SIZE` bytes, exclusively owned.
        unsafe { write_guard(ptr, requested, 250) };
        // SAFETY: same buffer, still exclusively owned, only read.
        assert!(unsafe { check_guard_seeded(ptr, requested, 250) });
        // A self-consistent ramp with the *wrong* seed is exactly what the unseeded
        // check cannot catch and this one must.
        // SAFETY: same buffer, only read.
        assert!(unsafe { check_guard(ptr, requested) });
        // SAFETY: same buffer, only read.
        assert!(!unsafe { check_guard_seeded(ptr, requested, 251) });
    }
}
