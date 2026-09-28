// SPDX-License-Identifier: MIT OR Apache-2.0
//! The Microsoft C runtime's `rand()`, reproduced exactly.
//!
//! `holdrand = holdrand * 214013 + 2531011; return (holdrand >> 16) & 0x7fff`. Taken
//! from Eric Jacopin's "Vintage RNGs" chapter (*Game AI Pro 3*), and verified against
//! the real CRT before being relied on: 200 000 draws after each of `srand(0)`,
//! `srand(1)`, `srand(42)`, `srand(1234)` and `srand(0xFFFF_FFFF)` are bit-identical to
//! `rand()` as linked on Windows (golden vectors pinned in `orisnik.rs`'s own test
//! module, where this generator first shipped as a test-only stress-workload helper).
//!
//! Promoted to production for `spomen`'s guard-byte ramp: HPHA seeds each allocation's
//! guard byte from `rand()` (`hpha.cpp:745-751`, `write_guard`), and this crate wants
//! that content cross-port-identical rather than merely per-port-plausible —
//! `orisnitsa` carries the identical generator (`Zig/src/rand.zig`), so both ports see
//! one stream for the same seed. Why this generator and not an arbitrary one: it is
//! also what Dimitar Lazarov's own `main.cpp` benchmark drives HPHA with
//! (`srand(1234)`), so the stress workload in `orisnik.rs`'s tests and `spomen`'s guard
//! bytes both trace back to the same, real, historically-grounded source.

/// One instance of the CRT's `rand()` state (`holdrand`). `Copy`/`Clone` so a caller
/// holding it in a `Cell` (e.g. [`crate::orisnik::Orisnik`]'s guard-byte seed stream)
/// can read-advance-store it through a shared reference without an extra indirection.
#[derive(Clone, Copy)]
pub(crate) struct VintageRand(u32);

impl VintageRand {
    pub(crate) const fn new(seed: u32) -> Self {
        Self(seed)
    }

    /// One `rand()` draw: `0..=0x7fff`.
    pub(crate) fn next(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(214_013).wrapping_add(2_531_011);
        (self.0 >> 16) & 0x7fff
    }
}

#[cfg(test)]
mod tests {
    use super::VintageRand;

    #[test]
    fn matches_the_microsoft_crt() {
        // Golden vector: the first draws of `random values from rand.txt` in the
        // Vintage RNGs corpus, produced by the real CRT after `srand(0)`.
        let mut r = VintageRand::new(0);
        for &expected in &[38_u32, 7719, 21238, 2437, 8855, 11797, 8365, 32285, 10450] {
            assert_eq!(r.next(), expected);
        }
        // And the seed Lazarov's own `main.cpp` uses.
        let mut r = VintageRand::new(1234);
        for &expected in &[4068_u32, 213, 12761, 8758, 23056, 7717, 15274, 24508] {
            assert_eq!(r.next(), expected);
        }
    }
}
