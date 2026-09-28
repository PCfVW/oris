// SPDX-License-Identifier: MIT OR Apache-2.0
//! Fixed constants for `DEBUG_ALLOCATOR`'s memory-guard bytes — deliberately always
//! compiled (unlike `spomen`, which the `debug-allocator` feature excludes entirely),
//! since `bucket.rs`/`tree.rs`/`orisnik.rs` must reference `MEMORY_GUARD_SIZE`
//! unconditionally for their size arithmetic to type-check in every configuration.
//! Ports `Cpp/hpha.h:936-942`'s `MEMORY_GUARD_SIZE` constant exactly, including its
//! value (16) and its being 0 outside a debug build.

/// Extra bytes reserved after every allocation's payload to detect a write past the end
/// of the block. `16` when the `debug-allocator` feature is enabled, `0` otherwise —
/// every `+ MEMORY_GUARD_SIZE` / `- MEMORY_GUARD_SIZE` site in `bucket.rs`/`tree.rs`/
/// `orisnik.rs`, and any loop bounded by this constant, becomes dead code the compiler
/// removes when it is 0, restoring v0.1.x's exact guard-free behaviour. Mirrors HPHA's
/// own `MEMORY_GUARD_SIZE` (`Cpp/hpha.h:936-942`).
// Not yet consumed — `bucket.rs`/`tree.rs`/`orisnik.rs` start reading this constant in
// the next phase of the debug-allocator work (guard-byte reservation). Defining it now,
// ahead of its consumers, lets that phase land as a pure "thread the existing constant
// through" diff instead of introducing the constant and its consumers together.
#[allow(dead_code)]
#[cfg(feature = "debug-allocator")]
pub(crate) const MEMORY_GUARD_SIZE: usize = 16;

/// See `MEMORY_GUARD_SIZE`'s `debug-allocator`-enabled doc above (this crate never
/// compiles both definitions at once).
#[allow(dead_code)]
#[cfg(not(feature = "debug-allocator"))]
pub(crate) const MEMORY_GUARD_SIZE: usize = 0;

#[cfg(test)]
mod tests {
    use super::MEMORY_GUARD_SIZE;

    #[test]
    fn matches_hpha_when_enabled_and_is_zero_otherwise() {
        #[cfg(feature = "debug-allocator")]
        assert_eq!(MEMORY_GUARD_SIZE, 16);
        #[cfg(not(feature = "debug-allocator"))]
        assert_eq!(MEMORY_GUARD_SIZE, 0);
    }
}
