// SPDX-License-Identifier: MIT OR Apache-2.0
//! The error type of the debug subsystem's off-hot-path surface: `Orisnik::check`. The hot
//! path never returns it — an allocation failure is a value (`None`), and detected
//! corruption on `free`/`realloc`/`resize` panics (see [`crate::spomen::failure`]); this is
//! for a caller who asks the allocator to audit itself.

use core::fmt;

/// Why a debug-allocator diagnostic failed. Wording follows `Rust/CONVENTIONS.md`: lowercase,
/// no trailing period, the offending value included.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum OrisError {
    /// The operating system refused something (`failed to <verb>: <cause>`). Reserved: no
    /// diagnostic in this crate asks the OS for anything that can fail as a *result* yet
    /// (out of memory is a value, `None`, on the allocation paths), but the variant is part
    /// of the documented shape so adding such a diagnostic later is not a breaking change.
    Os(String),
    /// The heap was found corrupted: a guard overrun, or a record that disagrees with the
    /// block it describes.
    Corruption(String),
}

impl fmt::Display for OrisError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Os(message) | Self::Corruption(message) => formatter.write_str(message),
        }
    }
}

impl core::error::Error for OrisError {}

#[cfg(test)]
mod tests {
    use super::OrisError;

    #[test]
    fn displays_its_message_and_is_a_std_error() {
        let corruption = OrisError::Corruption("guard bytes overwritten (block 0x10)".to_owned());
        assert_eq!(
            corruption.to_string(),
            "guard bytes overwritten (block 0x10)"
        );
        let os = OrisError::Os("failed to map 65536 bytes: out of memory".to_owned());
        assert_eq!(os.to_string(), "failed to map 65536 bytes: out of memory");
        // It composes with `?` into a boxed `dyn Error`, the usual way callers consume it.
        // TRAIT_OBJECT: the point of the test is that `OrisError` converts into the
        // type-erased error most callers propagate with `?`.
        let boxed: Box<dyn core::error::Error> = Box::new(corruption.clone());
        assert_eq!(boxed.to_string(), corruption.to_string());
        assert_ne!(corruption, os);
    }
}
