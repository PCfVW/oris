// SPDX-License-Identifier: MIT OR Apache-2.0
//! What the debug hooks do when they detect corruption. Ports the `assert()`s in
//! `Cpp/hpha.cpp`'s `debug_record_map::remove`/`check` ("if this asserts most likely the
//! pointer was already deleted", "if this asserts then the memory was corrupted past the
//! end of the block", "make sure the free size matches the allocation size").
//!
//! Detection is a plain value ([`Corruption`], returned by the hooks' `verify` step so it
//! is directly testable); the *reaction* is the single [`fail`] function: it panics with
//! a message that names the block, what is wrong, and where the block was allocated.
//! This is `spomen`'s one deliberate exception to "the hot path never panics"
//! (`Rust/CONVENTIONS.md`): fail-fast is the whole point of a debug allocator, and it is
//! compiled only with the `debug-allocator` feature.
//!
//! # As a `#[global_allocator]`
//! Unwinding out of a global allocator is undefined behaviour, so an `Orisnik` built with
//! `debug-allocator` that is installed as the global allocator must be built with
//! `panic = "abort"` (then the panic aborts instead of unwinding). An owned instance —
//! the ordinary test/debug use — can keep the default `unwind` and observe the panic.

use crate::spomen::record::Record;
use core::ptr::NonNull;

/// What a debug hook found wrong with a pointer handed to `free`/`realloc`/`resize`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(clippy::exhaustive_enums)]
// EXHAUSTIVE: exactly the three failures HPHA's `debug_record_map` asserts on.
pub(crate) enum Corruption {
    /// No record exists for the pointer: it was never allocated by this allocator, or it
    /// was already freed (a double free).
    UnknownPointer,
    /// A sized free named a size other than the one recorded for the allocation.
    SizeMismatch {
        /// The size the caller supplied (as compared: after the minimum-size clamp).
        given: usize,
    },
    /// The trailing guard ramp no longer matches the seed recorded for the allocation:
    /// something wrote past the end of the block.
    GuardOverrun,
}

/// The diagnostic for `what`, following the house wording (`Rust/CONVENTIONS.md`:
/// lowercase, no trailing period, the offending value included). `record`, when the
/// pointer had one, adds where the block was allocated.
///
/// # Safety
/// `record`, if `Some`, must point to a live [`Record`].
pub(crate) unsafe fn describe(
    what: Corruption,
    ptr: NonNull<u8>,
    record: Option<NonNull<Record>>,
) -> String {
    // PROVENANCE: address read for its bit pattern only (it is printed), never turned back
    // into a pointer.
    let addr = ptr.as_ptr().addr();
    let head = match what {
        Corruption::UnknownPointer => format!(
            "pointer was not allocated by this allocator or was already freed (block {addr:#x})"
        ),
        Corruption::SizeMismatch { given } => {
            let recorded = record.map_or(0, |r| {
                // SAFETY: `r` is live (this function's contract); reads one field.
                unsafe { (*r.as_ptr()).size }
            });
            format!(
                "free size does not match allocation size (block {addr:#x}, allocated as \
                 {recorded} bytes, freed as {given})"
            )
        }
        Corruption::GuardOverrun => {
            let size = record.map_or(0, |r| {
                // SAFETY: `r` is live (this function's contract); reads one field.
                unsafe { (*r.as_ptr()).size }
            });
            format!(
                "guard bytes overwritten, memory was written past the end of the block \
                 (block {addr:#x}, requested {size} bytes)"
            )
        }
    };
    match record {
        Some(r) => {
            // SAFETY: `r` is live (this function's contract); only borrowed for the
            // duration of this `format!`.
            let trace = unsafe { &(*r.as_ptr()).callstack };
            match trace {
                Some(trace) => format!("{head}\nallocated at:\n{trace}"),
                None => format!(
                    "{head}\n(allocation callstack not recorded: this allocator is the \
                     global allocator)"
                ),
            }
        }
        None => head,
    }
}

/// Reacts to detected corruption: panics with `message`. `#[cold]`/`#[inline(never)]` so
/// the checks around it stay on the fast path's side of the code layout.
#[cold]
#[inline(never)]
// `clippy::panic` is denied crate-wide for the allocator hot path; this is the one
// reviewed exception (see the module doc), compiled only under `debug-allocator`.
#[allow(clippy::panic)]
pub(crate) fn fail(message: &str) -> ! {
    panic!("{message}");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spomen::record::Source;

    fn ptr(addr: usize) -> NonNull<u8> {
        // PROVENANCE: no allocation behind it; only its address is printed.
        NonNull::new(core::ptr::without_provenance_mut::<u8>(addr)).expect("non-zero address")
    }

    #[test]
    fn unknown_pointer_names_the_block_and_the_cause() {
        // SAFETY: `None` record: nothing to dereference.
        let msg = unsafe { describe(Corruption::UnknownPointer, ptr(0x1230), None) };
        assert!(msg.contains("already freed"), "{msg}");
        assert!(msg.contains("0x1230"), "{msg}");
    }

    #[test]
    fn record_backed_messages_carry_sizes_and_the_allocation_site() {
        let record = Record::new(ptr(0x4000), 40, Source::Tree, 7);
        let rec = NonNull::from(&record);
        // SAFETY: `rec` points to a live local.
        let overrun = unsafe { describe(Corruption::GuardOverrun, ptr(0x4000), Some(rec)) };
        assert!(overrun.contains("guard bytes overwritten"), "{overrun}");
        assert!(overrun.contains("requested 40 bytes"), "{overrun}");
        assert!(overrun.contains("allocated at:"), "{overrun}");
        // SAFETY: as above.
        let mismatch = unsafe {
            describe(
                Corruption::SizeMismatch { given: 64 },
                ptr(0x4000),
                Some(rec),
            )
        };
        assert!(
            mismatch.contains("allocated as 40 bytes, freed as 64"),
            "{mismatch}"
        );
    }

    #[test]
    #[should_panic(expected = "guard bytes overwritten")]
    fn fail_panics_with_the_message() {
        fail("guard bytes overwritten (test)");
    }
}
