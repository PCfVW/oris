// SPDX-License-Identifier: MIT OR Apache-2.0
//! `letopis` (*летопис*, "chronicle"): traces and transition records — the machinery that
//! checks the cross-port invariant instead of arguing it.
//!
//! A **trace** is a language-agnostic allocation sequence; a **transition record** is what
//! one allocator did in response, event by event, with every address normalized away. Two
//! implementations satisfy the invariant on a trace exactly when their records are
//! byte-identical. Both formats are specified in `examples/traces/GRAMMAR.md` in the
//! repository; `docs/traces.md` is the user guide.
//!
//! - [`replay()`] runs a trace on a fresh [`Orisnik`](crate::Orisnik) and writes its record.
//! - [`Recorder`] wraps an [`Orisnik`](crate::Orisnik) and writes the calls made through it
//!   as a trace.
//!
//! Present only with the `trace` Cargo feature. Without it, every hook the allocator
//! carries is compiled out (`chronicle!` expands to nothing), so the shipped allocator is
//! unchanged — only the red-black tree's fixups always count their rotations, a local counter the compiler drops when nothing reads it. **This API is unstable until 1.0**: the record format may grow events as the
//! invariant is tightened.

mod event;
mod record;
mod recorder;
mod replay;
mod trace;

pub(crate) use event::{Event, EventLog, MapKind, Tap};
pub use recorder::Recorder;
pub use replay::replay;

use core::fmt;

/// Why [`replay()`] stopped.
#[derive(Debug)]
#[non_exhaustive]
pub enum ReplayError {
    /// The trace does not match the grammar (`GRAMMAR.md` §1.1). Nothing was executed.
    Syntax {
        /// The 1-based line of the first offending line.
        line: usize,
        /// What is wrong with it.
        message: String,
    },
    /// The trace breaks a semantic constraint (`GRAMMAR.md` §1.3) — it describes calls with
    /// no defined result. Nothing was executed.
    Semantic {
        /// The 1-based line of the first offending operation.
        line: usize,
        /// The rule (`C1`–`C8`) and what broke it.
        message: String,
    },
    /// The allocator reported an address outside every mapping it made — a bug in this
    /// crate's hooks, not in the trace.
    Unmapped {
        /// The address.
        address: usize,
    },
    /// Writing the record failed.
    Write(fmt::Error),
}

impl fmt::Display for ReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplayError::Syntax { line, message } => {
                write!(f, "syntax error (line {line}): {message}")
            }
            ReplayError::Semantic { line, message } => {
                write!(f, "trace rejected (line {line}): {message}")
            }
            ReplayError::Unmapped { address } => write!(
                f,
                "address {address:#x} outside every live mapping (a hook bug, not a trace error)"
            ),
            ReplayError::Write(error) => write!(f, "failed to write the record: {error}"),
        }
    }
}

impl std::error::Error for ReplayError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ReplayError::Write(error) => Some(error),
            ReplayError::Syntax { .. }
            | ReplayError::Semantic { .. }
            | ReplayError::Unmapped { .. } => None,
        }
    }
}

impl From<fmt::Error> for ReplayError {
    fn from(error: fmt::Error) -> Self {
        ReplayError::Write(error)
    }
}

#[cfg(test)]
mod tests;
