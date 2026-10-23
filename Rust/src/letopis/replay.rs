// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replaying a trace on a fresh allocator and writing its transition record.

use super::ReplayError;
use super::event::EventLog;
use super::record::Normalizer;
use super::trace::{self, Op};
use crate::Orisnik;
use core::fmt;
use core::ptr::NonNull;
use std::collections::HashMap;

/// What one operation returned, as the record writes it.
enum Outcome {
    /// A pointer, or null.
    Pointer(Option<NonNull<u8>>),
    /// A size (`resize`, `size`).
    Size(usize),
    /// Nothing (`free*`, `purge`).
    Nothing,
}

/// Replays `trace` on a fresh [`Orisnik`] and writes its transition record to `out`.
///
/// The trace is parsed and checked in full first (`examples/traces/GRAMMAR.md` §1.3), so
/// nothing is executed unless every operation is defined. The record — one entry per
/// operation, its events, and the closing summary — is byte-identical to what `orisnitsa`
/// and the HPHA reference write for the same trace; that is the cross-port invariant,
/// checked in CI over the committed corpus.
///
/// Built with `debug-allocator` as well, the record differs from the reference's (the
/// guard reservation changes every size class); compare non-debug builds.
///
/// # Errors
/// [`ReplayError::Syntax`] or [`ReplayError::Semantic`] for a trace that is rejected
/// (nothing is executed then); [`ReplayError::Write`] if `out` fails;
/// [`ReplayError::Unmapped`] if the allocator reports memory it never mapped, which would
/// be a bug in this crate.
pub fn replay<W: fmt::Write>(trace: &str, out: &mut W) -> Result<(), ReplayError> {
    let lines = trace::parse(trace)?;
    let allocator = Orisnik::new();
    let log = EventLog::new();
    // Bound handles only: `None` is a handle bound to null.
    let mut handles: HashMap<u64, Option<NonNull<u8>>> = HashMap::new();
    let result = allocator.with_letopis(&log, || {
        out.write_str("oris-record 1\n")?;
        let mut norm = Normalizer::default();
        for (index, line) in lines.iter().enumerate() {
            // SAFETY: the trace passed every semantic constraint, so each handle an
            // operation reads is bound to a live allocation of `allocator` (or to null).
            let outcome = unsafe { execute(&allocator, line.op, &mut handles) };
            let events = log
                .drain()
                .into_iter()
                .map(|event| norm.event_line(event))
                .collect::<Result<Vec<_>, _>>()?;
            let result = match outcome {
                // PROVENANCE: an address read for its value only (a table key or a record location).
                Outcome::Pointer(Some(ptr)) => norm.location(ptr.addr().get())?,
                Outcome::Pointer(None) => "null".to_owned(),
                Outcome::Size(size) => size.to_string(),
                Outcome::Nothing => "-".to_owned(),
            };
            writeln!(
                out,
                "#{index} {} -> {result} a={}",
                line.op,
                allocator.allocated()
            )?;
            for event in events {
                writeln!(out, "  {event}")?;
            }
        }
        writeln!(
            out,
            "end ops={} maps={} unmaps={} rotations={} allocated={}",
            lines.len(),
            norm.maps,
            norm.unmaps,
            norm.rotations,
            allocator.allocated()
        )?;
        Ok(())
    });
    // Teardown is outside the record: free what the trace left live, so a build with
    // `debug-allocator` does not report a leak, then let `allocator` drop.
    for ptr in handles.into_values().flatten() {
        // SAFETY: every bound, non-null handle is a live allocation of `allocator`.
        unsafe { allocator.free(Some(ptr)) };
    }
    result
}

/// Runs one operation, updating the handle bindings exactly as `GRAMMAR.md` §1.2 says.
///
/// # Safety
/// Every handle `op` reads must be bound to a live allocation of `allocator`, or to null,
/// or (for `realloc`/`realloc_aligned` only) be unbound — what a trace that passed
/// [`trace::parse`] guarantees.
unsafe fn execute(
    allocator: &Orisnik,
    op: Op,
    handles: &mut HashMap<u64, Option<NonNull<u8>>>,
) -> Outcome {
    let pointer =
        |handles: &HashMap<u64, Option<NonNull<u8>>>, h| handles.get(&h).copied().flatten();
    // CAST: u64 -> usize; the crate is 64-bit only, so the conversion is lossless (sizes and
    // alignments are moreover bounded by constraints C3/C4; a calloc's count is not, but fits).
    #[allow(clippy::as_conversions, clippy::cast_possible_truncation)]
    let us = |v: u64| v as usize;
    match op {
        Op::Alloc { h, size } => bind(handles, h, allocator.alloc(us(size))),
        Op::AllocAligned { h, size, align } => {
            bind(handles, h, allocator.alloc_aligned(us(size), us(align)))
        }
        Op::Calloc { h, count, size } => bind(handles, h, allocator.calloc(us(count), us(size))),
        Op::Realloc { h, size } => {
            let old = pointer(handles, h);
            // SAFETY: `old` is a live allocation of `allocator`, or null (this function's
            // contract).
            let new = unsafe { allocator.realloc(old, us(size)) };
            rebind(handles, h, size, new)
        }
        Op::ReallocAligned { h, size, align } => {
            let old = pointer(handles, h);
            // SAFETY: as for `Realloc`.
            let new = unsafe { allocator.realloc_aligned(old, us(size), us(align)) };
            rebind(handles, h, size, new)
        }
        Op::Resize { h, size } => {
            // SAFETY: the handle is bound to a live allocation or null.
            Outcome::Size(unsafe { allocator.resize(pointer(handles, h), us(size)) })
        }
        Op::Size { h } => {
            // SAFETY: as for `Resize`.
            Outcome::Size(unsafe { allocator.size(pointer(handles, h)) })
        }
        Op::Free { h } => {
            let ptr = handles.remove(&h).flatten();
            // SAFETY: as for `Resize`; the handle is unbound from here on.
            unsafe { allocator.free(ptr) };
            Outcome::Nothing
        }
        Op::FreeSized { h, size } => {
            let ptr = handles.remove(&h).flatten();
            // SAFETY: as for `Free`; constraint C6 makes `size` the allocation's own size.
            unsafe { allocator.free_with_size(ptr, us(size)) };
            Outcome::Nothing
        }
        Op::FreeSizedAligned { h, size, align } => {
            let ptr = handles.remove(&h).flatten();
            // SAFETY: as for `Free`; constraint C7 makes `size`/`align` the allocation's own.
            unsafe { allocator.free_with_size_aligned(ptr, us(size), us(align)) };
            Outcome::Nothing
        }
        Op::Purge => {
            allocator.purge();
            Outcome::Nothing
        }
    }
}

fn bind(
    handles: &mut HashMap<u64, Option<NonNull<u8>>>,
    h: u64,
    ptr: Option<NonNull<u8>>,
) -> Outcome {
    handles.insert(h, ptr);
    Outcome::Pointer(ptr)
}

/// A realloc rebinds its handle to the result — except a failed one (null for a nonzero
/// size), which leaves the original block, and so the binding, in place.
fn rebind(
    handles: &mut HashMap<u64, Option<NonNull<u8>>>,
    h: u64,
    size: u64,
    new: Option<NonNull<u8>>,
) -> Outcome {
    if new.is_some() || size == 0 {
        handles.insert(h, new);
    } else {
        handles.entry(h).or_insert(None);
    }
    Outcome::Pointer(new)
}
