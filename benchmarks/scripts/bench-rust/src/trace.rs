// SPDX-License-Identifier: MIT OR Apache-2.0
//! Loading a trace into a flat operation array, before anything is measured.
//!
//! The benchmarks replay `tracegen`'s traces, which are canonical and valid by construction
//! (tracegen replays each one through `orisnik` before writing it), so this reader is the
//! minimum: it maps every handle to a dense slot index and records, per operation, only
//! what a replay needs. It also computes the trace's peak live requested bytes, the
//! denominator of the fragmentation metric (`benchmarks/methodology.md`).

use std::collections::HashMap;

/// A live block, as the replay tracks it.
#[derive(Clone, Copy)]
pub struct Slot {
    pub ptr: *mut u8,
    /// The size the block was last requested (or resized) with.
    pub size: usize,
    /// The alignment it was requested with (0: the default).
    pub align: usize,
}

impl Default for Slot {
    fn default() -> Self {
        Self {
            ptr: std::ptr::null_mut(),
            size: 0,
            align: 0,
        }
    }
}

/// One operation, its handle resolved to a slot.
#[derive(Clone, Copy)]
pub enum Op {
    /// `alloc` (`align` 0) or `alloc_aligned`.
    Alloc {
        slot: usize,
        size: usize,
        align: usize,
    },
    Calloc {
        slot: usize,
        count: usize,
        size: usize,
    },
    /// `realloc` (`align` 0) or `realloc_aligned`.
    Realloc {
        slot: usize,
        size: usize,
        align: usize,
    },
    Resize {
        slot: usize,
        size: usize,
    },
    Size {
        slot: usize,
    },
    /// `free` (`sized` false), or `free_sized`/`free_sized_aligned` (the slot holds the size
    /// and alignment, which the trace repeats).
    Free {
        slot: usize,
        sized: bool,
    },
    Purge,
}

/// A loaded trace.
pub struct Trace {
    /// The file stem.
    pub name: String,
    pub ops: Vec<Op>,
    /// How many distinct handles (slots) it uses.
    pub slots: usize,
    /// The largest sum of requested sizes live at once.
    pub peak_live: u64,
}

pub fn load(path: &str) -> Result<Trace, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("failed to read: {e}"))?;
    let name = std::path::Path::new(path)
        .file_stem()
        .map_or_else(|| path.to_owned(), |s| s.to_string_lossy().into_owned());
    let mut lines = text.lines();
    if lines.next().map(str::trim) != Some("oris-trace 1") {
        return Err("missing header `oris-trace 1`".into());
    }
    let mut slot_of: HashMap<u64, usize> = HashMap::new();
    let mut ops = Vec::new();
    let mut live: Vec<u64> = Vec::new(); // requested size per slot
    let (mut live_now, mut peak_live) = (0u64, 0u64);
    for (number, line) in lines.enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let bad = || format!("line {}: cannot read `{line}`", number + 2);
        let mut tokens = line.split_ascii_whitespace();
        let keyword = tokens.next().ok_or_else(bad)?;
        if keyword == "purge" {
            ops.push(Op::Purge);
            continue;
        }
        let h: u64 = tokens
            .next()
            .and_then(|t| t.strip_prefix('h'))
            .and_then(|t| t.parse().ok())
            .ok_or_else(bad)?;
        let nums: Vec<usize> = tokens
            .map(|t| t.parse().map_err(|_| bad()))
            .collect::<Result<_, _>>()?;
        let next = slot_of.len();
        let slot = *slot_of.entry(h).or_insert(next);
        if slot == live.len() {
            live.push(0);
        }
        let arg = |i: usize| nums.get(i).copied().ok_or_else(bad);
        let mut set_live = |size: u64| {
            live_now = live_now - live[slot] + size;
            live[slot] = size;
            peak_live = peak_live.max(live_now);
        };
        let op = match keyword {
            "alloc" => Op::Alloc {
                slot,
                size: arg(0)?,
                align: 0,
            },
            "alloc_aligned" => Op::Alloc {
                slot,
                size: arg(0)?,
                align: arg(1)?,
            },
            "calloc" => Op::Calloc {
                slot,
                count: arg(0)?,
                size: arg(1)?,
            },
            "realloc" => Op::Realloc {
                slot,
                size: arg(0)?,
                align: 0,
            },
            "realloc_aligned" => Op::Realloc {
                slot,
                size: arg(0)?,
                align: arg(1)?,
            },
            "resize" => Op::Resize {
                slot,
                size: arg(0)?,
            },
            "size" => Op::Size { slot },
            "free" => Op::Free { slot, sized: false },
            "free_sized" | "free_sized_aligned" => Op::Free { slot, sized: true },
            _ => return Err(bad()),
        };
        match op {
            Op::Alloc { size, .. } | Op::Realloc { size, .. } => set_live(size as u64),
            Op::Calloc { count, size, .. } => set_live((count * size) as u64),
            Op::Free { .. } => set_live(0),
            Op::Resize { .. } | Op::Size { .. } | Op::Purge => {}
        }
        ops.push(op);
    }
    Ok(Trace {
        name,
        ops,
        slots: slot_of.len(),
        peak_live,
    })
}
