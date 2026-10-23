// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replays an Oris trace (`examples/traces/GRAMMAR.md`) through one allocator and reports
//! one measurement pass as JSON lines on stdout. See `benchmarks/methodology.md`.
//!
//! ```text
//! bench-rust --allocator orisnik --trace ../../traces/planner-1m.trace --pass wall
//! ```
//!
//! Allocators: `orisnik`, `system`, and — when built with their features — `mimalloc`,
//! `jemalloc` (not on MSVC) and `snmalloc`. Passes, each meant to run in its own process:
//!
//! - `wall`: `--warmup` untimed replays, then `--repetitions` timed ones (one record each).
//! - `latency`: `--warmup` untimed replays, then one replay timing every operation.
//! - `memory`: one replay (no warmup) sampling the resident set every 256 operations.
//! - `breakdown` (diagnosis): as `latency`, but every operation's time is filed under its kind
//!   and path (`alloc small`, `realloc small->large`, `free large`, `purge`, ...), with count,
//!   total and percentiles per category — where the wall time goes.
//!
//! `--no-purge` turns the trace's `purge` operations into no-ops for every allocator (they
//! already are for all but `orisnik`): the ablation that isolates what purging costs.
//!
//! The trace is parsed before anything is measured. One allocator instance serves every
//! replay of the process; between replays whatever the trace left live is freed, untimed.
//! Every allocation has one byte written per 4 KiB page, as a program would.

mod backend;
mod bump;
mod rss;
mod trace;

/// The harness's own allocations come from the OS directly, never from an allocator under
/// test (see `bump.rs`): the memory pass would otherwise measure the harness.
#[global_allocator]
static HARNESS: bump::Bump = bump::Bump::new();

use backend::Backend;
use std::process::ExitCode;
use std::time::Instant;
use trace::{Op, Trace};

struct Args {
    allocator: String,
    trace: String,
    pass: String,
    warmup: usize,
    repetitions: usize,
    env: serde_json::Value,
    /// Run the trace's `purge` operations (the default), or skip them (`--no-purge`).
    purge: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut args = Args {
        allocator: String::new(),
        trace: String::new(),
        pass: String::new(),
        warmup: 2,
        repetitions: 10,
        env: serde_json::Value::Null,
        purge: true,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let mut value = || it.next().ok_or_else(|| format!("{flag} needs a value"));
        match flag.as_str() {
            "--allocator" => args.allocator = value()?,
            "--trace" => args.trace = value()?,
            "--pass" => args.pass = value()?,
            "--warmup" => args.warmup = value()?.parse().map_err(|e| format!("--warmup: {e}"))?,
            "--repetitions" => {
                args.repetitions = value()?
                    .parse()
                    .map_err(|e| format!("--repetitions: {e}"))?;
            }
            "--env-file" => {
                let path = value()?;
                let text = std::fs::read_to_string(&path)
                    .map_err(|e| format!("failed to read {path}: {e}"))?;
                args.env = serde_json::from_str(&text).map_err(|e| format!("{path}: {e}"))?;
            }
            "--no-purge" => args.purge = false,
            "--list" => {
                println!("{}", backend::NAMES.join(" "));
                std::process::exit(0);
            }
            _ => return Err(format!("unknown argument `{flag}`")),
        }
    }
    if args.allocator.is_empty() || args.trace.is_empty() || args.pass.is_empty() {
        return Err("usage: bench-rust --allocator <name> --trace <file> --pass wall|latency|memory|breakdown [--warmup N] [--repetitions N] [--no-purge] [--env-file <json>]".into());
    }
    Ok(args)
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("bench-rust: {message}");
            return ExitCode::from(2);
        }
    };
    let trace = match trace::load(&args.trace) {
        Ok(trace) => trace,
        Err(message) => {
            eprintln!("bench-rust: {}: {message}", args.trace);
            return ExitCode::from(2);
        }
    };
    let Some(result) =
        backend::with_backend(&args.allocator, |backend| run(backend, &trace, &args))
    else {
        eprintln!(
            "bench-rust: unknown allocator `{}` (this build has: {})",
            args.allocator,
            backend::NAMES.join(", ")
        );
        return ExitCode::from(2);
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("bench-rust: {message}");
            ExitCode::FAILURE
        }
    }
}

/// The fields every record shares.
fn record(args: &Args, trace: &Trace, extra: serde_json::Value) -> serde_json::Value {
    let mut record = serde_json::json!({
        "schema_version": 1,
        "harness": "rust",
        "allocator": args.allocator,
        "trace": trace.name,
        "ops": trace.ops.len(),
        "pass": args.pass,
        "purge": args.purge,
        "env": args.env,
    });
    if let (Some(base), serde_json::Value::Object(fields)) = (record.as_object_mut(), extra) {
        base.extend(fields);
    }
    record
}

fn run(backend: &dyn Backend, trace: &Trace, args: &Args) -> Result<(), String> {
    let mut slots = vec![trace::Slot::default(); trace.slots];
    match args.pass.as_str() {
        "wall" => {
            for _ in 0..args.warmup {
                replay(backend, trace, &mut slots, args.purge, &mut Probe::None)?;
                release(backend, &mut slots);
            }
            for rep in 0..args.repetitions {
                let start = Instant::now();
                replay(backend, trace, &mut slots, args.purge, &mut Probe::None)?;
                let wall_ns = start.elapsed().as_nanos();
                release(backend, &mut slots);
                println!(
                    "{}",
                    record(
                        args,
                        trace,
                        serde_json::json!({ "rep": rep, "wall_ns": wall_ns })
                    )
                );
            }
        }
        "latency" => {
            for _ in 0..args.warmup {
                replay(backend, trace, &mut slots, args.purge, &mut Probe::None)?;
                release(backend, &mut slots);
            }
            let mut times = Vec::with_capacity(trace.ops.len());
            replay(
                backend,
                trace,
                &mut slots,
                args.purge,
                &mut Probe::Latency(&mut times),
            )?;
            release(backend, &mut slots);
            times.sort_unstable();
            let at = |q: f64| {
                let i = ((times.len() as f64 - 1.0) * q).round() as usize;
                times.get(i).copied().unwrap_or(0)
            };
            println!(
                "{}",
                record(
                    args,
                    trace,
                    serde_json::json!({
                        "p50_ns": at(0.5),
                        "p99_ns": at(0.99),
                        "p999_ns": at(0.999),
                        "max_ns": times.last().copied().unwrap_or(0),
                        "timer_overhead_ns": timer_overhead(),
                    })
                )
            );
        }
        "breakdown" => {
            for _ in 0..args.warmup {
                replay(backend, trace, &mut slots, args.purge, &mut Probe::None)?;
                release(backend, &mut slots);
            }
            let mut times: std::collections::BTreeMap<&'static str, Vec<u64>> =
                std::collections::BTreeMap::new();
            replay(
                backend,
                trace,
                &mut slots,
                args.purge,
                &mut Probe::Breakdown(&mut times),
            )?;
            release(backend, &mut slots);
            let mut categories = serde_json::Map::new();
            let mut total_ns = 0u64;
            for (name, mut t) in times {
                t.sort_unstable();
                let at = |q: f64| t[((t.len() as f64 - 1.0) * q).round() as usize];
                let sum: u64 = t.iter().sum();
                total_ns += sum;
                categories.insert(
                    name.to_owned(),
                    serde_json::json!({
                        "count": t.len(), "total_ns": sum, "p50_ns": at(0.5), "p99_ns": at(0.99),
                        "p999_ns": at(0.999), "max_ns": t[t.len() - 1],
                    }),
                );
            }
            println!(
                "{}",
                record(
                    args,
                    trace,
                    serde_json::json!({ "total_ns": total_ns, "categories": categories })
                )
            );
        }
        "memory" => {
            let baseline = rss::current();
            let mut sampler = Sampler {
                peak_rss: baseline,
                peak_mapped: backend.mapped().unwrap_or(0),
            };
            replay(
                backend,
                trace,
                &mut slots,
                args.purge,
                &mut Probe::Memory(&mut sampler),
            )?;
            let after = rss::current();
            sampler.peak_rss = sampler.peak_rss.max(after);
            let peak_live = trace.peak_live;
            let delta = sampler.peak_rss.saturating_sub(baseline);
            println!(
                "{}",
                record(
                    args,
                    trace,
                    serde_json::json!({
                        "baseline_rss_bytes": baseline,
                        "peak_rss_bytes": sampler.peak_rss,
                        "peak_rss_delta_bytes": delta,
                        "peak_live_bytes": peak_live,
                        "fragmentation": if peak_live == 0 { 0.0 } else { delta as f64 / peak_live as f64 },
                        "peak_mapped_bytes": backend.mapped().map(|_| sampler.peak_mapped),
                    })
                )
            );
            release(backend, &mut slots);
        }
        other => return Err(format!("unknown pass `{other}`")),
    }
    Ok(())
}

/// The median cost of one `Instant::now()` pair, subtracted by nobody but reported with
/// every latency record so a reader can judge the floor.
fn timer_overhead() -> u128 {
    let mut samples: Vec<u128> = (0..10_001)
        .map(|_| {
            let a = Instant::now();
            let b = Instant::now();
            (b - a).as_nanos()
        })
        .collect();
    samples.sort_unstable();
    samples[samples.len() / 2]
}

struct Sampler {
    peak_rss: u64,
    peak_mapped: u64,
}

enum Probe<'a> {
    None,
    Latency(&'a mut Vec<u64>),
    Memory(&'a mut Sampler),
    Breakdown(&'a mut std::collections::BTreeMap<&'static str, Vec<u64>>),
}

/// The category an operation's time is filed under in the `breakdown` pass: its kind and
/// path — `small` up to 256 bytes (the bucket path), `large` above — judged by the size
/// requested, or for a free/resize/size by the size the block has.
fn category(op: Op, slots: &[trace::Slot]) -> &'static str {
    let small = |size: usize| size <= 256;
    match op {
        Op::Alloc { size, align, .. } => match (small(size), align > 8) {
            (true, false) => "alloc small",
            (false, false) => "alloc large",
            (true, true) => "alloc_aligned small",
            (false, true) => "alloc_aligned large",
        },
        Op::Calloc { count, size, .. } => {
            if small(count * size) {
                "calloc small"
            } else {
                "calloc large"
            }
        }
        Op::Realloc { slot, size, .. } => {
            let old = slots[slot];
            match (old.ptr.is_null(), small(old.size), small(size)) {
                (true, _, true) => "realloc null->small",
                (true, _, false) => "realloc null->large",
                (false, true, true) => "realloc small->small",
                (false, true, false) => "realloc small->large",
                (false, false, true) => "realloc large->small",
                (false, false, false) => "realloc large->large",
            }
        }
        Op::Resize { slot, .. } => {
            if small(slots[slot].size) {
                "resize small"
            } else {
                "resize large"
            }
        }
        Op::Size { .. } => "size",
        Op::Free { slot, .. } => {
            if small(slots[slot].size) {
                "free small"
            } else {
                "free large"
            }
        }
        Op::Purge => "purge",
    }
}

/// One replay of `trace` through `backend`, with `slots` (one per handle) empty on entry.
fn replay(
    backend: &dyn Backend,
    trace: &Trace,
    slots: &mut [trace::Slot],
    purge: bool,
    probe: &mut Probe<'_>,
) -> Result<(), String> {
    for (i, op) in trace.ops.iter().enumerate() {
        if !purge && matches!(op, Op::Purge) {
            continue;
        }
        match probe {
            Probe::Breakdown(times) => {
                let name = category(*op, slots);
                let start = Instant::now();
                // SAFETY: the trace passed tracegen's constraints and `slots` mirrors it.
                unsafe { step(backend, *op, slots) };
                let ns = start.elapsed().as_nanos() as u64;
                times.entry(name).or_default().push(ns);
            }
            Probe::Latency(times) => {
                let start = Instant::now();
                // SAFETY: the trace passed tracegen's constraints and `slots` mirrors it.
                unsafe { step(backend, *op, slots) };
                times.push(start.elapsed().as_nanos() as u64);
            }
            Probe::Memory(sampler) => {
                // SAFETY: as above.
                unsafe { step(backend, *op, slots) };
                if i % 256 == 0 || matches!(op, Op::Purge) {
                    sampler.peak_rss = sampler.peak_rss.max(rss::current());
                    if let Some(mapped) = backend.mapped() {
                        sampler.peak_mapped = sampler.peak_mapped.max(mapped);
                    }
                }
            }
            Probe::None => {
                // SAFETY: as above.
                unsafe { step(backend, *op, slots) };
            }
        }
    }
    Ok(())
}

/// Writes one byte per 4 KiB page of a fresh block, as a program filling it would.
///
/// # Safety
/// `ptr` must be valid for `size` bytes.
unsafe fn touch(ptr: *mut u8, size: usize) {
    let mut offset = 0;
    while offset < size {
        // SAFETY: `offset < size`.
        unsafe { ptr.add(offset).write_volatile(1) };
        offset += 4096;
    }
}

/// # Safety
/// Each slot `op` reads must hold a live block of `backend` (or null).
unsafe fn step(backend: &dyn Backend, op: Op, slots: &mut [trace::Slot]) {
    use trace::Slot;
    // SAFETY (for every call below): forwarded from this function's contract.
    unsafe {
        match op {
            Op::Alloc { slot, size, align } => {
                let p = backend.alloc(size, align);
                if !p.is_null() {
                    touch(p, size);
                }
                slots[slot] = Slot {
                    ptr: p,
                    size,
                    align,
                };
            }
            Op::Calloc { slot, count, size } => {
                let p = backend.calloc(count, size);
                slots[slot] = Slot {
                    ptr: p,
                    size: count * size,
                    align: 0,
                };
            }
            Op::Realloc { slot, size, align } => {
                let old = slots[slot];
                let p = backend.realloc(old, size, align);
                if !p.is_null() && size > old.size {
                    touch(p.add(old.size), size - old.size);
                }
                if !p.is_null() || size == 0 {
                    slots[slot] = Slot {
                        ptr: p,
                        size,
                        align,
                    };
                }
            }
            Op::Resize { slot, size } => {
                let new_size = backend.resize(slots[slot], size);
                slots[slot].size = new_size;
            }
            Op::Size { slot } => {
                std::hint::black_box(backend.size(slots[slot]));
            }
            Op::Free { slot, sized } => {
                let s = std::mem::take(&mut slots[slot]);
                backend.free(s, sized);
            }
            Op::Purge => backend.purge(),
        }
    }
}

/// Frees whatever the replay left live (untimed), so the next replay starts the same way.
fn release(backend: &dyn Backend, slots: &mut [trace::Slot]) {
    for slot in slots.iter_mut() {
        let s = std::mem::take(slot);
        if !s.ptr.is_null() {
            // SAFETY: a non-null slot is a live block of `backend`.
            unsafe { backend.free(s, false) };
        }
    }
}
