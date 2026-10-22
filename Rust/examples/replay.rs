// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replays a trace file on a fresh `Orisnik` and prints its transition record on stdout.
//!
//! ```text
//! cargo run --example replay --features trace -- ../examples/traces/handwritten/realloc-branches.trace
//! ```
//!
//! The Rust leg of the cross-port trace gate: `orisnitsa`'s `zig build replay -- <file>` and
//! the HPHA oracle's `trace_replay.exe <file>` print the same record for the same trace,
//! byte for byte, and CI diffs all three against the committed `.record` file. See
//! `docs/traces.md` and `examples/traces/GRAMMAR.md` in the repository.

use std::io::Write;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(path), None) = (args.next(), args.next()) else {
        eprintln!("usage: replay <trace-file>");
        return ExitCode::from(2);
    };
    // Read as bytes and decode leniently: a comment may hold anything (GRAMMAR.md §1.5), and the
    // Zig and C++ replayers read raw bytes too; an operation line is ASCII or a syntax error.
    let trace = match std::fs::read(&path) {
        Ok(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
        Err(error) => {
            eprintln!("replay: failed to read {path}: {error}");
            return ExitCode::from(2);
        }
    };
    let mut record = String::new();
    if let Err(error) = orisnik::letopis::replay(&trace, &mut record) {
        eprintln!("replay: {path}: {error}");
        return ExitCode::FAILURE;
    }
    // `print!` would translate nothing, but writing the bytes directly states the intent:
    // the record is compared byte for byte, LF line endings on every OS.
    let mut stdout = std::io::stdout().lock();
    if let Err(error) = stdout
        .write_all(record.as_bytes())
        .and_then(|()| stdout.flush())
    {
        eprintln!("replay: failed to write the record: {error}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
