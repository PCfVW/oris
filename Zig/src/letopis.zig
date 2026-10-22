// SPDX-License-Identifier: MIT OR Apache-2.0
//! `letopis` (*летопис*, "chronicle"): traces and transition records — the machinery that
//! checks the cross-port invariant instead of arguing it. Ports `orisnik`'s `letopis`
//! module; `root.zig` exports this namespace as `orisnitsa.letopis`.
//!
//! A **trace** is a language-agnostic allocation sequence; a **transition record** is what
//! one allocator did in response, event by event, with every address normalized away. Two
//! implementations satisfy the invariant on a trace exactly when their records are
//! byte-identical. Both formats are specified in `examples/traces/GRAMMAR.md` in the
//! repository; `docs/traces.md` is the user guide.
//!
//! - `replay` runs a trace on a fresh `OrisnitsaWith(.{ .trace = true })` and writes its
//!   record.
//! - `Recorder(config)` wraps an `OrisnitsaWith(config)` instance and writes the calls made through it
//!   as a trace; its `allocator()` makes it a `std.mem.Allocator`.
//!
//! The hooks exist only in an instantiation with `Config.trace` set; in every other one
//! they are eliminated at compile time, so the shipped allocator is unchanged. **This API
//! is unstable until 1.0**: the record format may grow events as the invariant is
//! tightened.

const letopis_trace = @import("letopis_trace.zig");
const letopis_replay = @import("letopis_replay.zig");
const letopis_recorder = @import("letopis_recorder.zig");

pub const replay = letopis_replay.replay;
pub const Recorder = letopis_recorder.Recorder;
pub const Error = letopis_trace.Error;
pub const Diagnostic = letopis_trace.Diagnostic;

test {
    @import("std").testing.refAllDecls(@This());
    _ = @import("letopis_tests.zig");
}
