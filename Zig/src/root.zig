// SPDX-License-Identifier: MIT OR Apache-2.0
//! # orisnitsa
//!
//! The Zig port of Oris — a Rust and Zig port of Dimitar Lazarov's HPHA (2007).
//! See <https://github.com/PCfVW/oris>.
//!
//! **No implementation yet.** This stub establishes the `build.zig.zon`
//! manifest and a green `zig build test` baseline while the design documents
//! (`../BRIEF.md`, `../ROADMAP.md`) settle. The allocator itself — the bucket
//! and tree sub-allocators, the *orisnitsi* — lands in v0.1.0, in lockstep with
//! the `orisnik` Rust crate (same version, same internal state transitions).
const std = @import("std");

test "stub builds and tests run" {
    try std.testing.expect(true);
}
