// SPDX-License-Identifier: MIT OR Apache-2.0
//! Writing and checking the guard-byte ramp itself — `guard.zig` holds only the
//! always-compiled size arithmetic (`memoryGuardSize`/`inflate`/`deflate`); this
//! module holds the actual bytes, and so is a sibling file the way `guard.zig`
//! already is with respect to `spomen.zig` — usable only for a `config.debug ==
//! true` instantiation, unlike `guard.zig`'s unconditionally-referenced arithmetic.
//!
//! Ports `Cpp/hpha.cpp:745-760`'s `debug_record::write_guard`/`check_guard`
//! exactly, mirroring `orisnik`'s `Rust/src/spomen/guard.rs`:
//! `guard.memoryGuardSize(config)` bytes trailing at `ptr + requested_size`, filled
//! with a random-seeded incrementing ramp (`seed, seed+1, ..., seed+15`, wrapping
//! mod 256) rather than a fixed pattern.

const std = @import("std");
const spomen = @import("spomen.zig");
const guard = @import("guard.zig");

const Config = spomen.Config;

/// Writes the guard ramp trailing at `ptr + requested_size`: `seed`, then each
/// subsequent byte one more than the last (wrapping). Ports `write_guard`'s
/// `for (i = 0; i < MEMORY_GUARD_SIZE; i++) guard[i] = guardByte++`.
///
/// `seed` is a caller-supplied byte (`orisnitsa.zig` draws it from `rand.zig`'s
/// `VintageRand`, promoted to production so both ports write byte-identical
/// ramps for the same allocation sequence — see that module's doc) rather than
/// this function reading a global RNG itself, keeping it a pure, directly
/// testable primitive.
///
/// `config.debug` must be true — the comptime assert below documents that this
/// instantiation only ever makes sense once the debug subsystem is actually
/// active, and would catch it going stale (e.g. a future `memoryGuardSize`
/// change) at compile time for whichever `config` this function actually gets
/// called with. Mirrors `orisnik`'s own `spomen::guard` module, whose
/// `const _: () = assert!(MEMORY_GUARD_SIZE > 0);` plays the identical role for
/// a single cfg-gated global constant — this port's `config` is a per-call
/// `comptime` parameter instead, so the assert is per-instantiation rather than
/// module-wide, but the property it guards is the same.
///
/// `ptr` must be valid for `requested_size + memoryGuardSize(config)` bytes,
/// writable for at least the trailing `memoryGuardSize(config)` of them, and
/// exclusively owned for that span (no other live reference into it).
pub fn writeGuard(comptime config: Config, ptr: [*]u8, requested_size: usize, seed: u8) void {
    const memory_guard_size = comptime guard.memoryGuardSize(config);
    comptime std.debug.assert(memory_guard_size > 0);
    var byte = seed;
    // EXPLICIT: `byte` (the running ramp value) is state a loop over writes
    // carries most plainly as a local `var`, not via an iterator/formatter
    // adapter — this is HPHA's own `guardByte++` loop, ported directly.
    for (0..memory_guard_size) |i| {
        // INDEX: `i < memory_guard_size`, and `ptr` is valid for
        // `requested_size + memory_guard_size` bytes (caller's contract), so
        // `requested_size + i` stays within that span.
        // SAFETY: the raw write below discharges this function's own contract —
        // `ptr` writable for that whole span and exclusively owned, so no other
        // live reference observes the guard byte being written.
        ptr[requested_size + i] = byte;
        byte +%= 1;
    }
}

/// Checks that the guard ramp trailing at `ptr + requested_size` is still a
/// valid consecutive sequence — each byte one more than the last, wrapping,
/// exactly the shape `writeGuard` produces.
///
/// This is a **self-consistency** check only: it does not (yet) compare against
/// the allocation's originally-recorded seed byte, which needs `spomen`'s
/// allocation-record store (a later phase of this work) to supply — without it,
/// nothing else remembers what the first byte was supposed to be. It still
/// catches the overwhelming majority of real overflow corruption: an overrun
/// almost never happens to also land on a perfectly incrementing 16-byte
/// sequence starting from whatever the corrupted first guard byte now reads as.
/// `hpha.cpp`'s own `check_guard` early-exits on the first mismatch; this does
/// too.
///
/// Not yet called from any real dispatch path — wiring it into `free`/
/// `realloc`'s pre-reclaim check needs the allocation-record store (a later
/// phase) to supply the true original size a live pointer's usable size can
/// exceed; see this function's own doc. Exercised directly by this module's own
/// tests (and, indirectly, by `orisnitsa.zig`'s Phase 2 integration tests) until
/// then.
///
/// `ptr` must be valid for `requested_size + memoryGuardSize(config)` bytes,
/// readable for at least the trailing `memoryGuardSize(config)` of them.
pub fn checkGuard(comptime config: Config, ptr: [*]u8, requested_size: usize) bool {
    const memory_guard_size = comptime guard.memoryGuardSize(config);
    comptime std.debug.assert(memory_guard_size > 0);
    // SAFETY: `ptr` is valid and readable for `requested_size +
    // memory_guard_size` bytes (this function's caller contract), so reading
    // the byte at `requested_size` stays within that span.
    // INDEX: offset 0 is within `ptr`'s valid span (caller's contract: valid
    // for at least `memory_guard_size` trailing bytes, and the comptime assert
    // above guarantees that span is non-empty).
    var prev = ptr[requested_size];
    // EXPLICIT: `prev` (the last-seen ramp byte) is loop state a walk over
    // reads carries most plainly as a local `var`, one comparison per
    // iteration — mirrors `check_guard`'s own `guardByte++` walk.
    for (1..memory_guard_size) |i| {
        // SAFETY: `ptr` is readable for `requested_size + memory_guard_size`
        // bytes (caller's contract), and `i < memory_guard_size`, so this read
        // stays within that span.
        // INDEX: `i < memory_guard_size` (caller's contract, as above).
        const cur = ptr[requested_size + i];
        if (cur != prev +% 1) return false;
        prev = cur;
    }
    return true;
}

/// Checks that the guard ramp trailing at `ptr + requested_size` is *exactly* the
/// one `writeGuard` wrote for `seed` — the strict form of `checkGuard`, possible only
/// once something remembers the seed (`spomen_record.zig`'s `Record` does). Ports
/// `debug_record::check_guard`, which compares every byte against `mGuardByte++` and
/// early-exits on the first mismatch. Mirrors `orisnik`'s `check_guard_seeded`.
///
/// `ptr` must be valid for `requested_size + memoryGuardSize(config)` bytes,
/// readable for at least the trailing `memoryGuardSize(config)` of them.
pub fn checkGuardSeeded(comptime config: Config, ptr: [*]const u8, requested_size: usize, seed: u8) bool {
    const memory_guard_size = comptime guard.memoryGuardSize(config);
    comptime std.debug.assert(memory_guard_size > 0);
    var expected = seed;
    // EXPLICIT: `expected` (the running ramp value) is loop state, mirroring HPHA's own
    // `guardByte++` walk in `check_guard`.
    for (0..memory_guard_size) |i| {
        // SAFETY: `ptr` is readable for `requested_size + memory_guard_size` bytes
        // (caller's contract), and `i < memory_guard_size`, so this read stays within
        // that span.
        // INDEX: `i < memory_guard_size` (caller's contract, as above).
        const cur = ptr[requested_size + i];
        if (cur != expected) return false;
        expected +%= 1;
    }
    return true;
}

const testing = std.testing;

// Every test below allocates its own scratch buffer through `testing.allocator`
// (leak-detected) rather than touching `os.zig` — `writeGuard`/`checkGuard`
// only ever do pointer arithmetic over a caller-supplied span, so no real
// allocator page is needed to exercise them. Mirrors `orisnik`'s own
// `spomen::guard` tests, which likewise use a plain `Vec<u8>` rather than any
// real OS allocation.
const debug_config: Config = .{ .debug = true };

test "round-trips when untouched" {
    const requested = 40;
    const buf = try testing.allocator.alloc(u8, requested + guard.memoryGuardSize(debug_config));
    defer testing.allocator.free(buf);
    writeGuard(debug_config, buf.ptr, requested, 0x42);
    try testing.expect(checkGuard(debug_config, buf.ptr, requested));
}

test "detects a single corrupted byte anywhere in the ramp" {
    const requested = 8;
    const guard_size = guard.memoryGuardSize(debug_config);
    for (0..guard_size) |corrupt_at| {
        const buf = try testing.allocator.alloc(u8, requested + guard_size);
        defer testing.allocator.free(buf);
        writeGuard(debug_config, buf.ptr, requested, 0x99);
        // Flip one guard byte — guaranteed to break the ramp's `+1` invariant
        // at this position regardless of what value was there (a value and its
        // wrapped-increment are always distinct).
        // INDEX: `requested + corrupt_at < requested + guard_size == buf.len`
        // (`corrupt_at` ranges over `0..guard_size`, this loop's own bound).
        buf[requested + corrupt_at] +%= 1;
        try testing.expect(!checkGuard(debug_config, buf.ptr, requested));
    }
}

test "wraps at 255 like HPHA does" {
    const requested = 4;
    const buf = try testing.allocator.alloc(u8, requested + guard.memoryGuardSize(debug_config));
    defer testing.allocator.free(buf);
    // Seed near the top of `u8`'s range so the ramp must wrap during the write
    // — `checkGuard`'s wrapping addition must agree with `writeGuard`'s.
    writeGuard(debug_config, buf.ptr, requested, 250);
    try testing.expect(checkGuard(debug_config, buf.ptr, requested));
}

test "seeded check accepts only the written seed" {
    const requested = 12;
    const buf = try testing.allocator.alloc(u8, requested + guard.memoryGuardSize(debug_config));
    defer testing.allocator.free(buf);
    writeGuard(debug_config, buf.ptr, requested, 250);
    try testing.expect(checkGuardSeeded(debug_config, buf.ptr, requested, 250));
    // A self-consistent ramp with the *wrong* seed is exactly what the unseeded
    // check cannot catch and this one must.
    try testing.expect(checkGuard(debug_config, buf.ptr, requested));
    try testing.expect(!checkGuardSeeded(debug_config, buf.ptr, requested, 251));
}
