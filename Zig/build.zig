// SPDX-License-Identifier: MIT OR Apache-2.0
const std = @import("std");

/// Build graph for `orisnitsa` — the Zig port of Dimitar Lazarov's HPHA (2007).
///
/// Stub stage: exposes the `orisnitsa` module and a `test` step so CI has a
/// green baseline. The allocator core (the bucket and tree *orisnitsi*) lands
/// in v0.1.0; see `../ROADMAP.md`.
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // The consumer-facing module. Importable as `@import("orisnitsa")`.
    const mod = b.addModule("orisnitsa", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // `zig build test` runs the module's `test` blocks. CI runs this in both
    // Debug and ReleaseSafe (runtime safety checks on); see Zig/CONVENTIONS.md.
    const mod_tests = b.addTest(.{ .root_module = mod });
    const run_mod_tests = b.addRunArtifact(mod_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_mod_tests.step);
}
