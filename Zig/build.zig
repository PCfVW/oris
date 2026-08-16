// SPDX-License-Identifier: MIT OR Apache-2.0
const std = @import("std");

/// Build graph for `orisnitsa` — the Zig port of Dimitar Lazarov's HPHA (2007).
///
/// Exposes the `orisnitsa` module and a `test` step. The v0.1.0 allocator core (the
/// bucket and tree *orisnitsi*) is under active construction, module by module,
/// mirroring the already-complete `orisnik` Rust port; see `../ROADMAP.md`.
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // The consumer-facing module. Importable as `@import("orisnitsa")`.
    const mod = b.addModule("orisnitsa", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // `os.zig`'s Unix path calls `std.c.mmap`/`munmap` directly (not the
    // `std.posix` wrapper — see os.zig's module doc for why), which requires libc
    // to be linked. Windows uses hand-declared `kernel32` externs instead and needs
    // no libc; linking it there would be a no-op at best, so this stays conditional,
    // matching `orisnik`'s own `[target.'cfg(unix)'.dependencies] libc` in Cargo.toml.
    if (target.result.os.tag != .windows) {
        mod.link_libc = true;
    }

    // `zig build test` runs the module's `test` blocks. CI runs this in both
    // Debug and ReleaseSafe (runtime safety checks on); see Zig/CONVENTIONS.md.
    const mod_tests = b.addTest(.{ .root_module = mod });
    const run_mod_tests = b.addRunArtifact(mod_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_mod_tests.step);
}
