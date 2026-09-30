// SPDX-License-Identifier: MIT OR Apache-2.0
const std = @import("std");

/// Build graph for `orisnitsa` — the Zig port of Dimitar Lazarov's HPHA (2007).
///
/// Exposes the `orisnitsa` module, a `test` step, and — new since v0.1.0's
/// `capi.zig` — static and shared library artifacts so the `oris_*` C-ABI is
/// actually linkable by a C/C++ caller, not just compiled into the test binary.
/// See `../include/oris.h` for the C prototypes (shared with the Rust port,
/// which implements the identical ABI).
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

    // The debug allocator's leak panic cannot be caught in-process (Zig panics do not unwind,
    // and the test runner would die with it), so `src/leak_probe.zig` — a program that leaks
    // one block and calls `deinit()` — is run here and required to *fail*, reporting the leak.
    // Skipped in ReleaseSmall, where a panic is a bare trap with no message to check.
    if (optimize != .ReleaseSmall) {
        const probe = b.addExecutable(.{
            .name = "leak_probe",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/leak_probe.zig"),
                .target = target,
                .optimize = optimize,
            }),
        });
        if (target.result.os.tag != .windows) {
            probe.root_module.link_libc = true;
        }
        const run_probe = b.addRunArtifact(probe);
        run_probe.expectStdErrMatch("memory leaked: 1 allocation(s) still live");
        run_probe.expectStdErrMatch("REPORT =====");
        // How a panic ends the process is the OS's: an exit status on Windows, SIGABRT elsewhere.
        if (target.result.os.tag == .windows) {
            run_probe.expectExitCode(3);
        } else {
            run_probe.addCheck(.{ .expect_term = .{ .signal = std.posix.SIG.ABRT } });
        }
        test_step.dependOn(&run_probe.step);
    }

    // `zig build docs` emits the API documentation of the `orisnitsa` module (from its `///`
    // and `//!` comments) to `zig-out/docs/`; open `zig-out/docs/index.html` through a local
    // web server (the generated page loads a `.wasm`, which browsers refuse from `file://`).
    const docs_lib = b.addLibrary(.{ .name = "orisnitsa", .root_module = mod });
    const install_docs = b.addInstallDirectory(.{
        .source_dir = docs_lib.getEmittedDocs(),
        .install_dir = .prefix,
        .install_subdir = "docs",
    });
    b.step("docs", "Generate the API documentation into zig-out/docs").dependOn(&install_docs.step);

    // `zig build example` runs `examples/catch_an_overrun.zig` (the debug allocator catching an
    // overrun on purpose). It is also part of `test`, so it is compiled and run in CI and
    // cannot rot; unlike the leak probe it is fine in every optimize mode.
    const example = b.addExecutable(.{
        .name = "catch_an_overrun",
        .root_module = b.createModule(.{
            .root_source_file = b.path("examples/catch_an_overrun.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "orisnitsa", .module = mod }},
        }),
    });
    const run_example = b.addRunArtifact(example);
    run_example.expectStdErrMatch("check() found Corruption: guard bytes overwritten");
    run_example.expectStdErrMatch("check() after repair: true");
    b.step("example", "Run the debug-allocator example").dependOn(&run_example.step);
    test_step.dependOn(&run_example.step);

    // Static and shared C-linkable libraries, built from a *separate* module
    // rooted directly at `capi.zig`, not `mod` (rooted at `root.zig`). Zig only
    // auto-exports `export fn`s that live in a module's own root file — an
    // `export fn` in a file reached merely via an unreferenced `@import` (as
    // `root.zig` does for `capi.zig`, to make its `test` blocks reachable) is
    // never analyzed for a non-test artifact and is silently absent from the
    // built library. Confirmed empirically against Zig 0.16.0 with a minimal
    // two-file repro (`@import`-only vs. root-file placement produced an empty
    // vs. populated DLL export table) before relying on it here — do not
    // reintroduce the `root.zig`-rooted version for these artifacts.
    const capi_mod = b.createModule(.{
        .root_source_file = b.path("src/capi.zig"),
        .target = target,
        .optimize = optimize,
    });
    if (target.result.os.tag != .windows) {
        capi_mod.link_libc = true;
    }

    // `zig build` (the default step) installs both — mirroring `orisnik`'s
    // `cdylib`/`staticlib` Cargo crate-types.
    const static_lib = b.addLibrary(.{
        .name = "orisnitsa",
        .root_module = capi_mod,
        .linkage = .static,
    });
    b.installArtifact(static_lib); // -> zig-out/lib/liborisnitsa.a (or orisnitsa.lib on Windows)

    const shared_lib = b.addLibrary(.{
        .name = "orisnitsa",
        .root_module = capi_mod,
        .linkage = .dynamic,
    });
    // Windows names a DLL's own import library the same way it names a static
    // library (`orisnitsa.lib`) — both `static_lib` above and this one's import
    // stub would collide at `zig-out/lib/orisnitsa.lib` if installed the same
    // way (`b.installArtifact`'s default). `implib_dir` exists specifically to
    // redirect just that stub, independent of the actual runtime library
    // (`orisnitsa.dll`/`liborisnitsa.so`/`.dylib`, unaffected, still installed
    // to the usual per-platform default) — but only on Windows: an import
    // library is a PE/COFF-only concept (`-femit-implib` is a hard error on
    // every other target), and there is no collision to avoid elsewhere, since
    // `.so`/`.dylib` and `.a` never share an extension the way two `.lib`s do.
    if (target.result.os.tag == .windows) {
        b.getInstallStep().dependOn(&b.addInstallArtifact(shared_lib, .{
            .implib_dir = .{ .override = .{ .custom = "lib/import" } },
        }).step);
    } else {
        b.installArtifact(shared_lib);
    }
}
