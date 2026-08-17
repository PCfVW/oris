# Security Policy

## Posture — what Oris is, and isn't

Oris is a **single-threaded, performance-first heap allocator**, a faithful port of
HPHA (2007). It is **not a security-hardened allocator**, and does not try to be (see
the non-goals in [`ROADMAP.md`](ROADMAP.md)): no pointer/heap randomization, no
out-of-line metadata, no delayed-reuse quarantine, no release-mode canaries. HPHA
keeps allocator metadata **inline**, immediately before each block — a deliberate
speed/locality choice that is also a classic heap-corruption exposure (**CWE-122**):
an overflow past a payload can corrupt allocator state.

What Oris *does* offer is a set of defenses that cost **nothing at runtime** in a
release build — either because they are compile-time / correctness properties, or
because they live in the opt-in debug subsystem (`spomen`: a Rust feature and a Zig
`comptime` toggle) that is **entirely compiled out when disabled**.

> These describe Oris's **security model**, realized starting at v0.1.0 (the
> guard-byte debug subsystem lands in v0.2.0 — see [`ROADMAP.md`](ROADMAP.md)).

## CWEs addressed at no release-time cost

| CWE | Weakness | How Oris addresses it | Cost |
|---|---|---|---|
| **CWE-190** / **CWE-131** | Integer overflow / wrong buffer-size calc in a size + alignment request | Size and alignment are combined with **checked arithmetic** and the request is rejected (null / `error.OutOfMemory`) on overflow, before any allocation | always-on, cold path only — effectively free |
| **CWE-476** | NULL-pointer deref on allocation failure | OOM is a **value**, never a panic: `null` (C / Zig) or `Option<NonNull<_>>` (Rust); the never-null invariant is encoded in the type | always-on |
| **CWE-825** / **CWE-476** *(Rust)* | Dangling / provenance-invalid pointer use | All pointer arithmetic goes through **strict-provenance** APIs; the suite runs under **Miri** (`-Zmiri-strict-provenance -Zmiri-tree-borrows`) as a release gate | compile-time + CI; zero runtime cost |
| **CWE-908** | Use of uninitialized memory | `alloc` returns uninitialized bytes *by contract* (like `malloc`), modeled as such (`MaybeUninit`); `calloc` zeroes | always-on |
| **CWE-122** / **CWE-787** | Heap overflow into the adjacent block / inline metadata | **Guard bytes** around each allocation, checked on free | **debug only** — zero cost when the debug subsystem is off |
| **CWE-415** | Double free | Allocation-record tracking flags a free of an already-free block | **debug only** |
| **CWE-590** | Free of a pointer not owned by this allocator | Ownership / record check on free | **debug only** |
| **CWE-416** | Use after free | Debug poisoning surfaces reuse-after-free; Miri catches it in tests | **debug only** + CI |
| **CWE-401** | Memory leak | Leak detection on allocator drop / `deinit`; `std.testing.allocator` (Zig) and Miri (Rust) enforce it in CI | **debug only** + CI |

"Debug only" means the check ships in the debug subsystem and is **eliminated from
release builds** (Rust: the `debug-allocator` feature off; Zig: the `comptime` debug
flag false) — so enabling hardening never taxes a release hot path, and disabling it
costs nothing.

## Not defended (by design)

These need the hardening machinery Oris deliberately omits for speed. If your threat
model needs them, reach for `mimalloc`, `hardened_malloc`, or a hardened system
allocator:

- Release-mode heap / pointer randomization.
- Out-of-line or guarded metadata (**CWE-122** in release remains possible).
- Delayed-reuse quarantine for **CWE-416** in release.
- Concurrent / cross-thread corruption defenses (Oris is single-threaded).

## Supported versions

| Version | Supported |
|---|---|
| 0.1.x | ✅ |
| < 0.1.0 | ❌ — pre-release / name-reservation stubs only |

## Reporting a vulnerability

Please report suspected vulnerabilities **privately**, not as a public issue:

- Preferred: GitHub **private vulnerability reporting** — the **Security → Report a
  vulnerability** button on <https://github.com/PCfVW/oris>.
- Include a minimal reproducer (an alloc/free sequence, ideally as a trace), the
  affected port(s), and the version or commit.

Because both ports share one algorithm and one cross-port invariant, a memory-safety
issue in one port is assumed to affect the other until shown otherwise; fixes are
mirrored across `orisnik` and `orisnitsa`.
