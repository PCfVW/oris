# ROADMAP — Oris

*A Rust and Zig port of Dimitar Lazarov's HPHA (2007). For the project's design rationale, etymological grounding, target workloads, and prior-art positioning, see the [brief](./BRIEF.md).*

---

## Versioning policy

Oris ports ship in lockstep. **The same version number on `orisnik` (crates.io) and `orisnitsa` (Zig package registry) carries the same feature set and the same internal-state-transition behavior** — that is the project's defining invariant. Semantic versioning applies, with the understanding that any change to the public API or to the algorithm's externally-visible state transitions is at minimum a minor version bump.

### Fidelity fixes are patches

One class of change is exempt from the minor-bump rule above: **a change whose sole effect is to make a port agree with HPHA where it previously did not, or to remove undefined behavior, ships as a patch** — even when it is externally visible.

The reasoning is that such a change does not alter the contract; it makes the implementation meet the contract it always claimed. HPHA is the specification. Where a port diverged from it, the divergent behavior was never a promise to anyone, so nothing that depended on it was depending on a documented guarantee. The same holds for a wrapping arithmetic path or a silent misdispatch: behavior that is undefined cannot be relied upon, and replacing it with a defined refusal narrows what the allocator does rather than changing it.

Two conditions make a change eligible, and both must hold:

1. **The reference decides.** The fix is justified by pointing at `Cpp/hpha.h`/`hpha.cpp` and showing the port disagreeing with it, or by showing that the affected inputs reach arithmetic with no defined result. A change that makes a port *better* than HPHA by some other standard is a feature, not a fidelity fix, and takes a minor bump.
2. **No input that previously behaved correctly changes.** The set of affected inputs must be exactly those that were already broken. If a working call changes its result, it is a minor bump regardless of how the change is motivated.

Both ports must land the fix in the same release, as with any change under the cross-port invariant. The release notes name each fixed divergence and the reference behavior it restores; `v0.1.1` is the first release cut under this rule.

This does not weaken the invariant — it protects it. Under the strict reading, correcting a divergence from HPHA would cost a minor version, which makes fidelity repairs compete with feature milestones for version numbers and creates a standing incentive to defer them. Cheap, prompt fidelity fixes are exactly what a project defined by a cross-port invariant needs most.

## Cross-language invariant

From v0.1.0 onward, both Oris ports satisfy the following property:

> *Given an identical allocation/deallocation sequence at the public API level, both ports produce identical internal state transitions — same bucket-page spawns, same tree-rotation count, same coalescing operations, same final RSS.*

This is a stricter property than "the API behaves the same"; it is "the algorithm executes the same." Verified in CI from v0.3.0 onward against a corpus of reproducible traces.

This invariant is the property that justifies maintaining two ports rather than one. Without it, the ports are merely two implementations; with it, they are two views of the same machine.

---

## Milestones

### v0.1.0 — Foundation ✅ *Released 2026-08-17*

**Theme:** Faithful single-threaded port.

- **Bucket allocator** (small-allocation path, ≤256 B, 32 size classes at 8 B spacing)
- **Tree allocator** (large-allocation path, RB-tree of free blocks, best-fit, coalescing)
- **Public API:** `alloc`, `free`, `realloc`, `calloc`, `resize`, `size`, `purge`, `allocated` — both alignment-aware and alignment-naive variants
- **Cross-platform virtual-memory layer** (Linux + macOS + Windows; abstracts HPHA's Win32-only `VirtualAlloc`)
- **Per-language idiomatic surfaces:** Rust's `Allocator` trait surface, Zig's `std.mem.Allocator` interface — alongside the C-shaped `oris_*` functions
- **Unit test suites** per port, targeting 50+ tests each, with API parity
- **Documentation:** top-level README, per-language READMEs, lineage attribution to Lazarov / Luxoflux, `LICENSE` (dual MIT OR Apache-2.0, via `LICENSE-MIT`/`LICENSE-APACHE`), `CHANGELOG.md`, `INSTALL.md`
- **Out of scope for v0.1.0:** debug instrumentation, multithreaded mode, benchmarks, examples beyond the test suite

### v0.2.0 — Debug allocator

**Theme:** Observability and safety.

- Port HPHA's `DEBUG_ALLOCATOR` mode in both languages
- **Memory guard bytes** with overflow detection
- **Allocation record tracking** (HPHA uses an intrusive multi-RBT; each port adopts the idiomatic equivalent that preserves the state-transition invariant)
- **Callstack capture** (platform-specific; abstracted behind a stable interface in each port)
- **Leak detection** on allocator drop / deinit
- **`report()` and `check()` diagnostic methods**
- **Build-time toggleable:** Rust feature flag; Zig `comptime` bool — both with zero-cost-when-disabled guarantees
- Cross-port parity: same allocation sequence produces same debug-record contents (modulo platform-specific callstack symbols)

### v0.3.0 — Invariant verification and benchmarks

**Theme:** Reproducibility and credibility.

- **Trace format:** a small, language-agnostic allocation-sequence format. ISO/IEC 14977 EBNF grammar in `examples/traces/GRAMMAR.md` — mirroring the priority queue project's grammar discipline.
- **Trace recorder and replayer** in both ports
- **State-transition harness:** same trace → byte-identical transition record across both ports; CI gate enforces equality
- **Standalone trace generator** as a `benchmarks/scripts/tracegen/` crate (mirroring `graphgen/` from the priority queue project) producing seeded, reproducible traces from planner, parser, and synthetic workloads
- **mimalloc-bench integration:** Oris runs in the standard allocator benchmark harness against `mimalloc`, `jemalloc`, `snmalloc`, system malloc, plus Zig's `SmpAllocator` and Rust's allocator landscape where applicable
- **`benchmarks/methodology.md`** documenting the reproducibility protocol: 3-pass, warmup + median-of-N with IQR — same shape as the priority queue project's protocol
- **Initial published results:** wall-time, peak RSS, fragmentation, worst-case latency on each workload class, with the trace corpus shipped alongside

### v0.4.0 — Examples and the planner

**Theme:** Show the workload.

- **`examples/planner/`** — a small GOAP-style planner in both languages, demonstrating the target workload of the brief. Uses both `orisnik` / `orisnitsa` *and* `d-ary-heap` / `d-ary-heap.zig` — the priority-queue-inside-the-allocator connection becomes literal.
- **`examples/parser/`** — an AST-building parser demonstrating small-allocation churn
- **`examples/replay/`** — replays a recorded trace and plots RSS over time
- **Per-language documentation polish:** "Why this crate?" differentiator sections, instrumentation examples, absolute GitHub URLs verified for external rendering on crates.io and the Zig package registry
- **README polish across all surfaces** (top-level, per-port, registries)

### v1.0.0 — Stable API

**Theme:** Commitment.

- **Public API freeze.** Any post-1.0 change to the surface is a 2.0.
- **Test coverage targets:** 80+ tests per port; cross-port API parity verified
- **Full mimalloc-bench results** published in `benchmarks/results/v1.0.0/` against the major allocators
- **Migration guide:** replacing system allocator with Oris in real codebases
- **Long-term support commitment** for the v1.x line: bug fixes, security patches, no breaking changes
- **Cross-language invariant verified** on the full trace corpus, CI-enforced

---

## Beyond v1.0

These are candidate themes, not commitments. Order and scope subject to feedback from real use.

- **v1.x — Trace visualizer.** Web-based replay of allocation traces: block-layout animation, RSS curves, bucket activity heatmaps, fragmentation visualizations. The demo equivalent of the priority queue project's Dijkstra visualization. Substantial work; deliberately deferred past v1.0.
- **v2.x — Multithreaded mode.** Port HPHA's `MULTITHREADED` mode with per-bucket and per-tree locks. Modest scaling; not competitive with mimalloc on many-core. Offered as a convenience for users who want a single allocator across both single- and multi-threaded paths in their codebase, not as a serious bid for the server-allocator niche.
- **v2.x — Per-thread caches.** Optional thread-local bucket caching, opt-in. Changes the design's character; flagged as a deliberate divergence from HPHA rather than a faithful port.
- **Additional language ports** if and only if there's a sustained user base asking. The Bulgarian-folklore naming family can extend with native-speaker review, but the cross-language invariant cost grows linearly with the number of ports.
- **Experiment sidebar.** A small research piece, mirroring the priority queue project's AI code generation study. Candidate topic: *how well do AI models handle intrusive data structures and pointer tagging?* — the kind of code allocators rely on and AI models are notoriously uneven at.

---

## Non-goals

To make the project's scope legible, here is what Oris is **not** trying to be:

- **A general-purpose server allocator.** For high-concurrency server workloads, use `mimalloc`, `jemalloc`, or `snmalloc`. Oris is not their competitor; see the brief's "Why this architecture" section.
- **A security-hardened allocator.** HPHA's inline metadata is a classic exploit class. Oris offers guard bytes in debug mode but does not target adversarial environments.
- **A NUMA-aware allocator.** No NUMA bookkeeping, no remote-thread free protocol.
- **A drop-in libc malloc replacement.** Oris is an allocator *crate / module*, not a global-allocator shim. Users can opt in to it as a global allocator per port, explicitly.
- **A teaching tool that prioritizes pedagogical clarity over performance.** The code aims to be auditable, but the implementation follows HPHA's performance-first choices — intrusive metadata, pointer tagging, hand-tuned size classes.

---

## Methodological lineage

This roadmap follows the structural and methodological conventions established by the [d-ary heap priority queue project](https://github.com/PCfVW/d-Heap-priority-queue): synchronized cross-language versioning, EBNF-grammar-defined test corpora, multi-pass reproducible benchmarks, and explicit cross-language invariants verified in CI.

Oris extends that pattern from five readable languages to two systems-language ports, and from a textbook algorithm to a single canonical source (HPHA, 2007). The cross-language invariant tightens accordingly: from "byte-identical comparison counts" to "byte-identical internal state transitions."

The priority queue project taught the breadth of cross-language porting. Oris is the depth exercise on the next layer down.
