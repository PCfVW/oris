# ORIS

*A high-performance heap allocator, after the folk-allotters of fate.*
A Rust and Zig port of Dimitar Lazarov's **HPHA** (2007).

*Document revision 0.4.*

---

## Etymological grounding

In Bulgarian folk belief, the **Орисници** (*Orisnitsi*) are three sister-spirits who arrive on the third night after a child's birth to *allot* its fate — what it shall be, what it shall have, how long it shall live. The noun **ориса** (*orisa*) means "lot, portion, allotted destiny"; the verb **орисвам** (*orisvam*) means "to apportion, to ordain by lot."

The deeper etymology is uncanny for our purposes. The Bulgarian name does not come from a native Slavic root; it is borrowed from the Greek **ὁρίζοντες** (*horizontes*) — the present participle of **ὁρίζω**, "to bound, to delimit, to set the limits of." The same Greek verb gives English *horizon*. The Bulgarian *Orisnitsi* are, literally, **the female bounders** — those who set the limits.

A heap allocator that bounds regions of memory and sets the limits of each block is performing exactly the act the word names. This is not folkloric metaphor stretched to fit. It is the word's plain Greek meaning.

## References

1. **Máchal, Jan Hanuš.** *Slavic Mythology.* Vol. 3 of *The Mythology of All Races*, edited by Louis Herbert Gray, translated from the Czech by F. Krupička. Boston: Marshall Jones, 1918. Chapter IV, "Genii of Fate," pp. 249–252 (the Bulgarian *Orisnici*/*Urisnici* and their Greek etymology, ὁρίζοντες, discussed on p. 250). — The canonical scholarly source on the Bulgarian *Orisnici* and their Greek etymology. Verified against the scanned text at [archive.org](https://archive.org/details/mythologyofallra03gray).

2. **Procopius of Caesarea.** *History of the Wars*, Book VII (the Gothic War), ch. 14 (c. 553 CE). — The earliest written reference to Slavic religious beliefs about fate; Procopius reports that the Slavs did not regard fate as a power over man but offered sacrifices to a higher being who dealt out life and death. *Terminus a quo* for Slavic fate beliefs in the written record.

3. **Brother Rudolf** (Cistercian friar). *Catalogus magiae* / *Summa de confessionis discretione*, c. 1230–1250. — The earliest written record of the three-sister Slavic fate motif as such: Rudolf describes Western Slavic sacrifices to "three sisters, which the pagans call Clotho, Lachesis and Atropos." He used the Greek names because he had no Slavic ones; the figures are unmistakably the same as those later called *Rozhanitsy / Orisnitsi*. Modern critical edition: Edward Karwot, ed., *Katalog magii Rudolfa* (Wrocław: Ossolineum, 1955).

## Glossary — oris- root mapped to allocator concepts

| Bulgarian | Latin | Status | Role in the allocator |
|---|---|---|---|
| ориса / орис | *orisa* / *oris* | standard | a single allocation; a block of allotted memory |
| орисник | *orisnik* | standard (m.) | the allocator itself — the agent that allots |
| орисница | *orisnitsa* | standard (f.) | the allocator (feminine twin; folkloric form) |
| орисници | *orisnitsi* | standard (pl.) | the sub-allocators — the bucket and tree agents, the sisters |
| орисване | *orisvane* | standard | the act of allocation (verbal noun) |
| орисан | *orisan* | standard | the "allocated" state of a block (past participle) |
| неорисан | *neorisan* | well-formed coinage | the "free" / unallocated state |
| преорисвам | *preorisvam* | well-formed coinage | reallocation (re-allotment) |
| разорисвам | *razorisvam* | well-formed coinage | deallocation (un-allotment, by analogy with *развързвам* "to untie") |

A note on the coinages: Bulgarian readily forms verbs with the prefixes *не-* (un-), *пре-* (re-, over-), and *раз-* (un-, apart-). The three above are not dictionary entries but they are unambiguous and idiomatic to a native ear — exactly the register one wants for terms of art.

## Naming the moving parts

- **Rust crate:** `orisnik`
- **Zig module:** `orisnitsa` *(the feminine twin — two ports, two siblings of one Fate)*
- **Public API surface:** `oris_alloc`, `oris_free`, `oris_realloc`; or in long Bulgarian form, `orisvam` / `razorisvam` / `preorisvam`
- **The sub-allocators** (bucket and tree): the **orisnitsi**, optionally named after their folkloric roles as sisters
- **A debug / stats subsystem:** **`spomen`** (*спомен*, "remembrance, recollection") — a natural cousin of the family
- **The whole governed address space:** **`stopanstvo`** (*стопанство*, "household, domain") — useful when you need a word for "the heap as a whole" distinct from any single allocator instance

## Prior art and positioning — Rust

The Rust allocator landscape is dominated by bindings to mature C/C++ allocators: `mimalloc`, `tikv-jemallocator`, `snmalloc-rs`. Native-Rust allocators target either embedded / no_std use (`linked_list_allocator`, `talc`, `buddy_system_allocator`, `embedded-alloc`) or arena/bump patterns (`bumpalo`, `typed-arena`, `rustc_arena`). The nearest design cousin is **`context-allocator`** by lemonrock, whose `MultipleBinarySearchTreeAllocator` uses red-black trees of free blocks for defragmentation — but it does not combine with a small-allocation bucket, and the crate is dormant. **No actively-maintained Rust crate combines size-class buckets for small allocations with a red-black-tree best-fit allocator for large allocations.** HPHA's architecture is unrepresented.

## Prior art and positioning — Zig

Zig treats allocators as first-class; the standard `std.heap` ships `page_allocator`, `FixedBufferAllocator`, `ArenaAllocator`, `DebugAllocator` (safety-first, bucket-per-size-class, hash-map index for large blocks), `SmpAllocator` (performance-first, log-spaced size classes over per-thread slabs), and `c_allocator`. The notable third-party allocators — `jdz_allocator`, `zimalloc`, `rpmalloc-zig` — are all in the modern mimalloc / rpmalloc lineage: thread-local size-class arenas, no tree on the large-allocation path. **No Zig allocator, in stdlib or out, uses a red-black tree of free blocks for large allocations.** HPHA's architecture is, again, unrepresented.

## Why this architecture — strengths and trade-offs

The bucket-plus-RB-tree-best-fit design is not obsolete; it lost the dominant server-workload competition to size-class allocators with thread-local caches (tcmalloc 2005 → jemalloc → mimalloc → snmalloc / rpmalloc / Zig's `SmpAllocator`). The shift was driven primarily by multicore scalability — a global tree of free blocks serializes across cores in a way that thread-local size-class caches do not — and secondarily by cache locality, security hardening, latency predictability, and NUMA awareness. The older design retains real advantages in single-threaded and low-concurrency settings.

| ✅ Strengths | ⚠️ Trade-offs |
|---|---|
| **Best-fit + coalescing** → strong memory utilization on workloads with widely varied allocation sizes (slab allocators by design can't merge across size classes) | **Doesn't scale across many cores.** Global / coarse locking on the tree; no per-thread caches |
| **O(1) size queries** from a pointer via inline block header — no auxiliary table | **O(log n) on the large path** (RB-tree), vs O(1) free-list pop/push in slab designs |
| **Compact and auditable** (~1500 LOC). Easy to read, port, and reason about end-to-end | **Inline metadata is a security exposure.** A buffer overflow can corrupt allocator state — a classic heap-corruption exploit class |
| **No per-thread state.** No TLS, no thread-local init, no cross-thread free protocol, no thread-exit cleanup | **Worse cache locality.** Tree-best-fit jumps around the address space; size classes return recently-freed blocks of the same size |
| **Deterministic memory layout.** Useful for save-state replay, memory-mapped files, debugging | **No NUMA awareness, no remote-free machinery, no randomization / hardening** |
| **Lazy OS-return.** Memory returned only on explicit `purge()` — predictable RSS, no surprise `munmap` storms | **Higher RSS by default** — the flip side of lazy return |

Note: the technique isn't extinct in modern allocators — jemalloc still uses red-black trees to track *extents*. It got pushed up to a coarser granularity, not abandoned.

## Target workloads

> **Oris is a single-threaded heap allocator for workloads dominated by many small allocations and a handful of large ones — game-engine planners, AI search, parsers, interpreters, single-threaded simulations.**

The canonical case is a **goal-oriented planner** — GOAP, HTN, or any backtracking AI search — running inside a game's per-frame budget. F.E.A.R. (2005) set the template; the pattern dominated AAA NPC behavior through roughly 2010–2015. The workload is brutal on a general-purpose allocator and trivial for HPHA:

- **Tons of small, short-lived allocations.** Plan nodes, state copies, action preconditions, open/closed-set entries. All on the bucket path; all returning to recently-freed pages of the same size class on the next iteration. Cache behavior is excellent because the planner hammers the same handful of pages over and over.
- **Occasional large allocations.** A state vector, a frontier buffer, a working set — handled by the tree, best-fit, with coalescing so the planner's memory footprint stays bounded across long searches.
- **Single-threaded by design.** A planner's search loop is sequential with backtracking; you don't parallelize *within* a plan, you parallelize *across NPCs* by running independent planner instances on their own threads, each with its own allocator. Thread-local-cache machinery is pure overhead in that model — you'd be paying for synchronization primitives the workload never needs.
- **Latency, not throughput, is the metric.** Missing the frame budget is a visible glitch. The bucket path is branch-predictable and lock-free-because-no-locks; there are no background threads, no deferred `munmap`, no surprise tree rotations on the hot path.
- **Bounded lifetime.** When the plan is done you `purge()` and return to a clean slab. No leak-detection ceremony, no thread-exit cleanup, no orphaned thread-local arenas.

Note: the small-allocation threshold is **256 bytes** with 32 size classes at 8-byte spacing — exactly the payload distribution of a typical plan node with a handful of state slots. Lazarov tuned this for the workload.

The same shape applies to other domains: **parsers and interpreters** (AST nodes, environment frames), **compilers and analyzers** (IR nodes, symbol tables), **single-threaded simulation kernels** (entities, events, particles), **document processing** (tokens, layout boxes), and **anything backtracking** (SAT solvers, regex engines, constraint propagation). In each case the pattern is the same — many small things with similar sizes, a few large working buffers, sequential access with bounded plan lifetime — and the allocator pays for nothing the workload doesn't use.

For multi-threaded server workloads, reach for `mimalloc`, `jemalloc`, or `snmalloc`. Oris is not their competitor.

## Style & tone

The voice is **understated mythic**: a serious systems library with quiet folkloric resonance, never costume jewelry. Documentation should introduce each Bulgarian term once, then use it as a term of art — the way `mmap` or `arena` are used, not the way marketing slogans are used. Identifiers in code stay in diacritic-free Latin transliteration; Cyrillic is welcome in prose, comments, and the README header.

## Taglines (pick / discard / replace)

- *Памет, орисана за бързина.* — **Memory, allotted for speed.**
- *Three sisters allot. One heap delivers.*
- *Allocation as fate; deallocation as release.*
- *The Orisnitsi for your bytes.*

---

*Open questions:* per-thread cache naming (a fourth sister? a household servant?); whether to keep the gendered Rust/Zig split or pick one canonical name.
