# Traces and transition records

Oris's two ports promise more than the same API: an identical sequence of calls must drive
`orisnik` (Rust) and `orisnitsa` (Zig) through **identical internal state transitions** —
the same bucket pages spawned, the same blocks split and merged, the same red-black tree
rotations, the same memory mapped and returned ([`ROADMAP.md`](../ROADMAP.md#cross-language-invariant)).
This guide covers the machinery that checks it, **`letopis`** (*летопис*, "chronicle"), and
how to use it on your own programs.

> **Status:** new in v0.3.0 (unreleased, on `main`). The API is marked unstable until 1.0:
> the record format may grow events as the invariant is tightened.

## The two formats

- A **trace** (`*.trace`) is an allocation sequence, written with symbolic handles instead
  of addresses:

  ```text
  oris-trace 1
  alloc h0 24
  alloc h1 1000
  realloc h1 2000
  free_sized h0 24
  free h1
  purge
  ```

- A **transition record** (`*.record`) is what one allocator did in response — each
  operation, its result, and every state transition it caused, with every address
  normalized to *mapping id + offset*:

  ```text
  #2 realloc h1 2000 -> m1+0x20 a=131072
    mr -
    merge m1+0x410
    split m1+0x10 2000
    mr m1+0x7f0
  ```

  (`realloc` grew the block in place: it took the free block after it out of the
  most-recently-freed cache, absorbed it, and split the excess off again.)

Both are specified in [`examples/traces/GRAMMAR.md`](../examples/traces/GRAMMAR.md);
[`examples/traces/EVENTS.md`](../examples/traces/EVENTS.md) lists where each event fires in
HPHA and in both ports. Two implementations satisfy the invariant on a trace exactly when
their records are byte-identical.

## Turning it on

**Rust** — the `trace` feature adds the `orisnik::letopis` module:

```toml
[dependencies]
orisnik = { version = "0.3", features = ["trace"] }
```

**Zig** — `orisnitsa.letopis` is always there; the hooks it reads exist only in an
instantiation with `Config.trace` set, which `letopis.replay` creates itself
(`OrisnitsaWith(.{ .trace = true })`).

With the feature (Rust) or the flag (Zig) off, every hook is compiled out: the allocator you
ship is unchanged.

## Replaying a trace

From the command line, each port prints the record of a trace file:

```sh
# from Rust/
cargo run --example replay --features trace -- ../examples/traces/handwritten/realloc-branches.trace
# from Zig/
zig build replay -- ../examples/traces/handwritten/realloc-branches.trace
```

From code:

```rust
let mut record = String::new();
orisnik::letopis::replay(&trace_text, &mut record)?;
```

```zig
var record: std.Io.Writer.Allocating = .init(gpa);
defer record.deinit();
var diag: orisnitsa.letopis.Diagnostic = .{};
try orisnitsa.letopis.replay(gpa, trace_text, &record.writer, &diag);
```

A trace is checked in full before anything runs. A malformed line is a *syntax* error; a
call with no defined result — a double free, a `free_sized` with the wrong size, an
alignment above 64 KiB, an input on which HPHA itself is broken — is a *semantic* one
(constraints C1–C8 of GRAMMAR.md §1.3). Either way you get the line and the reason, and
nothing is executed:

```text
replay: my.trace: trace rejected (line 3): C2: h1 is not bound
```

Build with the debug allocator as well and the records change (its guard bytes shift every
size class); the invariant is defined on the non-debug allocator.

## Recording your own program

A **recorder** wraps an allocator, forwards every call, and writes it as a trace.

**Rust:**

```rust
use orisnik::Orisnik;
use orisnik::letopis::Recorder;

let allocator = Box::new(Orisnik::new());
let mut recorder = Recorder::new(&allocator, String::new());
let p = recorder.alloc(24);
// ... use the recorder exactly as the allocator ...
unsafe { recorder.free(p) };
let trace = recorder.finish()?;      // the trace text
```

**Zig** — the recorder also hands itself out as a `std.mem.Allocator`, so a program that
takes one records with no other change:

```zig
var backing: orisnitsa.Orisnitsa = .init();
defer backing.deinit();
var trace: std.Io.Writer.Allocating = .init(gpa);
defer trace.deinit();
var recorder = orisnitsa.letopis.Recorder(.{}).init(&backing, gpa, &trace.writer);
defer recorder.deinit();
const a = recorder.allocator();      // a std.mem.Allocator; every call is recorded
// ... run your code with `a` ...
try recorder.finish();
```

What to know:

- **A recorder is not a global allocator.** It keeps a pointer-to-handle table, and the
  writer may allocate; both must come from another allocator.
- **It records what happened, not what is allowed.** A program may legally free with a size
  after a `realloc`, or ask for more than 1 GiB; a trace may not (GRAMMAR.md §1.3). The
  recording is faithful, and the replayer then refuses it, naming the rule and the line.
- `free`, `resize` and `size` of a null pointer do nothing, and are not recorded.

## The corpus and the CI gate

[`examples/traces/`](../examples/traces/) holds the corpus:

- `handwritten/` — twelve short, commented traces, one per path through the allocator
  (every `realloc` branch, aligned padding, chains of equal-size free blocks, the small free
  list, purge, ...);
- `generated/` — seven traces of a few thousand operations from
  [`benchmarks/scripts/tracegen`](../benchmarks/scripts/tracegen/README.md): a GOAP-style
  planner, a parser, and five synthetic profiles.

Next to each trace is its `.record`, **generated by the 2007 HPHA reference itself**: a
scratch copy of `Cpp/hpha.h`/`hpha.cpp` with the same hooks added by a patch, the reference
files never touched ([`Cpp/oracle/README.md`](../Cpp/oracle/README.md)). On every push,
[`trace-ci.yml`](../.github/workflows/trace-ci.yml) replays the corpus with both ports on
Linux, Windows and macOS, and with HPHA on Windows, and requires every record to match byte
for byte. So the ports are held to the specification, not merely to each other.

## When records differ

A difference is a cross-port divergence (or a divergence from HPHA) — exactly what the gate
exists to find. The first differing line is the first transition that went differently;
everything after it is consequence. To investigate:

1. `diff` the two records and find the first differing entry (`#<n>` is the operation).
2. Cut the trace down to that operation (operations after it cannot matter) and replay the
   prefix on both sides.
3. Look up the event in [`EVENTS.md`](../examples/traces/EVENTS.md): it names the function
   in HPHA, `orisnik` and `orisnitsa` that performs the transition.

If the change was intended — a fidelity fix, say — it lands in Rust, Zig and
`Cpp/oracle/letopis.patch` in the same commit, and the records are regenerated from the
oracle, never from a port.

## Adding a trace

1. Write it by hand (in `handwritten/`, with a comment saying what it exercises), or add a
   `[[trace]]` table to [`benchmarks/traces.toml`](../benchmarks/traces.toml) and run
   `tracegen generate --tier ci`.
2. Generate its record with the oracle (Windows, MSVC):
   `& $oracle my.trace > my.record` — see [`Cpp/oracle/README.md`](../Cpp/oracle/README.md).
3. Check both ports reproduce it, and commit the trace and the record together.
