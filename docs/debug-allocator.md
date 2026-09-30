# The debug allocator

Both ports can run as a **debug allocator**: a port of HPHA's `DEBUG_ALLOCATOR` mode that
notices heap misuse when it can, and tells you where the block came from. In Rust it is the
opt-in `debug-allocator` Cargo feature of `orisnik`; in Zig it is the `debug` field of the
`comptime` config of `orisnitsa`. With it off (the default) none of it exists in the build:
no fields, no code, no cost.

> **Status:** implemented on `main`; it ships with v0.2.0, which is not released yet. Until
> then depend on the repository (see below). The names in this guide are the ones v0.2.0 will
> have.

## What it does

| Mistake | Caught? | When |
|---|---|---|
| **Overrun** — writing past the end of a block, into its 16 guard bytes | ✅ | on `free` / `realloc` / `resize` of that block, and in `check()` |
| **Double free**, or freeing a pointer the allocator never produced | ✅ (see the caveat below) | on the `free` |
| **Wrong sized free** — `free_with_size(ptr, n)` / `freeWithSize` with the wrong `n` | ✅ | on the `free` |
| **Leak** — a block still live when the allocator is dropped / `deinit`ed | ✅ | at drop / `deinit` |
| **Inconsistent record** — a record claiming more bytes than its block holds | ✅ | `check()`, and the leak audit at drop |
| **Read of uninitialized memory** | 🔎 a hint | fresh blocks are filled with the repeating bytes `FF C0 C0 FF` (a quiet NaN when read as an `f32`), so a read shows *that* instead of plausible leftovers. Not `calloc` (zeroed), and not the tail a `realloc` grew |
| **Read after free** | 🔎 a hint | freed blocks are filled with the same pattern — except the first 8 bytes of blocks of up to 240 bytes, which hold the free list's link |
| **Underrun** (writing *before* a block) | ❌ not reliably | usually invisible; occasionally it lands in the neighboring block's guard or the allocator's header and is reported against the *wrong* block |
| **Overrun by more than 16 bytes**, or by any amount that lands in a block's slack | ❌ | only what lands in the 16 guard bytes is seen |
| **Use after free, write** | ❌ | not detected (the fill is a hint for reads only) |

**Caveats.** A double free is only caught while the block is still free: if the allocator
has already handed the same address out again, the stale `free` succeeds silently, and it is
the *legitimate* owner's later `free` that panics — blaming the wrong site. And requests
smaller than 8 bytes are rounded up to 8, so an overrun that stays inside those 8 bytes is not
seen either.

Detected corruption **panics** (fail fast: a heap that has corrupted itself is not worth
continuing with). `check()` is the way to *ask* instead, and get an error back.

## Turning it on

**Rust** — `Cargo.toml` (v0.2.0 is not on crates.io yet, so point at the repository; once it
ships this becomes `orisnik = { version = "0.2", features = ["debug-allocator"] }`):

```toml
[dependencies]
orisnik = { git = "https://github.com/PCfVW/oris", features = ["debug-allocator"] }
```

**Zig** — instantiate the generic instead of using the plain `Orisnitsa`:

```zig
const orisnitsa = @import("orisnitsa");

const Debug = orisnitsa.OrisnitsaWith(.{ .debug = true });
var backing: Debug = .init();
defer backing.deinit();                    // required, see "Leaks" below
const gpa = orisnitsa.allocator(&backing); // a std.mem.Allocator, as usual
```

`OrisnitsaWith(.{})` is exactly the plain `Orisnitsa`; `allocator()` accepts either.

## A first run

Both ports ship a small program that makes a one-byte overrun on purpose and asks the
allocator about it:

```text
cargo run --example catch_an_overrun --features debug-allocator     # from Rust/
zig build example                                                    # from Zig/
```

The Rust program prints this to **standard output**:

```text
check() found: guard bytes overwritten, memory was written past the end of the block (block 0x1c759940000, requested 24 bytes)
check() after repair: true
REPORT =================================================
Total requested size=40 bytes
Total allocated size=65536 bytes
Currently allocated blocks:
ptr=0x1c759940000, size=24
===========================================================
drop panicked: memory leaked: 1 allocation(s) still live when the allocator was dropped (see the report above)
```

It then leaks its one block on purpose, so **standard error** also gets the drop-time leak
report — the same layout as [Leaks](#leaks) below, with a long callstack — before the panic the
program catches and prints as the last line above. The Zig program prints its lines to standard
error, says `check() found Corruption: guard bytes overwritten…`, and does not leak (a leak
would end its process with a panic); it stops after the report.

- **`requested`** is the bytes you asked for (at least 8) **plus 16 guard bytes per block** —
  24 + 16 = 40.
- **`allocated`** is what the allocator has mapped from the OS, in whole pages (64 KiB for the
  small-block path).

The sources are [`Rust/examples/catch_an_overrun.rs`](../Rust/examples/catch_an_overrun.rs) and
[`Zig/examples/catch_an_overrun.zig`](../Zig/examples/catch_an_overrun.zig). CI builds and
runs both and pins the lines this guide quotes from them; the snippets in this guide are
excerpts of them.

## The error messages

Every corruption message names the block's address and, for a block the allocator knows, where
it was allocated. They are lowercase, with no trailing period, and their first line is
identical in both ports.

- **`guard bytes overwritten, memory was written past the end of the block (block 0x…, requested N bytes)`**
  — Something wrote beyond the `N` bytes that were requested. Look at the code that fills that
  block: an off-by-one in a loop bound, a `strcpy` without room for the terminator, a `realloc`
  whose new size was not used for the copy. The callstack that follows says which allocation
  it was; the culprit is the code writing to it.
- **`pointer was not allocated by this allocator or was already freed (block 0x…)`** — A double
  free, a free of a pointer from another allocator (or the stack), or a free through the wrong
  allocator instance. The message cannot tell which of these it was, but a double free is by
  far the usual cause: look for two owners of one pointer.
- **`free size does not match allocation size (block 0x…, allocated as A bytes, freed as B)`**
  — A sized free with the wrong size. The sized frees are a fast path that trusts the size;
  the debug allocator does not. The size to pass is the block's *current* size: a sized free is
  only valid for a block that was never reallocated (after a `realloc` the recorded size is the
  new one, and the old one is reported as a mismatch). Use plain `free` for blocks that may have
  been reallocated.
- **`recorded size exceeds the block's size (block 0x…, recorded N bytes, block holds M)`** —
  Reported by `check()` and the drop-time audit. The allocator's own bookkeeping disagrees with
  the block, which points at a wild write into the allocator's memory rather than into a
  block's guard.
- **`memory leaked: N allocation(s) still live when the allocator was dropped (see the report above)`**
  — See [Leaks](#leaks). (No address: it is about the allocator, not a block.)
- **`records can no longer be audited (a corruption was already detected)`** — Rust's `check()`
  after an earlier detection: the records may be stale, so it refuses rather than read them.

For an *owned* Rust instance a message continues with the allocation callstack, for example
(cut):

```text
allocated at:
   0: std::backtrace_rs::backtrace::win64::trace
   …
   9: catch_an_overrun::main
             at .\examples\catch_an_overrun.rs
```

Rust resolves symbols and starts the trace with the allocator's own frames — skip to your own.
Zig prints raw return addresses, `allocated at (return addresses, symbols not resolved):`.
Those are run-time addresses: with address-space randomization they differ from run to run, so
subtract the module's load base before `addr2line` / `llvm-symbolizer` can use them.

## Leaks

A leak is detected when the allocator is dropped (Rust: `Drop for Orisnik`) or `deinit`ed
(Zig). If any block is still live it prints a report to standard error — every live block with
its address, size and callstack — releases every idle page, and **then panics**. Zig, for one
leaked 24-byte block:

```text
orisnitsa: 1 allocation(s) were still live when the allocator was dropped
REPORT =================================================
Total requested size=40 bytes
Total allocated size=65536 bytes
Currently allocated blocks:
ptr=0x14483080000, size=24
  0x7ff692a9d49c
  0x7ff692a9d418
===========================================================
thread 5340 panic: memory leaked: 1 allocation(s) still live when the allocator was dropped (see the report above)
```

Rust prints the same lines with an `orisnik:` prefix, a resolved callstack, and Rust's usual
`thread 'main' panicked at …` wrapper around the panic message.

- The drop-time report lists blocks in the allocator's record-storage order (which reuses
  the slots of freed blocks), so read it as "in no particular order". `report()` and `check()`
  on a *live* allocator list them by address.
- A page holding a live block stays mapped (the block was leaked, and it is not reclaimed
  behind your back).
- **Zig:** `deinit()` is not optional, in any build — Zig has no destructors, so it is what
  returns the memory. Under `debug` it also does the leak check. A Zig panic ends the process,
  so a leak is the last thing the program does.
- **Rust:** a leak is a panic during `drop`; it is skipped if the thread is already
  panicking, so it never turns one panic into an abort. Dropping *without* the feature is
  silent, and returns idle memory to the OS.
- **Rust, after a caught corruption panic:** the records may be stale, so the drop does not
  audit them; it prints one line saying so instead.

## Asking instead of panicking: `check()` and `report()`

| | Rust | Zig |
|---|---|---|
| Audit every live block | `allocator.check() -> Result<(), OrisError>` | `try allocator.check(&diagnostic)` |
| Print a report | `allocator.report()` (stderr) | `allocator.reportToStderr()` |
| Report into your own sink | `allocator.write_report(&mut string)` | `try allocator.report(&writer)` |
| Bytes requested (incl. guards) | `allocator.requested()` | `allocator.requested()` |
| Sized free | `free_with_size` | `freeWithSize` |

`check()` walks every live record and verifies its guard and size, stopping at the first
problem. In Rust the error is `OrisError::Corruption(message)` (`Display` gives the message);
in Zig it is `error.Corruption` and the message goes into the `Diagnostic` you pass (or `null`
if you only care that it failed). `report()` prints the totals and one entry per live block, as
in the example above. Use them from a test, or as a periodic self-check in a long-running
program.

## Rust as the `#[global_allocator]`

```rust
use orisnik::Orisnik;

#[global_allocator]
static ALLOCATOR: Orisnik = Orisnik::new();

fn main() {
    // ... the program ...
    ALLOCATOR.check().expect("the heap is corrupt");
    ALLOCATOR.report(); // to stderr
}
```

(The integration test [`Rust/tests/debug_global_allocator.rs`](../Rust/tests/debug_global_allocator.rs)
runs exactly this shape against a real workload.) Three things to know:

1. **Build with `panic = "abort"`** (`[profile.dev]` / `[profile.release]`). A corruption
   panic raised from inside the global allocator, on a code path that is itself allocating, is
   not one to unwind through. (The example program is the opposite: it catches a panic, so it
   needs the default `panic = "unwind"`.)
2. **It records no callstacks.** Capturing a `Backtrace` allocates and takes a lock inside
   `std` that is not re-entrant; doing it from the allocator deadlocks against any
   application backtrace. So an instance used through `GlobalAlloc` reports the block, the size
   and the cause, but not *where it was allocated*. Use an owned instance (below) for that.
3. **Single-threaded only**, as for the plain allocator: `Orisnik` has no locking, and that
   includes the default `cargo test` harness. See the `# Thread safety` section of its docs.

A `static` is never dropped, so there is no leak check at exit; call `check()` / `report()`
yourself where you want one.

## An owned instance, for tests

An owned `Orisnik` (not the global one) records callstacks and checks for leaks when dropped —
the best fit for a test that wants to know its code frees everything. It must not **move**
after first use (its internal lists are bound to its address), so keep it in a `Box`:

```rust
let allocator = Box::new(Orisnik::new());
let block = allocator.alloc(24).expect("out of memory");
// … use it …
unsafe { allocator.free(Some(block)) };
// dropped here: panics, after a report, if anything is still live
```

Moving an instance that has already been used is a bug the crate cannot always prevent. Debug
builds panic when they notice it. In release builds it is undefined: further `alloc` / `free`
calls on the moved instance can hang or corrupt, and only dropping one is safe — it leaks
rather than walk stale structures.

## What it costs

- **Memory:** 16 guard bytes per block (and requests under 8 bytes are rounded up to 8), plus
  one record per live block in pages of their own. A Zig record is a small fixed-size entry
  with an 8-frame callstack; a Rust record holds a `Backtrace`, which is variable-size and
  lives on the system heap.
- **Time:** every allocation and free does bookkeeping — a tree lookup, a fill of the payload,
  a guard write and check — and an owned Rust instance captures a backtrace per allocation.
  In one measurement (Rust, release build, 24-byte allocate-and-free pairs) that was about
  90 times slower than without the feature. This is a mode for tests and debugging, not for
  production.
- **Behavior:** the two ports produce the same *allocator* state for the same sequence of
  calls; what they record for diagnostics differs in detail (callstack depth and symbols,
  record page size), and that is not part of the compatibility promise.

## Limits, again, in one place

Single-threaded only. No reliable detection of underruns, of overruns that skip the 16 guard
bytes, or of writes after free. A pointer from another allocator is reported as "not allocated
by this allocator" without saying whose it is. No debug surface in the C ABI (`oris_*`) — a
Rust build with the feature does abort at `oris_destroy` if the instance leaked.
