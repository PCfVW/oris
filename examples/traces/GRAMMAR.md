# Trace and Transition-Record Formats — Grammar Specification

The cross-port invariant ([`ROADMAP.md`](../../ROADMAP.md#cross-language-invariant)) says that an
identical allocation sequence drives `orisnik` (Rust), `orisnitsa` (Zig) and the HPHA reference
(C++) through identical internal state transitions. Checking that needs two file formats, both
specified here:

1. **The trace** (`*.trace`) — a language-agnostic allocation sequence: *what the caller did*.
   Input to every replayer.
2. **The transition record** (`*.record`) — what one allocator did in response, operation by
   operation, with every raw address normalized away. Output of every replayer. Two
   implementations satisfy the invariant on a trace exactly when their records are
   byte-identical.

Each format has two layers, as in the priority-queue project's graph grammar:

- **Contract grammar** — what a conformant reader accepts.
- **Canonical output** — what a conformant writer emits, byte for byte. The canonical form is one
  instance of the contract grammar.

The trace's contract grammar is deliberately tolerant (tabs, runs of spaces, comment and blank
lines, CRLF) because traces are written by hand as well as by `tracegen` and the recorders. The
record has *only* a canonical form: it is never written by hand, and byte-identity is the whole
point of it.

The trace subsystem is called **`letopis`** (*летопис*, "chronicle"): the `trace` Cargo feature
in `orisnik`, `Config.trace` in `orisnitsa`. See [`docs/traces.md`](../../docs/traces.md) for
how to record, replay and compare traces, and [`EVENTS.md`](EVENTS.md) for where each record
event is emitted in each implementation.

---

## 1. The trace

### 1.1 Contract grammar (ISO/IEC 14977 EBNF)

```ebnf
(* oris-trace.ebnf — allocation-sequence trace, version 1 *)

trace              = header , { line } ;

header             = [ sp ] , "oris-trace" , sp , "1" , [ sp ] , eol ;

line               = blank_line | comment_line | op_line ;
blank_line         = [ sp ] , eol ;
comment_line       = [ sp ] , "#" , { text_char } , eol ;
op_line            = [ sp ] , op , [ sp ] , eol ;

op                 = alloc | alloc_aligned | calloc
                   | realloc | realloc_aligned | resize | size
                   | free | free_sized | free_sized_aligned
                   | purge ;

alloc              = "alloc"              , sp , handle , sp , number ;
alloc_aligned      = "alloc_aligned"      , sp , handle , sp , number , sp , number ;
calloc             = "calloc"             , sp , handle , sp , number , sp , number ;
realloc            = "realloc"            , sp , handle , sp , number ;
realloc_aligned    = "realloc_aligned"    , sp , handle , sp , number , sp , number ;
resize             = "resize"             , sp , handle , sp , number ;
size               = "size"               , sp , handle ;
free               = "free"               , sp , handle ;
free_sized         = "free_sized"         , sp , handle , sp , number ;
free_sized_aligned = "free_sized_aligned" , sp , handle , sp , number , sp , number ;
purge              = "purge" ;

handle             = "h" , number ;
number             = "0" | nonzero_digit , { digit } ;

nonzero_digit      = "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
digit              = "0" | nonzero_digit ;
sp                 = ( " " | tab ) , { " " | tab } ;
eol                = [ cr ] , lf ;
text_char          = ? any Unicode scalar value except carriage return and line feed ? ;

tab                = ? US-ASCII character 9 (horizontal tab) ? ;
cr                 = ? US-ASCII character 13 (carriage return) ? ;
lf                 = ? US-ASCII character 10 (line feed) ? ;
```

Every `number` must fit in an unsigned 64-bit integer; a reader rejects one that does not. The
operation keywords are matched as whole tokens: `alloc_aligned` is never read as `alloc`
followed by garbage, because a token ends only at `sp` or `eol`.

### 1.2 What each operation means

Every operation is one call on the allocator's public API. The argument order is the API's.

| Operation | Rust (`Orisnik`) | Zig (`Orisnitsa`) | HPHA (`allocator`) |
|---|---|---|---|
| `alloc h S` | `alloc(S)` | `alloc(S)` | `alloc(S)` |
| `alloc_aligned h S A` | `alloc_aligned(S, A)` | `allocAligned(S, A)` | `alloc(S, A)` |
| `calloc h N S` | `calloc(N, S)` | `calloc(N, S)` | `calloc(N, S)` |
| `realloc h S` | `realloc(p, S)` | `realloc(p, S)` | `realloc(p, S)` |
| `realloc_aligned h S A` | `realloc_aligned(p, S, A)` | `reallocAligned(p, S, A)` | `realloc(p, S, A)` |
| `resize h S` | `resize(p, S)` | `resize(p, S)` | `resize(p, S)` |
| `size h` | `size(p)` | `querySize(p)` | `size(p)` |
| `free h` | `free(p)` | `free(p)` | `free(p)` |
| `free_sized h S` | `free_with_size(p, S)` | `freeWithSize(p, S)` | `free(p, S)` |
| `free_sized_aligned h S A` | `free_with_size_aligned(p, S, A)` | `freeWithSizeAligned(p, S, A)` | `free(p, S, A)` |
| `purge` | `purge()` | `purge()` | `purge()` |

**Handles.** A handle `hN` names a pointer symbolically, so a trace never contains an address.
At any point a handle is either *unbound* (every handle starts unbound) or *bound* — to a
pointer, or to null.

- `alloc`, `alloc_aligned` and `calloc` bind their handle to the result (null when the call
  returns null, as `alloc h 0` does).
- `realloc` and `realloc_aligned` pass the handle's pointer — null if the handle is unbound or
  bound to null — and rebind the handle to the result. A `realloc` to size 0 frees, returns
  null, and so leaves the handle bound to null.
- `free`, `free_sized` and `free_sized_aligned` pass the handle's pointer and unbind the handle.
- `resize` and `size` pass the handle's pointer and leave the binding as it is.

A handle number has no meaning beyond identity: `h7` need not follow `h6`, and an unbound
handle may be bound again.

### 1.3 Semantic constraints

A trace that is syntactically valid can still describe a call sequence with no defined result:
a double free, say, or one of the inputs on which the 2007 reference is itself broken. A
conformant **reader rejects** a trace that breaks any rule below, before replaying any of it, so a
replayer never executes undefined behaviour and the C++ oracle never meets an input that
[`Cpp/ERRATA.md`](../../Cpp/ERRATA.md) records as broken upstream.

| # | Rule | Why |
|---|---|---|
| C1 | `alloc`, `alloc_aligned` and `calloc` name an **unbound** handle. | Rebinding a bound handle would lose its pointer: a leak, and a handle that no longer names one block. |
| C2 | `free`, `free_sized`, `free_sized_aligned`, `resize` and `size` name a **bound** handle. | An unbound handle is either never allocated or already freed: a use-after-free or double free. (A handle bound to null is fine; every one of these calls accepts null.) |
| C3 | Every alignment is 0 or a power of two, and at most **65536**. | HPHA asserts the power of two. Above 65536 (HPHA's `PAGE_SIZE`), `tree_extract_aligned` compares *absolute* addresses modulo the alignment, and the OS gives no guarantee about those; at or below it, every mapping is 65536-aligned in all three implementations, so the decision depends only on offsets. |
| C4 | Every size is at most **2³⁰** (1 GiB), and so is the product `N × S` of a `calloc` (its factors are bounded only through it). | Excludes E1 and E2 (wrapping size arithmetic). It also keeps every request one a real machine serves: an out-of-memory result would depend on the OS, so the record would too. |
| C5 | `resize` sizes are at least 1. | E7: HPHA asserts `size > 0`. |
| C6 | `free_sized h S` only directly after the handle was bound by `alloc h S`, or by `calloc h N M` with `N × M = S`, or by `alloc_aligned h S A` with `A ≤ 8` — no `realloc`, `realloc_aligned` or `resize` of the handle in between — and `S ≥ 1`. | The size of a sized free selects a bucket (`bucket_spacing_function(S)`); after a realloc that stayed in its slot, a different size would select a different bucket than the one the block lives in. `S = 0` is E3. |
| C7 | `free_sized_aligned h S A` only directly after the handle was bound by `alloc_aligned h S A`, with the same `S` and `A`, under the same no-intervening-call rule as C6; `S ≥ 1` and `A ≥ 1`. | As C6, with the alignment also selecting the bucket. `A = 0` is E4. |
| C8 | `realloc_aligned h S A` with `A > 256` requires `S > 256`. | E5: when the block is in a bucket, HPHA copies the whole slot into a tree block that a small `S` may not cover. The ports fix this; the reference does not, and the gate compares against the reference. |

These rules are what the implementations need, not a style guide: the generator emits nothing
else, and the recorders write only what they observed, which satisfies C1–C2 by construction.
The recorders do not check C3–C8 — a program can make calls a trace may not contain — so
replaying a recorded trace can be refused; see [`docs/traces.md`](../../docs/traces.md).

### 1.4 Canonical output

Writers (`tracegen`, the recorders) emit:

- UTF-8 with no BOM; LF line endings; exactly one trailing `\n`.
- The header `oris-trace 1`, then comment lines (`# ` and free text) if any, then one operation
  per line.
- Tokens separated by exactly one space; no leading or trailing whitespace; no blank lines.
- Numbers in decimal with no leading zeros.

### 1.5 Reader and writer obligations

- **Writers MUST** emit canonical output and only traces that satisfy §1.3.
- **Readers MUST** accept the whole contract grammar (including CRLF and tab separators), MUST
  reject a trace that violates §1.3 before replaying it, and MUST report the 1-based line number
  of the first offending line.
- **Readers MAY** accept a final line that lacks its `eol`.
- **Readers treat the file as bytes.** An operation line is ASCII or a syntax error; the bytes of
  a comment are skipped unread, so a comment need not be valid UTF-8 (all three replayers accept
  it).

### 1.6 Annotated example

```text
oris-trace 1
# The annotated example of GRAMMAR.md section 1.6: a small allocation, a large one,
# a realloc that grows in place, a sized free, a free, and a purge.
alloc h0 24
alloc h1 1000
realloc h1 2000
free_sized h0 24
free h1
purge
```

- `alloc h0 24` takes the bucket path: 24 bytes is at most 256, so the request goes to bucket
  2 (24-byte slots).
- `alloc h1 1000` takes the tree path and maps a 64 KiB arena.
- `realloc h1 2000` finds the rest of the arena free right after the block and grows into it in
  place, so the pointer does not move.
- `free_sized h0 24` is allowed by C6: the handle was bound by `alloc h0 24` and nothing has
  touched it since.
- `free h1` needs no size: the allocator recovers everything from the pointer.
- `purge` returns the now-idle arena and the empty bucket page to the OS.

---

## 2. The transition record

### 2.1 Grammar (ISO/IEC 14977 EBNF — canonical only)

```ebnf
(* oris-record.ebnf — transition record, version 1 *)

record        = "oris-record 1" , lf , { entry } , summary ;

entry         = "#" , number , " " , canonical_op , " -> " , result , " a=" , number , lf ,
                { "  " , event , lf } ;

(* A trace operation (section 1.1) in its canonical form (section 1.4): the same productions
   with every `sp` a single " ". *)
canonical_op  = ? op of section 1.1, each sp replaced by exactly one " " ? ;
result        = location | "null" | number | "-" ;

event         = map | unmap
              | page_spawn | page_release | page_full | page_refill
              | split | shift | merge
              | tree_insert | tree_erase | list_push | list_erase | mr ;

map           = "map " , ( "b" | "t" ) , " " , mapping , " " , number ;
unmap         = "unmap " , mapping , " " , number ;
page_spawn    = "page+ "       , bucket , " " , mapping ;
page_release  = "page- "       , bucket , " " , mapping ;
page_full     = "page-full "   , bucket , " " , mapping ;
page_refill   = "page-refill " , bucket , " " , mapping ;
split         = "split " , location , " " , number ;
shift         = "shift " , location , " " , number ;
merge         = "merge " , location ;
tree_insert   = "tree+ " , location , " " , number , " " , ( "chain" | "node" ) ,
                " rot=" , number ;
tree_erase    = "tree- " , location , " " , number , " " , ( "link" | "promote" | "node" ) ,
                " rot=" , number ;
list_push     = "list+ " , location , " " , number ;
list_erase    = "list- " , location , " " , number ;
mr            = "mr " , ( location | "-" ) ;

summary       = "end ops=" , number , " maps=" , number , " unmaps=" , number ,
                " rotations=" , number , " allocated=" , number , lf ;

location      = mapping , "+0x" , hex_digit , { hex_digit } ;
mapping       = "m" , number ;
bucket        = "b" , number ;
number        = "0" | nonzero_digit , { digit } ;

nonzero_digit = "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
digit         = "0" | nonzero_digit ;
hex_digit     = digit | "a" | "b" | "c" | "d" | "e" | "f" ;
lf            = ? US-ASCII character 10 (line feed) ? ;
```

### 2.2 Normalization

A record must not depend on where the OS put anything, so it contains no raw address.

- **Mappings.** Every OS mapping the allocator makes — a bucket page or a tree arena — gets the
  next id `m0`, `m1`, … in the order the mappings are made. An id is never reused, even after
  its mapping is returned to the OS.
- **Locations.** An address inside a live mapping is written `m<id>+0x<offset>`: the mapping's
  id and the byte offset from its base, in lowercase hexadecimal with no leading zeros (`+0x0`
  for the base itself).

This is exact, not approximate: every bucket page and tree arena is 65536-aligned in all three
implementations, and every block and slot sits at an offset that is a pure function of the
operation sequence.

### 2.3 Entries

Each trace operation produces one entry. Operations are numbered from 0, counting only operation
lines (not comments or blanks). The entry's first line is:

```text
#<index> <canonical op> -> <result> a=<allocated() after the operation>
```

`<result>` is a location or `null` for an operation that returns a pointer; the returned number
for `resize` and `size`; `-` for `free`, `free_sized`, `free_sized_aligned` and `purge`.

The operation's events follow, one per line, indented two spaces, **in the order the allocator
performed them**. An event names memory as it was at the moment the event happened (`merge`
names the block that is about to disappear; `unmap` names the mapping before its id is retired).

| Event | Meaning |
|---|---|
| `map b m<id> <bytes>` | A bucket page was mapped from the OS. |
| `map t m<id> <bytes>` | A tree arena was mapped from the OS. |
| `unmap m<id> <bytes>` | A page or arena was returned to the OS. |
| `page+ b<i> m<id>` | A new page entered bucket `i`'s page list, at the front. |
| `page- b<i> m<id>` | An empty page left bucket `i`'s page list (`purge`). |
| `page-full b<i> m<id>` | A page became full and moved to the back of bucket `i`'s list. |
| `page-refill b<i> m<id>` | A full page received a freed slot and moved to the front. |
| `split <blk> <size>` | The tree block at `<blk>` was cut to `<size>` payload bytes; the remainder became a new free block right after it. |
| `shift <blk> <n>` | The tree block at `<blk>` moved `<n>` bytes forward (an alignment pad too small to split off); its physical predecessor grew by `<n>`. |
| `merge <blk>` | The tree block at `<blk>` was absorbed into its physical predecessor (coalescing, or a realloc/resize growing into a free neighbour). |
| `tree+ <blk> <size> chain\|node rot=<k>` | A free block entered the red-black tree of free blocks: linked into the chain of an equal-size node (`chain`), or as a new tree node (`node`), costing `k` rotations. |
| `tree- <blk> <size> link\|promote\|node rot=<k>` | A free block left the tree: unlinked from a chain (`link`), as a chain head whose successor took its place (`promote`), or as a tree node (`node`), costing `k` rotations. |
| `list+ <blk> <size>` / `list- <blk> <size>` | A free block of at most 256 bytes entered / left the small free list. |
| `mr <blk>` / `mr -` | The most-recently-freed block cache now holds `<blk>` / is empty. |

`<blk>` is the location of the block's **header**, not of its payload; `<size>` is the block's
payload size as its header records it.

### 2.4 Summary

The last line totals the run: operations replayed, mappings made and returned, rotations
performed, and `allocated()` at the end. It is written **before** the allocator is dropped or
deinitialized: teardown is outside the invariant (see the roadmap's scope note), so the record
says nothing about it.

### 2.5 Annotated example

The record of the trace in §1.6 (committed as `handwritten/grammar-example.record`):

```text
oris-record 1
#0 alloc h0 24 -> m0+0x0 a=65536
  map b m0 65536
  page+ b2 m0
#1 alloc h1 1000 -> m1+0x20 a=131072
  map t m1 65536
  split m1+0x10 1008
  mr m1+0x410
#2 realloc h1 2000 -> m1+0x20 a=131072
  mr -
  merge m1+0x410
  split m1+0x10 2000
  mr m1+0x7f0
#3 free_sized h0 24 -> - a=131072
#4 free h1 -> - a=131072
  mr -
  merge m1+0x7f0
  mr m1+0x10
#5 purge -> - a=0
  tree+ m1+0x10 65488 node rot=0
  mr -
  tree- m1+0x10 65488 node rot=0
  unmap m1 65536
  mr -
  page- b2 m0
  unmap m0 65536
end ops=6 maps=2 unmaps=2 rotations=0 allocated=0
```

- `#0`: the first bucket allocation maps a page (`m0`), threads it into bucket 2's page list,
  and hands out slot 0, at the page's base.
- `#1`: the tree maps a 64 KiB arena (`m1`). Its one free block's header sits right after
  the opening fence (`+0x10`), its payload after that (`+0x20`, the pointer returned). The
  request (1000 bytes, rounded up to 1008) is split off, and the remainder (`+0x410`)
  becomes the most-recently-freed block.
- `#2`: growing to 2000 bytes empties the cache (`mr -`), absorbs that free neighbour in
  place (`merge`), splits the excess off again and caches it.
- `#3`: the bucket slot goes back to its page; nothing about the page's place in its list
  changes, so there is no event.
- `#4`: the freed block absorbs its free successor, then becomes the most-recently-freed
  block.
- `#5`: `purge` flushes the cached block into the tree, finds it spans the whole arena,
  takes it out again and unmaps the arena; flushes the (now empty) cache once more, as
  HPHA's `tree_purge` does; then releases the empty bucket page.

---

## 3. Evolution policy

Both formats carry a version in their first line (`oris-trace 1`, `oris-record 1`). Adding an
operation, an event, or a field to an existing line changes the version, and every reader and
writer in all three implementations moves to it in the same commit. A change to *which* events
an allocator emits — a new hook, or one moved — is a change under the cross-port invariant: it
lands in Rust, Zig and the C++ patch together, and the committed records are regenerated from the
C++ oracle.

## References

- ISO/IEC 14977:1996 — *Information technology — Syntactic metalanguage — Extended BNF.*
- [`Cpp/ERRATA.md`](../../Cpp/ERRATA.md) — the reference's known defects, entries E1–E10, each with
  its trace-visibility verdict.
