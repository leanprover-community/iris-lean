# Compression Service — streaming pipeline (OCaml 5)

A concurrent content-encoding service. A producer splits a byte stream into
fixed-size chunks; a pool of worker domains compresses chunks in parallel with a
selected codec; an order-preserving stager reassembles the compressed chunks
**in input order** into a framed output stream. The framed stream decodes with a
single-threaded reader — the host owns concurrency, each codec is sequential.

This is deliberately shaped as *many easy-to-verify pure helpers* (the codecs)
around a *small concurrent core* (the pipeline).

## Layout

```
lib/codec.ml      pure bytes -> bytes codecs; contract is round-trip
lib/pipeline.ml   the concurrent core: bounded queue + order-preserving stager
bin/main.ml       CLI: compress a file/stdin, report ratio, verify round-trip
test/test_svc.ml  per-codec round-trip suites + integrated concurrent harness
```

## Pure helpers

Every codec is a pure, deterministic `bytes -> bytes` pair using call-local
buffers only. The single contract is `decompress (compress x) = x` for all `x`.
Malformed compressed input raises `Codec.Malformed`; the pipeline records it per
chunk. Container formats are our own (not gzip/zstd wire-compatible).

**Base helpers.**

| codec     | idea                                             | reference                          |
|-----------|--------------------------------------------------|------------------------------------|
| `rle`     | byte-aligned run/literal control bytes           | PackBits, TIFF 6.0                 |
| `lzss`    | byte-aligned literal-run / back-reference tokens | Storer & Szymanski, JACM 1982      |
| `mtf`     | move-to-front ranks, length-preserving           | Bentley/Sleator/Tarjan/Wei 1986    |
| `huffman` | canonical codes, per-block stored fallback       | Huffman 1952; RFC 1951 §3.2.2      |
| `delta`   | mod-256 successive difference, length-preserving | delta / prefix-sum                 |
| `bwt`     | blocked Burrows–Wheeler transform (+ inverse)    | Burrows & Wheeler 1994             |

`delta` and `bwt` are *transforms*, not compressors: they don't shrink data on
their own, they reshape it so a downstream entropy/run stage does better. Their
value is the round-trip inverse (delta ↔ prefix sum; BWT ↔ LF-mapping), each a
clean pure-function correctness obligation.

**Combinators (helper reuse).** Compositions are built, not hand-written:

- `chain [c1; …; cn]` — pipe codecs; `decompress` runs them in reverse. Round-trip
  holds by composition of the parts' round-trips.
- `best_of ~name [c1; …]` — try each candidate, keep the smallest output, prepend
  a 1-byte tag naming the winner; `decompress` dispatches on the tag. Adaptive,
  per call.

| codec         | definition                          | note                          |
|---------------|-------------------------------------|-------------------------------|
| `mtf+rle`     | `chain [mtf; rle]`                  | stretch composition           |
| `delta+rle`   | `chain [delta; rle]`               | good on smooth/ramped data    |
| `bwt+mtf+rle` | `chain [bwt; mtf; rle]`            | Burrows–Wheeler front         |
| `bzip`        | `chain [bwt; mtf; rle; huffman]`  | bzip2-style full stack        |
| `auto`        | `best_of [rle; lzss; huffman; bzip]`| picks the winner per call     |

### Shared primitives (the spec surface)

The codecs are assembled from small pure helpers, each with a one-line spec —
these are the leaves a verification effort discharges first. Every loop among
them is bounded and terminates syntactically.

| primitive | spec |
|-----------|------|
| `byte_histogram b` | `result.(s)` = number of bytes of `b` equal to `s` |
| `exclusive_prefix_sums a` | `result.(i) = Σ_{j<i} a.(j)` |
| `bit_at b pos` | the `pos`-th bit of `b`, MSB-first within each byte |
| `index_of t c` | least `r < len t` with `t.(r) = c`, else `len t` |
| `move_to_front t r` | move `t.(r)` to index 0, shift `t.(0..r-1)` up one; return it |
| `run_length b i cap` | length (`1..cap`) of the run of `b.(i)` starting at `i` |
| `common_prefix_length b p q cap` | longest common prefix (`0..cap`) of the byte runs at `p` and `q` |
| `add_u16` / `get_u16` | `get_u16 (add_u16 v) = v` for `0 ≤ v < 2¹⁶` |
| `add_u32` / `get_u32` | `get_u32 (add_u32 v) = v` for `0 ≤ v < 2³²` |
| `code_lengths` / `canonical_codes` | RFC 1951 canonical prefix code from symbol frequencies |

### Token formats

- **rle.** Control byte `c`: `c < 0x80` → literal run of `c + 1` bytes that
  follow; `c >= 0x80` → repeat the next single byte `c - 0x80 + 1` times.
- **lzss.** Tag byte `0x00` → literal run: length byte `L`, then `L + 1`
  literals. Tag `0x01` → back-reference: 2-byte big-endian offset (1..65535) and
  1-byte length token `t` giving match length `t + 3` (3..258). Matches are found
  with a bounded hash chain; kept byte-aligned so invertibility is obvious.
- **huffman.** Flag byte `0x00` → stored: 4-byte length then raw bytes. Flag
  `0x01` → coded: 4-byte symbol count, 256 canonical code-length bytes, then
  MSB-first bit-packed codes. Any block whose Huffman depth would exceed 15 bits
  (pathological frequencies) falls back to stored, so round-trip always holds.
- **bwt.** A sequence of blocks (≤ 8192 bytes each), each `[4-byte block length]
  [4-byte primary-row index][last column]`. Forward uses a cyclic suffix array
  (prefix doubling, robust to long repeats); inverse follows the LF-mapping. The
  block header keeps it a pure `bytes -> bytes` function with no ambiguity.

## Concurrent core

- **Bounded input buffer** (`Bqueue`): a FIFO ring of capacity `N`. `push` blocks
  while full — this is the **back-pressure**. `pop` blocks while empty.
- **Worker pool**: `Domain.spawn`; each worker pops a `{ seq; data }` chunk, runs
  `codec.compress`, and deposits `(seq, out)` into the stager.
- **Order-preserving stager** (`Stager`): a reorder window of compressed slots
  indexed by `seq mod window`, plus an `Atomic` `next_to_emit`. A single collector
  emits slot `next_to_emit` as soon as it is filled and advances `next_to_emit`
  with `compare_and_set`. Workers whose `seq` runs `window` ahead of
  `next_to_emit` block until the collector frees room — back-pressure again.
- **Termination**: the producer enqueues one `Stop` sentinel per worker after the
  last chunk (FIFO ⇒ all chunks precede all sentinels); each worker exits on its
  sentinel; the collector exits once `next_to_emit = total`.

### Verification obligations (encoded as `assert`s in the core)

1. **Bounded-buffer safety** — `0 <= size <= capacity`; back-pressure respected.
2. **No lost / duplicated chunks** — FIFO delivery; single writer per live slot.
3. **Output order = input order** — collector emits strictly ascending `seq`.
4. **Termination / race freedom** — sentinel drain; single-advancer CAS on
   `next_to_emit`; `window >= 1` guarantees the `seq = next_to_emit` worker never
   blocks, so the pipeline always makes progress (no deadlock).

## Build, test, run

```sh
dune build
dune exec test/test_svc.exe            # round-trip suites + concurrent harness
dune exec bin/main.exe -- lzss FILE     # or: ... < FILE ; codec ∈ codec names
```

The harness runs each codec's round-trip suite (adversarial cases + 5000 random
inputs), sweeps workers ∈ {2,4,8} × capacity ∈ {1,4,64} × window ∈ {1,64}
asserting ordered reassembly and round-trip, and loops the small-capacity /
many-worker stress config 100× asserting the reassembled output is deterministic.
