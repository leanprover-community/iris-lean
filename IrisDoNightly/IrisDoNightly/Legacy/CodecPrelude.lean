module

public import IrisDoNightly.Notation
public import IrisDoNightly.Syntax

@[expose] public section

namespace Iris.HeapLang.Codec

open Iris.HeapLang

/-!
# Codec stdlib (HeapLang models of the OCaml runtime pieces used by `Reference/codec.ml`)

`codec.ml` is written against OCaml's `bytes`, `Buffer`, `Array`, and `List`.  This file provides
HeapLang models of exactly the operations the codecs use, so the transcriptions read like the
source.

Representations:
* **`bytes`** — a pair `(ptr, len)`; `ptr` is the base of a contiguous block of `len` byte cells.
* **`Buffer`** — a reference `b ↦ ((arr, cap), size)`: a size-tracked, capacity-doubling array with
  random access, matching OCaml's growable `Buffer` (including `Buffer.nth`).
* **`Array`** (mutable int arrays) — a bare `ptr` with the length tracked by the caller, allocated by
  `allocn`.
* **`list`** — the usual sum-of-products: `none()` is nil, `some((hd, tl))` is cons.

Bytes are integers kept in `[0, 256)`; OCaml's `Char.code` / `Char.unsafe_chr` are identities here,
and `land 0xff` becomes `% 256` (with `+ 256` first where the argument may be negative).
-/

/-! ## Small arithmetic helpers -/

/-- `min a b`. -/
def minV : Val := hl_val% λ a b, if a ≤ b then a else b
/-- `max a b`. -/
def maxV : Val := hl_val% λ a b, if a ≤ b then b else a

/-! ## Mutable arrays -/

/-- `arrCopy src dst n` copies `n` cells `src.(0..n) → dst.(0..n)`. -/
def arrCopy : Val := hl_val%
  λ src dst n,
    (rec go i := if i < n then ((dst +ₗ i) ← !(src +ₗ i); go (i + #1)) else #()) #0

/-! ## `bytes` accessors -/

/-- `Bytes.length b`. -/
def blen : Val := hl_val% λ b, snd(b)
/-- `Bytes.get b i` (as an int in `[0,256)`). -/
def bget : Val := hl_val% λ b i, !(fst(b) +ₗ i)
/-- `Bytes.set b i x`. -/
def bset : Val := hl_val% λ b i x, (fst(b) +ₗ i) ← x
/-- `Bytes.create n` — a fresh zero-filled buffer of length `n`. -/
def bcreate : Val := hl_val% λ n, (allocn(n, #0), n)

/-- `Bytes.sub b off len` — a fresh copy of `b.(off .. off+len)`. -/
def bsub : Val := hl_val%
  λ b off len,
    let d := allocn(len, #0);
    (rec go i := if i < len then ((d +ₗ i) ← !(fst(b) +ₗ (off + i)); go (i + #1)) else #()) #0;
    (d, len)

/-! ## Growable `Buffer`

`buf ↦ ((arr, cap), size)`.  `arr` is the base of the backing array of capacity `cap`, of which the
first `size` cells are live. -/

/-- `Buffer.create n`. -/
def bufCreate : Val := hl_val%
  λ n,
    let cap := if n < #1 then #1 else n;
    ref(((allocn(cap, #0), cap), #0))

/-- `Buffer.length buf`. -/
def bufLength : Val := hl_val% λ buf, snd(!buf)
/-- `Buffer.nth buf i`. -/
def bufNth : Val := hl_val% λ buf i, !(fst(fst(!buf)) +ₗ i)

/-- `Buffer.add_char buf x` — append one byte, doubling the backing array when full. -/
def bufAddByte : Val := hl_val%
  λ buf x,
    let s := !buf;
    let arr := fst(fst(s));
    let cap := snd(fst(s));
    let size := snd(s);
    if size < cap then
      ((arr +ₗ size) ← x;
       buf ← ((arr, cap), size + #1))
    else
      let ncap := cap * #2;
      let narr := allocn(ncap, #0);
      &arrCopy arr narr size;
      (narr +ₗ size) ← x;
      buf ← ((narr, ncap), size + #1)

/-- `Buffer.add_subbytes buf src off len` — append `src.(off .. off+len)`. -/
def bufAddSubbytes : Val := hl_val%
  λ buf src off len,
    (rec go i :=
      if i < len then (&bufAddByte buf (!(fst(src) +ₗ (off + i))); go (i + #1)) else #()) #0

/-- `Buffer.add_bytes buf src` — append all of `src`. -/
def bufAddBytes : Val := hl_val%
  λ buf src, &bufAddSubbytes buf src #0 (snd(src))

/-- `Buffer.to_bytes buf` — a `bytes` view of the live prefix (shares the backing array; the buffer
is not used afterwards). -/
def bufToBytes : Val := hl_val%
  λ buf, let s := !buf; (fst(fst(s)), snd(s))

/-! ## Immutable lists (`injl(#())` = nil, `injr((hd, tl))` = cons) -/

/-- `List.fold_left f acc xs`. -/
def listFoldl : Val := hl_val%
  rec go f acc xs :=
    match xs with
    | injl(u) => acc
    | injr(p) => go f (f acc (fst(p))) (snd(p))

/-- `List.rev xs`. -/
def listRev : Val := hl_val%
  λ xs,
    (rec go acc l :=
      match l with
      | injl(u) => acc
      | injr(p) => go (injr((fst(p), acc))) (snd(p))) (injl(#())) xs

/-- `List.nth xs i` (returns `#()` past the end). -/
def listNth : Val := hl_val%
  rec go xs i :=
    match xs with
    | injl(u) => #()
    | injr(p) => if i = #0 then fst(p) else go (snd(p)) (i - #1)

end Iris.HeapLang.Codec
