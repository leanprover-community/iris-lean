module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `lzss` codec — HeapLang programs (heap-free decoder core)

The output buffer is threaded as an immutable `Val` cons-list (the "state layer" carried
functionally, not on the heap); the back-copy's random access is realised with an `hlLength` +
`hlNth` pair.  Everything stays inside `HeapLangAxioms` — no `↦`, no framing. -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

@[expose] public section

/-- Heap-free length of a byte-list value (as an `Int`). -/
def hlLength : Val := hl_val%
  rec go t :=
    match t with
    | injl(u) => #0
    | injr(p) =>
        let xs := snd(p);
        let n := go xs;
        n + #1

/-- Heap-free append of one byte at the end of a byte-list value. -/
def hlSnoc : Val := hl_val%
  rec go t := λ b,
    match t with
    | injl(u) => injr((b, injl(#())))
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        let xs' := go xs b;
        injr((x, xs'))

/-- Heap-free overlapping back-copy: the `Val`-threaded realisation of `copyBack`.  `off` and `acc`
are curried so the recursive `go` is `hlCopyBack` itself (matching the induction hypothesis).  Each
step reads the byte `off` from the current end (`hlNth acc (hlLength acc - off)`) and snocs it. -/
def hlCopyBack : Val := hl_val%
  rec go k := λ off, λ acc,
    if k = #0 then acc
    else
      let n := v(&hlLength) acc;
      let idx := n - off;
      let b := v(&hlNth) acc idx;
      let acc' := v(&hlSnoc) acc b;
      let k' := k - #1;
      go k' off acc'

/-- Heap-free list concatenation (for the literal-run case of the decoder). -/
def hlAppend : Val := hl_val%
  rec go xs := λ ys,
    match xs with
    | injl(u) => ys
    | injr(p) =>
        let x := fst(p);
        let xs' := snd(p);
        let r := go xs' ys;
        injr((x, r))

/-- The `lzss` decoder loop: fold the token stream, threading the buffer as a `Val`.  A literal run
appends its bytes; a back-reference invokes the (heap-free) `hlCopyBack`. -/
def hlLzssDecodeAux : Val := hl_val%
  rec go ts := λ acc,
    match ts with
    | injl(u) => acc
    | injr(p) =>
        let t := fst(p);
        let ts' := snd(p);
        match t with
        | injl(bs) =>
            let acc1 := v(&hlAppend) acc bs;
            go ts' acc1
        | injr(q) =>
            let off := fst(q);
            let len := snd(q);
            let acc2 := v(&hlCopyBack) len off acc;
            go ts' acc2

/-- The full heap-free `lzss` decoder: decode a token stream starting from the empty buffer. -/
def hlLzssDecode : Val := hl_val%
  λ ts, v(&hlLzssDecodeAux) ts v(&(vList ([] : List Int)))

end

end Iris.HeapLang.Ax
