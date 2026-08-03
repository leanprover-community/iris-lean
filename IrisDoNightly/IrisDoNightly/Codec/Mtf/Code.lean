module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `mtf` (move-to-front) codec — HeapLang programs -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

@[expose] public section

def hlIndexOf : Val := hl_val%
  rec go t := λ c,
    match t with
    | injl(u) => #0
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if x = c then #0 else (#1 + go xs c)

def hlEraseIdx : Val := hl_val%
  rec go t := λ r,
    match t with
    | injl(u) => injl(#())
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if r = #0 then xs else (let r' := r - #1; injr((x, go xs r')))

def hlMtfCompress : Val := hl_val%
  rec go tbl := λ l,
    match l with
    | injl(u) => injl(#())
    | injr(p) =>
        let c := fst(p);
        let cs := snd(p);
        let r := v(&hlIndexOf) tbl c;
        let e := v(&hlEraseIdx) tbl r;
        let tbl' := injr((c, e));
        injr((r, go tbl' cs))

def hlMtfDecompress : Val := hl_val%
  rec go tbl := λ l,
    match l with
    | injl(u) => injl(#())
    | injr(p) =>
        let r := fst(p);
        let rs := snd(p);
        let c := v(&hlNth) tbl r;
        let e := v(&hlEraseIdx) tbl r;
        let tbl' := injr((c, e));
        injr((c, go tbl' rs))

end

end Iris.HeapLang.Ax
