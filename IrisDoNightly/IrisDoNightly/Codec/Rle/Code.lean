module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `rle` (run-length) codec — HeapLang programs -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

@[expose] public section

def hlRleAux : Val := hl_val%
  rec go c := λ k, λ l,
    match l with
    | injl(u) => injr((k, injr((c, injl(#())))))
    | injr(p) =>
        let x := fst(p);
        let xs := snd(p);
        if x = c then (let k' := k + #1; go c k' xs)
        else injr((k, injr((c, go x #1 xs))))

def hlRleEnc : Val := hl_val%
  λ l,
    match l with
    | injl(u) => injl(#())
    | injr(p) => let c := fst(p); let cs := snd(p); v(&hlRleAux) c #1 cs

def hlReplicateApp : Val := hl_val%
  rec go k := λ c, λ tail,
    if k = #0 then tail else (let k' := k - #1; injr((c, go k' c tail)))

def hlRleDec : Val := hl_val%
  rec go l :=
    match l with
    | injl(u) => injl(#())
    | injr(p) =>
        let k := fst(p);
        let rest1 := snd(p);
        match rest1 with
        | injl(u) => injl(#())
        | injr(q) =>
            let c := fst(q);
            let rest := snd(q);
            v(&hlReplicateApp) k c (go rest)

end

end Iris.HeapLang.Ax
