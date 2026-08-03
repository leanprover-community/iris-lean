module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `delta` codec — HeapLang programs -/

set_option mvcgen.warning false

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

open HeapLangAxioms

@[expose] public section

def deltaCPure : Val := hl_val%
  rec go prev := λ l,
    match l with
    | injl(u) => injl(#())
    | injr(p) =>
        let c := fst(p);
        let cs := snd(p);
        let d := ((c - prev) + #256) % #256;
        injr((d, go c cs))

def deltaDPure : Val := hl_val%
  rec go prev := λ l,
    match l with
    | injl(u) => injl(#())
    | injr(p) =>
        let d := fst(p);
        let ds := snd(p);
        let c := (prev + d) % #256;
        injr((c, go c ds))

end

end Iris.HeapLang.Ax
