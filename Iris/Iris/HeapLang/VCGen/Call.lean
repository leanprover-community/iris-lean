/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.HeapLang.VCGen.Specs
public import Iris.ProgramLogic.VCGen.FrameProc

@[expose] public section

/-!
# Unfolding a recursive call

A proof of a recursive function by induction passes the induction hypothesis to `vcgen` as a
specification of the call. At the top-level call the hypothesis does not apply, so the proof first
unfolds that call to the function body: `rec_call₁` for a function of one argument, `rec_call₂`
for a curried function of two arguments.

For `addV = rec f x := λ y, x + y`, the call `addV v₁ v₂` unfolds to the body
`msubst [("y", v₂), ("f", addV), ("x", v₁)] (x + y)`.
-/

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Iris.VCGen Lean.Order Std.WP

namespace Iris.HeapLang.VCGen

set_option experimental.vcgen true

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF] {s : Stuckness} {E : CoPset}
  {Q : Val → IProp GF} {P : IProp GF}

theorem rec_call₁ (f x : String) (body : Exp) (v : Val)
    (h : Triple (Prog := HLProg GF)
      ⟪(msubst [(f, .rec_ (.named f) (.named x) body), (x, v)] body) @ s ; E⟫ P Q ⊥) :
    Triple (Prog := HLProg GF)
      ⟪(Exp.app (ToVal.ofVal (Val.rec_ (.named f) (.named x) body)) (ToVal.ofVal v)) @ s ; E⟫ P Q ⊥ := by
  vcgen [h]

theorem rec_call₂ (f x y : String) (body : Exp) (v₁ v₂ : Val)
    (h : Triple (Prog := HLProg GF)
      ⟪(msubst [(y, v₂), (f, .rec_ (.named f) (.named x) (.rec_ .anon (.named y) body)), (x, v₁)]
        body) @ s ; E⟫ P Q ⊥) :
    Triple (Prog := HLProg GF)
      ⟪(Exp.app (Exp.app (ToVal.ofVal (Val.rec_ (.named f) (.named x) (.rec_ .anon (.named y) body)))
        (ToVal.ofVal v₁)) (ToVal.ofVal v₂)) @ s ; E⟫ P Q ⊥ := by
  vcgen [h]

end Iris.HeapLang.VCGen
