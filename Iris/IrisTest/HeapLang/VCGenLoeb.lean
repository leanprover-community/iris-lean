/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen
public import Iris.HeapLang.VCGen

@[expose] public section

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Lean.Order Std.WP Iris.VCGen Iris.HeapLang.VCGen

set_option experimental.vcgen true
set_option linter.heapLang.freeVars false

/-!
# Recursion by Löb induction

`vcgen invariants` verifies a recursive function from an invariant in continuation form, with no
measure. The function `divergeV` never returns, so it satisfies every postcondition, here `⌜False⌝`.
-/

namespace IrisTest.VCGen.Loeb

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

def divergeV : Val := hl_val(rec loop n := loop n)

theorem diverge_spec (n : Int) :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl(v(&divergeV) #n) ⦃ fun _ => ⌜False⌝ ⦄ := by
  unfold divergeV
  vcgen invariants
  · fun _ _ => BIBase.emp

end IrisTest.VCGen.Loeb
