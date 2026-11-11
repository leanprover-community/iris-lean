/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

public import Iris.ProgramLogic.VCGen
public import Iris.HeapLang.VCGen
public import Iris.Examples.HeapLang

@[expose] public section

open Iris Iris.BI Iris.ProgramLogic Iris.HeapLang Lean.Order Std.WP Iris.VCGen Iris.HeapLang.VCGen

set_option experimental.vcgen true
set_option linter.heapLang.freeVars false

/-!
# Value-form specifications

The heap primitives specified with the result in the postcondition: `load` returns a `w` with
`⌜w = v⌝`, and allocation returns some location `l` with `⌜w = #l⌝`. `vcgen` eliminates the index
`l` of `⨆ l, ⌜w = #l⌝ ⊓ l ↦ v` when the program fixes `w`, so `ref_val_spec` is proved by `vcgen`
alone.
-/

namespace IrisTest.VCGen.ValueForm

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

local notation "ov " v:max => (ToVal.ofVal (Expr := Exp) v)

theorem load_val_spec (l : Loc) (v : Val) :
    hl⦃ (l ↦ some v : IProp GF) ⦄ (Exp.load (ov (Val.lit (.loc l))))
      ⦃ fun w => ⌜w = v⌝ ⊓ (l ↦ some v : IProp GF) ⦄ := by
  vcgen with finish

theorem store_val_spec (l : Loc) (v w : Val) :
    hl⦃ (l ↦ some v : IProp GF) ⦄ (Exp.store (ov (Val.lit (.loc l))) (ov w))
      ⦃ fun r => ⌜r = .lit .unit⌝ ⊓ (l ↦ some w : IProp GF) ⦄ := by
  vcgen with finish

theorem ref_val_spec (v : Val) :
    hl⦃ (BIBase.emp : IProp GF) ⦄ (Exp.allocN (ov (Val.lit (.int 1))) (ov v))
      ⦃ fun w => ⨆ l : Loc, ⌜w = .lit (.loc l)⌝ ⊓ (l ↦ some v : IProp GF) ⦄ := by
  vcgen

/-- Allocation, load and store with value-form specifications only. -/
example :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl(let r := ref(#1); r ← !r + #1; !r)
      ⦃ fun v => ⌜v = hl_val(#2)⌝ ⦄ := by
  vcgen [load_val_spec, store_val_spec, ref_val_spec] with finish

/-- `counter` from iris-lean with value-form specifications. -/
example : hl⦃ (BIBase.emp : IProp GF) ⦄ Iris.Examples.HeapLang.counter ⦃ fun v => ⌜v = hl_val(#1)⌝ ⦄ := by
  unfold Iris.Examples.HeapLang.counter
  vcgen [load_val_spec, store_val_spec, ref_val_spec] with finish

/-- A function that returns a fresh cell. -/
example :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl((λ x, ref(x)) #5)
      ⦃ fun w => ⨆ l : Loc, ⌜w = .lit (.loc l)⌝ ⊓ (l ↦ some hl_val(#5) : IProp GF) ⦄ := by
  vcgen [ref_val_spec]

/-- A result that the specification states as an existential. -/
example :
    hl⦃ (BIBase.emp : IProp GF) ⦄ hl(#2 + #2)
      ⦃ fun w => ⨆ n : Int, ⌜w = .lit (.int n)⌝ ⊓ (⌜n % 2 = 0⌝ : IProp GF) ⦄ := by
  vcgen

end IrisTest.VCGen.ValueForm
