/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.Notation
public import Iris.HeapLang.TransfiniteProofMode

/-! Tests for the heap_lang tactics of Transfinite Iris (`twp_*`), over any step-index type. -/

namespace Iris.HeapLang.Transfinite.Test

open Iris Iris.BI Iris.Transfinite

variable {SI : Type _} [SIdx SI]
local stepindex SI

variable {GF : BundledGFunctors} [HeapLangTGS GF]
variable {s : Stuckness} {E : CoPset}
set_option linter.unusedVariables false

-- pure steps and values for `wp`
example : ⊢@{IProp GF} Iris.Transfinite.wp s E hl((λ x, x + #1) #2) (fun v => iprop(⌜v = hl_val(#3)⌝)) := by
  twp_pures
  itrivial

-- `if`, `let` and sequencing
example : ⊢@{IProp GF} Iris.Transfinite.wp s E hl(let x := #1; if #true then x + #1 else #0)
    (fun v => iprop(⌜v = hl_val(#2)⌝)) := by
  twp_pures
  itrivial

-- heap operations with `twp_apply`
example {l : Loc} {n : Int} : ⊢@{IProp GF}
    l ↦ some hl_val(#n) -∗ Iris.Transfinite.wp s E hl(!v(#l) + #1)
      (fun w => iprop(⌜w = hl_val(#(n + 1 : Int))⌝)) := by
  iintro Hpt
  twp_apply wp_load $$ Hpt
  iintro Hpt
  twp_pures
  itrivial

-- `swp`: a pure step turns `swp` into `wp`
example (k : Nat) : ⊢@{IProp GF} ▷ ⌜True⌝ -∗ swp k s E hl(#1 + #2) (fun v => iprop(⌜v = hl_val(#3)⌝)) := by
  iintro -
  twp_pure
  itrivial

-- `swp`: binding
example {l : Loc} (k : Nat) : ⊢@{IProp GF}
    ▷ l ↦ some hl_val(#1) -∗ swp k s E hl(!v(#l) + #1) (fun w => iprop(⌜w = hl_val(#2)⌝)) := by
  iintro Hpt
  twp_apply swp_load $$ Hpt
  iintro Hpt
  twp_pures
  itrivial

variable {A : Type _} [src : Source GF A]

-- `rwp`: pure steps cost no laters
example : ⊢@{IProp GF} rwp (src := src) (ι := heapRefIrisGS) s E hl((λ x, x + #1) #2) (fun v => iprop(⌜v = hl_val(#3)⌝)) := by
  twp_pures
  itrivial

example {l : Loc} : ⊢@{IProp GF}
    l ↦ some hl_val(#1) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(v(#l) ← (!v(#l) + #1))
      (fun _ => iprop(l ↦ some hl_val(#(1 + 1 : Int)))) := by
  iintro Hpt
  twp_smart_apply rwp_load $$ Hpt
  iintro Hpt
  twp_pures
  twp_apply rwp_store $$ Hpt
  iintro Hpt
  iexact Hpt

-- `rswp`
example : ⊢@{IProp GF} rswp (src := src) (ι := heapRefIrisGS) 0 s E hl(#1 + #2) (fun v => iprop(⌜v = hl_val(#3)⌝)) := by
  twp_pure
  itrivial

end Iris.HeapLang.Transfinite.Test
