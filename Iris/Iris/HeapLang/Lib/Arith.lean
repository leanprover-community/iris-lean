/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init -- shake: keep
public import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Arith

@[rocq_alias heap_lang.minimum]
def minimum : Val := hl_val%
  λ m n, if m < n then m else n

@[rocq_alias heap_lang.maximum]
def maximum : Val := hl_val%
  λ m n, if m < n then n else m

section Spec

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

@[rocq_alias heap_lang.minimum_spec]
theorem minimum_spec (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (m n : Int) :
    ▷ Φ (Val.lit (.int (min m n))) -∗
    WP hl(&minimum #m #n) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_lam
  wp_pures
  by_cases h : m < n
  · rw [decide_eq_true h]
    wp_pures
    rw [Int.min_eq_left (by omega)]
    itrivial
  · rw [decide_eq_false h]
    wp_pures
    rw [Int.min_eq_right (by omega)]
    itrivial

@[rocq_alias heap_lang.minimum_spec_nat]
theorem minimum_spec_nat (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (m n : Nat) :
    ▷ Φ (Val.lit (.int (Int.ofNat (min m n)))) -∗
    WP hl(&minimum #m #n) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply minimum_spec
  rw [show min (↑m : Int) ↑n = ↑(min m n) by omega]
  itrivial

@[rocq_alias heap_lang.maximum_spec]
theorem maximum_spec (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (m n : Int) :
    ▷ Φ (Val.lit (.int (max m n))) -∗
    WP hl(&maximum #m #n) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_lam
  wp_pures
  by_cases h : m < n
  · rw [decide_eq_true h]
    wp_pures
    rw [Int.max_eq_right (by omega)]
    itrivial
  · rw [decide_eq_false h]
    wp_pures
    rw [Int.max_eq_left (by omega)]
    itrivial

@[rocq_alias heap_lang.maximum_spec_nat]
theorem maximum_spec_nat (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (m n : Nat) :
    ▷ Φ (Val.lit (.int (Int.ofNat (max m n)))) -∗
    WP hl(&maximum #m #n) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply maximum_spec
  rw [show max (↑m : Int) ↑n = ↑(max m n) by omega]
  itrivial

end Spec

end Arith
end
