/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.HeapLang.Lib.Spawn
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic Spawn

@[expose] public section

namespace Par

@[rocq_alias heap_lang.parN]
def parN : Namespace := ndot nroot "par"

@[rocq_alias heap_lang.par]
def par : Val := hl_val%
  λ e1 e2,
    let handle := &spawn e1;
    let v2 := e2 #();
    let v1 := &join handle;
    (v1, v2)

/-- Parallel composition: `e1 ‖ e2` is sugar for `par` applied to two thunks. -/
syntax:55 hl_exp:56 " ‖ " hl_exp:55 : hl_exp

macro_rules
  | `(hl($e1 ‖ $e2)) => `(hl(&par (λ _, $e1) (λ _, $e2)))

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpawnG GF]

@[rocq_alias heap_lang.par_spec]
theorem par_spec (Ψ1 Ψ2 : Val → IProp GF) (f1 f2 : Val) (Φ : Val → IProp GF) :
    ⊢ WP hl(&f1 #()) {{ Ψ1 }} -∗
      WP hl(&f2 #()) {{ Ψ2 }} -∗
      (▷ ∀ (v1 v2 : Val), Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ hl_val((&v1, &v2))) -∗
      WP hl(&par &f1 &f2) {{ Φ }} := by
  iintro Hf1 Hf2 HΦ
  unfold par
  wp_smart_apply spawn_spec parN $$ Hf1 with %l Hl
  wp_pures
  wp_apply wp_wand $$ Hf2 with %v H2
  wp_smart_apply join_spec $$ Hl with %w H1
  ispecialize HΦ $$ [$H1 $H2]
  wp_pures
  iexact HΦ

@[rocq_alias heap_lang.wp_par]
theorem wp_par (Ψ1 Ψ2 : Val → IProp GF) (e1 e2 : Exp) (Φ : Val → IProp GF) :
    ⊢ WP hl(&e1) {{ Ψ1 }} -∗
      WP hl(&e2) {{ Ψ2 }} -∗
      (∀ (v1 v2 : Val), Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ hl_val((&v1, &v2))) -∗
      WP hl(&par v(λ _, &e1) v(λ _, &e2)) {{ Φ }} := by
  iintro H1 H2 H
  iapply par_spec Ψ1 Ψ2 $$ [H1] [H2] [$]
  · wp_pures; iexact H1
  · wp_pures; iexact H2

end Specs

end Par
end
