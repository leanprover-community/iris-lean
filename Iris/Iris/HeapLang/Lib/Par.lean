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

def parN : Namespace := ndot nroot "par"

def par : Val := hl_val%
  λ e1 e2,
    let handle := &spawn e1;
    let v2 := e2 #();
    let v1 := &join handle;
    (v1, v2)

/-- Parallel composition: `e1 ‖ e2` is sugar for `par` applied to two thunks. -/
syntax:55 hl_exp:56 " ‖ " hl_exp:55 : hl_exp

macro_rules
  | `(hl($e1 ‖ $e2)) => `(hl(&par v(λ _, $e1) v(λ _, $e2)))

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [SpawnG GF]

theorem par_spec (Ψ1 Ψ2 : Val → IProp GF) (f1 f2 : Val) (Φ : Val → IProp GF) :
    ⊢ WP hl(&f1 #()) {{ Ψ1 }} -∗
      WP hl(&f2 #()) {{ Ψ2 }} -∗
      (▷ ∀ (v1 v2 : Val), Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ hl_val((&v1, &v2))) -∗
      WP hl(&par &f1 &f2) {{ Φ }} := by
  iintro Hf1 Hf2 HΦ
  unfold par
  wp_pures
  wp_bind &spawn _
  iapply spawn_spec parN $$ Hf1
  iintro %l Hl
  wp_pures
  wp_bind &f2 _
  iapply wp_wand $$ Hf2
  iintro %v H2
  wp_pures
  wp_bind &join _
  iapply join_spec $$ Hl
  iintro %w H1
  ispecialize HΦ $$ [$H1 $H2]
  wp_pures
  iexact HΦ

theorem wp_par (Ψ1 Ψ2 : Val → IProp GF) (e1 e2 : Exp) (Φ : Val → IProp GF) :
    ⊢ WP hl(&e1) {{ Ψ1 }} -∗
      WP hl(&e2) {{ Ψ2 }} -∗
      (∀ (v1 v2 : Val), Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ hl_val((&v1, &v2))) -∗
      WP hl(&e1 ‖ &e2) {{ Φ }} := by
  iintro H1 H2 H
  iapply par_spec Ψ1 Ψ2 $$ [H1] [H2] [$]
  · wp_pures; iexact H1
  · wp_pures; iexact H2

end Specs

end Par
end
