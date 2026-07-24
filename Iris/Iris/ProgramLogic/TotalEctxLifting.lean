/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalLifting
public import Iris.ProgramLogic.EctxLifting

namespace Iris.ProgramLogic

open Iris Language.Notation EctxLanguage EctxLanguage.Notation

@[expose] public section

/-!
Total base-step rules for evaluation-context languages.  We intentionally stop
at the generic deterministic/no-fork interface needed by a Wasm language.
HeapLang primitive laws and concurrent convenience rules are not duplicated:
they add no capability for the initial single-threaded Wasm consumer.
-/

variable {hlc : outParam HasLC} {Expr Ectx State Obs Val}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e₁ e₂ : Expr}
variable {Φ : Val → IProp GF}

theorem twp_lift_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp_lift_step_no_fork h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    cases s
    · exact EctxLanguage.primStep_reducible_of_baseStep_reducible Hred
    · trivial
  · iintro %κ %e₂ %σ₂ %eₜ %Hstep
    have Hb := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Hstep
    iapply H $$ %κ %e₂ %σ₂ %eₜ %Hb

theorem twp_lift_pure_det_base_step_no_fork [Inhabited State]
    (h : toVal e₁ = none)
    (Hred : ∀ σ, BaseStep.Reducible (e₁, σ))
    (Hpure : ∀ σ κ e₂' σ₂ eₜ,
      (e₁, σ) -<κ>->ᵇ (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ ∧ e₂' = e₂ ∧ eₜ = []) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := by
  apply twp_lift_pure_det_step_no_fork
  · intro σ
    cases s
    · obtain ⟨κ, e', σ', efs, Hb⟩ := Hred σ
      have ⟨hκ, _, _, _⟩ := Hpure σ κ e' σ' efs Hb
      subst hκ
      exact ⟨e', σ', efs, EctxLanguage.primStep_of_baseStep Hb⟩
    · exact h
  · intro σ κ e₂' σ₂ eₜ Hstep
    exact Hpure _ _ _ _ _
      (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible (Hred σ) Hstep)

end
end Iris.ProgramLogic
