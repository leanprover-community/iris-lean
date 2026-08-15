/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Fornet, Zongyuan Liu
-/
module

public import Iris.ProgramLogic.TotalLifting
public import Iris.ProgramLogic.EctxiLanguage

namespace Iris.ProgramLogic

open Iris BI Language.Notation EctxLanguage EctxLanguage.Notation

@[expose] public section

/-! ## Total lifting rules for evaluation-context languages -/
namespace twp

variable {hlc : outParam HasLC} {Expr Ectx State Obs Val}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e₁ e₂ : Expr}
variable {Φ : Val → IProp GF}

attribute [local grind →] BaseStep.reducible_of_reducibleNoObs
  baseStep_of_primStep_of_baseStep_reducible primStep_reducibleNoObs_of_baseStep_reducibleNoObs

@[rocq_alias twp_lift_base_step]
theorem lift_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        WP e₂ @ s; E [{ Φ }] ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%_, H⟩
  imodintro
  isplit
  · ipureintro
    grind
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  iapply H $$ %κ %e₂ %σ₂ %eₜ %(by grind)

@[rocq_alias twp_lift_pure_base_step_no_fork]
theorem lift_pure_base_step_no_fork [Inhabited State]
    (Hred : ∀ σ, BaseStep.ReducibleNoObs (e₁, σ))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ, (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, eₜ) → κ = [] ∧ σ₂ = σ₁ ∧ eₜ = []) :
    (|={E}=> ∀ κ e₂' eₜ σ, ⌜(e₁, σ) -<κ>->ᵇ (e₂', σ, eₜ)⌝ → WP e₂' @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro >H
  iapply lift_pure_step_no_fork
  · grind
  · grind
  iintro !> %κ %e₂' %eₜ %σ %Hstep
  iapply H $$ %κ %e₂' %eₜ %σ
  ipureintro
  grind

@[rocq_alias twp_lift_atomic_base_step]
theorem lift_atomic_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply lift_atomic_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%_, H⟩
  imodintro
  isplit
  · ipureintro
    grind
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  iapply H
  ipureintro
  grind

@[rocq_alias twp_lift_atomic_base_step_no_fork]
theorem lift_atomic_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗ ∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v)
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply (lift_atomic_base_step h)
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨$, H⟩
  imodintro
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod H $$ [# //] with ⟨%heq1, %heq2, _, $⟩
  subst heq1
  subst heq2
  imodintro
  iframe
  isimp
  itrivial

@[rocq_alias lift_pure_det_base_step_no_fork]
theorem lift_pure_det_base_step_no_fork [Inhabited State]
    (_h : toVal e₁ = none)
    (Hred : ∀ σ, BaseStep.ReducibleNoObs (e₁, σ))
    (Hpure : ∀ σ κ e₂' σ₂ eₜ,
      (e₁, σ) -<κ>->ᵇ (e₂', σ₂, eₜ) → κ = [] ∧ σ₂ = σ ∧ e₂' = e₂ ∧ eₜ = []) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply lift_pure_det_step_no_fork $$ H <;> grind

end twp

end
end Iris.ProgramLogic
