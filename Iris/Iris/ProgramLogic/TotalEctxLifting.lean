/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalLifting
public import Iris.ProgramLogic.EctxiLanguage

namespace Iris.ProgramLogic

open Iris BI Language.Notation EctxLanguage EctxLanguage.Notation

@[expose] public section

/-! ## Total lifting rules for evaluation-context languages -/

variable {hlc : outParam HasLC} {Expr Ectx State Obs Val}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E : CoPset} {e₁ e₂ : Expr}
variable {Φ : Val → IProp GF}

private theorem baseStep_of_primStep {e₂' σ₁ σ₂ κ eₜ}
    (Hred : BaseStep.ReducibleNoObs (e₁, σ₁))
    (Hstep : (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ)) :
    (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, eₜ) :=
  baseStep_of_primStep_of_baseStep_reducible (BaseStep.reducible_of_reducibleNoObs Hred) Hstep

private theorem baseStep_mono {E₁ E₂ : CoPset}
    {Q : Nat → List Obs → Nat → List Obs → Expr → State → List Expr → IProp GF} :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E₁,E₂}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={E₂,E₁}=∗
        Q ns obs nt κ e₂ σ₂ eₜ) ⊢
    ∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E₁,E₂}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={E₂,E₁}=∗
        Q ns obs nt κ e₂ σ₂ eₜ := by
  iintro H %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  have Hred' : s.MaybeReducibleNoObs (e₁, σ₁) := by grind [primStep_reducibleNoObs_of_baseStep_reducibleNoObs]
  iframe %Hred'
  iintro !> %κ %e₂ %σ₂ %eₜ %Hstep
  iapply H $$ %κ %e₂ %σ₂ %eₜ %(baseStep_of_primStep Hred Hstep)

@[rocq_alias twp_lift_base_step]
theorem twp_lift_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        WP e₂ @ s; E [{ Φ }] ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] :=
  baseStep_mono.trans (twp_lift_step h)

theorem twp_lift_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] :=
  baseStep_mono.trans (twp_lift_step_no_fork h)

@[rocq_alias twp_lift_pure_base_step_no_fork]
theorem twp_lift_pure_base_step_no_fork [Inhabited State]
    (Hred : ∀ σ, BaseStep.ReducibleNoObs (e₁, σ))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ₁ ∧ eₜ = []) :
    (|={E}=> ∀ κ e₂' eₜ σ,
      ⌜(e₁, σ) -<κ>->ᵇ (e₂', σ, eₜ)⌝ -∗
      WP e₂' @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  refine (BIFUpdate.mono (forall_mono fun _ => forall_mono fun _ => forall_mono fun _ => forall_mono fun σ =>
    wand_mono_left <| pure_mono fun Hstep => baseStep_of_primStep (Hred σ) Hstep)).trans <| twp_lift_pure_step_no_fork
    (by grind [primStep_reducibleNoObs_of_baseStep_reducibleNoObs]) (by grind only [→ baseStep_of_primStep])

@[rocq_alias twp_lift_atomic_base_step]
theorem twp_lift_atomic_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] :=
  baseStep_mono.trans (twp_lift_atomic_step h)

@[rocq_alias twp_lift_atomic_base_step_no_fork]
theorem twp_lift_atomic_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜BaseStep.ReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        ∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v)
    ⊢ WP e₁ @ s; E [{ Φ }] :=
  baseStep_mono.trans (twp_lift_atomic_step_no_fork h)

@[rocq_alias twp_lift_pure_det_base_step_no_fork]
theorem twp_lift_pure_det_base_step_no_fork [Inhabited State]
    (_h : toVal e₁ = none)
    (Hred : ∀ σ, BaseStep.ReducibleNoObs (e₁, σ))
    (Hpure : ∀ σ κ e₂' σ₂ eₜ,
      (e₁, σ) -<κ>->ᵇ (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ ∧ e₂' = e₂ ∧ eₜ = []) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] :=
  fupd_intro.trans <| twp_lift_pure_det_step_no_fork (e₂ := e₂)
    (by grind [primStep_reducibleNoObs_of_baseStep_reducibleNoObs]) (by grind only [→ baseStep_of_primStep])

end
end Iris.ProgramLogic
