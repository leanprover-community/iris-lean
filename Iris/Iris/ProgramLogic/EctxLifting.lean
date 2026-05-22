module

public import Iris.ProgramLogic.Lifting
public import Iris.ProgramLogic.EctxiLanguage

namespace Iris.ProgramLogic

open Language.Notation
open EctxLanguage.Notation

variable {hlc : outParam Bool}
variable {Expr Ectx State Obs Val}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]

variable {s : Stuckness} {E E₁ E₂ : CoPset} {v : Val} {e e₁ e₂ : Expr}
variable {σ : State} {P Q : IProp GF} {Φ : Val → IProp GF}

theorem wp_lift_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁,σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁,σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ)⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipure_intro; grind only [EctxLanguage.primStep_reducible_of_baseStep_reducible]
  iintro %e₂ %σ₂ %eₜ %Hstep
  iapply H $$ %_ %_ %_
  ipure_intro
  apply EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Hstep

theorem wp_lift_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ)⌝ -∗ £ 1 ={∅,E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ [$] with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hbstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hbstep Hcred

theorem wp_lift_base_stuck (h : toVal e = none) :
    EctxLanguage.SubredexesAreValues e →
    (∀ σ ns obs' nt, stateInterp σ ns obs' nt ={E,∅}=∗ ⌜BaseStep.Stuck (e,σ)⌝)
    ⊢ WP e @ E ? {{ Φ }} := by
  iintro %sav_e H
  iapply wp_lift_stuck h
  iintro %σ %ns %obs' %nt Hσ
  imod H $$ Hσ with %H
  ipure_intro
  apply EctxLanguage.primStep_stuck_of_baseStep_stuck H sav_e

theorem wp_lift_pure_base_stuck (h : toVal e = none) :
    EctxLanguage.SubredexesAreValues e →
    (∀ σ, BaseStep.Stuck (e,σ)) →
    ⊢ WP e @ E ?{{ Φ }} := by
  iintro %sav_e %Hstuck
  iapply wp_lift_base_stuck h sav_e
  iintro %σ %ns %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipure_intro
  apply Hstuck

theorem wp_lift_atomic_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E1}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E1}[E2]▷=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (toVal e₂).rec iprop(False) Φ ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E1 {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨%Hbred, H⟩
  imodintro
  isplit
  · ipure_intro; grind only [EctxLanguage.primStep_reducible_of_baseStep_reducible]
  iintro %_ %_ %_ %Hstep
  iapply H
  ipure_intro
  apply EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hbred Hstep

theorem wp_lift_atomic_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (toVal e₂).rec iprop(False) Φ ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨%Hbred, H⟩
  imodintro
  isplit
  · ipure_intro; grind only [EctxLanguage.primStep_reducible_of_baseStep_reducible]
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  iapply H $$ %_ %_ %_ [] Hcred
  ipure_intro
  apply EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hbred Hstep

theorem wp_lift_atomic_base_step_no_fork_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E1}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E1}[E2]▷=∗
        ⌜eₜ = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' nt ∗  (toVal e₂).rec iprop(False) Φ)
    ⊢ WP e₁ @ s; E1 {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ %_ %_ %_ %_ %_ Hσ₁ with ⟨$, H⟩
  imodintro
  iintro %_ %_ %_ %Hbstep Hcred
  imod H $$ %_ %_ %_ %Hbstep Hcred with H
  iintro !> !>
  imod H with ⟨%h, _, _⟩
  subst h
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe
  iapply fupd_mask_intro_discard Std.LawfulSet.subset_refl
  exact .rfl

theorem wp_lift_atomic_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        ⌜eₜ = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' nt ∗ (toVal e₂).rec iprop(False) Φ )
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁  with ⟨$, H⟩
  imodintro
  inext
  iintro %v2 %σ₂ %eₜ %Hstep Hcred
  imod H $$ %_ %_ %_ %Hstep Hcred with ⟨%h, _, _⟩
  subst h
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe

theorem wp_lift_pure_det_base_step_no_fork [Inhabited State] (E₂ : CoPset) (h : toVal e₁ = none) :
    (∀ σ₁, BaseStep.Reducible (e₁, σ₁)) →
    (∀ σ₁ obs e₂' σ₂ eₜ',
      (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ') → obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) →
    (|={E}[E₂]▷=> £ 1 -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro %Hbred %Hpure _
  apply wp_lift_pure_det_step_no_fork
  · grind [EctxLanguage.primStep_reducible_of_baseStep_reducible]
  · grind only [→ EctxLanguage.baseStep_of_primStep_of_baseStep_reducible]

theorem wp_lift_pure_det_base_step_no_fork' [Inhabited State] (h : toVal e₁ = none) :
    (∀ σ₁, BaseStep.Reducible (e₁, σ₁)) →
    (∀ σ₁ obs e₂' σ₂ eₜ',
      (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ') → obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) →
    ▷ (£ 1 -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro %Hbred %Hpure _
  refine .trans ?_ <| wp_lift_pure_det_base_step_no_fork E h Hbred Hpure
  exact step_fupd_intro Std.LawfulSet.subset_refl
