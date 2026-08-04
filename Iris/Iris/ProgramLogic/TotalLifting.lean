/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Lifting

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI

@[expose] public section

/-!
The no-fork rules in this file make the single-threaded contract explicit
(`eₜ = []`) while the underlying TWP remains faithful to Iris and can account
for forks.

All total rules require the operational observation to be empty.  This is a
semantic requirement of Iris TWP, not proof bookkeeping.
-/

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset}
variable {e e₁ e₂ : Expr} {Φ : Val → IProp GF}

@[rocq_alias twp_lift_step]
theorem twp_lift_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        WP e₂ @ s; E [{ Φ }] ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  rw [twp.unfold.to_eq]
  simp only [twp.pre, h]
  exact .rfl

theorem twp_lift_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp_lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with ⟨%hκ, %heₜ, Hσ, Hwp⟩
  subst heₜ
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe %hκ Hσ Hwp

@[rocq_alias twp_lift_atomic_step]
theorem twp_lift_atomic_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp_lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact Hred
  · iintro %κ %e₂ %σ₂ %eₜ %Hstep
    imod Hclose with -
    imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with
      ⟨%hκ, Hσ, ⟨%v, %hval, HΦ⟩, Hefs⟩
    imodintro
    iframe %hκ Hσ Hefs
    iapply twp.value (ToVal.coe_of_toVal_eq_some hval).symm
    iexact HΦ

theorem twp_lift_atomic_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        ∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v)
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply twp_lift_atomic_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  iframe %Hred
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod H $$ %κ %e₂ %σ₂ %eₜ %Hstep with
    ⟨%hκ, %heₜ, Hσ, Hval⟩
  subst heₜ
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe %hκ Hσ Hval

@[rocq_alias twp_lift_pure_step_no_fork]
theorem twp_lift_pure_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, PrimStep.ReducibleNoObs (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ₁ ∧ eₜ = []) :
    (|={E}=> ∀ κ e₂' eₜ σ,
      ⌜(e₁, σ) -<κ>-> (e₂', σ, eₜ)⌝ -∗
      WP e₂' @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  have hnone : toVal e₁ = none :=
    Language.toVal_none_of_reducible
      (Language.reducible_of_reducibleNoObs (Hsafe default))
  iapply twp_lift_step_no_fork hnone
  iintro %σ₁ %ns %obs %nt Hσ
  imod H with H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    cases s
    · exact Hsafe σ₁
    · trivial
  · iintro %κ %e₂' %σ₂ %eₜ %Hstep
    obtain ⟨rfl, rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
    imod ι.stateInterp_mono σ₂ ns obs nt $$ Hσ with Hσ
    imod Hclose
    imodintro
    iframe Hσ
    isplit
    · ipureintro
      exact rfl
    · isplit
      · ipureintro
        exact rfl
      · iapply H $$ %([] : List Obs) %e₂' %([] : List Expr) %σ₂ %Hstep

@[rocq_alias twp_lift_pure_det_step_no_fork]
theorem twp_lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, PrimStep.ReducibleNoObs (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ = []) :
    (|={E}=> WP e₂ @ s; E [{ Φ }]) ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro Hwp
  iapply twp_lift_pure_step_no_fork Hsafe ?_
  · intro σ₁ κ e₂' σ₂ eₜ Hstep
    obtain ⟨hκ, hσ, _, heₜ⟩ := Hpure _ _ _ _ _ Hstep
    exact ⟨hκ, hσ, heₜ⟩
  · imod Hwp with Hwp
    imodintro
    iintro %κ %e₂' %eₜ %σ %Hstep
    obtain ⟨_, _, he₂, _⟩ := Hpure _ _ _ _ _ Hstep
    subst e₂'
    iexact Hwp

@[rocq_alias twp_pure_step]
theorem twp_pure_step [Inhabited State]
    (Hexec : PureExec φ n e₁ e₂) (Hφ : φ) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := by
  replace Hexec := Hexec.pureExec Hφ
  iinduction Hexec using Relation.Iterate.head_induction_on with
  | rfl =>
      iintro Hwp
      iexact Hwp
  | @head n e₁ e₃ _ _ IH =>
      iintro Hwp
      obtain ⟨Hsafe, Hdet⟩ := ‹e₁ -ᵖ-> e₃›
      iapply twp_lift_pure_det_step_no_fork Hsafe ?_
      · intro σ₁ κ e₂' σ₂ eₜ Hstep
        obtain ⟨hκ, hσ, he, heₜ⟩ := Hdet Hstep
        exact ⟨hκ, hσ.symm, he.symm, heₜ⟩
      · imodintro
        iapply IH
        iexact Hwp

end
end Iris.ProgramLogic
