/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Lifting

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI

@[expose] public section

/-!
The no-fork rules in this file are the intended entry point for Wasm.  They
make the single-threaded contract explicit (`eₜ = []`) while the underlying
TWP remains faithful to Iris and can account for forks.

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
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
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
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
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
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
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
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
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

theorem twp_lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, match s with
      | .NotStuck => PrimStep.ReducibleNoObs (e₁, σ₁)
      | .MaybeStuck => toVal e₁ = none)
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ = []) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro Hwp
  have hnone : toVal e₁ = none := by
    cases s
    · exact Language.toVal_none_of_reducible
        (Language.reducible_of_reducibleNoObs (Hsafe default))
    · exact Hsafe default
  iapply twp_lift_step_no_fork hnone
  iintro %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    cases s
    · exact Language.reducible_of_reducibleNoObs (Hsafe σ₁)
    · trivial
  · iintro %κ %e₂' %σ₂ %eₜ %Hstep
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
    imod Hclose
    ihave Hmono := ι.stateInterp_mono σ₂ ns obs nt $$ Hσ
    imod fupd_mask_mono Std.LawfulSet.empty_subset $$ Hmono with Hσ
    imodintro
    iframe Hσ Hwp
    ipureintro
    exact ⟨rfl, rfl⟩

end
end Iris.ProgramLogic
