/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI

@[expose] public section

/-! ## Total lifting rules -/

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
    ⊢ WP e₁ @ s; E [{ Φ }] := by rw [twp.unfold.to_eq, twp.pre, h]

theorem twp_lift_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        WP e₂ @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  refine .trans ?_ <| twp_lift_step h
  iintro H %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  iframe %Hred
  iintro !> %κ %e₂ %σ₂ %eₜ Hstep
  imod H $$ Hstep with ⟨%hκ, %heₜ, Hσ, Hwp⟩
  simp only [heₜ, List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil, BI.sep_emp.to_eq]
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
  refine .trans ?_ <| twp_lift_step h
  iintro H %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iframe %Hred
  iintro %κ %e₂ %σ₂ %eₜ Hstep
  imod Hclose with -
  imod H $$ Hstep with ⟨%hκ, Hσ, ⟨%v, %hval, HΦ⟩, Hefs⟩
  iframe %hκ Hσ Hefs
  iapply twp.value (ToVal.coe_of_toVal_eq_some hval).symm $$ HΦ

theorem twp_lift_atomic_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗ ⌜eₜ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs nt ∗
        ∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v)
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  refine .trans ?_ <| twp_lift_atomic_step h
  iintro H %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  iframe %Hred
  iintro !> %κ %e₂ %σ₂ %eₜ Hstep
  imod H $$ Hstep with ⟨%hκ, %heₜ, Hσ, Hval⟩
  simp only [heₜ, List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil, BI.sep_emp.to_eq]
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
  refine .trans ?_ <| twp_lift_step_no_fork (toVal_none_of_reducible <| reducible_of_reducibleNoObs (Hsafe default))
  iintro H %σ₁ %ns %obs %nt Hσ
  imod H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · exact BI.pure_intro (by grind [cases Stuckness])
  · iintro %κ %e₂' %σ₂ %eₜ %Hstep
    obtain ⟨hκ, rfl, heₜ⟩ := Hpure _ _ _ _ _ Hstep
    imod ι.stateInterp_mono σ₂ ns obs nt $$ Hσ with Hσ
    imod Hclose
    iframe %hκ %heₜ Hσ
    iapply H $$ %κ %e₂' %eₜ %σ₂ %Hstep

@[rocq_alias twp_lift_pure_det_step_no_fork]
theorem twp_lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, PrimStep.ReducibleNoObs (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ = []) :
    (|={E}=> WP e₂ @ s; E [{ Φ }]) ⊢ WP e₁ @ s; E [{ Φ }] := by
  refine (BIFUpdate.mono ?_).trans <| twp_lift_pure_step_no_fork Hsafe (by grind only)
  iintro Hwp %κ %e₂' %eₜ %σ %Hstep
  exact (Hpure _ _ _ _ _ Hstep).2.2.1 ▸ .rfl

@[rocq_alias twp_pure_step]
theorem twp_pure_step [Inhabited State]
    (Hexec : PureExec φ n e₁ e₂) (Hφ : φ) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := (Hexec.pureExec Hφ).head_induction_on
      (motive := fun _ e _ => WP e₂ @ s; E [{ Φ }] ⊢ WP e @ s; E [{ Φ }]) .rfl fun e₃ Hstep _ IH =>
    (IH.trans fupd_intro).trans <| twp_lift_pure_det_step_no_fork (e₂ := e₃) Hstep.1 (by grind only [Hstep.2])

end
end Iris.ProgramLogic
