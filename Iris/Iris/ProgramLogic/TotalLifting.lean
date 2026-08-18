/-
Copyright (c) 2026 Marcelo Fornet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Fornet, Zongyuan Liu
-/
module

public import Iris.ProgramLogic.TotalWeakestPre

namespace Iris.ProgramLogic

open Iris Language Language.Notation BI

@[expose] public section

/-! ## Total lifting rules -/
namespace twp

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset}
variable {e e₁ e₂ : Expr} {Φ : Val → IProp GF}

@[rocq_alias twp_lift_step]
theorem lift_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E,∅}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={∅,E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        WP e₂ @ s; E [{ Φ }] ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by rw [twp.unfold.to_eq, twp.pre, h]

@[rocq_alias twp_lift_atomic_step]
theorem lift_atomic_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs nt, stateInterp σ₁ ns obs nt ={E}=∗
      ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
      ∀ κ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, eₜ)⌝ ={E}=∗
        ⌜κ = []⌝ ∗
        stateInterp σ₂ (ns + 1) obs (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ [{ ι.forkPost }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro H
  iapply lift_step h
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ Hσ with ⟨$, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose %κ %e₂ %σ₂ %eₜ Hstep
  imod Hclose with -
  imod H $$ Hstep with ⟨%hκ, Hσ, ⟨%v, %hval, HΦ⟩, Hefs⟩
  iframe %hκ Hσ Hefs
  iapply twp.value (ToVal.coe_of_toVal_eq_some hval).symm $$ HΦ

@[rocq_alias twp_lift_pure_step_no_fork]
theorem lift_pure_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, PrimStep.ReducibleNoObs (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ, (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) → κ = [] ∧ σ₂ = σ₁ ∧ eₜ = []) :
    (|={E}=> ∀ κ e₂' eₜ σ, ⌜(e₁, σ) -<κ>-> (e₂', σ, eₜ)⌝ → WP e₂' @ s; E [{ Φ }])
    ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro >H
  iapply lift_step
  · exact (toVal_none_of_reducible <| reducible_of_reducibleNoObs (Hsafe default))
  iintro %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    grind [cases Stuckness]
  · iintro %κ %e₂' %σ₂ %eₜ %Hstep
    obtain ⟨hκ, rfl, rfl⟩ := Hpure _ _ _ _ _ Hstep
    imod ι.stateInterp_mono σ₂ ns obs nt $$ Hσ with Hσ
    imod Hclose
    iframe %hκ
    isimp
    ispecialize H $$ [//]
    iframe

@[rocq_alias twp_lift_pure_det_step_no_fork]
theorem lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, PrimStep.ReducibleNoObs (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ eₜ,
      (e₁, σ₁) -<κ>-> (e₂', σ₂, eₜ) → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ = []) :
    (|={E}=> WP e₂ @ s; E [{ Φ }]) ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro >H
  iapply lift_pure_step_no_fork Hsafe (by grind only)
  iintro !> %κ %e₂' %eₜ %σ %Hstep
  exact (Hpure _ _ _ _ _ Hstep).2.2.1 ▸ .rfl

@[rocq_alias twp_pure_step]
theorem pure_step [Inhabited State] (Hexec : PureExec φ n e₁ e₂) (Hφ : φ) :
    WP e₂ @ s; E [{ Φ }] ⊢ WP e₁ @ s; E [{ Φ }] := by
  iintro Hwp
  iinduction (Hexec.pureExec Hφ) with
  | rfl => itrivial
  | tail y n e1 e2 Hsteps Hstep IH =>
    iapply IH
    · ipureintro
      exact ⟨fun _ => Hsteps⟩
    iapply lift_pure_det_step_no_fork (e₁ := y) (e₂ := e2) Hstep.safe
    · grind only [Hstep.deterministic]
    iapply fupd_intro $$ Hwp

end twp

end
end Iris.ProgramLogic
