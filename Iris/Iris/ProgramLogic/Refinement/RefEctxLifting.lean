/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefLifting
public import Iris.ProgramLogic.EctxLiftingTransfinite

/-! # Lifting lemmas for the refinement WP in evaluation-context languages (Transfinite Iris)

This file ports `theories/program_logic/refinement/ref_ectx_lifting.v` of Transfinite Iris, with
Iris-Lean's naming (`head` → `base`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language.Notation EctxLanguage EctxLanguage.Notation Iris.Std Iris.BI OFE
  Relation

variable {Expr Ectx State Obs Val : Type _}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {A : Type _} [src : Source GF A] [ι : RefIrisGS Expr GF]
variable {k : Nat} {s : Stuckness} {E E' : CoPset} {e₁ e₂ : Expr} {Φ : Val → IProp GF}

/-- Rocq: `rwp_lift_head_step_fupd`. -/
theorem rwp_lift_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ n (a : A), src.interp a ∗ ι.refStateInterp σ₁ n ={E,∅}=∗
      ∃ b : Bool, ▷?b |={∅}=> (⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
        ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={∅,E}=∗
          (if b then ∃ a' : A, ⌜TransGen src.rel a a'⌝ ∗ src.interp a' else src.interp a) ∗
          ι.refStateInterp σ₂ (efs.length + n) ∗ rwp (src := src) (ι := ι) s E e₂ Φ ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rwp (src := src) (ι := ι) s E e₁ Φ := by
  iintro H
  iapply rwp_lift_step_fupd h
  unfold rwpStep
  iintro %σ₁ %n %a Hσ
  imod H $$ %σ₁ %n %a Hσ with ⟨%b, H⟩
  imodintro
  iexists b
  iapply laterN_mono _ ?_ $$ H
  iintro H
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro
    exact maybeReducible_of_baseStep_reducible Hred
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod H $$ %e₂ %σ₂ %efs %κ %(baseStep_of_primStep_of_baseStep_reducible Hred Hstep)
    with ⟨Hsrc, Hσ, Hwp, Hefs⟩
  imodintro
  dsimp only
  iframe

/-- Rocq: `rwp_lift_pure_det_head_step_no_fork`. -/
theorem rwp_lift_pure_det_base_step_no_fork [Inhabited State] (h : toVal e₁ = none)
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ efs',
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, efs') → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rwp (src := src) (ι := ι) s E e₁ Φ :=
  rwp_lift_pure_det_step_no_fork
    (fun σ => by
      have := primStep_reducible_of_baseStep_reducible (Hbred σ)
      cases s
      · exact this
      · exact h)
    (fun hs => Hpure _ _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible (Hbred _) hs))

/-- Rocq: `rswp_lift_head_step_fupd`. -/
theorem rswp_lift_base_step_fupd :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E,∅}=∗ |={∅}[∅]▷=>^[k] (⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ rwp (src := src) (ι := ι) s E e₂ Φ ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_step_fupd
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro ⟨%Hred, H⟩
  isplitr
  · ipureintro
    exact maybeReducible_of_baseStep_reducible Hred
  iintro %e₂ %σ₂ %efs %κ %Hstep
  iapply H $$ %e₂ %σ₂ %efs %κ %(baseStep_of_primStep_of_baseStep_reducible Hred Hstep)

/-- Rocq: `rswp_lift_atomic_head_step`. -/
theorem rswp_lift_atomic_base_step :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E}=∗ ▷^[k] (⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_atomic_step
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply laterN_mono _ ?_ $$ H
  iintro ⟨%Hred, H⟩
  isplitr
  · ipureintro
    exact maybeReducible_of_baseStep_reducible Hred
  iintro %e₂ %σ₂ %efs %κ %Hstep
  iapply H $$ %e₂ %σ₂ %efs %κ %(baseStep_of_primStep_of_baseStep_reducible Hred Hstep)

/-- Rocq: `rswp_lift_atomic_head_step_no_fork`. -/
theorem rswp_lift_atomic_base_step_no_fork :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E}=∗ ▷^[k] (⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ⌜efs = []⌝ ∗ ι.refStateInterp σ₂ n ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_atomic_base_step
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply laterN_mono _ ?_ $$ H
  iintro ⟨$, H⟩
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨%h, Hσ, HΦ⟩
  subst h
  imodintro
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `rswp_lift_pure_det_head_step_no_fork_fupd`. -/
theorem rswp_lift_pure_det_base_step_no_fork (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ efs',
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, efs') → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=>^[k] rwp (src := src) (ι := ι) s E e₂ Φ) ⊢
      rswp (src := src) (ι := ι) k s E e₁ Φ :=
  rswp_lift_pure_det_step_no_fork
    (fun σ _ => primStep_reducible_of_baseStep_reducible (Hbred σ))
    (fun hs => Hpure _ _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible (Hbred _) hs))

/-- Rocq: `rswp_lift_pure_det_head_step_no_fork`. -/
theorem rswp_lift_pure_det_base_step_no_fork' (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ efs',
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, efs') → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    ▷^[k] rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rswp (src := src) (ι := ι) k s E e₁ Φ :=
  (step_fupdN_intro Std.LawfulSet.subset_refl).trans
    (rswp_lift_pure_det_base_step_no_fork (E' := E) Hbred Hpure)

end Iris.Transfinite
