/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.LiftingTransfinite
public import Iris.ProgramLogic.EctxiLanguage

/-! # Lifting lemmas for evaluation-context languages (Transfinite Iris)

This file ports `theories/program_logic/ectx_lifting.v` of Transfinite Iris: lifting lemmas for
the transfinite weakest preconditions `wp` and `swp` in terms of base (head) steps.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris ProgramLogic Language.Notation EctxLanguage EctxLanguage.Notation Iris.Std Iris.BI OFE

variable {Expr Ectx State Obs Val : Type _}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS Expr GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset} {e e₁ e₂ : Expr} {Φ : Val → IProp GF}

theorem maybeReducible_of_baseStep_reducible {σ : State} (h : BaseStep.Reducible (e₁, σ)) :
    s.MaybeReducible (e₁, σ) := by
  cases s
  · exact primStep_reducible_of_baseStep_reducible h
  · trivial

/-- Rocq: `wp_lift_head_step_fupd`. -/
theorem wp_lift_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ -∗ |={∅,∅}=> ▷ |={∅,E}=>
        (ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost))
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact maybeReducible_of_baseStep_reducible Hred
  iintro %e₂ %σ₂ %efs %Hstep
  iapply H $$ %_ %_ %_
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hred Hstep

/-- Rocq: `wp_lift_head_step`. -/
theorem wp_lift_base_step (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_base_step_fupd h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- Rocq: `wp_lift_head_stuck`. -/
theorem wp_lift_base_stuck (h : toVal e = none) (sav : SubredexesAreValues e) :
    (∀ σ κs n, ι.stateInterp σ κs n ={E,∅}=∗ ⌜BaseStep.Stuck (e, σ)⌝)
    ⊢ wp .MaybeStuck E e Φ := by
  iintro H
  iapply wp_lift_stuck h
  iintro %σ %κs %n Hσ
  imod H $$ %σ %κs %n Hσ with %H
  ipureintro
  exact primStep_stuck_of_baseStep_stuck H sav

/-- Rocq: `wp_lift_pure_head_stuck`. -/
theorem wp_lift_pure_base_stuck (h : toVal e = none) (sav : SubredexesAreValues e)
    (Hstuck : ∀ σ, BaseStep.Stuck (e, σ)) : ⊢ wp .MaybeStuck E e Φ := by
  iapply wp_lift_base_stuck h sav
  iintro %σ %κs %n -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  exact Hstuck σ

/-- Rocq: `wp_lift_atomic_head_step_fupd`. -/
theorem wp_lift_atomic_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E₁}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E₁}[E₂]▷=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E₁ e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E₂ := E₂) h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact maybeReducible_of_baseStep_reducible Hred
  iintro %e₂ %σ₂ %efs %Hstep
  iapply H $$ %_ %_ %_
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hred Hstep

/-- Rocq: `wp_lift_atomic_head_step`. -/
theorem wp_lift_atomic_base_step (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact maybeReducible_of_baseStep_reducible Hred
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  iapply H $$ %_ %_ %_
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hred Hstep

/-- Rocq: `swp_lift_atomic_head_step`. -/
theorem swp_lift_atomic_base_step (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_atomic_step k
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact maybeReducible_of_baseStep_reducible Hred
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  iapply H $$ %_ %_ %_
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hred Hstep

/-- Rocq: `wp_lift_atomic_head_step_no_fork_fupd`. -/
theorem wp_lift_atomic_base_step_no_fork_fupd (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E₁}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E₁}[E₂]▷=∗
        ⌜efs = []⌝ ∗ ι.stateInterp σ₂ κs n ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ wp s E₁ e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_base_step_fupd (E₂ := E₂) h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  imodintro
  iintro %e₂ %σ₂ %efs %Hstep
  imod H $$ %_ %_ %_ %Hstep with H
  iintro !> !>
  imod H with ⟨%h, _, _⟩
  subst h
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `wp_lift_atomic_head_step_no_fork`. -/
theorem wp_lift_atomic_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ⌜efs = []⌝ ∗ ι.stateInterp σ₂ κs n ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_base_step h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  imodintro
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  imod H $$ %_ %_ %_ %Hstep with ⟨%h, _, _⟩
  subst h
  imodintro
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `swp_lift_atomic_head_step_no_fork`. -/
theorem swp_lift_atomic_base_step_no_fork (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>->ᵇ (e₂, σ₂, efs)⌝ ={E}=∗
        ⌜efs = []⌝ ∗ ι.stateInterp σ₂ κs n ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_atomic_base_step k
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  imodintro
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  imod H $$ %_ %_ %_ %Hstep with ⟨%h, _, _⟩
  subst h
  imodintro
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `wp_lift_pure_det_head_step_no_fork`. -/
theorem wp_lift_pure_det_base_step_no_fork [Inhabited State] (E' : CoPset) (h : toVal e₁ = none)
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ efs',
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, efs') → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=> wp s E e₂ Φ) ⊢ wp s E e₁ Φ :=
  wp_lift_pure_det_step_no_fork E'
    (fun σ => by
      have := primStep_reducible_of_baseStep_reducible (Hbred σ)
      cases s
      · exact this
      · exact h)
    (fun hs => Hpure _ _ _ _ _ (baseStep_of_primStep_of_baseStep_reducible (Hbred _) hs))

/-- Rocq: `wp_lift_pure_det_head_step_no_fork'`. -/
theorem wp_lift_pure_det_base_step_no_fork' [Inhabited State] (h : toVal e₁ = none)
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ κ e₂' σ₂ efs',
      (e₁, σ₁) -<κ>->ᵇ (e₂', σ₂, efs') → κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    ▷ wp s E e₂ Φ ⊢ wp s E e₁ Φ :=
  (step_fupd_intro Std.LawfulSet.subset_refl).trans
    (wp_lift_pure_det_base_step_no_fork E h Hbred Hpure)

end Iris.Transfinite
