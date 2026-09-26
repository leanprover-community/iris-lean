/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefWeakestPre
public import Iris.ProgramLogic.LiftingTransfinite

/-! # Lifting lemmas for the refinement weakest precondition (Transfinite Iris)

This file ports `theories/program_logic/refinement/ref_lifting.v` of Transfinite Iris. The lemmas
for `rswp` are designed for a single step: after the step, `rswp` continues as `rwp`.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.BI

open Iris.Std LawfulSet BIFUpdate

variable [BI PROP] [BIFUpdate PROP]

/-- Rocq: `step_fupdN_mask_comm`. -/
theorem step_fupdN_mask_comm (n : Nat) {E1 E2 E3 E4 : CoPset} {P : PROP} (h12 : E1 ⊆ E2)
    (h43 : E4 ⊆ E3) :
    (|={E1,E2}=> |={E2}[E3]▷=>^[n] P) ⊢ |={E1}[E4]▷=>^[n] |={E1,E2}=> P := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    dsimp only [Nat.repeat]
    iintro H
    imod H
    imod H
    iapply fupd_mask_intro h43
    iintro Hclose
    inext
    imod Hclose
    imod H
    iapply fupd_mask_intro h12
    iintro Hclose'
    iapply ih
    imod Hclose'
    imodintro
    iexact H

/-- Rocq: `step_fupdN_mask_comm'`. -/
theorem step_fupdN_mask_comm' (n : Nat) {E1 E2 : CoPset} {P : PROP} (h : E2 ⊆ E1) :
    (|={E1}[E1]▷=>^[n] |={E1,E2}=> P) ⊢ |={E1,E2}=> |={E2}[E2]▷=>^[n] P := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    dsimp only [Nat.repeat]
    iintro H
    imod H
    iapply fupd_mask_intro h
    iintro Hclose
    imodintro
    inext
    imod Hclose
    imod H
    iapply ih $$ H

end Iris.BI

namespace Iris.Transfinite

open Iris ProgramLogic Language Language.Notation Iris.Std Iris.BI OFE PrimStep ToVal Relation

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} {A : Type _} [src : Source GF A] [ι : RefIrisGS Expr GF]
variable {k : Nat} {s : Stuckness} {E E' : CoPset} {e₁ e₂ : Expr} {Φ : Val → IProp GF}

/-- Rocq: `rwp_lift_step_fupd`. -/
theorem rwp_lift_step_fupd (h : toVal e₁ = none) :
    rwpStep (src := src) E s e₁ (fun e₂ efs =>
      iprop(rwp (src := src) (ι := ι) s E e₂ Φ ∗
        [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rwp (src := src) (ι := ι) s E e₁ Φ := by
  refine .trans ?_ rwp_unfold.mpr
  unfold rwpPre
  rw [h]

/-- Rocq: `rwp_lift_pure_step_no_fork`. -/
theorem rwp_lift_pure_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, match s with | .NotStuck => Reducible (e₁, σ₁) | _ => toVal e₁ = none)
    (Hstep : ∀ κ σ₁ e₂ σ₂ efs, (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → κ = [] ∧ σ₂ = σ₁ ∧ efs = []) :
    (∀ κ e₂ efs σ, ⌜(e₁, σ) -<κ>-> (e₂, σ, efs)⌝ → rwp (src := src) (ι := ι) s E e₂ Φ) ⊢
      rwp (src := src) (ι := ι) s E e₁ Φ := by
  have Hnone : toVal e₁ = none := by
    have := Hsafe default
    cases s
    · exact toVal_none_of_reducible this
    · exact this
  iintro H
  iapply rwp_lift_step_fupd Hnone
  unfold rwpStep
  iintro %σ₁ %n %a ⟨Ha, Hσ⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iexists false
  rw [laterIf_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  imodintro
  isplitr
  · ipureintro
    have := Hsafe σ₁
    cases s
    · exact this
    · trivial
  iintro %e₂ %σ₂ %efs %κ %Hst
  obtain ⟨rfl, rfl, rfl⟩ := Hstep _ _ _ _ _ Hst
  imod Hclose
  imodintro
  ihave H := H $$ %_ %_ %_ %_ %Hst
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `rwp_lift_pure_det_step_no_fork`. -/
theorem rwp_lift_pure_det_step_no_fork [Inhabited State]
    (Hsafe : ∀ σ₁, match s with | .NotStuck => Reducible (e₁, σ₁) | _ => toVal e₁ = none)
    (Hpuredet : ∀ {σ₁ κ e₂' σ₂ efs'}, (e₁, σ₁) -<κ>-> (e₂', σ₂, efs') →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rwp (src := src) (ι := ι) s E e₁ Φ := by
  iintro H
  iapply rwp_lift_pure_step_no_fork Hsafe
    (fun _ _ _ _ _ h => ⟨(Hpuredet h).1, (Hpuredet h).2.1, (Hpuredet h).2.2.2⟩)
  iintro %κ %e' %efs' %σ %Hst
  obtain ⟨-, -, rfl, -⟩ := Hpuredet Hst
  iexact H

/-- Rocq: `rwp_pure_step` (for an explicit sequence of pure steps). -/
theorem rwp_pure_steps [Inhabited State] {n : Nat} (hsteps : e₁ -ᵖ->^[n] e₂) :
    rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rwp (src := src) (ι := ι) s E e₁ Φ := by
  induction hsteps using Relation.Iterate.head_induction_on with
  | rfl => exact .rfl
  | head c hstep _ IH =>
    refine IH.trans ?_
    obtain ⟨Hsafe, Hdet⟩ := hstep
    refine rwp_lift_pure_det_step_no_fork (fun σ => ?_) (fun h => ?_)
    · have hred : Reducible (_, σ) := reducible_of_reducibleNoObs (Hsafe σ)
      cases s
      · exact hred
      · exact toVal_none_of_reducible hred
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := Hdet h
      exact ⟨h₁, h₂.symm, h₃.symm, h₄⟩

/-- Rocq: `rwp_pure_step`. -/
theorem rwp_pure_step [Inhabited State] {φ : Prop} {n : Nat} [Hexec : PureExec φ n e₁ e₂]
    (Hφ : φ) : rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rwp (src := src) (ι := ι) s E e₁ Φ :=
  rwp_pure_steps (Hexec.pureExec Hφ)

/-- Rocq: `rswp_lift_step_fupd`. -/
theorem rswp_lift_step_fupd :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E,∅}=∗ |={∅}[∅]▷=>^[k] (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ rwp (src := src) (ι := ι) s E e₂ Φ ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  unfold rswp rswpStep
  iintro H %σ₁ %n %a ⟨Ha, Hσ⟩
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro ⟨$, H⟩
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  dsimp only
  iframe

/-- Rocq: `rswp_lift_step`. -/
theorem rswp_lift_step :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E,∅}=∗ ▷^[k] (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ rwp (src := src) (ι := ι) s E e₂ Φ ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_step_fupd
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply step_fupdN_intro LawfulSet.subset_refl $$ H

/-- Rocq: `rswp_lift_pure_step_no_fork`. -/
theorem rswp_lift_pure_step_no_fork
    (Hsafe : ∀ σ₁, s = .NotStuck → Reducible (e₁, σ₁))
    (Hstep : ∀ κ σ₁ e₂ σ₂ efs, (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → κ = [] ∧ σ₂ = σ₁ ∧ efs = []) :
    (|={E}=> |={E}[E']▷=>^[k] ∀ κ e₂ efs σ, ⌜(e₁, σ) -<κ>-> (e₂, σ, efs)⌝ →
      rwp (src := src) (ι := ι) s E e₂ Φ) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_step_fupd
  iintro %σ₁ %n Hσ
  imod H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply step_fupdN_wand $$ [Hclose H]
  · iapply step_fupdN_mask_comm k (E1 := ∅) (E2 := E) (E3 := E') (E4 := ∅)
      LawfulSet.empty_subset LawfulSet.empty_subset
    imod Hclose
    imodintro
    iexact H
  iintro H
  isplitr
  · ipureintro
    cases s
    · exact Hsafe σ₁ rfl
    · trivial
  iintro %e₂ %σ₂ %efs %κ %Hst
  imod H
  imodintro
  obtain ⟨rfl, rfl, rfl⟩ := Hstep _ _ _ _ _ Hst
  ihave H := H $$ %_ %_ %_ %_ %Hst
  simp only [List.length_nil, Nat.zero_add, Algebra.BigOpL.bigOpL_nil]
  iframe

/-- Rocq: `rswp_lift_atomic_step_fupd`. -/
theorem rswp_lift_atomic_step_fupd :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E}=∗ |={E}[E]▷=>^[k] (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_step_fupd
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  iapply step_fupdN_mask_comm' k LawfulSet.empty_subset
  iapply step_fupdN_wand $$ H
  iintro ⟨%Hred, H⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact Hred
  iintro %e₂ %σ₂ %efs %κ %Hstep
  imod Hclose
  imod H $$ %e₂ %σ₂ %efs %κ %Hstep with ⟨Hσ, ⟨%v, %hv, HΦ⟩, Hefs⟩
  obtain rfl := (ToVal.toVal_eq_iff_coe e₂ v).mpr hv
  imodintro
  iframe Hσ Hefs
  iapply rwp_value' $$ HΦ

/-- Rocq: `rswp_lift_atomic_step`. -/
theorem rswp_lift_atomic_step :
    (∀ σ₁ n, ι.refStateInterp σ₁ n ={E}=∗ ▷^[k] (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs (κ : List Obs), ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E}=∗
        ι.refStateInterp σ₂ (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, rwp (src := src) (ι := ι) s ⊤ ef ι.refForkPost)) ⊢
    rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_atomic_step_fupd
  iintro %σ₁ %n Hσ
  imod H $$ %σ₁ %n Hσ with H
  imodintro
  iapply step_fupdN_intro LawfulSet.subset_refl $$ H

/-- Rocq: `rswp_lift_pure_det_step_no_fork`. -/
theorem rswp_lift_pure_det_step_no_fork
    (Hsafe : ∀ σ₁, s = .NotStuck → Reducible (e₁, σ₁))
    (Hpuredet : ∀ {σ₁ κ e₂' σ₂ efs'}, (e₁, σ₁) -<κ>-> (e₂', σ₂, efs') →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=>^[k] rwp (src := src) (ι := ι) s E e₂ Φ) ⊢
      rswp (src := src) (ι := ι) k s E e₁ Φ := by
  iintro H
  iapply rswp_lift_pure_step_no_fork Hsafe
    (fun _ _ _ _ _ h => ⟨(Hpuredet h).1, (Hpuredet h).2.1, (Hpuredet h).2.2.2⟩)
  imodintro
  iapply step_fupdN_wand $$ H
  iintro H %κ %e' %efs' %σ %Hst
  obtain ⟨-, -, rfl, -⟩ := Hpuredet Hst
  iexact H

/-- Rocq: `rswp_pure_step_fupd`. -/
theorem rswp_pure_step_fupd {φ : Prop} [Hexec : PureExec φ 1 e₁ e₂] (Hφ : φ) :
    (|={E}[E']▷=>^[k] rwp (src := src) (ι := ι) s E e₂ Φ) ⊢
      rswp (src := src) (ι := ι) k s E e₁ Φ := by
  obtain ⟨e', ⟨Hsafe, Hdet⟩, hrest⟩ := Relation.Iterate.succ_head_inv (Hexec.pureExec Hφ)
  cases hrest
  refine rswp_lift_pure_det_step_no_fork (fun σ _ => reducible_of_reducibleNoObs (Hsafe σ))
    (fun h => ?_)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Hdet h
  exact ⟨h₁, h₂.symm, h₃.symm, h₄⟩

/-- Rocq: `rswp_pure_step_later`. -/
theorem rswp_pure_step_later {φ : Prop} [PureExec φ 1 e₁ e₂] (Hφ : φ) :
    ▷^[k] rwp (src := src) (ι := ι) s E e₂ Φ ⊢ rswp (src := src) (ι := ι) k s E e₁ Φ :=
  (step_fupdN_intro LawfulSet.subset_refl).trans (rswp_pure_step_fupd (E' := E) Hφ)

end Iris.Transfinite
