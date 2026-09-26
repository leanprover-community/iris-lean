/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.WeakestPreTransfinite

/-! # Lifting lemmas for the weakest precondition of Transfinite Iris

This file ports `theories/program_logic/lifting.v` of Transfinite Iris: lifting lemmas for the
weakest precondition `wp` and for the strong weakest precondition `swp`. The lemmas for `swp` do
not require the expression to be a non-value, since `swp` always takes a program step.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Relation

theorem Iterate.succ_head_inv {α : Type _} {r : α → α → Prop} {n : Nat} {a c : α}
    (h : Iterate r (n + 1) a c) : ∃ b, r a b ∧ Iterate r n b c := by
  induction n generalizing c with
  | zero =>
    cases h with
    | tail y h₁ h₂ => cases h₁; exact ⟨c, h₂, .rfl c⟩
  | succ m ih =>
    cases h with
    | tail y h₁ h₂ =>
      obtain ⟨b, hab, hbc⟩ := ih h₁
      exact ⟨b, hab, .tail y hbc h₂⟩

end Relation

namespace Iris.Transfinite

open Iris ProgramLogic Language Language.Notation Iris.Std Iris.BI OFE PrimStep ToVal

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS Expr GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset} {e e₁ e₂ : Expr} {Φ : Val → IProp GF}

/-- Rocq: `wp_lift_step_fupd`. -/
theorem wp_lift_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗ |={∅,∅}=> ▷ |={∅,E}=>
        (ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost))
    ⊢ wp s E e₁ Φ := by
  rw [wp_unfold]
  simp only [wpPre, h]
  iintro H %σ₁ %κ %κs %n Hσ
  iapply lstep_intro
  iapply H $$ %σ₁ %κ %κs %n Hσ

/-- Rocq: `swp_lift_step_fupd`. -/
theorem swp_lift_step_fupd (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗ |={∅,∅}=> ▷ |={∅,E}=>
        (ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost))
    ⊢ swp k s E e₁ Φ := by
  unfold swp
  iintro H %σ₁ %κ %κs %n Hσ
  iapply lstepN_intro k
  iapply H $$ %σ₁ %κ %κs %n Hσ

/-- Rocq: `wp_lift_stuck`. -/
theorem wp_lift_stuck (h : toVal e = none) :
    (∀ σ κs n, ι.stateInterp σ κs n ={E,∅}=∗ ⌜Stuck (e, σ)⌝) ⊢ wp .MaybeStuck E e Φ := by
  rw [wp_unfold]
  simp only [wpPre, h]
  iintro H %σ₁ %κ %κs %n Hσ
  iapply lstep_intro
  imod H $$ %σ₁ %(κ ++ κs) %n Hσ with %Hstuck
  imodintro
  isplitr
  · ipureintro; trivial
  iintro %e₂ %σ₂ %efs %Hstep
  exact (Hstuck.2 _ _ _ _ Hstep).elim

/-! ## Derived lifting lemmas -/

/-- Rocq: `wp_lift_step`. -/
theorem wp_lift_step (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- Rocq: `swp_lift_step`. -/
theorem swp_lift_step (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E,∅}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_step_fupd k
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- A pure step without forks, given the premise of `wp_lift_step`. -/
private theorem lift_pure_step_body {σ₁ : State} {κ κs : List Obs} {n : Nat} (E' : CoPset)
    (hred : s.MaybeReducible (e₁, σ₁))
    (Hstep : ∀ κ σ₁ e₂ σ₂ efs, (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → κ = [] ∧ σ₂ = σ₁ ∧ efs = []) :
    ι.stateInterp σ₁ (κ ++ κs) n ∗
      (|={E}[E']▷=> ∀ κ e₂ efs σ, ⌜(e₁, σ) -<κ>-> (e₂, σ, efs)⌝ -∗ wp s E e₂ Φ) ⊢
    |={E,∅}=> ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={∅,E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost := by
  iintro ⟨Hσ, H⟩
  imod H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact hred
  inext
  iintro %e₂ %σ₂ %efs %Hst
  obtain ⟨rfl, rfl, rfl⟩ := Hstep _ _ _ _ _ Hst
  imod Hclose
  imod H
  imodintro
  ispecialize H $$ %_ %_ %_ %_ %Hst
  simp only [List.nil_append, List.length_nil, Nat.zero_add]
  iframe
  simp only [Algebra.BigOpL.bigOpL_nil]
  itrivial

/-- Rocq: `wp_lift_pure_step_no_fork`. -/
theorem wp_lift_pure_step_no_fork [Inhabited State] (E' : CoPset)
    (Hsafe : ∀ σ₁, match s with | .NotStuck => Reducible (e₁, σ₁) | _ => toVal e₁ = none)
    (Hstep : ∀ κ σ₁ e₂ σ₂ efs, (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → κ = [] ∧ σ₂ = σ₁ ∧ efs = []) :
    (|={E}[E']▷=> ∀ κ e₂ efs σ, ⌜(e₁, σ) -<κ>-> (e₂, σ, efs)⌝ -∗ wp s E e₂ Φ)
    ⊢ wp s E e₁ Φ := by
  have Hnone : toVal e₁ = none := by
    have := Hsafe default
    cases s
    · exact toVal_none_of_reducible this
    · exact this
  iintro H
  iapply wp_lift_step Hnone
  iintro %σ₁ %κ %κs %n Hσ
  have hred : s.MaybeReducible (e₁, σ₁) := by
    have := Hsafe σ₁
    cases s
    · exact this
    · trivial
  iapply lift_pure_step_body E' hred Hstep $$ [Hσ H]
  iframe

/-- Rocq: `swp_lift_pure_step_no_fork`. -/
theorem swp_lift_pure_step_no_fork (k : Nat) (E' : CoPset)
    (Hsafe : ∀ σ₁, s = .NotStuck → Reducible (e₁, σ₁))
    (Hstep : ∀ κ σ₁ e₂ σ₂ efs, (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → κ = [] ∧ σ₂ = σ₁ ∧ efs = []) :
    (|={E}[E']▷=> ∀ κ e₂ efs σ, ⌜(e₁, σ) -<κ>-> (e₂, σ, efs)⌝ -∗ wp s E e₂ Φ)
    ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_step k
  iintro %σ₁ %κ %κs %n Hσ
  have hred : s.MaybeReducible (e₁, σ₁) := by
    cases s
    · exact Hsafe σ₁ rfl
    · trivial
  iapply lift_pure_step_body E' hred Hstep $$ [Hσ H]
  iframe

/-- Rocq: `wp_lift_pure_stuck`. -/
theorem wp_lift_pure_stuck [Inhabited State] (Hstuck : ∀ σ, Stuck (e, σ)) :
    True ⊢ wp .MaybeStuck E e Φ := by
  iintro -
  iapply wp_lift_stuck (Hstuck default).1
  iintro %σ %κs %n -
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  exact Hstuck σ

/-- The atomic step body shared by `wp_lift_atomic_step_fupd` and `swp_lift_atomic_step_fupd`. -/
private theorem lift_atomic_step_body {σ₁ : State} {κ κs : List Obs} {n : Nat} :
    (⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E₁}[E₂]▷=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost) ⊢
    |={E₁,∅}=> ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ -∗ |={∅,∅}=> ▷ |={∅,E₁}=>
        (ι.stateInterp σ₂ κs (efs.length + n) ∗ wp s E₁ e₂ Φ ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost) := by
  iintro ⟨$, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose %e₂ %σ₂ %efs %Hstep
  imod Hclose with -
  imod H $$ %_ %_ %_ %Hstep with H
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose !>
  imod Hclose with -
  imod H with ⟨$, ⟨%v, %hv, HQ⟩, $⟩
  obtain rfl := (toVal_eq_iff_coe e₂ v).mpr hv
  iapply wp_value v $$ HQ

/-- Rocq: `wp_lift_atomic_step_fupd`. -/
theorem wp_lift_atomic_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E₁}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E₁}[E₂]▷=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E₁ e₁ Φ := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with H
  iapply lift_atomic_step_body $$ H

/-- Rocq: `swp_lift_atomic_step_fupd`. -/
theorem swp_lift_atomic_step_fupd (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E₁}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E₁}[E₂]▷=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ swp k s E₁ e₁ Φ := by
  iintro H
  iapply swp_lift_step_fupd k
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with H
  iapply lift_atomic_step_body $$ H

/-- Rocq: `wp_lift_atomic_step`. -/
theorem wp_lift_atomic_step (h : toVal e₁ = none) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E₂ := E) h
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- Rocq: `swp_lift_atomic_step`. -/
theorem swp_lift_atomic_step (k : Nat) :
    (∀ σ₁ κ κs n, ι.stateInterp σ₁ (κ ++ κs) n ={E}=∗
      ⌜s.MaybeReducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ efs, ⌜(e₁, σ₁) -<κ>-> (e₂, σ₂, efs)⌝ ={E}=∗
        ι.stateInterp σ₂ κs (efs.length + n) ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
          [∗list] ef ∈ efs, wp s ⊤ ef ι.forkPost)
    ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_atomic_step_fupd (E₂ := E) k
  iintro %σ₁ %κ %κs %n Hσ
  imod H $$ %σ₁ %κ %κs %n Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

/-- Rocq: `wp_lift_pure_det_step_no_fork`. -/
theorem wp_lift_pure_det_step_no_fork [Inhabited State] (E' : CoPset)
    (Hsafe : ∀ σ₁, match s with | .NotStuck => Reducible (e₁, σ₁) | _ => toVal e₁ = none)
    (Hpuredet : ∀ {σ₁ κ e₂' σ₂ efs'}, (e₁, σ₁) -<κ>-> (e₂', σ₂, efs') →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=> wp s E e₂ Φ) ⊢ wp s E e₁ Φ := by
  iintro H
  iapply wp_lift_pure_step_no_fork E' Hsafe
    (fun _ _ _ _ _ h => ⟨(Hpuredet h).1, (Hpuredet h).2.1, (Hpuredet h).2.2.2⟩)
  iapply step_fupd_wand $$ H
  iintro H %κ %e' %efs' %σ %Hst
  obtain ⟨-, -, rfl, -⟩ := Hpuredet Hst
  iexact H

/-- Rocq: `swp_lift_pure_det_step_no_fork`. -/
theorem swp_lift_pure_det_step_no_fork (k : Nat) (E' : CoPset)
    (Hsafe : ∀ σ₁, s = .NotStuck → Reducible (e₁, σ₁))
    (Hpuredet : ∀ {σ₁ κ e₂' σ₂ efs'}, (e₁, σ₁) -<κ>-> (e₂', σ₂, efs') →
      κ = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=> wp s E e₂ Φ) ⊢ swp k s E e₁ Φ := by
  iintro H
  iapply swp_lift_pure_step_no_fork k E' Hsafe
    (fun _ _ _ _ _ h => ⟨(Hpuredet h).1, (Hpuredet h).2.1, (Hpuredet h).2.2.2⟩)
  iapply step_fupd_wand $$ H
  iintro H %κ %e' %efs' %σ %Hst
  obtain ⟨-, -, rfl, -⟩ := Hpuredet Hst
  iexact H

/-- A pure step can be lifted to the weakest precondition. -/
private theorem wp_pure_prim_step [Inhabited State] (E' : CoPset) (hstep : e₁ -ᵖ-> e₂) :
    (|={E}[E']▷=> wp s E e₂ Φ) ⊢ wp s E e₁ Φ := by
  obtain ⟨Hsafe, Hdet⟩ := hstep
  refine wp_lift_pure_det_step_no_fork E' (fun σ => ?_) (fun h => ?_)
  · have hred : Reducible (e₁, σ) := reducible_of_reducibleNoObs (Hsafe σ)
    cases s
    · exact hred
    · exact toVal_none_of_reducible hred
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := Hdet h
    exact ⟨h₁, h₂.symm, h₃.symm, h₄⟩

/-- Rocq: `wp_pure_step_fupd` (for an explicit sequence of pure steps). -/
theorem wp_pure_steps_fupd [Inhabited State] (E' : CoPset) {n : Nat} (hsteps : e₁ -ᵖ->^[n] e₂) :
    (|={E}[E']▷=>^[n] wp s E e₂ Φ) ⊢ wp s E e₁ Φ := by
  induction hsteps using Relation.Iterate.head_induction_on with
  | rfl => exact .rfl
  | head c hstep _ IH => exact (step_fupd_mono IH).trans (wp_pure_prim_step E' hstep)

/-- Rocq: `wp_pure_step_fupd`. -/
theorem wp_pure_step_fupd [Inhabited State] (E' : CoPset) {φ : Prop} {n : Nat}
    [Hexec : PureExec φ n e₁ e₂] (Hφ : φ) :
    (|={E}[E']▷=>^[n] wp s E e₂ Φ) ⊢ wp s E e₁ Φ :=
  wp_pure_steps_fupd E' (Hexec.pureExec Hφ)

/-- Rocq: `wp_pure_step_later`. -/
theorem wp_pure_step_later [Inhabited State] {φ : Prop} {n : Nat} [PureExec φ n e₁ e₂]
    (Hφ : φ) : ▷^[n] wp s E e₂ Φ ⊢ wp s E e₁ Φ := by
  refine .trans ?_ (wp_pure_step_fupd E Hφ)
  generalize wp s E e₂ Φ = P
  induction n with
  | zero => exact .rfl
  | succ n IH =>
    rw [(laterN_succ_left n).to_eq]
    exact (later_mono IH).trans (step_fupd_intro Std.LawfulSet.subset_refl)

/-- Rocq: `swp_pure_step_fupd`. -/
theorem swp_pure_step_fupd [Inhabited State] (k : Nat) (E' : CoPset) {φ : Prop} {n : Nat}
    [Hexec : PureExec φ (n + 1) e₁ e₂] (Hφ : φ) :
    (|={E}[E']▷=>^[n + 1] wp s E e₂ Φ) ⊢ swp k s E e₁ Φ := by
  obtain ⟨e', ⟨Hsafe, Hdet⟩, hrest⟩ := Relation.Iterate.succ_head_inv (Hexec.pureExec Hφ)
  refine .trans ?_ (swp_lift_pure_det_step_no_fork (e₂ := e') k E'
    (fun σ _ => reducible_of_reducibleNoObs (Hsafe σ)) (fun h => ?_))
  · exact step_fupd_mono (wp_pure_steps_fupd E' hrest)
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := Hdet h
    exact ⟨h₁, h₂.symm, h₃.symm, h₄⟩

/-- Rocq: `swp_pure_step_later`. -/
theorem swp_pure_step_later [Inhabited State] (k : Nat) {φ : Prop} {n : Nat}
    [PureExec φ (n + 1) e₁ e₂] (Hφ : φ) : ▷^[n + 1] wp s E e₂ Φ ⊢ swp k s E e₁ Φ := by
  refine .trans ?_ (swp_pure_step_fupd k E Hφ)
  generalize wp s E e₂ Φ = P
  generalize n + 1 = m
  induction m with
  | zero => exact .rfl
  | succ m IH =>
    rw [(laterN_succ_left m).to_eq]
    exact (later_mono IH).trans (step_fupd_intro Std.LawfulSet.subset_refl)

end Iris.Transfinite
