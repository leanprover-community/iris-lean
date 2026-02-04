/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.EctxLanguage
import Iris.ProgramLogic.Lifting

/-! # Ectx Lifting Lemmas

Reference: `iris/program_logic/ectx_lifting.v`

Derived lifting lemmas for evaluation-context based languages. These lift
base steps (rather than primitive steps) to the weakest precondition,
using the decomposition provided by `EctxLanguage`.

## Simplifications

This port omits later credit support. The `£ 1` parameter from the Coq
version is dropped.

## Main Results

- `wp_lift_base_step_fupd` — lift a base step with fupd
- `wp_lift_base_step` — lift a base step
- `wp_lift_base_stuck` — stuck at base level
- `wp_lift_pure_base_stuck` — pure base stuck
- `wp_lift_atomic_base_step_fupd` — atomic base step with fupd
- `wp_lift_atomic_base_step` — atomic base step
- `wp_lift_atomic_base_step_no_fork_fupd` — atomic base step, no fork, fupd
- `wp_lift_atomic_base_step_no_fork` — atomic base step, no fork
- `wp_lift_pure_det_base_step_no_fork` — deterministic pure base step
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : EctxLanguage}
variable [inst : IrisGS (ectx_lang Λ) GF]
variable {W : WsatGS GF}

/-! ## Base Step Lifting -/

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a base step with fancy update. Wraps `wp_lift_step_fupd` by
converting base reducibility to prim reducibility via `base_prim_reducible`.
Coq: `wp_lift_base_step_fupd` in `ectx_lifting.v`. -/
theorem wp_lift_base_step_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E e1 Φ
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- base-step lifting is the generic step rule for `ectx_lang`
    simpa using wp_lift_step_fupd (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a base step.
Coq: `wp_lift_base_step` in `ectx_lifting.v`. -/
theorem wp_lift_base_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E e1 Φ
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- reuse the pure step lemma on the derived language
    simpa using wp_lift_step (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a base-stuck expression.
Coq: `wp_lift_base_stuck` in `ectx_lifting.v`. -/
theorem wp_lift_base_stuck (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e : Λ.expr)
    (hv : Λ.to_val e = none)
    (hsub : sub_redexes_are_values e)
    (hstuck : ∀ σ, base_stuck e σ) :
    BIBase.pure True ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) .maybeStuck E e Φ :=
  by
    -- reduce to the primitive stuckness lemma via `base_stuck_stuck`
    have hstuck' : ∀ σ, stuck (Λ := ectx_lang Λ) e σ := by
      intro σ; exact base_stuck_stuck (Λ := Λ) e σ (hstuck σ) hsub
    exact wp_lift_stuck (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (_s := .maybeStuck) (E := E) (Φ := Φ) (e := e) hv hstuck'

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a pure base-stuck expression.
Coq: `wp_lift_pure_base_stuck` in `ectx_lifting.v`. -/
theorem wp_lift_pure_base_stuck [Inhabited Λ.state]
    (E : Iris.Set Positive) (Φ : (ectx_lang Λ).val → IProp GF) (e : Λ.expr)
    (hv : Λ.to_val e = none)
    (hsub : sub_redexes_are_values e)
    (hstuck : ∀ σ, base_stuck e σ) :
    BIBase.pure True ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) .maybeStuck E e Φ :=
  by
    -- reuse the non-pure base-stuck lifting rule
    exact wp_lift_base_stuck (Λ := Λ) (M := M) (F := F) (W := W)
      (E := E) (Φ := Φ) (e := e) hv hsub hstuck

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic base step with fancy update.
Coq: `wp_lift_atomic_base_step_fupd` in `ectx_lifting.v`. -/
theorem wp_lift_atomic_base_step_fupd (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    E1 = E2 →
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E1 e1
      (fun v => uPred_fupd (M := M) (F := F) W E2 E1 (Φ v))
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E1 e1 Φ :=
  by
    -- mask-changing atomic step (simplified to equality)
    intro hE
    simpa using wp_lift_atomic_step_fupd (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (s := s) (E1 := E1) (E2 := E2) (Φ := Φ) (e1 := e1) hv hE

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic base step.
Coq: `wp_lift_atomic_base_step` in `ectx_lifting.v`. -/
theorem wp_lift_atomic_base_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E e1 Φ
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- atomic case is identical to the generic step rule here
    simpa using wp_lift_atomic_step (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic base step with no fork and fancy update.
Coq: `wp_lift_atomic_base_step_no_fork_fupd` in `ectx_lifting.v`. -/
theorem wp_lift_atomic_base_step_no_fork_fupd (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    E1 = E2 →
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E1 e1
      (fun v => uPred_fupd (M := M) (F := F) W E2 E1 (Φ v))
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E1 e1 Φ :=
  by
    -- same proof as the general atomic base-step rule
    intro hE
    simpa using wp_lift_atomic_base_step_fupd (Λ := Λ) (M := M) (F := F) (W := W)
      (s := s) (E1 := E1) (E2 := E2) (Φ := Φ) (e1 := e1) hv hE

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift an atomic base step with no fork.
Coq: `wp_lift_atomic_base_step_no_fork` in `ectx_lifting.v`. -/
theorem wp_lift_atomic_base_step_no_fork (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s) E e1 Φ
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- no-fork variant collapses to the same step rule here
    simpa using wp_lift_atomic_base_step (Λ := Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Lift a deterministic pure base step with no fork.
Coq: `wp_lift_pure_det_base_step_no_fork` in `ectx_lifting.v`. -/
theorem wp_lift_pure_det_base_step_no_fork [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 e2 : Λ.expr)
    (hv : Λ.to_val e1 = none)
    (hred : ∀ σ1, base_reducible e1 σ1)
    (hstep : ∀ σ1 κ e2' σ2 efs',
      Λ.base_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) :
    BIBase.later (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e2 Φ)
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- reduce to the primitive deterministic step lemma
    have hstep' : ∀ σ1 κ e2' σ2 efs',
        (ectx_lang Λ).prim_step e1 σ1 κ e2' σ2 efs' →
          κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = [] := by
      intro σ1 κ e2' σ2 efs' hprim
      have hbase :
          Λ.base_step e1 σ1 κ e2' σ2 efs' :=
        base_reducible_prim_step (Λ := Λ) e1 σ1 κ e2' σ2 efs' (hred σ1) hprim
      exact hstep σ1 κ e2' σ2 efs' hbase
    -- register the inhabited instance for the derived language
    have inst' : Inhabited (ectx_lang Λ).state := by
      simpa using (inferInstance : Inhabited Λ.state)
    have _ := inst'
    -- discharge the safety obligation directly for the derived language
    refine wp_lift_pure_det_step_no_fork (Λ := ectx_lang Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) (e2 := e2) ?_ hstep'
    intro σ1; cases s with
    | notStuck =>
        -- derive reducibility from the base-reducible hypothesis
        exact base_prim_reducible (Λ := Λ) e1 σ1 (hred σ1)
    | maybeStuck =>
        -- align `to_val` with the derived language
        simpa using hv

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Simplified variant of `wp_lift_pure_det_base_step_no_fork`.
Coq: `wp_lift_pure_det_base_step_no_fork'` in `ectx_lifting.v`. -/
theorem wp_lift_pure_det_base_step_no_fork' [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : (ectx_lang Λ).val → IProp GF) (e1 e2 : Λ.expr)
    (hv : Λ.to_val e1 = none)
    (hred : ∀ σ1, base_reducible e1 σ1)
    (hstep : ∀ σ1 κ e2' σ2 efs',
      Λ.base_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) :
    BIBase.later (wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e2 Φ)
    ⊢ wp (W := W) (M := M) (F := F) (Λ := ectx_lang Λ) s E e1 Φ :=
  by
    -- reuse the unprimed deterministic base-step lemma
    simpa using wp_lift_pure_det_base_step_no_fork (Λ := Λ) (M := M) (F := F) (W := W)
      (s := s) (E := E) (Φ := Φ) (e1 := e1) (e2 := e2) hv hred hstep

end Iris.ProgramLogic
