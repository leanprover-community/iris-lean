/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.WeakestPre

/-! # Lifting Lemmas

Reference: `iris/program_logic/lifting.v`

The lifting lemmas serve to lift the rules of the operational semantics
to the program logic. They connect the primitive step relation of the
language to the weakest precondition.

## Simplifications

This port omits later credit support. The `£ 1` and `step_fupdN`
infrastructure from the Coq version is dropped. The `num_laters_per_step`
is fixed to 0.

## Main Results

- `wp_lift_step_fupd` — lift a single step to WP (with fupd)
- `wp_lift_step` — lift a single step to WP
- `wp_lift_stuck` — stuck expression satisfies any WP at `maybeStuck`
- `wp_lift_pure_step_no_fork` — lift a pure, fork-free step
- `wp_lift_atomic_step_fupd` — lift an atomic step with fupd
- `wp_lift_atomic_step` — lift an atomic step
- `wp_lift_pure_det_step_no_fork` — lift a deterministic pure step
- `wp_lift_pure_stuck` — pure stuck expression
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

variable {Λ : Language}
variable [inst : IrisGS Λ GF]

/-! ## Core Lifting Lemmas -/

/-- Lift a single step to WP with fupd. Unfolds the WP fixpoint one step.
The hypothesis must provide state interpretation update and recursive WP
for the continuation, with a `▷` guarding the post-step obligation.
Coq: `wp_lift_step_fupd` in `lifting.v`. -/
noncomputable def wp_lift_step_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (M := M) (F := F) s (wp (M := M) (F := F) s) E e1 Φ ⊢ wp (M := M) (F := F) s E e1 Φ :=
  sorry

/-- Lift a single step to WP. Like `wp_lift_step_fupd` but with `▷`
before the continuation rather than fupd.
Coq: `wp_lift_step` in `lifting.v`. -/
theorem wp_lift_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (M := M) (F := F) s (wp (M := M) (F := F) s) E e1 Φ ⊢ wp (M := M) (F := F) s E e1 Φ :=
  sorry

/-- Lift a stuck expression: if `e` is stuck in every reachable state,
then `WP e @ E ?{{ Φ }}` holds.
Coq: `wp_lift_stuck` in `lifting.v`. -/
theorem wp_lift_stuck (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e : Λ.expr)
    (hv : Λ.to_val e = none)
    (hstuck : ∀ σ, stuck e σ) :
    BIBase.pure True ⊢ wp (M := M) (F := F) .maybeStuck E e Φ :=
  sorry

/-- Lift a pure, fork-free step.
Coq: `wp_lift_pure_step_no_fork` in `lifting.v`. -/
theorem wp_lift_pure_step_no_fork [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ κ σ1 e2 σ2 efs, Λ.prim_step e1 σ1 κ e2 σ2 efs →
      κ = [] ∧ σ2 = σ1 ∧ efs = []) :
    BIBase.later
      (BIBase.forall fun κ =>
        BIBase.forall fun e2 =>
          BIBase.forall fun efs =>
            BIBase.forall fun σ =>
              BIBase.wand
                (BIBase.pure (Λ.prim_step e1 σ κ e2 σ efs))
                (wp (M := M) (F := F) s E e2 Φ))
    ⊢ wp (M := M) (F := F) s E e1 Φ :=
  sorry

/-- Lift an atomic step with fancy update.
Coq: `wp_lift_atomic_step_fupd` in `lifting.v`. -/
theorem wp_lift_atomic_step_fupd (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (M := M) (F := F) s (wp (M := M) (F := F) s) E1 e1
      (fun v => uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst) E2 E1 (Φ v))
    ⊢ wp (M := M) (F := F) s E1 e1 Φ :=
  sorry

/-- Lift an atomic step.
Coq: `wp_lift_atomic_step` in `lifting.v`. -/
theorem wp_lift_atomic_step (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 : Λ.expr)
    (hv : Λ.to_val e1 = none) :
    wp_pre (M := M) (F := F) s (wp (M := M) (F := F) s) E e1 Φ ⊢ wp (M := M) (F := F) s E e1 Φ :=
  sorry

/-- Lift a deterministic pure step with no fork.
Coq: `wp_lift_pure_det_step_no_fork` in `lifting.v`. -/
theorem wp_lift_pure_det_step_no_fork [Inhabited Λ.state]
    (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (e1 e2 : Λ.expr)
    (hsafe : ∀ σ1, match s with
      | .notStuck => reducible e1 σ1
      | .maybeStuck => Λ.to_val e1 = none)
    (hstep : ∀ σ1 κ e2' σ2 efs', Λ.prim_step e1 σ1 κ e2' σ2 efs' →
      κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) :
    BIBase.later (wp (M := M) (F := F) s E e2 Φ)
    ⊢ wp (M := M) (F := F) s E e1 Φ :=
  sorry

/-- Lift a pure stuck expression.
Coq: `wp_lift_pure_stuck` in `lifting.v`. -/
theorem wp_lift_pure_stuck [Inhabited Λ.state]
    (E : Iris.Set Positive) (Φ : Λ.val → IProp GF) (e : Λ.expr)
    (hstuck : ∀ σ, stuck e σ) :
    BIBase.pure True ⊢ wp (M := M) (F := F) .maybeStuck E e Φ :=
  sorry

end Iris.ProgramLogic
