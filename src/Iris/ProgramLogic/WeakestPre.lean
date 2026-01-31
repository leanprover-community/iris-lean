/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.ProgramLogic.Language

/-! # Weakest Precondition

Reference: `iris/program_logic/weakestpre.v`

The weakest precondition `WP e @ s; E {{ Φ }}` asserts that expression `e`,
starting in mask `E` with stuckness `s`, either:
- is a value `v` satisfying `|={E}=> Φ v`, or
- can take a step, and after stepping the WP holds recursively.

The fixpoint is well-founded because the recursive occurrence is guarded
under `▷` (via the step-taking fancy update `|={∅}▷=>^n`).

## Definition

```
wp_pre s wp E e Φ :=
  match to_val e with
  | Some v => |={E}=> Φ v
  | None => ∀ σ ns κ κs nt,
      state_interp σ ns (κ ++ κs) nt ={E,∅}=∗
        ⌜if s is NotStuck then reducible e σ else True⌝ ∗
        ∀ e2 σ2 efs, ⌜prim_step e σ κ e2 σ2 efs⌝ ={∅}▷=∗^(S n) |={∅,E}=>
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        wp E e2 Φ ∗
        [∗ list] ef ∈ efs, wp ⊤ ef fork_post
  end
```

## Main Results

- `wp_value_fupd` — value case: `WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v`
- `wp_strong_mono` — monotonicity in stuckness, mask, and postcondition
- `wp_bind` — compositionality via evaluation contexts
- `wp_frame_l` / `wp_frame_r` — frame rules
- `wp_fupd` — absorb postcondition update
- `wp_wand` — weakening postcondition via wand

## Simplifications

This port omits later credit support and the `step_fupdN` infrastructure.
The `num_laters_per_step` is fixed to 0 (one later per step).
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

/-! ## Iris Ghost State for WP -/

/-- The Iris ghost state typeclass for the weakest precondition.
Packages the state interpretation, fork postcondition, and per-step laters.
Coq: `irisGS_gen` in `weakestpre.v`. -/
class IrisGS (Λ : Language) (GF : BundledGFunctors) where
  /-- World satisfaction witness. -/
  wsatGS : WsatGS GF
  /-- State interpretation invariant: `state → step_count → observations → num_forks → iProp`. -/
  state_interp : Λ.state → Nat → List Λ.observation → Nat → IProp GF
  /-- Fixed postcondition for forked threads. -/
  fork_post : Λ.val → IProp GF
  /-- State interpretation is monotone in step count.
  Full version uses `uPred_fupd wsatGS ∅ ∅ (state_interp σ (ns+1) κs nt)`;
  simplified here to avoid threading `M`/`F` into the class. -/
  state_interp_mono : ∀ σ ns κs nt,
    state_interp σ ns κs nt ⊢ state_interp σ (ns + 1) κs nt

variable [inst : IrisGS Λ GF]

private noncomputable abbrev fupd' (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  uPred_fupd (M := M) (F := F) (@IrisGS.wsatGS Λ GF inst) E1 E2 P

/-! ## WP Pre-fixpoint -/

/-- The pre-fixpoint for weakest preconditions. Takes the recursive `wp` as
a parameter. In the value case, returns `|={E}=> Φ v`. In the step case,
requires stepping and recursive WP for the continuation.
Coq: `wp_pre` in `weakestpre.v`. -/
noncomputable def wp_pre
    (s : Stuckness)
    (wp : Iris.Set Positive → Λ.expr → (Λ.val → IProp GF) → IProp GF)
    (E : Iris.Set Positive) (e : Λ.expr) (Φ : Λ.val → IProp GF) : IProp GF :=
  sorry

/-! ## WP Fixpoint -/

/-- The weakest precondition, defined as the fixpoint of `wp_pre`.
The fixpoint is well-founded because `wp_pre` is contractive: the
recursive call to `wp` appears under `▷`.
Coq: `wp_def` in `weakestpre.v`. -/
noncomputable def wp
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) : IProp GF :=
  sorry

/-! ## Unfold -/

/-- Unfold the WP fixpoint one step.
Coq: `wp_unfold` in `weakestpre.v`. -/
theorem wp_unfold (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp s E e Φ = wp_pre s (wp s) E e Φ :=
  sorry

/-! ## Core Rules -/

/-- Value case: `WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v`.
Coq: `wp_value_fupd'` in `weakestpre.v`. -/
theorem wp_value_fupd (s : Stuckness) (E : Iris.Set Positive)
    (Φ : Λ.val → IProp GF) (v : Λ.val) :
    wp s E (Λ.of_val v) Φ =
      fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v) :=
  sorry

/-- Strong monotonicity: weaken stuckness, enlarge mask, transform postcondition.
Coq: `wp_strong_mono` in `weakestpre.v`. -/
theorem wp_strong_mono (s1 s2 : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF) :
    wp s1 E1 e Φ ⊢
    BIBase.wand
      (BIBase.forall fun v =>
        BIBase.wand (Φ v)
          (fupd' (Λ := Λ) (M := M) (F := F) E2 E2 (Ψ v)))
      (wp s2 E2 e Ψ) :=
  sorry

/-- Fancy update can be absorbed into WP.
Coq: `fupd_wp` in `weakestpre.v`. -/
theorem fupd_wp (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    fupd' (Λ := Λ) (M := M) (F := F) E E
      (wp s E e Φ) ⊢
    wp s E e Φ :=
  sorry

/-- Postcondition update can be absorbed.
Coq: `wp_fupd` in `weakestpre.v`. -/
theorem wp_fupd (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp s E e
      (fun v => fupd' (Λ := Λ) (M := M) (F := F) E E (Φ v)) ⊢
    wp s E e Φ :=
  sorry

/-- Bind rule: compositionality via evaluation contexts.
Coq: `wp_bind` in `weakestpre.v`. -/
theorem wp_bind (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp s E e
      (fun v => wp s E (K (Λ.of_val v)) Φ) ⊢
    wp s E (K e) Φ :=
  sorry

/-- Inverse bind rule.
Coq: `wp_bind_inv` in `weakestpre.v`. -/
theorem wp_bind_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) :
    wp s E (K e) Φ ⊢
    wp s E e
      (fun v => wp s E (K (Λ.of_val v)) Φ) :=
  sorry

/-! ## Derived Rules -/

/-- Monotonicity in postcondition.
Coq: `wp_mono` in `weakestpre.v`. -/
theorem wp_mono (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF)
    (h : ∀ v, Φ v ⊢ Ψ v) :
    wp s E e Φ ⊢ wp s E e Ψ :=
  sorry

/-- Frame rule (left).
Coq: `wp_frame_l` in `weakestpre.v`. -/
theorem wp_frame_l (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) (R : IProp GF) :
    BIBase.sep R (wp s E e Φ) ⊢
    wp s E e (fun v => BIBase.sep R (Φ v)) :=
  sorry

/-- Frame rule (right).
Coq: `wp_frame_r` in `weakestpre.v`. -/
theorem wp_frame_r (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF) (R : IProp GF) :
    BIBase.sep (wp s E e Φ) R ⊢
    wp s E e (fun v => BIBase.sep (Φ v) R) :=
  sorry

/-- Wand rule: weaken postcondition via wand.
Coq: `wp_wand` in `weakestpre.v`. -/
theorem wp_wand (s : Stuckness) (E : Iris.Set Positive)
    (e : Λ.expr) (Φ Ψ : Λ.val → IProp GF) :
    wp s E e Φ ⊢
    BIBase.wand
      (BIBase.forall fun v => BIBase.wand (Φ v) (Ψ v))
      (wp s E e Ψ) :=
  sorry

/-- Atomic expression rule: open invariants around an atomic step.
Coq: `wp_atomic` in `weakestpre.v`. -/
theorem wp_atomic (s : Stuckness) (E1 E2 : Iris.Set Positive)
    (e : Λ.expr) (Φ : Λ.val → IProp GF)
    [Atomic (Λ := Λ) (match s with | .notStuck => .stronglyAtomic | .maybeStuck => .weaklyAtomic) e] :
    fupd' (Λ := Λ) (M := M) (F := F) E1 E2
      (wp s E2 e
        (fun v => fupd' (Λ := Λ) (M := M) (F := F) E2 E1 (Φ v))) ⊢
    wp s E1 e Φ :=
  sorry

end Iris.ProgramLogic
