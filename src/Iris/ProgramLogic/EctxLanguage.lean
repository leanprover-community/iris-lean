/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Language

/-! # Evaluation Context Language

Reference: `iris/program_logic/ectx_language.v`

An axiomatization of evaluation-context based languages, including a proof
that this gives rise to a `Language` in the Iris sense. An `EctxLanguage`
factors the step relation through a decomposition into evaluation contexts
and base redexes, which simplifies reasoning about contextual stepping.

## Main Definitions

- `EctxLanguageMixin` — axioms for ectx-based languages
- `EctxLanguage` — structure bundling expr, val, ectx, state, observation,
  and the mixin axioms
- `ectx_lang` — construct a `Language` from an `EctxLanguage`
- `base_reducible`, `base_irreducible`, `base_stuck` — base-level stepping predicates
- `sub_redexes_are_values` — all sub-redexes are values
- `pure_base_step` — pure step at the base level

## Key Results

- `fill_not_val` — filling a non-value gives a non-value
- `base_redex_unique` — decomposition into base redex is unique
- `ectx_lang_ctx` — every evaluation context is a `LanguageCtx`
- `ectx_language_atomic` — base-atomic + sub-redexes-are-values implies `Atomic`
- `base_reducible_prim_step` — base-reducible implies base step
- `pure_base_step_pure_step` — base pure step implies language pure step
-/

namespace Iris.ProgramLogic

/-! ## Ectx Language Mixin -/

/-- Axioms for an evaluation-context based language.
Coq: `EctxLanguageMixin` in `ectx_language.v`. -/
structure EctxLanguageMixin (expr val ectx : Type) (state : Type) (observation : Type)
    (of_val : val → expr) (to_val : expr → Option val)
    (empty_ectx : ectx) (comp_ectx : ectx → ectx → ectx)
    (fill : ectx → expr → expr)
    (base_step : expr → state → List observation → expr → state → List expr → Prop) where
  /-- `to_val (of_val v) = some v` -/
  to_of_val : ∀ v, to_val (of_val v) = some v
  /-- `to_val e = some v → of_val v = e` -/
  of_to_val : ∀ e v, to_val e = some v → of_val v = e
  /-- Base values do not step. -/
  val_base_stuck : ∀ e1 σ1 κ e2 σ2 efs,
    base_step e1 σ1 κ e2 σ2 efs → to_val e1 = none
  /-- Filling with the empty context is the identity. -/
  fill_empty : ∀ e, fill empty_ectx e = e
  /-- Filling distributes over context composition. -/
  fill_comp : ∀ K1 K2 e, fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e
  /-- Filling is injective. -/
  fill_inj : ∀ K, Function.Injective (fill K)
  /-- Filling preserves value-ness. -/
  fill_val : ∀ K e, (∃ v, to_val (fill K e) = some v) → ∃ v, to_val e = some v
  /-- Step-by-value: decompositions agree up to context extension. -/
  step_by_val : ∀ K' K_redex e1' e1_redex σ1 κ e2 σ2 efs,
    fill K' e1' = fill K_redex e1_redex →
    to_val e1' = none →
    base_step e1_redex σ1 κ e2 σ2 efs →
    ∃ K'', K_redex = comp_ectx K' K''
  /-- Base steps only happen at the root or on values. -/
  base_ctx_step_val : ∀ K e σ1 κ e2 σ2 efs,
    base_step (fill K e) σ1 κ e2 σ2 efs → (∃ v, to_val e = some v) ∨ K = empty_ectx

/-! ## Ectx Language Structure -/

/-- An evaluation-context based language.
Coq: `ectxLanguage` in `ectx_language.v`. -/
structure EctxLanguage where
  /-- Expression type -/
  expr : Type
  /-- Value type -/
  val : Type
  /-- Evaluation context type -/
  ectx : Type
  /-- State type -/
  state : Type
  /-- Observation type -/
  observation : Type
  /-- Inject a value into an expression -/
  of_val : val → expr
  /-- Extract a value from an expression -/
  to_val : expr → Option val
  /-- Empty evaluation context -/
  empty_ectx : ectx
  /-- Compose evaluation contexts -/
  comp_ectx : ectx → ectx → ectx
  /-- Fill an evaluation context with an expression -/
  fill : ectx → expr → expr
  /-- Base step relation -/
  base_step : expr → state → List observation → expr → state → List expr → Prop
  /-- The mixin axioms hold -/
  mixin : EctxLanguageMixin expr val ectx state observation of_val to_val
    empty_ectx comp_ectx fill base_step

variable {Λ : EctxLanguage}

/-! ## Mixin Projections -/

/-- Coq: `val_base_stuck` in `ectx_language.v`. -/
theorem val_base_stuck' (e1 : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e1 σ1 κ e2 σ2 efs → Λ.to_val e1 = none :=
  Λ.mixin.val_base_stuck e1 σ1 κ e2 σ2 efs

/-- Coq: `fill_empty` in `ectx_language.v`. -/
theorem fill_empty (e : Λ.expr) : Λ.fill Λ.empty_ectx e = e :=
  Λ.mixin.fill_empty e

/-- Coq: `fill_comp` in `ectx_language.v`. -/
theorem fill_comp (K1 K2 : Λ.ectx) (e : Λ.expr) :
    Λ.fill K1 (Λ.fill K2 e) = Λ.fill (Λ.comp_ectx K1 K2) e :=
  Λ.mixin.fill_comp K1 K2 e

/-- Coq: `fill_inj` in `ectx_language.v`. -/
theorem fill_inj (K : Λ.ectx) : Function.Injective (Λ.fill K) :=
  Λ.mixin.fill_inj K

/-- Coq: `fill_val` in `ectx_language.v`. -/
theorem fill_val (K : Λ.ectx) (e : Λ.expr) :
    (∃ v, Λ.to_val (Λ.fill K e) = some v) → ∃ v, Λ.to_val e = some v :=
  Λ.mixin.fill_val K e

/-- Coq: `step_by_val` in `ectx_language.v`. -/
theorem step_by_val (K' K_redex : Λ.ectx) (e1' e1_redex : Λ.expr)
    (σ1 : Λ.state) (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) :
    Λ.fill K' e1' = Λ.fill K_redex e1_redex →
    Λ.to_val e1' = none →
    Λ.base_step e1_redex σ1 κ e2 σ2 efs →
    ∃ K'', K_redex = Λ.comp_ectx K' K'' :=
  Λ.mixin.step_by_val K' K_redex e1' e1_redex σ1 κ e2 σ2 efs

/-- Coq: `base_ctx_step_val` in `ectx_language.v`. -/
theorem base_ctx_step_val (K : Λ.ectx) (e : Λ.expr)
    (σ1 : Λ.state) (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) :
    Λ.base_step (Λ.fill K e) σ1 κ e2 σ2 efs →
    (∃ v, Λ.to_val e = some v) ∨ K = Λ.empty_ectx :=
  Λ.mixin.base_ctx_step_val K e σ1 κ e2 σ2 efs

/-! ## Base Stepping Predicates -/

/-- An expression is base-reducible if it can take a base step.
Coq: `base_reducible` in `ectx_language.v`. -/
def base_reducible (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∃ κ e' σ' efs, Λ.base_step e σ κ e' σ' efs

/-- An expression is base-reducible with no observations.
Coq: `base_reducible_no_obs` in `ectx_language.v`. -/
def base_reducible_no_obs (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∃ e' σ' efs, Λ.base_step e σ [] e' σ' efs

/-- An expression is base-irreducible if it cannot take any base step.
Coq: `base_irreducible` in `ectx_language.v`. -/
def base_irreducible (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∀ κ e' σ' efs, ¬Λ.base_step e σ κ e' σ' efs

/-- An expression is base-stuck if it is not a value and is base-irreducible.
Coq: `base_stuck` in `ectx_language.v`. -/
def base_stuck (e : Λ.expr) (σ : Λ.state) : Prop :=
  Λ.to_val e = none ∧ base_irreducible e σ

/-- All sub-redexes are values: if `e = fill K e'` and `e'` is not a value,
then `K` is the empty context.
Coq: `sub_redexes_are_values` in `ectx_language.v`. -/
def sub_redexes_are_values (e : Λ.expr) : Prop :=
  ∀ K e', e = Λ.fill K e' → Λ.to_val e' = none → K = Λ.empty_ectx

/-! ## Prim Step from Base Step -/

/-- Primitive step for an ectx language: decompose into context and base redex.
Coq: `prim_step` (inductive) in `ectx_language.v`. -/
inductive ectx_prim_step (Λ : EctxLanguage) :
    Λ.expr → Λ.state → List Λ.observation → Λ.expr → Λ.state → List Λ.expr → Prop where
  | ectx_step (K : Λ.ectx) (e1' e2' : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
      (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e1' σ1 κ e2' σ2 efs →
    ectx_prim_step Λ (Λ.fill K e1') σ1 κ (Λ.fill K e2') σ2 efs

/-- Construct a `Language` from an `EctxLanguage`.
Coq: `ectx_lang` / `LanguageOfEctx` in `ectx_language.v`. -/
def ectx_lang (Λ : EctxLanguage) : Language where
  expr := Λ.expr
  val := Λ.val
  state := Λ.state
  observation := Λ.observation
  of_val := Λ.of_val
  to_val := Λ.to_val
  prim_step := ectx_prim_step Λ
  mixin := {
    to_of_val := Λ.mixin.to_of_val
    of_to_val := Λ.mixin.of_to_val
    val_stuck := sorry
  }

/-! ## Base-Level Lemmas -/

/-- Coq: `fill_not_val` in `ectx_language.v`. -/
theorem fill_not_val (K : Λ.ectx) (e : Λ.expr) :
    Λ.to_val e = none → Λ.to_val (Λ.fill K e) = none :=
  sorry

/-- Coq: `base_reducible_no_obs_reducible` in `ectx_language.v`. -/
theorem base_reducible_no_obs_base_reducible (e : Λ.expr) (σ : Λ.state) :
    base_reducible_no_obs e σ → base_reducible e σ :=
  sorry

/-- Coq: `not_base_reducible` in `ectx_language.v`. -/
theorem not_base_reducible (e : Λ.expr) (σ : Λ.state) :
    ¬base_reducible e σ ↔ base_irreducible e σ :=
  sorry

/-- Decomposition into base redex and context is unique.
Coq: `base_redex_unique` in `ectx_language.v`. -/
theorem base_redex_unique (K K' : Λ.ectx) (e e' : Λ.expr) (σ : Λ.state) :
    Λ.fill K e = Λ.fill K' e' →
    base_reducible e σ →
    base_reducible e' σ →
    K = Λ.comp_ectx K' Λ.empty_ectx ∧ e = e' :=
  sorry

/-- Coq: `base_prim_step` in `ectx_language.v`. -/
theorem base_prim_step (e1 : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e1 σ1 κ e2 σ2 efs → ectx_prim_step Λ e1 σ1 κ e2 σ2 efs :=
  sorry

/-- Coq: `base_step_not_stuck` in `ectx_language.v`. -/
theorem base_step_not_stuck' (e : Λ.expr) (σ : Λ.state)
    (κ : List Λ.observation) (e' : Λ.expr) (σ' : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e σ κ e' σ' efs → not_stuck (Λ := ectx_lang Λ) e σ :=
  sorry

/-- Coq: `fill_prim_step` in `ectx_language.v`. -/
theorem fill_prim_step (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs →
    ectx_prim_step Λ (Λ.fill K e1) σ1 κ (Λ.fill K e2) σ2 efs :=
  sorry

/-- Coq: `fill_reducible` in `ectx_language.v`. -/
theorem fill_reducible' (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state) :
    reducible (Λ := ectx_lang Λ) e σ → reducible (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  sorry

/-- Coq: `base_prim_reducible` in `ectx_language.v`. -/
theorem base_prim_reducible (e : Λ.expr) (σ : Λ.state) :
    base_reducible e σ → reducible (Λ := ectx_lang Λ) e σ :=
  sorry

/-- Coq: `base_prim_fill_reducible` in `ectx_language.v`. -/
theorem base_prim_fill_reducible (e : Λ.expr) (K : Λ.ectx) (σ : Λ.state) :
    base_reducible e σ → reducible (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  sorry

/-- Coq: `base_prim_irreducible` in `ectx_language.v`. -/
theorem base_prim_irreducible (e : Λ.expr) (σ : Λ.state) :
    irreducible (Λ := ectx_lang Λ) e σ → base_irreducible e σ :=
  sorry

/-- Coq: `prim_base_reducible` in `ectx_language.v`. -/
theorem prim_base_reducible (e : Λ.expr) (σ : Λ.state) :
    reducible (Λ := ectx_lang Λ) e σ → sub_redexes_are_values e → base_reducible e σ :=
  sorry

/-- Coq: `prim_base_irreducible` in `ectx_language.v`. -/
theorem prim_base_irreducible (e : Λ.expr) (σ : Λ.state) :
    base_irreducible e σ → sub_redexes_are_values e → irreducible (Λ := ectx_lang Λ) e σ :=
  sorry

/-- Coq: `base_stuck_stuck` in `ectx_language.v`. -/
theorem base_stuck_stuck (e : Λ.expr) (σ : Λ.state) :
    base_stuck e σ → sub_redexes_are_values e → stuck (Λ := ectx_lang Λ) e σ :=
  sorry

/-- Base-atomic + sub-redexes-are-values implies `Atomic`.
Coq: `ectx_language_atomic` in `ectx_language.v`. -/
theorem ectx_language_atomic (a : Atomicity) (e : Λ.expr) :
    (∀ σ κ e' σ' efs, Λ.base_step e σ κ e' σ' efs →
      match a with
      | .weaklyAtomic => irreducible (Λ := ectx_lang Λ) e' σ'
      | .stronglyAtomic => ∃ v, Λ.to_val e' = some v) →
    sub_redexes_are_values e →
    Atomic (Λ := ectx_lang Λ) a e :=
  sorry

/-- Coq: `base_reducible_prim_step_ctx` in `ectx_language.v`. -/
theorem base_reducible_prim_step_ctx (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    base_reducible e1 σ1 →
    ectx_prim_step Λ (Λ.fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', e2 = Λ.fill K e2' ∧ Λ.base_step e1 σ1 κ e2' σ2 efs :=
  sorry

/-- Coq: `base_reducible_prim_step` in `ectx_language.v`. -/
theorem base_reducible_prim_step (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    base_reducible e1 σ1 →
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs →
    Λ.base_step e1 σ1 κ e2 σ2 efs :=
  sorry

/-- Every evaluation context is a `LanguageCtx`.
Coq: `ectx_lang_ctx` in `ectx_language.v`. -/
theorem ectx_lang_ctx (K : Λ.ectx) : LanguageCtx (Λ := ectx_lang Λ) (Λ.fill K) :=
  sorry

/-! ## Pure Base Steps -/

/-- A pure base step: deterministic, state-independent, no observations, no forks.
Coq: `pure_base_step` in `ectx_language.v`. -/
structure PureBaseStep (e1 e2 : Λ.expr) : Prop where
  /-- The expression is base-reducible with no observations in any state. -/
  pure_base_step_safe : ∀ σ1, base_reducible_no_obs e1 σ1
  /-- The step is deterministic and pure. -/
  pure_base_step_det : ∀ σ1 κ e2' σ2 efs,
    Λ.base_step e1 σ1 κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []

/-- A pure base step gives a pure step.
Coq: `pure_base_step_pure_step` in `ectx_language.v`. -/
theorem pure_base_step_pure_step (e1 e2 : Λ.expr) :
    PureBaseStep e1 e2 → PureStep (Λ := ectx_lang Λ) e1 e2 :=
  sorry

/-- Coq: `pure_exec_fill` in `ectx_language.v`. -/
theorem pure_exec_fill (K : Λ.ectx) (φ : Prop) (n : Nat) (e1 e2 : Λ.expr) :
    PureExec (Λ := ectx_lang Λ) φ n e1 e2 →
    PureExec (Λ := ectx_lang Λ) φ n (Λ.fill K e1) (Λ.fill K e2) :=
  sorry

end Iris.ProgramLogic
