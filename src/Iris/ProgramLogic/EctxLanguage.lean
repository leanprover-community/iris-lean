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
    (fill : ectx → expr → expr) (base_step : expr → state → List observation → expr → state → List expr → Prop) where
  -- axioms governing evaluation contexts and base steps
  /-- `to_val (of_val v) = some v` -/ to_of_val : ∀ v, to_val (of_val v) = some v
  /-- `to_val e = some v → of_val v = e` -/ of_to_val : ∀ e v, to_val e = some v → of_val v = e
  /-- Base values do not step. -/ val_base_stuck :
    ∀ e1 σ1 κ e2 σ2 efs, base_step e1 σ1 κ e2 σ2 efs → to_val e1 = none
  /-- Filling with the empty context is the identity. -/ fill_empty :
    ∀ e, fill empty_ectx e = e
  /-- Filling distributes over context composition. -/ fill_comp :
    ∀ K1 K2 e, fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e
  /-- Filling is injective. -/ fill_inj : ∀ K, Function.Injective (fill K)
  /-- Filling preserves value-ness. -/ fill_val :
    ∀ K e, (∃ v, to_val (fill K e) = some v) → ∃ v, to_val e = some v
  /-- Step-by-value: decompositions agree up to context extension. -/ step_by_val :
    ∀ K' K_redex e1' e1_redex σ1 κ e2 σ2 efs,
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = none →
      base_step e1_redex σ1 κ e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K''
  /-- Base steps only happen at the root or on values. -/ base_ctx_step_val :
    ∀ K e σ1 κ e2 σ2 efs,
      base_step (fill K e) σ1 κ e2 σ2 efs → (∃ v, to_val e = some v) ∨ K = empty_ectx

/-! ## Ectx Language Structure -/

/-- An evaluation-context based language.
Coq: `ectxLanguage` in `ectx_language.v`. -/
structure EctxLanguage where
  -- bundle types, operations, and axioms for ectx languages
  /-- Expression type -/ expr : Type
  /-- Value type -/ val : Type
  /-- Evaluation context type -/ ectx : Type
  /-- State type -/ state : Type
  /-- Observation type -/ observation : Type
  /-- Inject a value into an expression -/ of_val : val → expr
  /-- Extract a value from an expression -/ to_val : expr → Option val
  /-- Empty evaluation context -/ empty_ectx : ectx
  /-- Compose evaluation contexts -/ comp_ectx : ectx → ectx → ectx
  /-- Fill an evaluation context with an expression -/ fill : ectx → expr → expr
  /-- Base step relation -/ base_step :
    expr → state → List observation → expr → state → List expr → Prop
  /-- The mixin axioms hold -/ mixin :
    EctxLanguageMixin expr val ectx state observation of_val to_val
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
      (σ2 : Λ.state) (efs : List Λ.expr) (e1 e2 : Λ.expr) :
    e1 = Λ.fill K e1' →
    e2 = Λ.fill K e2' →
    Λ.base_step e1' σ1 κ e2' σ2 efs →
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs

/-! ## Prim Step Helpers -/

/-- Helper: invert an ectx primitive step into its context and redex. -/
private theorem ectx_prim_step_inv (e1 : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs →
    ∃ K e1' e2', e1 = Λ.fill K e1' ∧ e2 = Λ.fill K e2' ∧ Λ.base_step e1' σ1 κ e2' σ2 efs :=
  by
    -- unpack the constructor and expose the equalities
    intro hstep
    cases hstep with
    | ectx_step K e1' e2' σ1 κ σ2 efs e1 e2 hEq1 hEq2 hbase =>
        exact ⟨K, e1', e2', hEq1, hEq2, hbase⟩

/-- Helper: solve the hole equation produced by `step_by_val`. -/
private theorem fill_eq_of_step_by_val (K K' K'' : Λ.ectx) (e1 e1' : Λ.expr)
    (hEq : Λ.fill K e1 = Λ.fill K' e1') (hK' : K' = Λ.comp_ectx K K'') :
    e1 = Λ.fill K'' e1' := by
  -- rewrite by context composition and apply injectivity
  have hfill : Λ.fill K e1 = Λ.fill K (Λ.fill K'' e1') := by
    simpa [hK', fill_comp] using hEq
  exact (fill_inj (Λ := Λ) K) hfill

/-- Helper: values do not take primitive steps in the ectx language. -/
private theorem ectx_lang_val_stuck (e : Λ.expr) (σ : Λ.state) (κ : List Λ.observation)
    (e' : Λ.expr) (σ' : Λ.state) (efs : List Λ.expr) :
    ectx_prim_step Λ e σ κ e' σ' efs → Λ.to_val e = none :=
  by
    -- reduce to the base step and use `fill_val` to rule out values
    intro hstep
    cases hstep with
    | ectx_step K e1' e2' σ1 κ σ2 efs e1 e2 hEq1 _ hbase =>
        have hnone : Λ.to_val e1' = none :=
          val_base_stuck' (Λ := Λ) e1' _ _ _ _ _ hbase
        have hfill : Λ.to_val (Λ.fill K e1') = none := by
          -- split on value-ness of the filled expression
          cases hto : Λ.to_val (Λ.fill K e1') with
          | none => rfl
          | some v =>
              have hval : ∃ v, Λ.to_val (Λ.fill K e1') = some v := ⟨v, hto⟩
              rcases fill_val (Λ := Λ) K e1' hval with ⟨v', hv'⟩
              have : False := by
                -- contradict non-value by discriminating `none = some`
                cases hnone.symm.trans hv'
              exact (False.elim this)
        simpa [hEq1] using hfill

/-- Construct a `Language` from an `EctxLanguage`.
Coq: `ectx_lang` / `LanguageOfEctx` in `ectx_language.v`. -/
def ectx_lang (Λ : EctxLanguage) : Language :=
  -- assemble the language structure from the ectx components
  { expr := Λ.expr
    val := Λ.val
    state := Λ.state
    observation := Λ.observation
    of_val := Λ.of_val
    to_val := Λ.to_val
    prim_step := ectx_prim_step Λ
    mixin := {
      to_of_val := Λ.mixin.to_of_val
      of_to_val := Λ.mixin.of_to_val
      val_stuck := ectx_lang_val_stuck (Λ := Λ)
    } }

/-! ## Base-Level Lemmas -/

/-- Coq: `fill_not_val` in `ectx_language.v`. -/
theorem fill_not_val (K : Λ.ectx) (e : Λ.expr) :
    Λ.to_val e = none → Λ.to_val (Λ.fill K e) = none :=
  by
    -- use `fill_val` to contradict value-ness after filling
    intro hnone
    cases hto : Λ.to_val (Λ.fill K e) with
    | none => rfl
    | some v =>
        have hval : ∃ v, Λ.to_val (Λ.fill K e) = some v := ⟨v, hto⟩
        rcases fill_val (Λ := Λ) K e hval with ⟨v', hv'⟩
        have : False := by
          -- contradict non-value by discriminating `none = some`
          cases hnone.symm.trans hv'
        exact (False.elim this)

/-- Coq: `base_reducible_no_obs_reducible` in `ectx_language.v`. -/
theorem base_reducible_no_obs_base_reducible (e : Λ.expr) (σ : Λ.state) :
    base_reducible_no_obs e σ → base_reducible e σ :=
  by
    -- widen the witness by adding empty observations
    rintro ⟨e', σ', efs, hstep⟩
    exact ⟨[], e', σ', efs, hstep⟩

/-- Coq: `not_base_reducible` in `ectx_language.v`. -/
theorem not_base_reducible (e : Λ.expr) (σ : Λ.state) :
    ¬base_reducible e σ ↔ base_irreducible e σ :=
  by
    -- unfold and push negation through the existential
    constructor
    · intro h κ e' σ' efs hstep
      exact h ⟨κ, e', σ', efs, hstep⟩
    · intro h hred
      rcases hred with ⟨κ, e', σ', efs, hstep⟩
      exact h κ e' σ' efs hstep

/-- Helper: a base step in a context forces the context to be empty
when the hole itself can step. -/
private theorem ctx_empty_of_base_steps (K : Λ.ectx) (e1' : Λ.expr) (σ1 : Λ.state)
    (κ1 : List Λ.observation) (e2r : Λ.expr) (σ2r : Λ.state) (efsr : List Λ.expr)
    (κ2 : List Λ.observation) (e2' : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step (Λ.fill K e1') σ1 κ1 e2r σ2r efsr →
    Λ.base_step e1' σ1 κ2 e2' σ2 efs →
    K = Λ.empty_ectx := by
  -- use `base_ctx_step_val` and rule out the value case
  intro hctx hstep
  have hval := base_ctx_step_val (Λ := Λ) K e1' σ1 κ1 e2r σ2r efsr hctx
  cases hval with
  | inl hsome =>
      rcases hsome with ⟨v, hv⟩
      have hnv : Λ.to_val e1' = none :=
        val_base_stuck' (Λ := Λ) e1' σ1 κ2 e2' σ2 efs hstep
      have : False := by
        -- contradict the non-value hypothesis by discriminating constructors
        cases hnv.symm.trans hv
      exact (False.elim this)
  | inr hK => exact hK

/-- Decomposition into base redex and context is unique.
Coq: `base_redex_unique` in `ectx_language.v`. -/
theorem base_redex_unique (K K' : Λ.ectx) (e e' : Λ.expr) (σ : Λ.state) :
    Λ.fill K e = Λ.fill K' e' →
    base_reducible e σ →
    base_reducible e' σ →
    K = Λ.comp_ectx K' Λ.empty_ectx ∧ e = e' :=
  by
    -- compare decompositions via `step_by_val` and rule out value cases
    intro hEq hred hred'
    rcases hred with ⟨κ, e2, σ2, efs, hstep⟩
    rcases hred' with ⟨κ', e2', σ2', efs', hstep'⟩
    have hnv' : Λ.to_val e' = none :=
      val_base_stuck' (Λ := Λ) e' σ κ' e2' σ2' efs' hstep'
    obtain ⟨K'', hK⟩ :=
      step_by_val (Λ := Λ) K' K e' e σ κ e2 σ2 efs hEq.symm hnv' hstep
    have he' : e' = Λ.fill K'' e :=
      fill_eq_of_step_by_val (Λ := Λ) K' K K'' e' e hEq.symm hK
    have hctx : Λ.base_step (Λ.fill K'' e) σ κ' e2' σ2' efs' := by
      -- transport the base step along `he'`
      simpa [he'] using hstep'
    have hK'' : K'' = Λ.empty_ectx :=
      ctx_empty_of_base_steps (Λ := Λ) K'' e σ κ' e2' σ2' efs' κ e2 σ2 efs hctx hstep
    refine ⟨?_, ?_⟩
    · simpa [hK''] using hK
    · simpa [hK'', fill_empty] using he'.symm

/-- Coq: `base_prim_step` in `ectx_language.v`. -/
theorem base_prim_step (e1 : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e1 σ1 κ e2 σ2 efs → ectx_prim_step Λ e1 σ1 κ e2 σ2 efs :=
  by
    -- embed a base step as a prim step using the empty context
    intro hstep
    -- show the equality witnesses using `fill_empty`
    refine ectx_prim_step.ectx_step (Λ := Λ) (K := Λ.empty_ectx)
      (e1' := e1) (e2' := e2) (σ1 := σ1) (κ := κ) (σ2 := σ2) (efs := efs)
      (e1 := e1) (e2 := e2) ?_ ?_ hstep
    · simp [fill_empty]
    · simp [fill_empty]

/-- Coq: `base_step_not_stuck` in `ectx_language.v`. -/
theorem base_step_not_stuck' (e : Λ.expr) (σ : Λ.state)
    (κ : List Λ.observation) (e' : Λ.expr) (σ' : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e σ κ e' σ' efs → not_stuck (Λ := ectx_lang Λ) e σ :=
  by
    -- base steps give reducibility in the induced language
    intro hstep
    refine Or.inr ?_
    exact ⟨κ, e', σ', efs, base_prim_step (Λ := Λ) e σ κ e' σ' efs hstep⟩

/-- Coq: `fill_prim_step` in `ectx_language.v`. -/
theorem fill_prim_step (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs →
    ectx_prim_step Λ (Λ.fill K e1) σ1 κ (Λ.fill K e2) σ2 efs :=
  by
    -- compose the context of the step with the outer context `K`
    intro hstep
    cases hstep with
    | ectx_step K' e1' e2' σ1 κ σ2 efs e1 e2 hEq1 hEq2 hbase =>
        have hfill1 : Λ.fill K e1 = Λ.fill (Λ.comp_ectx K K') e1' := by
          -- rewrite with the inner context and compose
          simp [hEq1, fill_comp]
        have hfill2 : Λ.fill K e2 = Λ.fill (Λ.comp_ectx K K') e2' := by
          -- rewrite with the inner context and compose
          simp [hEq2, fill_comp]
        exact ectx_prim_step.ectx_step (Λ := Λ) (K := Λ.comp_ectx K K')
          (e1' := e1') (e2' := e2') (σ1 := σ1) (κ := κ) (σ2 := σ2)
          (efs := efs) (e1 := Λ.fill K e1) (e2 := Λ.fill K e2) hfill1 hfill2 hbase

/-- Coq: `ectx_step'` in `ectx_language.v`. -/
theorem ectx_step' (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state) (κ : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    Λ.base_step e1 σ1 κ e2 σ2 efs →
    ectx_prim_step Λ (Λ.fill K e1) σ1 κ (Λ.fill K e2) σ2 efs :=
  by
    -- combine the base step with context filling
    intro hstep
    exact fill_prim_step (Λ := Λ) K e1 σ1 κ e2 σ2 efs
      (base_prim_step (Λ := Λ) e1 σ1 κ e2 σ2 efs hstep)

/-- Coq: `fill_reducible` in `ectx_language.v`. -/
theorem fill_reducible' (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state) :
    reducible (Λ := ectx_lang Λ) e σ → reducible (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  by
    -- lift a primitive step through the outer evaluation context
    rintro ⟨κ, e', σ', efs, hstep⟩
    exact ⟨κ, Λ.fill K e', σ', efs, fill_prim_step (Λ := Λ) K e σ κ e' σ' efs hstep⟩

/-- Coq: `fill_reducible_no_obs` in `ectx_language.v`. -/
theorem fill_reducible_no_obs' (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state) :
    reducible_no_obs (Λ := ectx_lang Λ) e σ →
    reducible_no_obs (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  by
    -- lift a no-observation step through the outer evaluation context
    rintro ⟨e', σ', efs, hstep⟩
    exact ⟨Λ.fill K e', σ', efs, fill_prim_step (Λ := Λ) K e σ [] e' σ' efs hstep⟩

/-- Coq: `base_prim_reducible` in `ectx_language.v`. -/
theorem base_prim_reducible (e : Λ.expr) (σ : Λ.state) :
    base_reducible e σ → reducible (Λ := ectx_lang Λ) e σ :=
  by
    -- package a base step as a primitive step
    rintro ⟨κ, e', σ', efs, hstep⟩
    exact ⟨κ, e', σ', efs, base_prim_step (Λ := Λ) e σ κ e' σ' efs hstep⟩

/-- Coq: `base_prim_reducible_no_obs` in `ectx_language.v`. -/
theorem base_prim_reducible_no_obs (e : Λ.expr) (σ : Λ.state) :
    base_reducible_no_obs e σ → reducible_no_obs (Λ := ectx_lang Λ) e σ :=
  by
    -- package a base step with no observations as a primitive step
    rintro ⟨e', σ', efs, hstep⟩
    exact ⟨e', σ', efs, base_prim_step (Λ := Λ) e σ [] e' σ' efs hstep⟩

/-- Coq: `base_prim_fill_reducible` in `ectx_language.v`. -/
theorem base_prim_fill_reducible (e : Λ.expr) (K : Λ.ectx) (σ : Λ.state) :
    base_reducible e σ → reducible (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  by
    -- combine base reducibility with `fill_reducible'`
    intro hred
    exact fill_reducible' (Λ := Λ) K e σ (base_prim_reducible (Λ := Λ) e σ hred)

/-- Coq: `base_prim_fill_reducible_no_obs` in `ectx_language.v`. -/
theorem base_prim_fill_reducible_no_obs (e : Λ.expr) (K : Λ.ectx) (σ : Λ.state) :
    base_reducible_no_obs e σ → reducible_no_obs (Λ := ectx_lang Λ) (Λ.fill K e) σ :=
  by
    -- combine base reducibility (no observations) with `fill_reducible_no_obs'`
    intro hred
    exact fill_reducible_no_obs' (Λ := Λ) K e σ (base_prim_reducible_no_obs (Λ := Λ) e σ hred)

/-- Coq: `base_prim_irreducible` in `ectx_language.v`. -/
theorem base_prim_irreducible (e : Λ.expr) (σ : Λ.state) :
    irreducible (Λ := ectx_lang Λ) e σ → base_irreducible e σ :=
  by
    -- any base step would lift to a primitive step
    intro hir κ e' σ' efs hstep
    exact hir κ e' σ' efs (base_prim_step (Λ := Λ) e σ κ e' σ' efs hstep)

/-- Coq: `prim_base_reducible` in `ectx_language.v`. -/
theorem prim_base_reducible (e : Λ.expr) (σ : Λ.state) :
    reducible (Λ := ectx_lang Λ) e σ → sub_redexes_are_values e → base_reducible e σ :=
  by
    -- extract the base redex and use `sub_redexes_are_values` to force root position
    rintro ⟨κ, e', σ', efs, hstep⟩ hsub
    rcases ectx_prim_step_inv (Λ := Λ) e σ κ e' σ' efs hstep with
      ⟨K, e1', e2', hEq1, hEq2, hbase⟩
    have hnv : Λ.to_val e1' = none :=
      val_base_stuck' (Λ := Λ) e1' σ κ e2' σ' efs hbase
    have hK : K = Λ.empty_ectx := hsub K e1' hEq1 hnv
    refine ⟨κ, e2', σ', efs, ?_⟩
    simpa [hK, fill_empty, hEq1] using hbase

/-- Coq: `prim_base_irreducible` in `ectx_language.v`. -/
theorem prim_base_irreducible (e : Λ.expr) (σ : Λ.state) :
    base_irreducible e σ → sub_redexes_are_values e → irreducible (Λ := ectx_lang Λ) e σ :=
  by
    -- reduce to `prim_base_reducible` and use contradiction
    intro hbase hsub κ e' σ' efs hstep
    have hred : base_reducible e σ :=
      prim_base_reducible (Λ := Λ) e σ ⟨κ, e', σ', efs, hstep⟩ hsub
    rcases hred with ⟨κ0, e0, σ0, efs0, hstep0⟩
    exact hbase κ0 e0 σ0 efs0 hstep0

/-- Coq: `base_stuck_stuck` in `ectx_language.v`. -/
theorem base_stuck_stuck (e : Λ.expr) (σ : Λ.state) :
    base_stuck e σ → sub_redexes_are_values e → stuck (Λ := ectx_lang Λ) e σ :=
  by
    -- combine base stuckness with irreducibility lifting
    intro hst hsub
    refine ⟨hst.1, ?_⟩
    exact prim_base_irreducible (Λ := Λ) e σ hst.2 hsub

/-- Base atomicity for an ectx language.
Coq: `base_atomic` in `ectx_language.v`. -/
def base_atomic (a : Atomicity) (e : Λ.expr) : Prop :=
  -- characterize atomicity directly on base steps
  ∀ σ κ e' σ' efs, Λ.base_step e σ κ e' σ' efs →
    match a with
    | .weaklyAtomic => irreducible (Λ := ectx_lang Λ) e' σ'
    | .stronglyAtomic => ∃ v, Λ.to_val e' = some v

/-- Base-atomic + sub-redexes-are-values implies `Atomic`.
Coq: `ectx_language_atomic` in `ectx_language.v`. -/
theorem ectx_language_atomic (a : Atomicity) (e : Λ.expr) :
    (∀ σ κ e' σ' efs, Λ.base_step e σ κ e' σ' efs →
      match a with
      | .weaklyAtomic => irreducible (Λ := ectx_lang Λ) e' σ'
      | .stronglyAtomic => ∃ v, Λ.to_val e' = some v) →
    sub_redexes_are_values e →
    Atomic (Λ := ectx_lang Λ) a e :=
  by
    -- reduce atomicity to the base step at the root
    intro hatomic hsub
    refine ⟨?_⟩
    intro σ e' κ σ' efs hstep
    rcases ectx_prim_step_inv (Λ := Λ) e σ κ e' σ' efs hstep with
      ⟨K, e1', e2', hEq1, hEq2, hbase⟩
    have hnv : Λ.to_val e1' = none :=
      val_base_stuck' (Λ := Λ) e1' σ κ e2' σ' efs hbase
    have hK : K = Λ.empty_ectx := hsub K e1' hEq1 hnv
    have he : e = e1' := by
      -- reduce to the empty context
      simpa [hK, fill_empty] using hEq1
    have hbase' : Λ.base_step e σ κ e2' σ' efs := by
      -- rewrite the base step along `he`
      simpa [he] using hbase
    have hres := hatomic σ κ e2' σ' efs hbase'
    simpa [hK, fill_empty, hEq2] using hres

/-- Coq: `base_reducible_prim_step_ctx` in `ectx_language.v`. -/
theorem base_reducible_prim_step_ctx (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    base_reducible e1 σ1 →
    ectx_prim_step Λ (Λ.fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', e2 = Λ.fill K e2' ∧ Λ.base_step e1 σ1 κ e2' σ2 efs := by
  -- peel the prim step and align contexts using `step_by_val`
  intro hred hstep
  rcases hred with ⟨κr, e2r, σ2r, efsr, hbase⟩
  rcases ectx_prim_step_inv (Λ := Λ) (Λ.fill K e1) σ1 κ e2 σ2 efs hstep with
    ⟨K', e1', e2', hEq1, hEq2, hstep'⟩
  have hnv : Λ.to_val e1 = none :=
    val_base_stuck' (Λ := Λ) e1 σ1 κr e2r σ2r efsr hbase
  obtain ⟨K'', hK'⟩ :=
    step_by_val (Λ := Λ) K K' e1 e1' σ1 κ e2' σ2 efs hEq1 hnv hstep'
  have he1 : e1 = Λ.fill K'' e1' :=
    fill_eq_of_step_by_val (Λ := Λ) K K' K'' e1 e1' hEq1 hK'
  have hctx : Λ.base_step (Λ.fill K'' e1') σ1 κr e2r σ2r efsr := by
    -- rewrite the base step along `he1`
    simpa [he1] using hbase
  have hK'' : K'' = Λ.empty_ectx :=
    ctx_empty_of_base_steps (Λ := Λ) K'' e1' σ1 κr e2r σ2r efsr κ e2' σ2 efs hctx hstep'
  refine ⟨e2', ?_, ?_⟩
  · -- simplify the composed context using `fill_comp` and `fill_empty`
    have hEq2' : e2 = Λ.fill (Λ.comp_ectx K K'') e2' := by simpa [hK'] using hEq2
    have hEq2'' : e2 = Λ.fill K (Λ.fill K'' e2') := by simpa [fill_comp] using hEq2'
    simpa [hK'', fill_empty] using hEq2''
  · -- transport the base step using `he1`
    simpa [he1, hK'', fill_empty] using hstep'

/-- Coq: `base_reducible_prim_step` in `ectx_language.v`. -/
theorem base_reducible_prim_step (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) :
    base_reducible e1 σ1 →
    ectx_prim_step Λ e1 σ1 κ e2 σ2 efs →
    Λ.base_step e1 σ1 κ e2 σ2 efs :=
  by
    -- specialize `base_reducible_prim_step_ctx` to the empty context
    intro hred hstep
    have hstep' : ectx_prim_step Λ (Λ.fill Λ.empty_ectx e1) σ1 κ e2 σ2 efs := by
      -- rewrite the source expression with `fill_empty`
      simpa [fill_empty] using hstep
    rcases base_reducible_prim_step_ctx (Λ := Λ) Λ.empty_ectx e1 σ1 κ e2 σ2 efs hred hstep' with
      ⟨e2', hEq, hbase⟩
    have hEq' : e2 = e2' := by
      -- simplify the empty context equality
      simpa [fill_empty] using hEq
    simpa [hEq'] using hbase

/-- Every evaluation context is a `LanguageCtx`.
Coq: `ectx_lang_ctx` in `ectx_language.v`. -/
theorem ectx_lang_ctx (K : Λ.ectx) : LanguageCtx (Λ := ectx_lang Λ) (Λ.fill K) :=
  by
    -- show `fill` preserves non-values, lifts steps, and supports inversion
    refine ⟨?_, ?_, ?_⟩
    · intro e hnv
      exact fill_not_val (Λ := Λ) K e hnv
    · intro e1 σ1 κ e2 σ2 efs hstep
      exact fill_prim_step (Λ := Λ) K e1 σ1 κ e2 σ2 efs hstep
    · intro e1' σ1 κ e2 σ2 efs hnv hstep
      rcases ectx_prim_step_inv (Λ := Λ) (Λ.fill K e1') σ1 κ e2 σ2 efs hstep with
        ⟨K', e1'', e2'', hEq1, hEq2, hbase⟩
      obtain ⟨K'', hK'⟩ :=
        step_by_val (Λ := Λ) K K' e1' e1'' σ1 κ e2'' σ2 efs hEq1 hnv hbase
      have he1 : e1' = Λ.fill K'' e1'' :=
        fill_eq_of_step_by_val (Λ := Λ) K K' K'' e1' e1'' hEq1 hK'
      refine ⟨Λ.fill K'' e2'', ?_, ?_⟩
      · -- rewrite the target using context composition
        simpa [hK', fill_comp] using hEq2
      · -- rebuild the prim step at the smaller context
        exact ectx_prim_step.ectx_step (Λ := Λ) (K := K'') (e1' := e1'')
          (e2' := e2'') (σ1 := σ1) (κ := κ) (σ2 := σ2) (efs := efs)
          (e1 := e1') (e2 := Λ.fill K'' e2'') he1 rfl hbase

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
  by
    -- lift base purity to primitive purity via `base_prim_step`
    intro h
    refine ⟨?_, ?_⟩
    · intro σ1
      rcases h.pure_base_step_safe σ1 with ⟨e', σ', efs, hstep⟩
      exact ⟨e', σ', efs, base_prim_step (Λ := Λ) e1 σ1 [] e' σ' efs hstep⟩
    · intro σ1 κ e2' σ2 efs hstep
      have hred : base_reducible e1 σ1 :=
        base_reducible_no_obs_base_reducible (Λ := Λ) e1 σ1 (h.pure_base_step_safe σ1)
      have hbase := base_reducible_prim_step (Λ := Λ) e1 σ1 κ e2' σ2 efs hred hstep
      exact h.pure_base_step_det σ1 κ e2' σ2 efs hbase

/-- Coq: `pure_exec_fill` in `ectx_language.v`. -/
theorem pure_exec_fill (K : Λ.ectx) (φ : Prop) (n : Nat) (e1 e2 : Λ.expr) :
    PureExec (Λ := ectx_lang Λ) φ n e1 e2 →
    PureExec (Λ := ectx_lang Λ) φ n (Λ.fill K e1) (Λ.fill K e2) :=
  by
    -- reuse the generic `pure_exec_ctx` with the `LanguageCtx` instance
    intro h
    have _ : LanguageCtx (Λ := ectx_lang Λ) (Λ.fill K) := ectx_lang_ctx (Λ := Λ) K
    simpa using (pure_exec_ctx (Λ := ectx_lang Λ) (K := Λ.fill K) φ n e1 e2 h)

end Iris.ProgramLogic
