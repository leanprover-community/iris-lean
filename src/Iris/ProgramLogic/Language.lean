/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.Algebra.OFE

/-! # Language Interface

Reference: `iris/program_logic/language.v`

Abstract language interface that the weakest precondition is parameterized over.
A `Language` packages expression, value, state, and observation types together
with an injection `of_val`/`to_val` and a primitive step relation `prim_step`.

## Main Definitions

- `Language` — structure bundling expr, val, state, observation, of_val, to_val, prim_step
- `LanguageCtx` — evaluation context: preserves values, lifts steps, inverts steps
- `Atomic` — expression that reduces to a value (or irreducible) in one step
- `reducible`, `irreducible`, `stuck`, `not_stuck` — stepping predicates
- `pure_step` — deterministic, state-independent step
- `PureExec` — typeclass for pure execution
-/

namespace Iris.ProgramLogic

/-! ## Language Mixin -/

/-- Axioms that a language must satisfy.
Coq: `LanguageMixin` in `language.v`. -/
structure LanguageMixin (expr val : Type) (state : Type) (observation : Type)
    (of_val : val → expr) (to_val : expr → Option val)
    (prim_step : expr → state → List observation → expr → state → List expr → Prop) where
  /-- `to_val (of_val v) = some v` -/
  to_of_val : ∀ v, to_val (of_val v) = some v
  /-- `to_val e = some v → of_val v = e` -/
  of_to_val : ∀ e v, to_val e = some v → of_val v = e
  /-- Values do not step. -/
  val_stuck : ∀ e σ κ e' σ' efs, prim_step e σ κ e' σ' efs → to_val e = none

/-! ## Language Structure -/

/-- A programming language: expressions, values, state, observations, and a
step relation satisfying the language mixin axioms.
Coq: `language` in `language.v`. -/
structure Language where
  /-- Expression type -/
  expr : Type
  /-- Value type -/
  val : Type
  /-- State type -/
  state : Type
  /-- Observation type -/
  observation : Type
  /-- Inject a value into an expression -/
  of_val : val → expr
  /-- Extract a value from an expression (if it is one) -/
  to_val : expr → Option val
  /-- Primitive step relation -/
  prim_step : expr → state → List observation → expr → state → List expr → Prop
  /-- The mixin axioms hold -/
  mixin : LanguageMixin expr val state observation of_val to_val prim_step

variable {Λ : Language}

/-! ## Basic Lemmas -/

/-- Coq: `to_of_val` in `language.v`. -/
theorem to_of_val (v : Λ.val) : Λ.to_val (Λ.of_val v) = some v :=
  Λ.mixin.to_of_val v

/-- Coq: `of_to_val` in `language.v`. -/
theorem of_to_val (e : Λ.expr) (v : Λ.val) :
    Λ.to_val e = some v → Λ.of_val v = e :=
  Λ.mixin.of_to_val e v

/-- Coq: `val_stuck` in `language.v`. -/
theorem val_stuck (e : Λ.expr) (σ : Λ.state) (κ : List Λ.observation)
    (e' : Λ.expr) (σ' : Λ.state) (efs : List Λ.expr) :
    Λ.prim_step e σ κ e' σ' efs → Λ.to_val e = none :=
  Λ.mixin.val_stuck e σ κ e' σ' efs

/-! ## Stepping Predicates -/

/-- An expression is reducible if it can take a step.
Coq: `reducible` in `language.v`. -/
def reducible (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∃ κ e' σ' efs, Λ.prim_step e σ κ e' σ' efs

/-- An expression is irreducible if it cannot take any step.
Coq: `irreducible` in `language.v`. -/
def irreducible (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∀ κ e' σ' efs, ¬Λ.prim_step e σ κ e' σ' efs

/-- An expression is stuck if it is not a value and is irreducible.
Coq: `stuck` in `language.v`. -/
def stuck (e : Λ.expr) (σ : Λ.state) : Prop :=
  Λ.to_val e = none ∧ irreducible e σ

/-- An expression is not stuck if it is a value or reducible.
Coq: `not_stuck` in `language.v`. -/
def not_stuck (e : Λ.expr) (σ : Λ.state) : Prop :=
  (∃ v, Λ.to_val e = some v) ∨ reducible e σ

/-- Coq: `reducible_not_val` in `language.v`. -/
theorem reducible_not_val (e : Λ.expr) (σ : Λ.state) :
    reducible e σ → Λ.to_val e = none :=
  by
  -- unpack the step and use `val_stuck` to rule out values
  rintro ⟨κ, e', σ', efs, hstep⟩
  exact val_stuck (e := e) (σ := σ) (κ := κ) (e' := e') (σ' := σ') (efs := efs) hstep

/-- Coq: `val_irreducible` in `language.v`. -/
theorem val_irreducible (e : Λ.expr) (σ : Λ.state) :
    (∃ v, Λ.to_val e = some v) → irreducible e σ :=
  by
  -- a value cannot step, since any step would contradict `to_val`
  rintro ⟨v, hv⟩ κ e' σ' efs hstep
  have hnone : Λ.to_val e = none :=
    val_stuck (e := e) (σ := σ) (κ := κ) (e' := e') (σ' := σ') (efs := efs) hstep
  have : False := by simpa [hv] using hnone
  exact this.elim

/-- Coq: `not_reducible` in `language.v`. -/
theorem not_reducible (e : Λ.expr) (σ : Λ.state) :
    ¬reducible e σ ↔ irreducible e σ :=
  by
  -- unfold `reducible` and push negation through the existential
  constructor
  · intro h κ e' σ' efs hstep
    exact h ⟨κ, e', σ', efs, hstep⟩
  · intro h hred
    rcases hred with ⟨κ, e', σ', efs, hstep⟩
    exact h κ e' σ' efs hstep

/-! ## Atomicity -/

/-- Atomicity levels for expressions.
Coq: `atomicity` in `language.v`. -/
inductive Atomicity where
  | stronglyAtomic
  | weaklyAtomic

/-- Stuckness levels.
Coq: `stuckness` in Iris BI. -/
inductive Stuckness where
  | notStuck
  | maybeStuck

/-- An expression is atomic if every step results in a value (strong)
or an irreducible expression (weak).
Coq: `Atomic` in `language.v`. -/
class Atomic (a : Atomicity) (e : Λ.expr) : Prop where
  atomic : ∀ σ e' κ σ' efs,
    Λ.prim_step e σ κ e' σ' efs →
    match a with
    | .weaklyAtomic => irreducible e' σ'
    | .stronglyAtomic => ∃ v, Λ.to_val e' = some v

/-- Coq: `strongly_atomic_atomic` in `language.v`. -/
theorem strongly_atomic_atomic (e : Λ.expr) (a : Atomicity)
    [Atomic Atomicity.stronglyAtomic e] : Atomic a e :=
  by
  -- strong atomicity implies the weak form by `val_irreducible`
  refine ⟨?_⟩
  intro σ e' κ σ' efs hstep
  have hstrong :
      ∃ v, Λ.to_val e' = some v :=
    Atomic.atomic (a := Atomicity.stronglyAtomic) (e := e) σ e' κ σ' efs hstep
  cases a with
  | stronglyAtomic => exact hstrong
  | weaklyAtomic =>
      exact val_irreducible (e := e') (σ := σ') hstrong

/-! ## Language Context -/

/-- An evaluation context: a function on expressions that preserves
non-values, lifts steps, and supports step inversion.
Coq: `LanguageCtx` in `language.v`. -/
class LanguageCtx (K : Λ.expr → Λ.expr) where
  /-- Contexts preserve non-values. -/
  fill_not_val : ∀ e, Λ.to_val e = none → Λ.to_val (K e) = none
  /-- Contexts lift steps. -/
  fill_step : ∀ e1 σ1 κ e2 σ2 efs,
    Λ.prim_step e1 σ1 κ e2 σ2 efs →
    Λ.prim_step (K e1) σ1 κ (K e2) σ2 efs
  /-- Step inversion through contexts. -/
  fill_step_inv : ∀ e1' σ1 κ e2 σ2 efs,
    Λ.to_val e1' = none → Λ.prim_step (K e1') σ1 κ e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ Λ.prim_step e1' σ1 κ e2' σ2 efs

/-- Coq: `reducible_fill` in `language.v`. -/
theorem reducible_fill (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    reducible e σ → reducible (K e) σ :=
  by
  -- lift the primitive step through the evaluation context
  rintro ⟨κ, e', σ', efs, hstep⟩
  exact ⟨κ, K e', σ', efs,
    LanguageCtx.fill_step (K := K) (e1 := e) (σ1 := σ) (κ := κ)
      (e2 := e') (σ2 := σ') (efs := efs) hstep⟩

/-- Coq: `reducible_fill_inv` in `language.v`. -/
theorem reducible_fill_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    Λ.to_val e = none → reducible (K e) σ → reducible e σ :=
  by
  -- invert the context step to recover a step of the hole expression
  intro hval hred
  rcases hred with ⟨κ, e', σ', efs, hstep⟩
  rcases LanguageCtx.fill_step_inv (K := K) (e1' := e) (σ1 := σ)
    (κ := κ) (e2 := e') (σ2 := σ') (efs := efs) hval hstep with
    ⟨e2', _hEq, hstep'⟩
  exact ⟨κ, e2', σ', efs, hstep'⟩

/-- Coq: `irreducible_fill` in `language.v`. -/
theorem irreducible_fill (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    Λ.to_val e = none → irreducible e σ → irreducible (K e) σ :=
  by
  -- any step of `K e` would invert to a step of `e`
  intro hval hir κ e' σ' efs hstep
  rcases LanguageCtx.fill_step_inv (K := K) (e1' := e) (σ1 := σ)
    (κ := κ) (e2 := e') (σ2 := σ') (efs := efs) hval hstep with
    ⟨e2', _hEq, hstep'⟩
  exact hir κ e2' σ' efs hstep'

/-! ## Pure Steps -/

/-- A pure step: deterministic, state-independent, no observations, no forks.
Coq: `pure_step` in `language.v`. -/
structure PureStep (e1 e2 : Λ.expr) : Prop where
  /-- The expression is reducible in any state with no observations. -/
  pure_step_safe : ∀ σ1, ∃ e' σ' efs, Λ.prim_step e1 σ1 [] e' σ' efs
  /-- The step is deterministic and pure. -/
  pure_step_det : ∀ σ1 κ e2' σ2 efs,
    Λ.prim_step e1 σ1 κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []

/-- Typeclass for pure execution of `n` steps.
Coq: `PureExec` in `language.v`. -/
class PureExec (φ : Prop) (n : Nat) (e1 e2 : Λ.expr) : Prop where
  pure_exec : φ → Relation.TransGen PureStep e1 e2

/-! ## Configuration and Multi-Step -/

/-- A configuration is a thread pool and a state.
Coq: `cfg` in `language.v`. -/
def cfg (Λ : Language) := List Λ.expr × Λ.state

/-- Single step of the thread pool.
Coq: `step` in `language.v`. -/
inductive Step : cfg Λ → List Λ.observation → cfg Λ → Prop where
  | step_atomic (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr)
      (σ2 : Λ.state) (efs : List Λ.expr)
      (t1 t2 : List Λ.expr) (κ : List Λ.observation) :
    Λ.prim_step e1 σ1 κ e2 σ2 efs →
    Step (t1 ++ [e1] ++ t2, σ1) κ (t1 ++ [e2] ++ t2 ++ efs, σ2)

end Iris.ProgramLogic
