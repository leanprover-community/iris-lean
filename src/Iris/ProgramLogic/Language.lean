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

/-- Reducible without observations.
Coq: `reducible_no_obs` in `language.v`. -/
def reducible_no_obs (e : Λ.expr) (σ : Λ.state) : Prop :=
  ∃ e' σ' efs, Λ.prim_step e σ [] e' σ' efs

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

/-- Coq: `reducible_no_obs_reducible` in `language.v`. -/
theorem reducible_no_obs_reducible (e : Λ.expr) (σ : Λ.state) :
    reducible_no_obs e σ → reducible e σ :=
  by
  -- lift the no-observation step into the general reducible witness
  rintro ⟨e', σ', efs, hstep⟩
  exact ⟨[], e', σ', efs, hstep⟩

/-- Coq: `val_irreducible` in `language.v`. -/
theorem val_irreducible (e : Λ.expr) (σ : Λ.state) :
    (∃ v, Λ.to_val e = some v) → irreducible e σ :=
  by
  -- a value cannot step, since any step would contradict `to_val`
  rintro ⟨v, hv⟩ κ e' σ' efs hstep
  have hnone : Λ.to_val e = none :=
    val_stuck (e := e) (σ := σ) (κ := κ) (e' := e') (σ' := σ') (efs := efs) hstep
  have : False := by
    simp [hv] at hnone
  exact this.elim

/-- Coq: `of_val_inj` in `language.v`. -/
theorem of_val_inj : Function.Injective (@Language.of_val Λ) := by
  -- compare `to_val` on both sides to recover equality of values
  intro v v' h
  have h' : Λ.to_val (Λ.of_val v) = Λ.to_val (Λ.of_val v') := by
    simp [h]
  have : some v = some v' := by simpa [to_of_val] using h'
  exact Option.some.inj this

/-- Coq: `of_to_val_flip` in `language.v`. -/
theorem of_to_val_flip (v : Λ.val) (e : Λ.expr) :
    Λ.of_val v = e → Λ.to_val e = some v := by
  -- rewrite and use `to_of_val`
  intro h
  simpa [h] using (to_of_val (Λ := Λ) v)

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

/-- Coq: `not_not_stuck` in `language.v`. -/
theorem not_not_stuck (e : Λ.expr) (σ : Λ.state) :
    ¬not_stuck e σ ↔ stuck e σ := by
  -- use the definitions of `stuck` and `not_stuck`
  constructor
  · intro h
    have hval : Λ.to_val e = none := by
      -- otherwise `e` would be a value and hence not stuck
      cases hto : Λ.to_val e with
      | none => rfl
      | some v =>
          exact (h (Or.inl ⟨v, hto⟩)).elim
    refine ⟨hval, ?_⟩
    intro κ e' σ' efs hstep
    exact h (Or.inr ⟨κ, e', σ', efs, hstep⟩)
  · intro h hns
    cases hns with
  | inl hval =>
      rcases hval with ⟨v, hv⟩
      have : False := by
        simp [h.1] at hv
      exact this.elim
    | inr hred =>
        rcases hred with ⟨κ, e', σ', efs, hstep⟩
        exact h.2 κ e' σ' efs hstep

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

/-- Map stuckness to atomicity.
Coq: `stuckness_to_atomicity` in `language.v`. -/
def stuckness_to_atomicity : Stuckness → Atomicity
  | .maybeStuck => .stronglyAtomic
  | .notStuck => .weaklyAtomic

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

instance language_ctx_id (Λ : Language) : LanguageCtx (Λ := Λ) (fun e => e) := by
  -- identity context preserves values and steps by reflexivity
  refine ⟨?_, ?_, ?_⟩
  · intro e h; simpa using h
  · intro e1 σ1 κ e2 σ2 efs hstep; simpa using hstep
  · intro e1' σ1 κ e2 σ2 efs _hval hstep
    exact ⟨e2, rfl, hstep⟩

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

/-- Coq: `reducible_no_obs_fill` in `language.v`. -/
theorem reducible_no_obs_fill (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    reducible_no_obs e σ → reducible_no_obs (K e) σ := by
  -- lift the no-observation step through the context
  rintro ⟨e', σ', efs, hstep⟩
  exact ⟨K e', σ', efs,
    LanguageCtx.fill_step (K := K) (e1 := e) (σ1 := σ) (κ := [])
      (e2 := e') (σ2 := σ') (efs := efs) hstep⟩

/-- Coq: `reducible_no_obs_fill_inv` in `language.v`. -/
theorem reducible_no_obs_fill_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    Λ.to_val e = none → reducible_no_obs (K e) σ → reducible_no_obs e σ := by
  -- invert a context step with empty observations
  intro hval hred
  rcases hred with ⟨e', σ', efs, hstep⟩
  rcases LanguageCtx.fill_step_inv (K := K) (e1' := e) (σ1 := σ)
    (κ := []) (e2 := e') (σ2 := σ') (efs := efs) hval hstep with
    ⟨e2', _hEq, hstep'⟩
  exact ⟨e2', σ', efs, hstep'⟩

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

/-- Coq: `irreducible_fill_inv` in `language.v`. -/
theorem irreducible_fill_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    irreducible (K e) σ → irreducible e σ := by
  -- any step of `e` would lift to a step of `K e`
  intro hir κ e' σ' efs hstep
  exact hir κ (K e') σ' efs
    (LanguageCtx.fill_step (K := K) (e1 := e) (σ1 := σ)
      (κ := κ) (e2 := e') (σ2 := σ') (efs := efs) hstep)

/-- Coq: `not_stuck_fill_inv` in `language.v`. -/
theorem not_stuck_fill_inv (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    not_stuck (K e) σ → not_stuck e σ := by
  -- split into value or reducible cases for the context expression
  intro hns
  cases hns with
  | inl hval =>
      cases hto : Λ.to_val e with
      | some v =>
          exact Or.inl ⟨v, hto⟩
      | none =>
          have hnone : Λ.to_val (K e) = none :=
            LanguageCtx.fill_not_val (K := K) e hto
          rcases hval with ⟨v, hv⟩
          -- contradict `to_val (K e) = none`
          have : False := by
            simp [hv] at hnone
          exact this.elim
  | inr hred =>
      cases hto : Λ.to_val e with
      | some v =>
          exact Or.inl ⟨v, hto⟩
      | none =>
          exact Or.inr (reducible_fill_inv (K := K) (e := e) (σ := σ) hto hred)

/-- Coq: `stuck_fill` in `language.v`. -/
theorem stuck_fill (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (e : Λ.expr) (σ : Λ.state) :
    stuck e σ → stuck (K e) σ := by
  -- use the contrapositive formulation of stuckness
  intro hst
  have hns : ¬not_stuck e σ := (not_not_stuck (Λ := Λ) (e := e) (σ := σ)).2 hst
  have hnsK : ¬not_stuck (K e) σ := by
    intro hnsK
    exact hns (not_stuck_fill_inv (K := K) (e := e) (σ := σ) hnsK)
  exact (not_not_stuck (Λ := Λ) (e := K e) (σ := σ)).1 hnsK

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

/-! ## Small-Step Iteration -/

/-- `n`-step iteration of a relation. -/
inductive rel_nsteps {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop
  | refl (a : α) : rel_nsteps (R := R) 0 a a
  | step {n : Nat} {a b c : α} :
      R a b → rel_nsteps (R := R) n b c → rel_nsteps (R := R) (n + 1) a c

/-- Typeclass for pure execution of `n` steps.
Coq: `PureExec` in `language.v`. -/
class PureExec (φ : Prop) (n : Nat) (e1 e2 : Λ.expr) : Prop where
  pure_exec : φ → rel_nsteps (R := PureStep) n e1 e2

/-- Coq: `pure_step_ctx` in `language.v`. -/
theorem pure_step_ctx (K : Λ.expr → Λ.expr) [LanguageCtx K]
    {e1 e2 : Λ.expr} :
    PureStep e1 e2 → PureStep (K e1) (K e2) := by
  -- lift safety/determinism through the evaluation context
  intro h
  refine ⟨?_, ?_⟩
  · intro σ1
    rcases h.pure_step_safe σ1 with ⟨e', σ', efs, hstep⟩
    exact ⟨K e', σ', efs,
      LanguageCtx.fill_step (K := K) (e1 := e1) (σ1 := σ1) (κ := [])
        (e2 := e') (σ2 := σ') (efs := efs) hstep⟩
  · intro σ1 κ e2' σ2 efs hstep
    have hnone : Λ.to_val e1 = none := by
      rcases h.pure_step_safe σ1 with ⟨e', σ', efs', hstep'⟩
      exact val_stuck (e := e1) (σ := σ1) (κ := []) (e' := e') (σ' := σ') (efs := efs') hstep'
    rcases LanguageCtx.fill_step_inv (K := K) (e1' := e1) (σ1 := σ1)
      (κ := κ) (e2 := e2') (σ2 := σ2) (efs := efs) hnone hstep with
      ⟨e2'', hEq, hstep'⟩
    rcases h.pure_step_det σ1 κ e2'' σ2 efs hstep' with ⟨hκ, hσ, hE, hfs⟩
    refine ⟨hκ, hσ, ?_, hfs⟩
    have : e2' = K e2 := by
      calc
        e2' = K e2'' := hEq
        _ = K e2 := by
          simp [hE]
    exact this

/-- Coq: `pure_step_nsteps_ctx` in `language.v`. -/
theorem pure_step_nsteps_ctx (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (n : Nat) (e1 e2 : Λ.expr) :
    rel_nsteps (R := PureStep) n e1 e2 →
      rel_nsteps (R := PureStep) n (K e1) (K e2) := by
  -- map each pure step through the context
  intro h
  induction h with
  | refl _ => exact rel_nsteps.refl _
  | step hstep hrest ih =>
      exact rel_nsteps.step (R := PureStep) (pure_step_ctx (K := K) hstep) ih

/-- Coq: `pure_exec_ctx` in `language.v`. -/
theorem pure_exec_ctx (K : Λ.expr → Λ.expr) [LanguageCtx K]
    (φ : Prop) (n : Nat) (e1 e2 : Λ.expr) :
    PureExec (Λ := Λ) φ n e1 e2 → PureExec (Λ := Λ) φ n (K e1) (K e2) := by
  -- lift the witness for `PureExec` through `pure_step_nsteps_ctx`
  intro h
  refine ⟨?_⟩
  intro hφ
  exact pure_step_nsteps_ctx (K := K) (n := n) (e1 := e1) (e2 := e2) (h.pure_exec hφ)

/-! ## Values via Typeclasses -/

/-- A hint that an expression is a value.
Coq: `IntoVal` in `language.v`. -/
class IntoVal (e : Λ.expr) (v : Λ.val) : Prop where
  into_val : Λ.of_val v = e

/-- An expression that can be viewed as a value.
Coq: `AsVal` in `language.v`. -/
class AsVal (e : Λ.expr) : Prop where
  as_val : ∃ v, Λ.of_val v = e

/-- Coq: `as_val_is_Some` in `language.v`. -/
theorem as_val_is_Some (e : Λ.expr) :
    (∃ v, Λ.of_val v = e) → ∃ v, Λ.to_val e = some v := by
  -- rewrite through `of_val` and use `to_of_val`
  rintro ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simpa [hv] using (to_of_val (Λ := Λ) v)

/-! ## Configuration and Multi-Step -/

/-- A configuration is a thread pool and a state.
Coq: `cfg` in `language.v`. -/
def cfg (Λ : Language) := List Λ.expr × Λ.state

/-- Single step of the thread pool.
Coq: `step` in `language.v`. -/
inductive step : cfg Λ → List Λ.observation → cfg Λ → Prop where
  | step_atomic (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr)
      (σ2 : Λ.state) (efs : List Λ.expr)
      (t1 t2 : List Λ.expr) (κ : List Λ.observation) :
    Λ.prim_step e1 σ1 κ e2 σ2 efs →
    step (t1 ++ [e1] ++ t2, σ1) κ (t1 ++ [e2] ++ t2 ++ efs, σ2)

/-- Multi-step execution with accumulated observations.
Coq: `nsteps` in `language.v`. -/
inductive nsteps : Nat → cfg Λ → List Λ.observation → cfg Λ → Prop where
  | nsteps_refl (ρ : cfg Λ) :
      nsteps 0 ρ [] ρ
  | nsteps_l (n : Nat) (ρ1 ρ2 ρ3 : cfg Λ) (κ κs : List Λ.observation) :
      step ρ1 κ ρ2 →
      nsteps n ρ2 κs ρ3 →
      nsteps (n + 1) ρ1 (κ ++ κs) ρ3

/-- Append a single step to the right of an `nsteps` chain. -/
theorem nsteps_snoc {n : Nat} {ρ1 ρ2 : cfg Λ} {κs : List Λ.observation} :
    nsteps (Λ := Λ) n ρ1 κs ρ2 →
    ∀ {ρ3 κ}, step (Λ := Λ) ρ2 κ ρ3 →
      nsteps (Λ := Λ) (n + 1) ρ1 (κs ++ κ) ρ3 := by
  intro hsteps
  induction hsteps with
  | nsteps_refl ρ =>
      intro ρ3 κ hstep
      simpa using
        (nsteps.nsteps_l (Λ := Λ) 0 ρ ρ3 ρ3 κ [] hstep
          (nsteps.nsteps_refl (Λ := Λ) ρ3))
  | nsteps_l n ρ1 ρ2 ρ3 κ κs hstep hrest ih =>
      intro ρ4 κ' hstep'
      have ih' := ih (ρ3 := ρ4) (κ := κ') hstep'
      have hsteps' :
          nsteps (Λ := Λ) (n + 1 + 1) ρ1 (κ ++ (κs ++ κ')) ρ4 :=
        nsteps.nsteps_l (Λ := Λ) (n := n + 1) ρ1 ρ2 ρ4 κ (κs ++ κ') hstep ih'
      simpa [List.append_assoc, Nat.add_assoc] using hsteps'

/-- Erased step: forget observations.
Coq: `erased_step` in `language.v`. -/
def erased_step (ρ1 ρ2 : cfg Λ) : Prop :=
  ∃ κ, step ρ1 κ ρ2

/-- Reflexive-transitive closure of a relation. -/
inductive rtc {α : Type _} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : rtc R a a
  | tail {a b c : α} : rtc R a b → R b c → rtc R a c

private theorem rtc_trans {α : Type _} {R : α → α → Prop} {a b c : α} :
    rtc (R := R) a b → rtc (R := R) b c → rtc (R := R) a c := by
  -- append a tail of steps to the front chain
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | tail hprev hstep ih => exact rtc.tail ih hstep

/-- `rtc` of erased steps corresponds to some `nsteps`.
Coq: `erased_steps_nsteps` in `language.v`. -/
theorem erased_steps_nsteps (ρ1 ρ2 : cfg Λ) :
    rtc (erased_step (Λ := Λ)) ρ1 ρ2 ↔ ∃ n κs, nsteps (Λ := Λ) n ρ1 κs ρ2 := by
  -- unfold both directions by induction on `rtc`/`nsteps`
  constructor
  · intro h
    induction h with
    | refl =>
        exact ⟨0, [], nsteps.nsteps_refl (Λ := Λ) ρ1⟩
    | tail hprev hstep ih =>
        rcases ih with ⟨n, κs, hsteps⟩
        rcases hstep with ⟨κ, hstep⟩
        exact ⟨n + 1, κs ++ κ, nsteps_snoc (Λ := Λ) hsteps hstep⟩
  · rintro ⟨n, κs, hsteps⟩
    induction hsteps with
    | nsteps_refl ρ =>
        exact rtc.refl (R := erased_step (Λ := Λ)) ρ
    | nsteps_l n ρ1 ρ2 ρ3 κ κs hstep hrest ih =>
        have h01 : rtc (R := erased_step (Λ := Λ)) ρ1 ρ2 :=
          rtc.tail (R := erased_step (Λ := Λ)) (rtc.refl (R := erased_step (Λ := Λ)) ρ1) ⟨κ, hstep⟩
        exact rtc_trans (R := erased_step (Λ := Λ)) h01 ih

end Iris.ProgramLogic
