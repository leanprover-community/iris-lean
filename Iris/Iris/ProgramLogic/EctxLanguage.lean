/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import Iris.Std.RocqPorting

public import Iris.ProgramLogic.Language

namespace Iris.ProgramLogic

open Language.Notation

@[expose] public section

variable {Expr Val State Obs Ectx : Type _}

/-- Whether a type `Ectx` has the `comp` and `empty` operations expected
of evaluation contexts.

These operations are kept inside a separate typeclass so they don't
depend on a specific `Expr`. In particular, if `empty` was defined
inside of `EvContext`, then since `EvContext.empty` is not enough to
infer the type of `Expr` from a given call, it is asked to be given
explicitly as `EvContext.empty Expr`, which is inconvenient in practice.
-/
class EvContextOps (Ectx : Type c) where
  empty : Ectx
  comp  : Ectx → Ectx → Ectx
export EvContextOps (empty comp)

-- attribute [rocq_alias empty_ectx] EvContextOps.empty
-- attribute [rocq_alias comp_ectx] EvContextOps.comp

/-- An evaluation context `Ectx` of expressions `Expr` is an "expression
with a hole". This hole can be filled in using the `fill` operation.

For example, for a lambda calculus `t ::= v | λ x . t | t t` with
values `v`, the evaluation contexts could be defined inductively as
`K ::= □ | v K | K t`.  -/
class EvContext (Expr : Type e) (Ectx : outParam <| Type c)
  extends EvContextOps Ectx where
  fill : Ectx → Expr → Expr
  fill_empty (e : Expr) : fill empty e = e
  fill_comp K₁ K₂ (e : Expr) : fill K₁ (fill K₂ e) = fill (comp K₁ K₂) e
  fill_inj {K} : Function.Injective (fill K)
export EvContext (fill)

attribute [rocq_alias fill] EvContext.fill
attribute [rocq_alias fill_empty] EvContext.fill_empty
attribute [rocq_alias fill_comp] EvContext.fill_comp
attribute [rocq_alias fill_inj] EvContext.fill_inj

attribute [grind =] EvContext.fill_empty
attribute [grind =_] EvContext.fill_comp

attribute [local simp] EvContext.fill_inj Function.Injective.eq_iff

/-- A base step is a reduction step which is only defined on base terms.

The generic reduction relation is then derived from taking the closure
of these base steps over any context.

For example, for a lambda calculus `t ::= v | λ x . t | t t` with
values `v` and evaluation contexts `K ::= □ | v K | K t`, the base step
relation could be defined as `(λ x . t) v -->ᵇ t[v/x]`, where `t[v/x]`
stands for "`t` but with all references to `x` replaced with `x`". In
particular, this is the only reduction defined for `-->ᵇ`, so a term
like `v₂ ((λ x . t) v)` does not reduce under `-->ᵇ`! -/
class BaseStep (Expr : Type _) (State : outParam (Type _)) (Obs : outParam (Type _)) where
  /-- The base reduction relation of the language. See `BaseStep`. -/
  baseStep : Expr × State → List Obs → Expr × State × List Expr → Prop

-- attribute [rocq_alias base_step] BaseStep.baseStep

namespace EctxLanguage.Notation

@[inherit_doc BaseStep.baseStep]
scoped notation (name := baseStep) conf:40 " -<" obs:max ">->ᵇ " conf':41  =>
  BaseStep.baseStep conf obs conf'

end EctxLanguage.Notation

open EctxLanguage.Notation

namespace BaseStep

variable [BaseStep Expr State Obs]

/-- The context closure of a base relation. A term `e` reduces under the context closure
to a term `e'` if `e` and `e'` share a common context `K`, and their remaining redexes
`e₁` and `e₂` reduce under a base step. -/
@[grind, rocq_alias prim_step]
inductive ContextStep [EvContext Expr Ectx] [BaseStep Expr State Obs] (obs : List Obs)
    (eₜ : List Expr) (σ₁ σ₂ : State) : Expr → Expr → Prop where
  | intro {e₁ e₂} {K : Ectx} :
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) → ContextStep obs eₜ σ₁ σ₂ (fill K e₁) (fill K e₂)

@[match_pattern, rocq_alias Ectx_step']
abbrev ContextStep.ofBaseStep [EvContext Expr Ectx] [BaseStep Expr State Obs] {e₁ : Expr}
    {σ₁ obs e₂ σ₂ eₜ} (K : Ectx) :
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) → ContextStep obs eₜ σ₁ σ₂ (fill K e₁) (fill K e₂) :=
  (ContextStep.intro ·)

-- @[rocq_alias Ectx_step]
abbrev ContextStep.ofBaseStep' [EvContext Expr Ectx] [BaseStep Expr State Obs] {e e' e₁ : Expr}
    {σ₁ obs e₂ σ₂ eₜ} (K : Ectx) : fill K e₁ = e → fill K e₂ = e' →
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) → ContextStep obs eₜ σ₁ σ₂ e e' := fun
  | rfl, rfl => (ContextStep.intro ·)

/-- The primitive reduction step generated from a base step is the context closure of
the base step.  -/
@[grind]
instance [BaseStep Expr State Obs] [EvContext Expr Ectx] : PrimStep Expr State (List Obs) where
  primStep | (e₁, σ₁), obs, (e₂, σ₂, eₜ) => ContextStep obs eₜ σ₁ σ₂ e₁ e₂

@[rocq_alias base_reducible]
def Reducible : Expr × State → Prop
  | (e,σ) => ∃ obs e' σ' eₜ, (e,σ) -<obs>->ᵇ (e',σ',eₜ)

@[rocq_alias base_reducible_no_obs]
def ReducibleNoObs : Expr × State → Prop
  | (e,σ) => ∃ e' σ' eₜ, (e,σ) -<[]>->ᵇ (e',σ', eₜ)

@[rocq_alias base_irreducible]
def Irreducible : Expr × State → Prop
  | (e,σ) => ∀ obs e' σ' eₜ, ¬ (e,σ) -<obs>->ᵇ (e',σ',eₜ)

@[rocq_alias base_stuck]
def Stuck [ToVal Expr Val]: Expr × State → Prop
  | (e,σ) => toVal e = none ∧ Irreducible (e,σ)

variable {e : Expr}{σ : State}

@[rocq_alias not_base_reducible, grind =]
theorem not_reducible_iff_irreducible : (¬ Reducible (e, σ)) ↔ Irreducible (e, σ) := by
  grind only [Reducible, Irreducible]

@[rocq_alias base_reducible_no_obs_reducible, grind .]
theorem reducible_of_reducibleNoObs : ReducibleNoObs (e, σ) → Reducible (e, σ) := by
  grind only [ReducibleNoObs, Reducible]

end BaseStep

/-- A language with evaluation contexts.

This typeclass is defined in terms of a base step relation `baseStep`,
a type of evaluation contexts `Ectx` and a set of values `Val`, and
extended with theorems that relate these concepts to one another. -/
class EctxLanguage (Expr  : Type _) (Ectx State Obs Val : outParam (Type _))
  extends BaseStep Expr State Obs, ToVal Expr Val, EvContext Expr Ectx where
  /-- Removing a context out of a value gives a value -/
  fill_val K e : (toVal (fill K e)).isSome → (toVal e).isSome
  /-- If some expression can be obtained from different contexts over
      expressions, at least one of which is reducible, then one of
      the expressions can be obtained from applying some context to
      the other. -/
  step_by_val {K' K_redex e₁' e₁_redex σ₁ obs e₂ σ₂ eₜ} :
    fill K' e₁' = fill K_redex e₁_redex →
    toVal e₁' = none →
    (e₁_redex, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) →
    ∃ K'', K_redex = comp K' K''

  /-- An expression which reduces cannot be a value -/
  val_stuck {e} {σ : State} {obs e' σ' eₜ} :
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → toVal e = none

  /-- If an expression under a context reduces in the base relation,
      either it was a value or the context was empty. -/
  base_ctx_step_val {K e σ₁ obs e₂ σ₂ eₜ} :
    (fill K e, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) →
    (toVal e).isSome ∨ K = empty

attribute [rocq_alias val_base_stuck] EctxLanguage.val_stuck
attribute [rocq_alias fill_val] EctxLanguage.fill_val
attribute [rocq_alias step_by_val] EctxLanguage.step_by_val
attribute [rocq_alias base_ctx_step_val] EctxLanguage.base_ctx_step_val

attribute [grind .] EctxLanguage.val_stuck
attribute [grind →] EctxLanguage.base_ctx_step_val

namespace EctxLanguage
open BaseStep

variable [EctxLanguage Expr Ectx State Obs Val]

@[grind =>]
theorem fill_not_val K (e : Expr) : (toVal e) = none → (toVal (fill K e)) = none := by
  grind only [!fill_val, Option.not_isSome_iff_eq_none]

@[rocq_alias sub_redexes_are_values]
def SubredexesAreValues (e : Expr) :=
  ∀ {K : Ectx} {e'}, e = fill K e' → toVal e' = none → K = empty

@[rocq_alias LanguageOfEctx]
instance : Language Expr State Obs Val where
  val_stuck {e σ obs e' σ' eₜ} primStep := by
    rcases primStep with ⟨bstep⟩
    grind only [val_stuck, fill_not_val]

@[rocq_alias base_atomic]
def BaseAtomic (a : Language.Atomicity) (e : Expr) : Prop :=
  ∀ σ obs e' σ' eₜ, (e,σ) -<obs>->ᵇ (e',σ',eₜ) →
    match a with
    | .WeaklyAtomic => PrimStep.Irreducible (e',σ')
    | .StronglyAtomic => (toVal e').isSome

variable {e e' e₁ e₂ : Expr} {σ σ' σ₁ σ₂ : State}
variable {K K' K₁ K₂ : Ectx} {obs obs' : List Obs}
variable {eₜ eₜ : List Expr}

open EvContext in
@[rocq_alias base_redex_unique]
theorem base_redex_unique K K' (e e' : Expr) σ σ' (heq : fill K e = fill K' e') :
    BaseStep.Reducible (e, σ) → BaseStep.Reducible (e', σ') →
    K = comp K' empty ∧ e = e' := by
  rintro ⟨obs, e₂, σ₂, eₜ, bstep⟩ ⟨obs', e₂', σ₂', eₜ', bstep'⟩
  obtain ⟨K'', rfl⟩ := step_by_val heq.symm (by grind) bstep
  simp only [← fill_comp, fill_inj, Function.Injective.eq_iff] at heq
  subst heq
  match base_ctx_step_val bstep' with
  | .inl h => grind only [val_stuck, = Option.isSome_none]
  | .inr h => grind only [fill_empty]

@[rocq_alias base_prim_step]
theorem primStep_of_baseStep {e₁ : Expr} {σ₁ obs e₂ σ₂ eₜ}
    (h : (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)) : (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) := by
  simpa only [EvContext.fill_empty] using ContextStep.ofBaseStep empty h

theorem baseStep_of_primStep {e₁ : Expr} {σ₁ obs e₂ σ₂ eₜ}
    (pstep : (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)) (hsr : SubredexesAreValues e₁) :
    (e₁, σ₁) -<obs>->ᵇ  (e₂, σ₂, eₜ) := by
  have ⟨bstep⟩ := pstep
  grind only [EvContext.fill_empty, hsr rfl (val_stuck bstep)]

@[grind =>]
theorem baseStep_iff_primStep_of_subredexesAreValues {e₁ : Expr} {σ₁ obs e₂ σ₂ eₜ}
    (hsr : SubredexesAreValues e₁) :
    ((e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) ↔ (e₁, σ₁) -<obs>->ᵇ  (e₂, σ₂, eₜ)) :=
  ⟨(baseStep_of_primStep · hsr), primStep_of_baseStep⟩

@[rocq_alias base_step_not_stuck]
theorem base_step_not_stuck {e : Expr} {σ obs e' σ' eₜ} :
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → PrimStep.NotStuck (e, σ) :=
  Language.notStuck_of_primStep ∘ primStep_of_baseStep

@[rocq_alias fill_prim_step]
theorem fill_primStep (K : Ectx) {e : Expr} {σ obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) → (fill K e, σ) -<obs>-> (fill K e', σ', eₜ) := by
  rintro ⟨pstep⟩
  rename_i K₁
  simpa only [EvContext.fill_comp] using ContextStep.ofBaseStep (comp K K₁) pstep

@[rocq_alias fill_reducible]
theorem fill_reducible (K : Ectx) {e : Expr} {σ} :
    PrimStep.Reducible (e, σ) → PrimStep.Reducible (fill K e, σ) :=
  fun ⟨obs, e', σ', eₜ, h⟩ => ⟨obs, fill K e', σ', eₜ, fill_primStep K h⟩

@[rocq_alias fill_reducible_no_obs]
theorem reducibleNoObs_fill (K : Ectx) {e : Expr} {σ : State} :
    PrimStep.ReducibleNoObs (e, σ) → PrimStep.ReducibleNoObs (fill K e, σ) :=
  fun ⟨e', σ', eₜ, h⟩ => ⟨fill K e', σ', eₜ, fill_primStep K h⟩

@[rocq_alias base_prim_reducible]
theorem primStep_reducible_of_baseStep_reducible :
    BaseStep.Reducible (e, σ) → PrimStep.Reducible (e, σ) :=
  fun ⟨obs, e', σ', eₜ, bstep⟩ => ⟨obs, e', σ', eₜ, primStep_of_baseStep bstep⟩

@[rocq_alias base_prim_fill_reducible]
theorem primStep_reducible_fill_of_baseStep_reducible :
    BaseStep.Reducible (e, σ) → PrimStep.Reducible (fill K e, σ) :=
  fun ⟨obs, e', σ', eₜ, bstep⟩ => ⟨obs, fill K e', σ', eₜ, .ofBaseStep K bstep⟩

@[rocq_alias base_prim_reducible_no_obs]
theorem primStep_reducibleNoObs_of_baseStep_reducibleNoObs :
    BaseStep.ReducibleNoObs (e, σ) → PrimStep.ReducibleNoObs (e, σ) :=
  fun ⟨e', σ', eₜ, bstep⟩ => ⟨e', σ', eₜ, primStep_of_baseStep bstep⟩

@[rocq_alias base_prim_fill_reducible_no_obs]
theorem primStep_reducibleNoObs_fill_of_baseStep_reducibleNoObs :
    BaseStep.ReducibleNoObs (e, σ) → PrimStep.ReducibleNoObs (fill K e, σ) :=
  fun ⟨e', σ', eₜ, bstep⟩ => ⟨fill K e', σ', eₜ, .ofBaseStep K bstep⟩

@[rocq_alias base_prim_irreducible]
theorem baseStep_irreducible_of_primStep_irreducible :
    PrimStep.Irreducible (e, σ) → BaseStep.Irreducible (e, σ) :=
  fun h obs e' σ' eₜ bstep => h obs e' σ' eₜ <| primStep_of_baseStep bstep

@[rocq_alias prim_base_reducible]
theorem baseStep_reducible_of_primStep_reducible :
    PrimStep.Reducible (e, σ) → SubredexesAreValues e → BaseStep.Reducible (e, σ) :=
  fun ⟨obs, e', σ', eₜ, pstep⟩ hsr => ⟨obs, e', σ', eₜ, baseStep_of_primStep pstep hsr⟩

@[rocq_alias prim_base_irreducible]
theorem primStep_irreducible_of_baseStep_irreducible :
    BaseStep.Irreducible (e, σ) → SubredexesAreValues e → PrimStep.Irreducible (e, σ) :=
  fun irr hsr obs e' σ' eₜ pstep => irr obs e' σ' eₜ (baseStep_of_primStep pstep hsr)

@[rocq_alias base_stuck_stuck]
theorem primStep_stuck_of_baseStep_stuck :
    BaseStep.Stuck (e, σ) → SubredexesAreValues e → PrimStep.Stuck (e, σ) :=
  fun ⟨toVal_none, irr⟩ hsr => ⟨toVal_none, primStep_irreducible_of_baseStep_irreducible irr hsr⟩

@[rocq_alias ectx_language_atomic, implicit_reducible]
def Atomic.ofBaseAtomic (a : Language.Atomicity) :
    BaseAtomic a e →
    SubredexesAreValues e →
    Language.Atomic a e := fun _ _ => ⟨by grind [BaseAtomic]⟩

@[rocq_alias base_reducible_prim_step_ctx]
theorem exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible :
    Reducible (e₁, σ₁) → (fill K e₁, σ₁) -<obs>-> (e', σ₂, eₜ) →
    ∃ e₂, e' = fill K e₂ ∧ (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) := by
  generalize heq : fill K e₁ = e at *
  rintro ⟨obs', e₂, σ₂', eₜ', bstep⟩ ⟨bstep'⟩
  rename_i e₁' e₂' K
  obtain ⟨K'', rfl⟩ := step_by_val heq (by grind) bstep'
  simp only [← EvContext.fill_comp, EvContext.fill_inj, Function.Injective.eq_iff] at heq ⊢
  subst heq
  have : K'' = empty := by grind only [val_stuck, = Option.isSome_none, base_ctx_step_val bstep]
  grind only [= EvContext.fill_empty]

@[rocq_alias base_reducible_prim_step]
theorem baseStep_of_primStep_of_baseStep_reducible (bred : Reducible (e₁, σ₁))
    (pstep : (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)) : (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) :=
  have ⟨e₂', heq, bstep⟩ :=
    exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible bred (EvContext.fill_empty e₁ ▸ pstep)
  heq ▸ (EvContext.fill_empty e₂' |>.symm ▸ bstep)

@[rocq_alias ectx_lang_ctx]
instance (K : Ectx) : Language.Context (fill (Expr := Expr) K) where
  toVal_eq_none_fill := fill_not_val K _
  primStep_fill {e σ obs e' σ' eₜ} := fun ⟨bstep⟩ => by
    rename_i e₁ e₂ K'
    rw [EvContext.fill_comp K K' e₁, EvContext.fill_comp K K' e₂]
    exact .ofBaseStep (comp K K') bstep
  primStep_fill_inv {e σ obs K_e' σ' eₜ} toVal_none pstep := by
    generalize heq : fill K e = K_e at *
    have ⟨bstep⟩ := pstep
    rename_i e₁ e₂ K'
    obtain ⟨K'', rfl⟩ := step_by_val heq toVal_none bstep
    simp only [← EvContext.fill_comp, EvContext.fill_inj, Function.Injective.eq_iff,
      exists_eq_left'] at *
    subst heq
    exact ContextStep.ofBaseStep K'' bstep

/-- There is a pure base step between `e₁` and `e₂` if there is a unique base step between
    them which produces no observations nor spawns new threads.  -/
@[rocq_alias pure_base_step]
structure PureBaseStep (e₁ e₂ : Expr) : Prop where
  safe σ : ReducibleNoObs (e₁, σ)
  deterministic {σ₁ σ₂ : State} {obs e₂' eₜ} :
    (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ) → obs = [] ∧ σ₁ = σ₂ ∧ e₂ = e₂' ∧ eₜ = []

namespace Notation

@[inherit_doc EctxLanguage.PureBaseStep]
scoped notation (name := PureBaseStep) conf:40 " -ᵖ->ᵇ " conf':41  =>
  EctxLanguage.PureBaseStep conf conf'

end Notation

@[rocq_alias pure_base_step_pure_step]
theorem purePrimStep_of_pureBaseStep : e₁ -ᵖ->ᵇ e₂ → e₁ -ᵖ-> e₂ := fun ⟨bsafe, bdet⟩ =>
  have psafe := (primStep_reducibleNoObs_of_baseStep_reducibleNoObs <| bsafe ·)
  have bred := (BaseStep.reducible_of_reducibleNoObs <| bsafe ·)
  ⟨psafe , (bdet <| baseStep_of_primStep_of_baseStep_reducible (bred _) ·)⟩

open Language in
@[rocq_alias pure_exec_fill]
theorem pureExec_fill φ n : PureExec φ n e₁ e₂ → PureExec φ n (fill K e₁) (fill K e₂) :=
  Language.pureExec_fill _

end EctxLanguage
