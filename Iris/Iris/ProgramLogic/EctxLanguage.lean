module

meta import Iris.Std.RocqPorting
public import Iris.ProgramLogic.Language

namespace Iris.ProgramLogic

@[expose] public section

variable {Expr : Type e}{Val : Type v}{State : Type σ}{Obs : Type o}
variable {Ectx : Type c}

class IsEvContext (Ectx : Type c) where
  empty : Ectx
  comp  : Ectx → Ectx → Ectx
export IsEvContext (empty comp)

class EvContext (Expr : Type e) (Ectx : outParam <| Type c)
  extends IsEvContext Ectx
  where
  fill  : Ectx → Expr → Expr
  fill_empty (e : Expr) : fill empty e = e
  fill_comp K₁ K₂ (e : Expr) :
    fill K₁ (fill K₂ e) = fill (comp K₁ K₂) e
  fill_inj {K} : Function.Injective (fill K)
export EvContext (fill)

attribute [grind =] EvContext.fill_empty
attribute [grind =_] EvContext.fill_comp

attribute [local simp] EvContext.fill_inj Function.Injective.eq_iff

class BaseStep
    (Expr : Type e)
    (State : outParam (Type σ))
    (Obs : outParam (Type o)) where
  /-- The base reduction relation of the language -/
  baseStep : Expr × State → List Obs → Expr × State × List Expr → Prop

namespace BaseStep

variable [BaseStep Expr State Obs]

@[inherit_doc BaseStep.baseStep]
scoped notation conf:40 " -<" obs:max ">->ᵇ " conf':41  => BaseStep.baseStep conf obs conf'

@[grind]
inductive ToPrimStep [EvContext Expr Ectx] [BaseStep Expr State Obs]
  (obs : List Obs) (eₜ : List Expr) (σ₁ σ₂ : State) :
    Expr → Expr → Prop where
  | intro : ∀ (e₁ e₂) (K : Ectx),
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) →
    ToPrimStep obs eₜ σ₁ σ₂ (fill K e₁) (fill K e₂)

@[match_pattern]
abbrev ToPrimStep.ofBaseStep [EvContext Expr Ectx] [BaseStep Expr State Obs]
  {e₁ : Expr} {σ₁ obs e₂ σ₂ eₜ} (K : Ectx) :
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) →
    ToPrimStep obs eₜ σ₁ σ₂ (fill K e₁) (fill K e₂) :=
  (ToPrimStep.intro _ _ _ ·)

@[match_pattern]
abbrev ToPrimStep.ofBaseStep' [EvContext Expr Ectx] [BaseStep Expr State Obs]
  {e e' e₁ : Expr} {σ₁ obs e₂ σ₂ eₜ} (K : Ectx) :
    fill K e₁ = e →
    fill K e₂ = e' →
    (e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ) →
    ToPrimStep obs eₜ σ₁ σ₂ e e' := fun
  | rfl, rfl => (ToPrimStep.intro _ _ _ ·)

@[grind]
instance [BaseStep Expr State Obs] [EvContext Expr Ectx] :
    PrimStep Expr State (List Obs) where
  primStep
  | (e₁, σ₁), obs, (e₂, σ₂, eₜ) =>
    ToPrimStep obs eₜ σ₁ σ₂ e₁ e₂

@[rocq_alias base_reducible]
def reducible : Expr × State → Prop
| (e,σ) => ∃ obs e' σ' eₜ, (e,σ) -<obs>->ᵇ (e',σ',eₜ)

@[rocq_alias base_reducible_no_obs]
def reducibleNoObs : Expr × State → Prop
| (e,σ) => ∃ e' σ' eₜ, (e,σ) -<[]>->ᵇ (e',σ', eₜ)

@[rocq_alias base_irreducible]
def irreducible : Expr × State → Prop
| (e,σ) => ∀ obs e' σ' eₜ, ¬ (e,σ) -<obs>->ᵇ (e',σ',eₜ)

@[rocq_alias base_stuck]
def stuck [ToVal Expr Val]: Expr × State → Prop
| (e,σ) => toVal e = none ∧ irreducible (e,σ)

variable {e : Expr}{σ : State}

@[rocq_alias not_base_reducible, grind =]
theorem not_reducible_iff_irreducible :
    (¬ reducible (e, σ)) ↔ irreducible (e, σ) := by
  grind only [reducible, irreducible]

@[rocq_alias base_reducible_no_obs_reducible, grind .]
theorem reducible_of_reducibleNoObs :
    reducibleNoObs (e, σ) → reducible (e, σ) := by
  grind only [reducibleNoObs, reducible]

end BaseStep

open BaseStep in
class EctxLanguage
    (Expr  : Type e)
    (Ectx  : outParam <| Type c)
    (State : outParam <| Type σ)
    (Obs   : outParam <| Type o)
    (Val   : outParam <| Type v)
  extends
    BaseStep Expr State Obs,
    ToVal Expr Val,
    EvContext Expr Ectx where
  fill_val K e :
    (toVal (fill K e)).isSome →
    (toVal e).isSome
  step_by_val {K' K_redex e₁' e₁_redex σ₁ obs e₂ σ₂ eₜ } :
    fill K' e₁' = fill K_redex e₁_redex →
    toVal e₁' = none →
    (e₁_redex, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) →
    ∃ K'', K_redex = comp K' K''

  val_stuck : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → toVal e = none

  /- NOTE: Steps now occur only in redex posiitons! -/
  base_ctx_step_val {K e σ₁ obs e₂ σ₂ eₜ} :
    (fill K e, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) →
    (toVal e).isSome ∨ K = empty

attribute [grind .] EctxLanguage.val_stuck

namespace EctxLanguage
open BaseStep

variable [EctxLanguage Expr Ectx State Obs Val]

@[grind =>]
theorem fill_not_val K (e : Expr) :
    (toVal e) = none → (toVal (fill K e)) = none := by
  grind only [!fill_val, Option.not_isSome_iff_eq_none]


@[rocq_alias subredexes_are_values]
def subredexesAreValues (e : Expr) := ∀ (K : Ectx) e',
  e = fill K e' →
  toVal e' = none →
  K = empty

@[rocq_alias LanguageOfEctx]
instance : Language Expr State Obs Val where
  val_stuck {e σ obs e' σ' eₜ} primStep := by
    rcases primStep with ⟨K, bstep⟩
    grind only [val_stuck, fill_not_val]

@[rocq_alias base_atomic]
def baseAtomic (a : Language.Atomicity) (e : Expr) : Prop :=
    ∀ σ obs e' σ' eₜ,
      (e,σ) -<obs>->ᵇ (e',σ',eₜ) →
      match a with
      | .WeaklyAtomic => PrimStep.irreducible (e',σ')
      | .StronglyAtomic => (toVal e').isSome

variable {e e' e₁ e₂ : Expr} {σ σ' σ₁ σ₂ : State}
variable {K K' K₁ K₂ : Ectx} {obs obs' : List Obs}
variable {eₜ eₜ : List Expr}

open EvContext in
@[rocq_alias base_redex_unique]
theorem base_redex_unique K K' (e e' : Expr) σ σ' :
    fill K e = fill K' e' →
    reducible (e, σ) →
    reducible (e', σ') →
    K = comp K' empty ∧
    e = e' := by
  rintro heq ⟨obs, e₂, σ₂, eₜ, bstep⟩ ⟨obs', e₂', σ₂', eₜ', bstep'⟩
  obtain ⟨K'', rfl⟩ := step_by_val heq.symm (by grind) bstep
  simp only [← fill_comp, fill_inj, Function.Injective.eq_iff] at heq
  subst heq
  match base_ctx_step_val bstep' with
  | .inl h =>
    grind only [val_stuck, = Option.isSome_none]
  | .inr h =>
    grind only [fill_empty]

open PrimStep in
@[rocq_alias base_prim_step]
theorem primStep_of_baseStep {e₁ : Expr}{σ₁ obs e₂ σ₂ eₜ}:
    (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) →
    (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) := by
  intros h
  have := ToPrimStep.ofBaseStep empty h
  simpa only [EvContext.fill_empty]

open PrimStep in
theorem baseStep_of_primStep {e₁ : Expr}{σ₁ obs e₂ σ₂ eₜ}:
    (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) →
    subredexesAreValues e₁ →
    (e₁, σ₁) -<obs>->ᵇ  (e₂, σ₂, eₜ) := fun pstep subredexValues =>
  have ⟨e₁, e₂, K, bstep⟩ := pstep
  have K_empty := subredexValues K e₁ rfl (val_stuck bstep)
  by grind only [EvContext.fill_empty]

open PrimStep in
@[grind =>]
theorem baseStep_iff_primStep_of_subredexesAreValues {e₁ : Expr}{σ₁ obs e₂ σ₂ eₜ}:
    subredexesAreValues e₁ →
    ((e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) ↔
    (e₁, σ₁) -<obs>->ᵇ  (e₂, σ₂, eₜ)) := fun subredexValues =>
  ⟨(baseStep_of_primStep · subredexValues), primStep_of_baseStep⟩

@[rocq_alias base_step_not_stuck]
theorem base_step_not_stuck {e : Expr} {σ obs e' σ' eₜ} :
    (e, σ) -<obs>->ᵇ (e', σ', eₜ) → PrimStep.notStuck (e, σ) :=
  Language.notStuck_of_primStep ∘ primStep_of_baseStep

open PrimStep in
@[rocq_alias fill_prim_step]
theorem fill_primStep (K : Ectx) {e : Expr} {σ obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) →
    (fill K e, σ) -<obs>-> (fill K e', σ', eₜ) := fun ⟨e₁, e₂, K₁, pstep⟩ => by
    have := ToPrimStep.ofBaseStep (comp K K₁) pstep
    simpa only [EvContext.fill_comp]

@[rocq_alias fill_reducible]
theorem fill_reducible (K : Ectx) {e : Expr} {σ} :
    PrimStep.reducible (e, σ) → PrimStep.reducible (fill K e, σ) :=
  fun ⟨obs, e', σ', eₜ, h⟩ =>
    ⟨obs, fill K e', σ', eₜ, fill_primStep K h⟩

@[rocq_alias fill_reducible_no_obs]
theorem reducibleNoObs_fill (K : Ectx) {e : Expr} {σ : State} :
    PrimStep.reducibleNoObs (e, σ) →
    PrimStep.reducibleNoObs (fill K e, σ) :=
  fun ⟨e', σ', eₜ, h⟩ =>
    ⟨fill K e', σ', eₜ, fill_primStep K h⟩

@[rocq_alias base_prim_reducible]
theorem primStep_reducible_of_baseStep_reducible :
    BaseStep.reducible (e, σ) →
    PrimStep.reducible (e, σ) := fun ⟨obs, e', σ', eₜ, bstep⟩ =>
  ⟨obs, e', σ', eₜ, primStep_of_baseStep bstep⟩

@[rocq_alias base_prim_fill_reducible]
theorem primStep_reducible_fill_of_baseStep_reducible :
    BaseStep.reducible (e, σ) →
    PrimStep.reducible (fill K e, σ) := fun ⟨obs, e', σ', eₜ, bstep⟩ =>
  ⟨obs, fill K e', σ', eₜ, .ofBaseStep K bstep⟩

@[rocq_alias base_prim_reducible_no_obs]
theorem primStep_reducibleNoObs_of_baseStep_reducibleNoObs :
    BaseStep.reducibleNoObs (e, σ) →
    PrimStep.reducibleNoObs (e, σ) := fun ⟨e', σ', eₜ, bstep⟩ =>
  ⟨e', σ', eₜ, primStep_of_baseStep bstep⟩

@[rocq_alias base_prim_fill_reducible_no_obs]
theorem primStep_reducibleNoObs_fill_of_baseStep_reducibleNoObs :
    BaseStep.reducibleNoObs (e, σ) →
    PrimStep.reducibleNoObs (fill K e, σ) := fun ⟨e', σ', eₜ, bstep⟩ =>
  ⟨fill K e', σ', eₜ, .ofBaseStep K bstep⟩

@[rocq_alias base_prim_irreducible]
theorem baseStep_irreducible_of_primStep_irreducible :
    PrimStep.irreducible (e, σ) →
    BaseStep.irreducible (e, σ) := fun h obs e' σ' eₜ bstep =>
  h obs e' σ' eₜ <| primStep_of_baseStep bstep

@[rocq_alias prim_base_reducible]
theorem baseStep_reducible_of_primStep_reducible :
    PrimStep.reducible (e, σ) →
    subredexesAreValues e →
    BaseStep.reducible (e, σ) := fun ⟨obs, e', σ', eₜ, pstep⟩ subredexValues =>
  ⟨obs, e', σ', eₜ, baseStep_of_primStep pstep subredexValues⟩

@[rocq_alias prim_base_irreducible]
theorem primStep_irreducible_of_baseStep_irreducible :
    BaseStep.irreducible (e, σ) →
    subredexesAreValues e →
    PrimStep.irreducible (e, σ) := fun birred subredexValues obs e' σ' eₜ pstep =>
  birred obs e' σ' eₜ (baseStep_of_primStep pstep subredexValues)

@[rocq_alias base_stuck_stuck]
theorem primStep_stuck_of_baseStep_stuck :
    BaseStep.stuck (e, σ) →
    subredexesAreValues e →
    PrimStep.stuck (e, σ) := fun ⟨toVal_none, birred⟩ subredexValues =>
  ⟨toVal_none, primStep_irreducible_of_baseStep_irreducible birred subredexValues⟩

@[rocq_alias ectx_language_atomic, implicit_reducible]
def Atomic.ofBaseAtomic (a : Language.Atomicity) :
    baseAtomic a e →
    subredexesAreValues e →
    Language.Atomic a e := fun batomic subredexValues => {
      atomic := fun σ obs e' σ' eₜ pstep =>
        by grind [baseAtomic]
    }

open PrimStep in
@[rocq_alias base_reducible_prim_step_ctx]
theorem exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible :
    BaseStep.reducible (e₁, σ₁) →
    (fill K e₁, σ₁) -<obs>-> (e', σ₂, eₜ) →
    ∃ e₂, e' = fill K e₂ ∧ (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) := by
  generalize heq : fill K e₁ = e at *
  rintro ⟨obs', e₂, σ₂', eₜ', bstep⟩ ⟨e₁', e₂', K, bstep'⟩
  obtain ⟨K'', rfl⟩ := step_by_val heq (by grind) bstep'
  simp only [← EvContext.fill_comp, EvContext.fill_inj, Function.Injective.eq_iff] at heq ⊢
  subst heq
  have : K'' = empty := by grind only [val_stuck, = Option.isSome_none, base_ctx_step_val bstep]
  grind only [= EvContext.fill_empty]

open PrimStep in
@[rocq_alias base_reducible_prim_step]
theorem baseStep_of_primStep_of_baseStep_reducible :
    BaseStep.reducible (e₁, σ₁) →
    (e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ) →
    (e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ) := fun bred pstep =>
  have ⟨e₂', heq, bstep⟩ := exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible (K := empty) bred (EvContext.fill_empty e₁ ▸ pstep)
  heq ▸ (EvContext.fill_empty e₂' |>.symm ▸ bstep)

open PrimStep in
instance (K : Ectx) : Language.Context (fill (Expr := Expr) K) where
  toVal_eq_none_fill := fill_not_val K _
  primStep_fill {e σ obs e' σ' eₜ} := fun ⟨e₁, e₂, K', bstep⟩ =>
    EvContext.fill_comp K K' e₁ ▸
    EvContext.fill_comp K K' e₂ ▸
    .ofBaseStep (comp K K') bstep
  primStep_fill_inv {e σ obs K_e' σ' eₜ} toVal_none pstep := by
    generalize heq : fill K e = K_e at *
    have ⟨e₁, e₂, K', bstep⟩ := pstep
    obtain ⟨K'', rfl⟩:= step_by_val heq toVal_none bstep
    simp only [← EvContext.fill_comp, EvContext.fill_inj, Function.Injective.eq_iff,
      exists_eq_left'] at *
    subst heq
    exact ToPrimStep.ofBaseStep K'' bstep

@[rocq_alias pure_base_step]
structure PureBaseStep (e₁ e₂ : Expr) : Prop where
  safe : ∀ σ : State, BaseStep.reducibleNoObs (e₁, σ)
  deterministic : ∀ {σ₁ σ₂ : State} {obs e₂' eₜ},
    (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ) →
    obs = [] ∧ σ₁ = σ₂ ∧ e₂ = e₂' ∧ eₜ = []

@[inherit_doc BaseStep.baseStep]
scoped notation conf:40 " -ᵖ->ᵇ " conf':41  => PureBaseStep conf conf'

open Language in
@[rocq_alias pure_base_step_pure_step]
theorem purePrimStep_of_pureBaseStep :
    e₁ -ᵖ->ᵇ e₂ →
    e₁ -ᵖ-> e₂ := fun ⟨bsafe, bdet⟩ =>
  have psafe := (primStep_reducibleNoObs_of_baseStep_reducibleNoObs <| bsafe ·)
  have bred := (BaseStep.reducible_of_reducibleNoObs <| bsafe ·)
  ⟨ psafe , fun pstep => bdet <| baseStep_of_primStep_of_baseStep_reducible (bred _) pstep⟩

open Language in
@[rocq_alias pure_exec_fill]
theorem pureExec_fill φ n :
    PureExec φ n e₁ e₂ →
    PureExec φ n (fill K e₁) (fill K e₂) :=
  Language.pureExec_fill _

end EctxLanguage
