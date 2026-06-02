/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import Iris.Std.RocqPorting
public import Iris.Std.Relation
public import Iris.BI.WeakestPre

#rocq_ignore LanguageMixin "This feature was implemented differently using typeclasses"
#rocq_ignore language      "This feature was implemented differently using typeclasses"

namespace Iris.ProgramLogic

@[expose] public section

open FromMathlib

variable {Expr Val State Obs : Type _}

class ToVal (Expr : Type _) (Val : outParam (Type _)) where
  toVal : Expr → Option Val
  ofVal : Val → Expr
  /-- If `toVal` is defined for an expression, `coe` is its inverse -/
  coe_of_toVal_eq_some {e : Expr} {v : Val} : toVal e = some v → ofVal v = e
  /-- `toVal` is defined `coe`, and works as its inverse -/
  toVal_coe (v : Val) : toVal (ofVal v) = some v
export ToVal (toVal coe_of_toVal_eq_some toVal_coe)

-- attribute [rocq_alias language.to_val] ToVal.toVal
-- attribute [rocq_alias language.of_val] ToVal.ofVal
attribute [rocq_alias of_to_val] coe_of_toVal_eq_some
attribute [rocq_alias to_of_val] ToVal.toVal_coe
attribute [simp, grind =] ToVal.toVal_coe
attribute [coe] ToVal.ofVal

namespace ToVal

variable [ι : ToVal Expr Val]

instance : Coe Val Expr where coe := ofVal

@[grind! ., rocq_alias of_to_val_flip]
theorem toVal_eq_iff_coe (e : Expr) (v : Val) : v = e ↔ toVal e = some v :=
  ⟨(· ▸ toVal_coe v), coe_of_toVal_eq_some⟩

@[rocq_alias of_val_inj]
instance : ι.ofVal.Injective := by
  intro x y h
  simpa [toVal_coe] using congrArg (toVal) h

end ToVal

class PrimStep (Expr : Type _) (State : outParam (Type _)) (Obs : outParam (Type _)) where
  /-- The primitive reduction relation of the language -/
  primStep : Expr × State → Obs → Expr × State × List Expr → Prop

namespace Language.Notation

@[inherit_doc PrimStep.primStep]
scoped notation (name := primStep) conf:40 " -<" obs:max ">-> " conf':41 =>
  PrimStep.primStep conf obs conf'

end Language.Notation

open Language.Notation

namespace PrimStep

variable [PrimStep Expr State Obs]

@[rocq_alias reducible]
def Reducible : Expr × State → Prop
  | (e, σ) => ∃ obs e' σ' eₜ, (e, σ) -<obs>-> (e', σ', eₜ)

@[rocq_alias reducible_no_obs]
def ReducibleNoObs [PrimStep Expr State (List Obs)] : Expr × State → Prop
  | (e, σ) => ∃ e' σ' eₜ, (e, σ) -<[]>-> (e', σ', eₜ)

def Irreducible : Expr × State → Prop
  | (e, σ) => ∀ obs e' σ' eₜ, ¬ (e, σ) -<obs>-> (e', σ', eₜ)

def Stuck [ToVal Expr Val] : Expr × State → Prop
  | (e, σ) => toVal e = none ∧ Irreducible (e, σ)

def NotStuck [ToVal Expr Val] : Expr × State → Prop
  | (e, σ) => (toVal e).isSome ∨ Reducible (e, σ)

end PrimStep

open PrimStep

class Language (Expr : Type _) (State : outParam (Type _)) (Obs : outParam (Type _))
    (Val : outParam (Type _)) extends PrimStep Expr State (List Obs), ToVal Expr Val where
  /-- Values in a language should not reduce -/
  val_stuck {e} {σ : State} {obs e' σ' eₜ} : (e, σ) -<obs>-> (e', σ', eₜ) → toVal e = none

attribute [rocq_alias val_stuck] Language.val_stuck

namespace Language

variable [Λ : Language Expr State Obs Val]

variable {e e' : Expr} {σ σ' : State} {v v' : Val}

/-- A single atomic step in a threaded context.
NOTE: Using the simp-normal-form  `t₁ ++ e :: t₂` instead of `t₁ ++ [e] ++ t₂`.
This will change some downstream proofs. -/
@[grind, rocq_alias step]
inductive Step : List Expr × State → List Obs → List Expr × State → Prop where
  | atomic {e σ obs e' σ' eₜ} (H : (e, σ) -<obs>-> (e', σ', eₜ)) (t₁ t₂ : List Expr) :
    Step (t₁ ++ e :: t₂, σ) obs (t₁ ++ e' :: t₂ ++ eₜ, σ')

namespace Notation

@[inherit_doc Language.Step]
scoped notation (name := Step) conf:40 " -<" obs:max ">->ₜₚ " conf':41 =>
  Language.Step conf obs conf'

end Notation

open Notation

def Step.of_primStep {e σ} {obs : List Obs} {e'} {σ' : State} {eₜ}
    (H : (e, σ) -<obs>-> (e', σ', eₜ)) {t₁ t₂: List Expr} :
    Step (t₁ ++ e :: t₂, σ) obs (t₁ ++ e' :: t₂ ++ eₜ, σ') :=
  atomic H ..

/-- The (possibly zero) sequence of `Language.step`s -/
@[grind, rocq_alias nsteps]
inductive NSteps : Nat → List Expr × State → List Obs → List Expr × State → Prop
  where
  | refl (ρ : List Expr × State): NSteps 0 ρ [] ρ
  | cons {n} {ρ₁ ρ₂ ρ₃ : List Expr × State} {obs obs' : List Obs} :
      ρ₁ -<obs>->ₜₚ ρ₂ →
      NSteps n ρ₂ obs' ρ₃ →
      NSteps (n+1) ρ₁ (obs ++ obs') ρ₃

namespace Notation

@[inherit_doc Language.NSteps]
scoped notation (name := NSteps) conf:40 " -<" obs:max ">->ₜₚ^[" n:max "] " conf':41 =>
 Language.NSteps n conf obs conf'

end Notation

/-- A `Language.step`s with no observation information -/
@[rocq_alias erased_step]
def ErasedStep (ρ ρ₂ : List Expr × State) := ∃ obs, Step ρ obs ρ₂

namespace Notation

@[inherit_doc Language.ErasedStep]
scoped notation (name := ErasedStep) conf:40 " -·->ₜₚ " conf':41 => Language.ErasedStep conf conf'

/-- A sequence of `Language.erasedStep`s -/
scoped notation (name := erasedStepStar) conf:40 " -·->ₜₚ* " conf':41 =>
  Relation.ReflTransGen Language.ErasedStep conf conf'

end Notation

open Notation

open Relation in
-- @[rocq_alias erased_step_nsteps]
theorem erasedStep_nSteps (ρ₁ ρ₂ : List Expr × State) :
    ρ₁ -·->ₜₚ* ρ₂ ↔ ∃ n obs, ρ₁ -<obs>->ₜₚ^[n] ρ₂ := by
  refine ⟨fun hyp => ?_, fun hyp => ?_⟩
  · replace ⟨n, hyp⟩ := ReflTrans_iff_exists_iterate.1 hyp
    exists n
    induction hyp using Iterate.head_induction_on with
    | rfl => exact ⟨_, .refl ρ₂⟩
    | head ρ' firstStep lastSteps IH =>
      replace ⟨obs, firstStep⟩ := firstStep
      replace ⟨obs', IH⟩ := IH
      exact ⟨_, .cons firstStep IH⟩
  · replace ⟨n, obs, hyp⟩ := hyp
    apply ReflTrans_iff_exists_iterate.2
    exists n
    induction hyp with
    | refl => exact .rfl _
    | cons H _ IH => exact .head ⟨_, H⟩ IH

section ReducibilityLemmas

@[rocq_alias not_reducible, grind =]
theorem not_reducible_iff_irreducible {e : Expr} {σ : State} :
    (¬ Reducible (e, σ)) ↔ Irreducible (e, σ) := by
  grind only [Reducible, Irreducible]

@[rocq_alias reducible_no_obs_reducible, grind .]
theorem reducible_of_reducibleNoObs : ReducibleNoObs (e, σ) → Reducible (e, σ) := by
  grind only [ReducibleNoObs, Reducible]

@[rocq_alias prim_step_not_stuck]
theorem notStuck_of_primStep {e : Expr} {σ obs e' σ' eₜ} (h : (e, σ) -<obs>-> (e', σ', eₜ)) :
    NotStuck (e, σ) := .inr ⟨_, _, _, _, h⟩

@[rocq_alias not_not_stuck, grind =]
theorem not_not_suck {e : Expr} {σ : State} : (¬ NotStuck (e, σ)) ↔ Stuck (e, σ) := by
  dsimp only [Stuck, NotStuck]
  cases h : (toVal e) <;> simp [not_reducible_iff_irreducible,]

@[rocq_alias reducible_not_val, grind .]
theorem toVal_none_of_reducible : Reducible (e, σ) → toVal e = none := by
  grind only [Reducible, val_stuck]

@[rocq_alias val_irreducible]
theorem val_irreducible : (toVal e).isSome → ∀ σ, Irreducible (e, σ) := by
  grind only [Irreducible, val_stuck, = Option.isSome_none]

end ReducibilityLemmas

@[rocq_alias atomicity]
inductive Atomicity where
  | WeaklyAtomic
  | StronglyAtomic

@[rocq_alias stuckness_to_atomicity, coe]
abbrev Atomicity.ofStuckness : Stuckness → Atomicity
  | .MaybeStuck => .StronglyAtomic
  | .NotStuck => .WeaklyAtomic

instance : Coe Stuckness Atomicity where coe := Atomicity.ofStuckness

@[rocq_alias Atomic]
class Atomic (a : Atomicity) (e : Expr) : Prop where
  atomic {σ : State} {obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) →
    match a with
    | .WeaklyAtomic => Irreducible (e', σ')
    | .StronglyAtomic => (toVal e').isSome

@[rocq_alias strongly_atomic_atomic]
theorem stronglyAtomic_atomic {a} :
    Atomic (State := State) .StronglyAtomic e →
    Atomic (State := State) a e :=
  match a with
  | .StronglyAtomic => id
  | .WeaklyAtomic => fun ⟨h⟩ => ⟨by grind only [not_reducible_iff_irreducible, val_irreducible]⟩


/-- The function `K` models an evaluation context for the language -/
@[rocq_alias LanguageCtx]
class Context (K : Expr → Expr) where
  toVal_eq_none_fill {e : Expr} :
    toVal e = none → toVal (K e) = none
  primStep_fill {e : Expr} {σ : State} {obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) →
    (K e, σ) -<obs>-> (K e', σ', eₜ)
  primStep_fill_inv {e : Expr} {σ : State} {obs K_e' σ' eₜ} :
    toVal e = .none →
    (K e, σ) -<obs>-> (K_e', σ', eₜ) →
    ∃ e', K_e' = K e' ∧ (e, σ) -<obs>-> (e', σ', eₜ)

attribute [rocq_alias fill_not_val] Context.toVal_eq_none_fill
-- attribute [rocq_alias fill_step] Context.primStep_fill
-- attribute [rocq_alias fill_step_inv] Context.primStep_fill_inv

instance instContext_id : Context (id (α := Expr)) where
  toVal_eq_none_fill e := by grind only [id]
  primStep_fill      := by grind only [id]
  primStep_fill_inv  := by grind only [id]

namespace Context

variable (K : Expr → Expr) [Context K]

@[rocq_alias reducible_fill]
theorem reducible_fill ⦃e : Expr⦄ ⦃σ : State⦄ : Reducible (e,σ) → Reducible ((K e), σ) :=
  fun ⟨obs, e', σ', eₜ, h⟩ => ⟨obs, K e', σ', eₜ, primStep_fill h⟩

@[rocq_alias reducible_fill_inv]
theorem reducible_fill_inv ⦃e : Expr⦄ ⦃σ : State⦄ (toVal_none : toVal e = none) :
    Reducible (K e, σ) → Reducible (e,σ) :=
  fun ⟨obs, _, σ', eₜ, K_red⟩ =>
    have ⟨e₂, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨obs, e₂, σ', eₜ, red⟩

@[rocq_alias reducible_no_obs_fill]
theorem reducibleNoObs_fill ⦃e : Expr⦄ ⦃σ : State⦄ :
    ReducibleNoObs (e, σ) → ReducibleNoObs (K e, σ) :=
  fun ⟨e', σ', eₜ, h⟩ => ⟨K e', σ', eₜ, primStep_fill h⟩

@[rocq_alias reducible_no_obs_fill_inv]
theorem reducibleNoObs_fill_inv ⦃e : Expr⦄ ⦃σ : State⦄ (toVal_none : toVal e = none) :
    ReducibleNoObs (K e, σ) → ReducibleNoObs (e,σ) :=
  fun ⟨_, σ', eₜ, K_red⟩ =>
    have ⟨e₂, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨e₂, σ', eₜ, red⟩

-- @[rocq_alias irrreducible_fill]
theorem irreducible_fill ⦃e : Expr⦄ ⦃σ : State⦄ (hv : toVal e = none) (irr : Irreducible (e, σ)) :
    Irreducible (K e, σ) :=
  not_reducible_iff_irreducible.1 fun red =>
  not_reducible_iff_irreducible.2 irr <|
  reducible_fill_inv K hv red

@[rocq_alias irreducible_fill_inv]
theorem irreducible_fill_inv ⦃e : Expr⦄ ⦃σ : State⦄ (irr : Irreducible (K e, σ)) :
    Irreducible (e,σ) :=
  not_reducible_iff_irreducible.1 fun red =>
  not_reducible_iff_irreducible.2 irr <|
  reducible_fill K red

@[rocq_alias not_stuck_fill_inv]
theorem notStuck_fill_inv (hyp : NotStuck (K e, σ)) :
    NotStuck (e, σ)  := by
  dsimp only [NotStuck]
  match hyp with
  | .inl hyp =>
    left
    match h : toVal e with
    | none => grind [toVal_eq_none_fill (K := K) h]
    | some v => simp
  | .inr hyp =>
    match h₂ : toVal e with
    | none => exact .inr <| reducible_fill_inv K h₂ hyp
    | some v => grind

@[rocq_alias stuck_fill]
theorem stuck_fill : Stuck (e, σ) → Stuck (K e, σ) :=
  fun ⟨toVal_e, irred⟩ => ⟨toVal_eq_none_fill toVal_e, irreducible_fill K toVal_e irred⟩

end Context

open List in
@[rocq_alias step_Permutation]
theorem perm_of_step {t₁ t₁' t₂ : List Expr} ⦃obs : List Obs⦄ ⦃σ₁ σ₂ : State⦄
    (t1p : t₁ ~ t₁') : (t₁, σ₁) -<obs>->ₜₚ (t₂, σ₂) →
    ∃ t₂', t₂ ~ t₂' ∧ (t₁', σ₁) -<obs>->ₜₚ (t₂', σ₂) := by
  rintro ⟨red, ps, ss⟩
  rename_i e e' eₜ
  obtain ⟨ps', ss', rfl⟩ := t₁'.mem_iff_append.1 (show e ∈ t₁' by grind)
  exists ps' ++ e' :: ss' ++ eₜ
  refine ⟨?_, .of_primStep red⟩
  refine .append_right _ ?_
  calc ps ++ e' :: ss
    _ ~ e' :: (ps ++ ss) := perm_middle
    _ ~ e' :: (ps' ++ ss') := by
      refine (perm_cons e').mpr <| (perm_cons e).mp ?_
      exact (perm_middle.symm.trans t1p).trans perm_middle
    _ ~ ps' ++ e' :: ss' := perm_middle.symm

@[rocq_alias step_insert]
theorem step_update_of_getElem? {i obs efs} {t : List Expr} (σ₁ σ₂ : State) :
    t[i]? = some e → (e, σ₁) -<obs>-> (e', σ₂, efs) → (t, σ₁) -<obs>->ₜₚ (t.set i e' ++ efs, σ₂) := by
  grind

open List in
@[rocq_alias erased_step_Permutation]
theorem perm_of_erasedStep (t₁ t₁' t₂ : List Expr) ⦃σ₁ σ₂ : State⦄ (t1p : t₁ ~ t₁') :
    (t₁, σ₁) -·->ₜₚ (t₂, σ₂) → ∃ t₂', t₂ ~ t₂' ∧ (t₁', σ₁) -·->ₜₚ (t₂', σ₂) :=
  fun ⟨obs, red⟩ =>
  have ⟨t₂', t2perm, red'⟩ := perm_of_step t1p red
  ⟨t₂', t2perm, obs, red'⟩

section PureSteps

/-- There is a pure step between `e₁` and `e₂` iff there is a reduction step
`(e₁, σ) -<[]>-> (e₂, σ, [])` for some σ and it is unique.
Intuitively, the reduction is deterministic and does not depend on the environment. -/
@[rocq_alias pure_step]
structure PurePrimStep (e₁ e₂ : Expr) : Prop where
  safe (σ : State) : ReducibleNoObs (e₁, σ)
  deterministic {σ₁ σ₂ : State} {obs e₂' eₜ} :
    (e₁, σ₁) -<obs>-> (e₂', σ₂, eₜ) →
    obs = [] ∧ σ₁ = σ₂ ∧ e₂ = e₂' ∧ eₜ = []

namespace Notation

@[inherit_doc Language.PurePrimStep]
scoped notation (name := PurePrimStep) conf:40 " -ᵖ-> " conf':41 => Language.PurePrimStep conf conf'

/-- `e₁ -ᵖ->^[n] e₂` represents a sequence of `n` pure steps taken from `e₁` up to `e₂`. -/
scoped notation (name := PurePrimStepN) conf:40 " -ᵖ->^[" n "] " conf':41 =>
  Relation.Iterate Language.PurePrimStep n conf conf'

/-- `e₁ -ᵖ->* e₂` represents a sequence of some number of pure steps taken from `e₁` up to `e₂`.
-/
scoped notation (name := PurePrimStepStar) conf:40 " -ᵖ->* " conf':41 =>
  Relation.ReflTransGen Language.PurePrimStep conf conf'

end Notation

abbrev PureSteps (t₁ t₂ : List Expr) := List.Forall₂ (· -ᵖ->* ·) t₁ t₂

#rocq_concept program_logic "pure_steps_tp" ported "Implemented as an abbreviation"

namespace Notation

/-- `e₁ -ᵖ->ₜₚ* e₂` represents a sequence of some number of pure steps taken from `e₁` up to `e₂`. -/
scoped notation (name := PureSteps) conf:40 " -ᵖ->ₜₚ* " conf':41 => Language.PureSteps conf conf'

end Notation

@[rocq_alias PureExec]
class PureExec (φ : Prop) (n : outParam <| Nat) (e₁ : Expr) (e₂ : outParam <| Expr) : Prop where
  pureExec : φ → e₁ -ᵖ->^[n] e₂

variable (K : Expr → Expr) [Context K]

@[rocq_alias pure_step_ctx]
theorem purePrimStep_fill {e₁ e₂ : Expr} : e₁ -ᵖ-> e₂ → K e₁ -ᵖ-> K e₂ := by
  rintro ⟨pRed,Hstep⟩
  refine ⟨(Context.reducibleNoObs_fill K <| pRed ·), @fun σ₁ σ₂ obs K_e₂' eₜ primStep => ?_⟩
  have hv : toVal e₁ = none := toVal_none_of_reducible <| reducible_of_reducibleNoObs (pRed σ₁)
  obtain ⟨e₂', rfl, primStep⟩ := Context.primStep_fill_inv hv primStep
  grind

@[rocq_alias pure_step_nsteps_ctx]
theorem iterate_purePrimStep_fill {e₁ e₂} (h : e₁ -ᵖ->^[n] e₂) : K e₁ -ᵖ->^[n] K e₂ :=
  match h with
  | .rfl _ => .rfl (K e₁)
  | .tail y first last => .tail (K y) (iterate_purePrimStep_fill first) (purePrimStep_fill K last)

@[rocq_alias rtc_pure_step_ctx]
theorem ReflTransGen_pureStep_fill {e₁ e₂} (h : e₁ -ᵖ->* e₂) :  K e₁ -ᵖ->* K e₂ := by
  replace ⟨n, h⟩ := Relation.ReflTrans_iff_exists_iterate.1 h
  exact Relation.ReflTrans_iff_exists_iterate.2 ⟨n, iterate_purePrimStep_fill K h⟩

@[rocq_alias pure_exec_ctx]
theorem pureExec_fill {φ n e₁ e₂} (h : PureExec φ n e₁ e₂) : PureExec φ n (K e₁) (K e₂) :=
  ⟨fun hφ => iterate_purePrimStep_fill K (h.1 hφ)⟩

@[rocq_alias rtc_pure_step_val]
theorem ReflTransGen_purePrimStep_val [Inhabited State] {v : Val} {e : Expr}
    (h : (v : Expr) -ᵖ->* e) : toVal e = some v := by
  induction h with
  | refl => exact toVal_coe _
  | tail H1 H2 IH =>
    obtain ⟨red, stepUniq⟩ := H2
    have ⟨e', σ', eₜ, step⟩ := red default
    grind only [Language.val_stuck]

end PureSteps

class IntoVal (e : Expr) (v : Val) where
  into_val : (v : Expr) = e

class AsVal (e : Expr) where
  as_val : ∃ v : Val, (v : Expr) = e

@[rocq_alias as_val_is_Some]
theorem as_val_isSome e : (∃ v : Val, (v : Expr) = e) → (toVal e).isSome := by
  grind only [!ToVal.toVal_eq_iff_coe, = Option.isSome_some]

/--
  Let `t₂` be a thread pool such that `t₁` under state
  `σ₁` makes a (single) step to threadpool `t₂` and
  state `σ₂`.

  Let thread pools `t₁` and `t₃` be such that each thread
  in `t₁` makes (zero or more) pure steps to the
  corresponding thread in `t₃`.

  In this situation, either the step from `t₁` to `t₂`
  corresponds to one of the pure steps between `t₁` and
  `t₃` or, there is an `i` such that the `i`-th thread
  does not participate in the pure steps between `t₁`
  and `t₃` and `t₂` corresponds t taking a step in the
  `i`-th thread starting from `t₁`.
-/
theorem erasedStep_pureSteps {t₁ t₂ t₃ : List Expr} {σ₁ σ₂ : State} (h1 : (t₁, σ₁) -·->ₜₚ (t₂, σ₂))
    (h2 : t₁ -ᵖ->ₜₚ* t₃) :
    (σ₁ = σ₂ ∧ t₂ -ᵖ->ₜₚ* t₃) ∨
    (∃ i e eₜ e' obs,  t₁[i]? = some e ∧ t₃[i]? = some e ∧ t₂ = t₁.set i e' ++ eₜ ∧
    (e, σ₁) -<obs>-> (e', σ₂, eₜ)) := by
  obtain ⟨obs, ⟨pstep, ps, ss⟩⟩ := h1
  rename_i e e' eₜ
  obtain ⟨ps₃, e₃, ss₃, rfl, ss_ss₃, ps_ps₃, length_ps, e_e₃⟩ :=
    show ∃ ps₃ e₃ ss₃, t₃ = ps₃ ++ e₃ :: ss₃ ∧ ss -ᵖ->ₜₚ* ss₃
         ∧ ps -ᵖ->ₜₚ* ps₃ ∧ ps.length = ps₃.length ∧ e -ᵖ->* e₃ by grind
  rcases Relation.ReflTransGen.cases_head e_e₃ with (rfl | ⟨e', firstPureStep, lastSteps⟩)
  · right
    exists (ps₃.length), e, eₜ, e', obs
    simp [length_ps, pstep]
  · left
    obtain ⟨pRed, uniqStep⟩ := firstPureStep
    obtain ⟨rlf, rfl, rfl, rfl⟩ := uniqStep pstep
    have : e -ᵖ-> e' := by grind only [PurePrimStep]
    simp only [PureSteps, List.append_nil, true_and]
    exact Std.List.Forall₂.append ps_ps₃ <| .cons lastSteps ss_ss₃

end Language
