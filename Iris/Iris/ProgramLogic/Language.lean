module

meta import Iris.Std.RocqPorting
public import Iris.Std.FromMathlib
public import Iris.Std.Relation
public import Iris.Std.List
public meta import Lean.PrettyPrinter.Delaborator
public import Batteries.Data.List.Basic

#rocq_ignore LanguageMixin "This feature was implemented differently using typeclasses"
#rocq_ignore language      "This feature was implemented differently using typeclasses"

-- TODO: Consider renaming `ToVal` typeclass to something better, since
--       it's not just the `toVal` operation it carries.

namespace Iris.ProgramLogic

@[expose] public section

open FromMathlib

variable {Expr : Type e}{Val : Type v}{State : Type σ}{Obs : Type o}

class ToVal (Expr : Type e) (Val : outParam <| Type v ) where
  toVal : Expr → Option Val
  ofVal : Val → Expr
  /-- If `toVal` is defined for an expression, `coe` is its inverse -/
  coe_of_toVal_eq_some (e : Expr)(v : Val) : toVal e = some v → ofVal v = e
  /-- `toVal` is defined `coe`, and works as its inverse -/
  toVal_coe (v : Val) : toVal (ofVal v) = some v
export ToVal (toVal coe_of_toVal_eq_some toVal_coe)

attribute [rocq_alias language.to_val] ToVal.toVal
attribute [rocq_alias language.of_val] ToVal.ofVal
attribute [rocq_alias mixin_of_to_val] coe_of_toVal_eq_some
attribute [rocq_alias mixin_to_of_val] ToVal.toVal_coe
attribute [simp, grind =] ToVal.toVal_coe

namespace ToVal

variable [ToVal Expr Val]

attribute [coe] ToVal.ofVal
instance : Coe Val Expr where coe := ToVal.ofVal

@[grind! ., rocq_alias of_to_val_flip]
theorem toVal_eq_iff_coe (e : Expr)(v : Val): (v : Expr) = e ↔ toVal e = some v :=
  ⟨(· ▸ ToVal.toVal_coe v), coe_of_toVal_eq_some e v⟩

@[rocq_alias of_val_inj]
instance [ι : ToVal Expr Val]: Function.Injective (ι.ofVal) := by
  intro x y h
  simpa [ToVal.toVal_coe] using congrArg (toVal) h

end ToVal

class PrimStep
    (Expr : Type e)
    (State : outParam (Type σ))
    (Obs : outParam (Type o)) where
  /-- The primitive reduction relation of the language -/
  primStep   : Expr × State → Obs → Expr × State × List Expr → Prop

namespace PrimStep

@[inherit_doc PrimStep.primStep]
scoped notation conf:40 " -<" obs:max ">-> " conf':41  => PrimStep.primStep conf obs conf'

end PrimStep
open PrimStep

section PureConfigurationTypes
variable [PrimStep Expr State Obs]

@[rocq_alias reducible]
def reducible : Expr × State → Prop
| (e, σ) => ∃ obs e' σ' eₜ,
    (e, σ) -<obs>-> (e', σ', eₜ)

@[rocq_alias reducible_no_obs]
def pureReducible [PrimStep Expr State (List Obs)] : Expr × State → Prop
| (e, σ) => ∃ e' σ' eₜ,
    (e, σ) -<[]>-> (e', σ', eₜ)

def irreducible : Expr × State → Prop
| (e, σ) => ∀ obs e' σ' eₜ, ¬ (e, σ) -<obs>-> (e', σ', eₜ)

def stuck [ToVal Expr Val]: Expr × State → Prop
| (e, σ) => toVal e = none ∧ irreducible (e, σ)

def notStuck [ToVal Expr Val]: Expr × State → Prop
| (e, σ) => (toVal e).isSome ∨ reducible (e, σ)

end PureConfigurationTypes

class Language
    (Expr  : Type e)
    (State : outParam (Type σ))
    (Obs   : outParam (Type o))
    (Val   : outParam (Type v))
  extends
    PrimStep Expr State (List Obs),
    ToVal Expr Val where
  /-- Values in a language should not reduce -/
  val_stuck : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (e, σ) -<obs>-> (e', σ', eₜ) → toVal e = none

attribute [rocq_alias mixin_val_stuck] Language.val_stuck

namespace Language

variable [Λ : Language Expr State Obs Val]

variable {e e': Expr}{σ σ': State}{v v' : Val}

/-- A single atomic step in a threaded context -/
@[grind, rocq_alias step]
inductive Step : List Expr × State → List Obs → List Expr × State → Prop
  where
  | atomic : ∀ e σ  obs e' σ' eₜ,
    (e, σ) -<obs>-> (e', σ', eₜ) →
    ∀ (t₁ t₂: List Expr),
    Step (t₁ ++ e :: t₂, σ) obs (t₁ ++ e' :: t₂ ++ eₜ, σ')
    -- NOTE: Using `t₁ ++ e :: t₂` instead of `t₁ ++ [e] ++ t₂` because
    -- most lemmas about an element appearing in the middle of a list
    -- are in the shape `t₁ ++ e :: t₂`, this form is preferred.

def Step.of_primStep : ∀ {e σ}{obs : List Obs}{e'} {σ' : State} {eₜ},
    (e, σ) -<obs>-> (e', σ', eₜ) →
    ∀ {t₁ t₂: List Expr},
    Step (t₁ ++ e :: t₂, σ) obs (t₁ ++ e' :: t₂ ++ eₜ, σ') :=
  (Language.Step.atomic _ _ _ _ _ _ · _ _)

@[inherit_doc Step]
scoped notation conf:40 " -<" obs:max ">->ₜₚ " conf':41 => Language.Step conf obs conf'

/-- The (possibly zero) sequence of `Language.step`s -/
@[grind, rocq_alias nsteps]
inductive NSteps : Nat → List Expr × State → List Obs → List Expr × State → Prop
  where
  | refl (ρ : List Expr × State): NSteps 0 ρ [] ρ
  | cons n (ρ₁ ρ₂ ρ₃ : List Expr × State) (obs obs' : List Obs) :
      ρ₁ -<obs>->ₜₚ ρ₂ →
      NSteps n ρ₂ obs' ρ₃ →
      NSteps (n+1) ρ₁ (obs ++ obs') ρ₃

@[inherit_doc NSteps]
scoped notation conf:40 " -<" obs:max ">->ₜₚ^[" n:max "] " conf':41 =>
 Language.NSteps n conf obs conf'

/-- A `Language.step`s with no observation information -/
@[rocq_alias erased_step]
def erasedStep (ρ  ρ₂: List Expr × State) := ∃ obs, Step ρ obs ρ₂

@[inherit_doc erasedStep]
scoped notation conf:40 " -·->ₜₚ " conf':41 => Language.erasedStep conf conf'

/-- A sequence of `Language.erasedStep`s -/
scoped notation conf:40 " -·->ₜₚ* " conf':41 =>
  Relation.ReflTransGen erasedStep conf conf'

open Relation in
@[rocq_alias erased_step_nsteps]
theorem erasedStep_NSteps (ρ₁ ρ₂ : List Expr × State) :
    ρ₁ -·->ₜₚ* ρ₂ ↔ ∃ n obs, ρ₁ -<obs>->ₜₚ^[n] ρ₂ := by
  constructor <;> intros hyp
  · replace ⟨n, hyp⟩ := ReflTrans_iff_exists_iterate.1 hyp
    exists n
    induction hyp using Relation.Iterate.head_induction_on with
    | rfl => exists []; constructor
    | head ρ' firstStep lastSteps IH =>
      replace ⟨obs, firstStep⟩ := firstStep
      replace ⟨obs', IH⟩ := IH
      exists (obs ++ obs')
      constructor <;> assumption
  · replace ⟨n, obs, hyp⟩ := hyp
    apply ReflTrans_iff_exists_iterate.2
    exists n
    induction hyp with
    | refl => constructor
    | cons n ρ₁ ρ₂ ρ₃ obs obs' =>
      apply Iterate.head
      · exists obs
      · assumption

section ReducibilityLemmas

@[rocq_alias not_reducible, grind =]
theorem not_reducible_iff_irreducible {e : Expr} {σ : State} :
    (¬ reducible (e, σ)) ↔ irreducible (e, σ) := by
  grind only [reducible, irreducible]

@[rocq_alias reducible_not_val, grind .]
theorem toVal_none_of_reducible :
    reducible (e, σ) → toVal e = none := by
  grind only [reducible, val_stuck]

@[rocq_alias reducible_no_obs_reducible, grind .]
theorem reducible_of_pureReducible :
    pureReducible (e, σ) → reducible (e, σ) := by
  grind only [pureReducible, reducible]

@[rocq_alias val_irreducible]
theorem val_irreducible :
    (toVal e).isSome →
    irreducible (e, σ) := by
  grind only [irreducible, val_stuck, = Option.isSome_none]

@[rocq_alias not_not_stuck, grind =]
theorem not_not_suck {e : Expr} {σ : State} :
    (¬ notStuck (e, σ)) ↔ stuck (e, σ) := by
  dsimp [stuck, notStuck]
  match h : (toVal e) with
  | some v =>
    simp only [Option.isSome_some, true_or, not_true_eq_false, reduceCtorEq, false_and]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_or, not_reducible_iff_irreducible,
      true_and]

@[rocq_alias prim_step_not_stuck]
theorem primStep_notStuck {e : Expr} {σ obs e' σ' eₜ} :
    (e, σ) -<obs>-> (e', σ', eₜ) →
    notStuck (e, σ) :=
  fun h => .inr ⟨_, _, _, _, h⟩
end ReducibilityLemmas

@[rocq_alias atomicity]
inductive Atomicity where
| WeaklyAtomic
| StronglyAtomic

#rocq_ignore stuckness_to_atomicity "There is no `Stuckness` implementation yet."

@[rocq_alias Atomic]
class Atomic (a : Atomicity) (e : Expr) : Prop where
  atomic : ∀ (σ : State) obs e' σ' eₜ,
    (e, σ) -<obs>-> (e', σ', eₜ) →
    match a with
    | .WeaklyAtomic => ¬ reducible (e', σ')
    | .StronglyAtomic => (toVal e').isSome

@[rocq_alias strongly_atomic_atomic]
theorem stronglyAtomic_atomic a :
    Atomic (State := State) .StronglyAtomic e →
    Atomic (State := State) a e := by
  match a with
  | .StronglyAtomic => intros; assumption
  | .WeaklyAtomic =>
    rintro ⟨h⟩
    constructor
    grind only [not_reducible_iff_irreducible, val_irreducible]


/-- `Context K` says `K` models an evaluation context for the language -/
@[rocq_alias LanguageCtx]
class Context(K: Expr → Expr) where
  toVal_eq_none_fill : ∀ {e : Expr},
    toVal e = none → toVal (K e) = none
  primStep_fill : ∀ {e} {σ : State} {obs e' σ' eₜ},
    (e, σ) -<obs>-> (e', σ', eₜ) →
    (K e, σ) -<obs>-> (K e', σ', eₜ)
  primStep_fill_inv : ∀ {e} {σ : State} {obs K_e' σ' eₜ},
    toVal e = .none →
    (K e, σ) -<obs>-> (K_e', σ', eₜ) →
    ∃ e', K_e' = K e' ∧ (e, σ) -<obs>-> (e', σ', eₜ)

attribute [rocq_alias fill_not_val] Context.toVal_eq_none_fill
attribute [rocq_alias fill_step] Context.primStep_fill
attribute [rocq_alias fill_step_inv] Context.primStep_fill_inv

namespace Context

instance : Context (Λ := Λ) (id (α := Expr)) where
  toVal_eq_none_fill e := by grind only [id]
  primStep_fill      := by grind only [id]
  primStep_fill_inv  := by grind only [id]

@[rocq_alias reducible_fill]
theorem reducible_fill (K : Expr → Expr) [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    reducible (e,σ) → reducible ((K e), σ) :=
  fun ⟨obs, e', σ', eₜ, h⟩ =>
    ⟨obs, K e', σ', eₜ, primStep_fill h⟩

@[rocq_alias reducible_fill_inv]
theorem reducible_fill_inv (K : Expr → Expr) [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    toVal e = none → reducible (K e, σ) → reducible (e,σ) :=
  fun toVal_none ⟨obs, _, σ', eₜ, K_red⟩ =>
    have ⟨e₂, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨obs, e₂, σ', eₜ, red⟩

@[rocq_alias reducible_no_obs_fill]
theorem pureReducible_fill (K : Expr → Expr) [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    pureReducible (e, σ) →
    pureReducible (K e, σ) :=
  fun ⟨e', σ', eₜ, h⟩ =>
    ⟨K e', σ', eₜ, primStep_fill h⟩

@[rocq_alias reducible_no_obs_fill_inv]
theorem pureReducible_fill_inv (K : Expr → Expr) [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    toVal e = none → pureReducible (K e, σ) → pureReducible (e,σ) :=
  fun toVal_none ⟨_, σ', eₜ, K_red⟩ =>
    have ⟨e₂, _, red⟩ := primStep_fill_inv toVal_none K_red
    ⟨e₂, σ', eₜ, red⟩

@[rocq_alias irrreducible_fill]
theorem irreducible_fill (K : Expr → Expr) [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    toVal e = none →
    irreducible (e, σ) →
    irreducible (K e, σ) :=
  fun toVal_none irred =>
    not_reducible_iff_irreducible.1 <|
    fun red =>
    not_reducible_iff_irreducible.2 irred <|
    reducible_fill_inv K toVal_none red

@[rocq_alias irreducible_fill_inv]
theorem irreducible_fill_inv {K : Expr → Expr} [Λ.Context K] ⦃e : Expr⦄ ⦃σ : State⦄ :
    irreducible (K e, σ) →
    irreducible (e,σ) :=
  fun irred =>
    not_reducible_iff_irreducible.1 <|
    fun red =>
    not_reducible_iff_irreducible.2 irred <|
    reducible_fill K red

@[rocq_alias not_stuck_fill_inv]
theorem notStuck_fill_inv (K : Expr → Expr) [Λ.Context K] :
    notStuck (K e, σ) → notStuck (e, σ)  := by
  intros hyp
  dsimp only [notStuck]
  match hyp with
  | .inl hyp =>
    simp [Option.isSome_iff_exists] at hyp ⊢
    match h : toVal e with
    | none =>
      left
      have := toVal_eq_none_fill (K := K) h
      grind only
    | some v => grind only
  | .inr hyp =>
    match h₂ : toVal e with
    | none =>
      right
      apply reducible_fill_inv K h₂ hyp
    | some v =>
      left
      simp only [Option.isSome]

@[rocq_alias stuck_fill]
theorem stuck_fill (K : Expr → Expr) [Λ.Context K] :
    stuck (e, σ) → stuck (K e, σ)  :=
  fun ⟨toVal_e, irred⟩ =>
    ⟨ toVal_eq_none_fill toVal_e
    , irreducible_fill K toVal_e irred⟩

end Context

open List in
@[rocq_alias step_Permutation]
theorem perm_of_step (t₁ t₁' t₂ : List Expr) :
    ∀ ⦃obs : List Obs⦄⦃σ₁ σ₂ : State⦄,
    t₁ ~ t₁' →
    (t₁, σ₁) -<obs>->ₜₚ (t₂, σ₂) →
    ∃ t₂', t₂ ~ t₂'
         ∧ (t₁', σ₁) -<obs>->ₜₚ (t₂', σ₂)
     := by
  rintro obs σ₁ σ₂ t1perm
    ⟨e, σ₁, obs, e', σ₂, eₜ, red, ps, ss⟩
  obtain ⟨ps', ss', rfl⟩ := t₁'.mem_iff_append.1 (show e ∈ t₁' from by
    grind only [usr append_assoc, usr Perm.mem_iff, = cons_append, = mem_append, = mem_cons])
  exists ps' ++ e' :: ss' ++ eₜ
  constructor
  · apply List.Perm.append_right
    calc ps ++ e' :: ss
      _ ~ e' :: (ps ++ ss) := perm_middle
      _ ~ e' :: (ps' ++ ss') := by
        apply (List.perm_cons e').mpr
        apply (List.perm_cons e).mp
        exact (perm_middle.symm.trans t1perm).trans perm_middle
      _ ~ ps' ++ e' :: ss' := perm_middle.symm
  · apply Language.Step.of_primStep red

@[rocq_alias step_insert]
theorem step_update_of_getElem? {i obs efs} {t : List Expr} (σ₁ σ₂ : State):
    t[i]? = some e →
    (e, σ₁) -<obs>-> (e', σ₂, efs) →
    (t, σ₁) -<obs>->ₜₚ (t.set i e' ++ efs, σ₂) := by
  grind only [= getElem?_neg, = getElem?_pos, = Iris.Std.List.getElem?_some_iff_append,
    = List.getElem?_append, = List.getElem?_cons, = List.set_append, = List.set_cons_zero,
    Step.atomic]

open List in
@[rocq_alias erased_step_Permutation]
theorem perm_of_erasedStep (t₁ t₁' t₂ : List Expr) :
    ∀ ⦃σ₁ σ₂ : State⦄,
    t₁ ~ t₁' →
    (t₁, σ₁) -·->ₜₚ (t₂, σ₂) →
    ∃ t₂', t₂ ~ t₂'
         ∧ (t₁', σ₁) -·->ₜₚ (t₂', σ₂)
     :=
  fun _ _ t1perm ⟨obs, red⟩ =>
  have ⟨t₂', t2perm, red'⟩ := perm_of_step _ _ _ t1perm red
  ⟨t₂', t2perm, obs, red'⟩

section PureSteps

/-- There is a pure step between `e₁` and `e₂` iff there is
    a reduction step `(e₁, σ) -<[]>-> (e₂, σ, [])` for some
    σ and it is unique.

    Intuitively, the reduction is deterministic and does not
    depend on the environment.
-/
@[rocq_alias pure_step]
def purePrimStep (e₁ e₂ : Expr) :=
  (∀ σ : State, pureReducible (e₁, σ)) ∧
  (∀ {σ₁ σ₂ : State} {obs e₂' eₜ},
    (e₁, σ₁) -<obs>-> (e₂', σ₂, eₜ) →
    obs = [] ∧ σ₁ = σ₂ ∧ e₂ = e₂' ∧ eₜ = []
  )

@[inherit_doc purePrimStep]
scoped notation conf:40 " -ᵖ-> " conf':41 => purePrimStep conf conf'

/-- `e₁ -ᵖ->^[n] e₂` represents a sequence of `n` pure steps taken
    from `e₁` up to `e₂`.
-/
scoped notation conf:40 " -ᵖ->^[" n "] " conf':41 => Relation.Iterate purePrimStep n conf conf'

/-- `e₁ -ᵖ->* e₂` represents a sequence of some number of pure steps
    taken from `e₁` up to `e₂`.
-/
scoped notation conf:40 " -ᵖ->* " conf':41 => Relation.ReflTransGen purePrimStep conf conf'

@[rocq_alias pure_steps_tp]
abbrev pureSteps (t₁ t₂ : List Expr) := List.Forall₂ (· -ᵖ->* ·) t₁ t₂

/-- `e₁ -ᵖ->ₜₚ* e₂` represents a sequence of some number of pure steps
    taken from `e₁` up to `e₂`.
-/
scoped notation conf:40 " -ᵖ->ₜₚ* " conf':41 => Language.pureSteps conf conf'

open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Language.pureSteps]
meta def unexpandLanguagePureSteps : Unexpander
| `(pureSteps $conf $conf') =>
  `($conf -ᵖ->ₜₚ* $conf')
| _ => throw ()

@[rocq_alias PureExec]
class PureExec (φ : Prop) (n : Nat) (e₁ e₂ : Expr) : Prop where
  pureExec : φ → e₁ -ᵖ->^[n] e₂

@[rocq_alias pure_step_ctx]
theorem purePrimStep_fill (K : Expr → Expr) [Context K] {e₁ e₂ : Expr} :
    e₁ -ᵖ-> e₂ →
    K e₁ -ᵖ-> K e₂ := by
  rintro ⟨pRed,Hstep⟩
  constructor
  · exact (Context.pureReducible_fill K <| pRed ·)
  · intros σ₁ σ₂ obs K_e₂' eₜ primStep
    have : toVal e₁ = none := by
      apply toVal_none_of_reducible (σ := σ₁)
      -- Any state works
      apply reducible_of_pureReducible
      apply pRed
    obtain ⟨e₂', rfl, primStep⟩ := Context.primStep_fill_inv this primStep
    grind only

@[rocq_alias pure_step_nsteps_ctx]
theorem iterate_purePrimStep_fill (K : Expr → Expr) [Context K] {e₁ e₂} :
    e₁ -ᵖ->^[n] e₂ →
    K e₁ -ᵖ->^[n] K e₂ := by
  intro h
  induction h with
  | rfl => constructor
  | tail y first last IH =>
    apply Relation.Iterate.tail (K y) IH (purePrimStep_fill K last)

@[rocq_alias rtc_pure_step_ctx]
theorem ReflTransGen_pureStep_fill (K : Expr → Expr) [Context K] {e₁ e₂} :
    e₁ -ᵖ->* e₂ →
    K e₁ -ᵖ->* K e₂ := by
  intros h
  replace ⟨n, h⟩:= Relation.ReflTrans_iff_exists_iterate.1 h
  exact Relation.ReflTrans_iff_exists_iterate.2 ⟨n, iterate_purePrimStep_fill K h⟩

@[rocq_alias pure_exec_ctx]
theorem pureExec_fill (K : Expr → Expr) [Context K] {φ n e₁ e₂} :
    PureExec φ n e₁ e₂ →
    PureExec φ n (K e₁) (K e₂) := by
  rintro ⟨h⟩
  constructor
  intros hφ
  exact iterate_purePrimStep_fill K (h hφ)


@[rocq_alias rtc_pure_step_val]
theorem ReflTransGen_purePrimStep_val [Inhabited State] {v : Val} {e : Expr} :
    (v: Expr) -ᵖ->* e →
    toVal e = some v := by
  intros h
  induction h with
  | refl => exact (ToVal.toVal_coe _)
  | tail H1 H2 IH =>
    obtain ⟨red, stepUniq⟩ := H2
    have ⟨e', σ', eₜ, step⟩ := red default
    grind only [Language.val_stuck]

end PureSteps

class IntoVal (e : Expr)(v : Val) where
  into_val : (v : Expr) = e

class AsVal (e : Expr) where
  as_val : ∃ v, (v : Expr) = e

#rocq_ignore as_vals_of_val "We have not yet implemented TCForall."

@[rocq_alias as_val_is_Some]
theorem as_val_isSome e :
    (∃ v : Val, (v : Expr) = e) → (toVal e).isSome := by
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
theorem erasedStep_pureSteps (t₁ t₂ t₃ : List Expr) (σ₁ σ₂ : State) :
    (t₁, σ₁)  -·->ₜₚ  (t₂, σ₂) →
       t₁     -ᵖ->ₜₚ*    t₃ →
    (σ₁ = σ₂ ∧ t₂ -ᵖ->ₜₚ* t₃) ∨ -- t₂ was actually obtained form a pure reduction
    (∃ i e eₜ e' obs,           -- t₃ didn't touch the expression e which changed in t₂
      t₁[i]? = some e ∧
      t₃[i]? = some e ∧
      t₂ = t₁.set i e' ++ eₜ ∧
      (e, σ₁) -<obs>-> (e', σ₂, eₜ)
    ) := by
  rintro ⟨obs, ⟨e, σ₁, obs, e₂, σ₂, eₜ, pstep, ps, ss⟩⟩ Hps
  obtain ⟨ps₃, e₃, ss₃, rfl, ss_ss₃, ps_ps₃, length_ps, e_e₃⟩ :=
    show ∃ ps₃ e₃ ss₃, t₃ = ps₃ ++ e₃ :: ss₃
         ∧ ss -ᵖ->ₜₚ* ss₃
         ∧ ps -ᵖ->ₜₚ* ps₃ ∧ ps.length = ps₃.length
         ∧ e -ᵖ->* e₃ from by
      grind
  rcases Relation.ReflTransGen.cases_head e_e₃ with (rfl | ⟨e', firstPureStep, lastSteps⟩)
  · right
    exists (ps₃.length), e, eₜ, e₂, obs
    simp only [List.length_append, List.length_cons, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ,
      getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero,
      List.append_assoc, List.cons_append, List.set_append_right, List.set_cons_zero, and_self,
      length_ps, pstep]
  · left
    obtain ⟨pRed, uniqStep⟩ := firstPureStep
    obtain ⟨rlf, rfl, rfl, rfl⟩ := uniqStep pstep
    have : e -ᵖ-> e' := by grind only [purePrimStep]
    simp only [pureSteps, List.append_nil, true_and]
    apply Iris.Std.List.Forall₂.append ps_ps₃
    apply List.Forall₂.cons lastSteps ss_ss₃

end Language

section test
open Language

section notations

/--
info: (e, σ) -<obs>-> (e, σ, []) : Prop
-/
#guard_msgs in
variable (e : Expr) (σ : State) (obs : Obs) [PrimStep Expr State Obs] in
#check (PrimStep.primStep (e, σ) obs (e,σ,[]))

/--
info: (t, σ) -<obs>->ₜₚ (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) (obs : List Obs) [Language Expr State Obs Val] in
#check (Language.Step (t, σ) obs (t,σ))

/--
info: (t, σ) -<obs>->ₜₚ^[0] (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) (obs : List Obs) [Language Expr State Obs Val] in
#check (Language.NSteps 0 (t, σ) obs (t,σ))

/--
info: (t, σ) -·->ₜₚ (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) [Language Expr State Obs Val] in
#check (Language.erasedStep (t, σ) (t,σ))

/--
info: e -ᵖ-> e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (Language.purePrimStep e e)

/--
info: e -ᵖ->^[0] e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (Relation.Iterate Language.purePrimStep 0 e e)

/--
info: e -ᵖ->* e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (Relation.ReflTransGen Language.purePrimStep e e)

/--
info: e -ᵖ->* e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (Relation.ReflTransGen Language.purePrimStep e e)

/--
info: t -ᵖ->ₜₚ* t : Prop
-/
#guard_msgs in
variable (t : List Expr) [Language Expr State Obs Val] in
#check (Language.pureSteps t t)

end notations

end test
