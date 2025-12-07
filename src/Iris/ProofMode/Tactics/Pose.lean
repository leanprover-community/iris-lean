/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Cases
import Iris.ProofMode.Instances
import Iris.Std

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pose {PROP} [BI PROP] {P Q R : PROP}
    (H1 : P ∗ Q ⊢ R) (H2 : ⊢ Q) : P ⊢ R :=
  sep_emp.mpr.trans <| (sep_mono_r H2).trans H1

-- TODO: clean up

theorem emp_wand {PROP} [BI PROP] {P : PROP}: (emp ⊢ P) → (⊢ P) := by
 intros H
 assumption

/-- Instantiate Iris-level forall with `x`.
  - `Q` is `∀ x, P x`
-/
theorem pose_forall [BI PROP] (x : α) (P : α → PROP) {Q : PROP}
    [H1 : IntoForall Q P] (H2 : ⊢ Q) : ⊢ P x :=
  Entails.trans H2 <| H1.into_forall.trans <| forall_elim x

/-- Instantiate Iris-level foralls in `hyp` with the given `terms`.
    - `hyp`: The Iris hypothesis type (e.g., `P -∗ Q` or `∀ x, P x`)
    - `pf`: A proof that can convert to `⊢ hyp` via `AsEmpValid1`
           (e.g., `pf : P ⊢ Q` when `hyp = P -∗ Q`)
    - Returns: `(final_hyp, proof of ⊢ final_hyp)` -/
partial def instantiateForalls {prop : Q(Type u)} (bi : Q(BI $prop)) (hyp : Q($prop))
    (pf : Expr) (terms : List Term) : TacticM (Expr × Expr) := do
  if let some t := terms.head? then
    let texpr ← mkAppM' (← elabTerm t none) #[]
    let ⟨_, ttype, texpr⟩ ← inferTypeQ texpr
    let Φ ← mkFreshExprMVarQ q($ttype → $prop)
    let _ ← synthInstanceQ q(IntoForall $hyp $Φ)
    let res ← mkAppM' Φ #[texpr]
    let pf' ← mkAppM ``pose_forall #[texpr, Φ, pf]
    return ← instantiateForalls bi res pf' terms.tail
  else
    let pf'Ty ← inferType pf
    if let some #[_, _, hh, (P : Q($prop))] := (← whnfR pf'Ty).appM? ``Entails then
      if (← whnfR hh).isAppOfArity ``BI.emp 2 then
        -- special case for `emp ⊢ P`
        let pf' : Expr ← mkAppM ``emp_wand #[pf]
        let pf ← mkAppM ``as_emp_valid_1 #[P, pf']
        return ⟨P, pf⟩
      else
      -- case for `P ⊢ Q`
      let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
      return ⟨hyp, pf⟩
    else
      -- case for `⊢ P`
      let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
      return ⟨hyp, pf⟩

/-- Process Lean-level foralls/implications in the type of `val`.

    For each `∀` binder in the type:
    - If the binder type is `Prop` (a Lean implication like `cond → ...`),
      creates a metavar and adds it as a proof obligation goal
    - If the binder type is a type parameter (like `∀ (x : A), ...`),
      creates a metavar but does NOT add it as a goal

    Parameters:
    - `val`: The proof term whose type contains foralls
    - `goals`: Accumulator for Prop-typed proof obligations

    Returns: `(applied_val, final_type)` where `val` has been applied to
    fresh metavars for all forall binders

    Example: If `val : ∀ (x : A), cond x → (P x ⊢ Q x)`, returns
    `(val ?x ?h, P ?x ⊢ Q ?x)` with `?h : cond ?x` added to goals -/
partial def handleDependentArrows {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (goals : IO.Ref (Array MVarId)) : TacticM (Expr × Q(Prop)) := do
  let p : Q(Prop) ← inferType val
  if let .forallE _ binderType _ _ := p then
    let m ← mkFreshExprMVar binderType
    let val' := mkApp val m
    let binderTypeType ← inferType binderType
    -- Only add as goal if binderType is Prop (i.e., this is a Lean implication)
    -- For type parameters (Sort u), we just use metavars without adding goals
    if binderTypeType.isProp then
      goals.modify (·.push m.mvarId!)
    return ← handleDependentArrows bi val' goals
  else
    return (val, p)



/-- Synthesize an `IntoEmpValid φ P` instance, recursively handling:
    - `let` bindings (zeta-reduce)
    - Implications `φ → ψ` (using `intoEmpValid_impl`)
    - Foralls `∀ x, φ x` (using `intoEmpValid_forall`)
    - Base cases `⊢ P`, `P ⊢ Q`, `P ⊣⊢ Q` (direct synthesis)

    Returns: proof of `IntoEmpValid φ P` (as Expr, to avoid Qq type issues with whnf)
-/
partial def synthIntoEmpValid {prop : Q(Type u)} (bi : Q(BI $prop))
    (φ : Q(Prop)) (P : Q($prop)) (goals : IO.Ref (Array MVarId)) : MetaM Expr := do
  -- First, zeta-reduce any let bindings
  let φReduced ← whnf φ
  -- logInfo m!"reduced: {φReduced}"

  -- Check for implication (non-dependent arrow): φ → ψ
  if let .forallE _name binderType body .default := φReduced then
    if !body.hasLooseBVars then
      -- Non-dependent: this is an implication φ → ψ
      let φ' := binderType
      let ψ := body
      -- Create a metavar for the premise φ and add it as a goal
      let hφ ← mkFreshExprMVar φ'
      goals.modify (·.push hφ.mvarId!)
      -- Recursively synthesize IntoEmpValid for ψ
      let innerInst ← synthIntoEmpValid bi ψ P goals
      -- Build intoEmpValid_impl instance
      return ← mkAppOptM ``intoEmpValid_impl #[prop, bi, P, φ', ψ, hφ, innerInst]

  -- Check for forall (dependent): ∀ x : A, φ x
  if let .forallE name binderType body _ := φReduced then
    -- Dependent forall: ∀ x : A, φ x
    let A := binderType
    -- Create a fresh metavar for x : A
    let x ← mkFreshExprMVar A
    -- Substitute x into the body to get φ x
    let φx := body.instantiate1 x
    -- Recursively synthesize IntoEmpValid for φ x
    let innerInst ← synthIntoEmpValid bi φx P goals
    -- Build intoEmpValid_forall instance
    -- We need: intoEmpValid_forall [BI PROP] (P : PROP) {α : Sort _} (φ : α → Prop) (x : α) [h : IntoEmpValid (φ x) P]
    let φFn := Expr.lam name binderType body .default
    return ← mkAppOptM ``intoEmpValid_forall #[prop, bi, P, A, φFn, x, innerInst]

  -- Base case: try to synthesize directly (handles ⊢ P, P ⊢ Q, P ⊣⊢ Q)
  try
    synthInstance q(@IntoEmpValid $φ $prop $P $bi)
  catch _ =>
    throwError "ipose: cannot find IntoEmpValid instance for {φ}"



/-- Core logic for `ipose`: converts a Lean proof into an Iris hypothesis.

    Parameters:
    - `val`: The Lean proof term to pose (e.g., a proof of `P ⊢ Q` or `cond → (P ⊢ Q)`)
    - `terms`: Optional terms to instantiate Iris-level foralls (from `ipose H x y as HR`)
    - `goals`: Accumulator for proof obligations from Lean implications

    Returns: `(hyp, pf)` where:
    - `hyp`: The Iris hypothesis type (e.g., `P -∗ Q`)
    - `pf`: A proof of `⊢ hyp`

    Example: If `val : P ⊢ Q`, returns `(P -∗ Q, proof of ⊢ P -∗ Q)` -/
def iPoseCore {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (terms : List Term)
    (goals : IO.Ref (Array MVarId)) : TacticM (Q($prop) × Expr) := do
  let hyp ← mkFreshExprMVarQ q($prop)
  let (v, p) ← handleDependentArrows bi val goals
  -- if
  let _ ← synthIntoEmpValid bi p hyp goals
  -- if let some _ ← try? <| synthIntoEmpValid bi p hyp goals then
  return ← instantiateForalls bi hyp v terms

  -- else
  --   throwError "ipose: {val} is not an Iris entailment\n  p = {p}\n"

elab "ipose" colGt pmt:pmTerm "as" pat:(colGt icasesPat) : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let goals ← IO.mkRef #[]

    -- Elaborate the term
    let val ← elabTerm pmt.term none true
    let val ← instantiateMVars val
    let ⟨hyp, pf⟩ := ← iPoseCore bi val pmt.terms goals

    let m ← iCasesCore bi hyps goal q(false) hyp hyp ⟨⟩ pat (λ hyps => goalTracker goals .anonymous hyps goal)
    mvar.assign <| ← mkAppM ``pose #[m, pf]
    replaceMainGoal (← goals.get).toList
