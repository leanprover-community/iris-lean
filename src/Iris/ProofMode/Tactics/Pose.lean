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

theorem emp_wand {PROP} [BI PROP] {P : PROP}: (emp ⊢ P) → (⊢ P) := id

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
    -- Check for special case: `emp ⊢ P` needs `emp_wand` to convert to `⊢ P`
    if let some #[_, _, hh, (P : Q($prop))] := (← whnfR pf'Ty).appM? ``Entails then
      if (← whnfR hh).isAppOfArity ``BI.emp 2 then
        let pf ← mkAppM ``emp_wand #[pf]
        let pf ← mkAppM ``as_emp_valid_1 #[P, pf]
        return ⟨P, pf⟩
    -- Default case: wrap with as_emp_valid_1
    let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
    return ⟨hyp, pf⟩

/-- Process Lean-level foralls/implications in the type of `val`.

    For each `∀` binder in the type (after whnf reduction to expose hidden foralls):
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
  -- Use whnf to expose foralls hidden behind let-bindings
  let pReduced ← whnf p
  if let .forallE _ binderType _ _ := pReduced then
    let m ← mkFreshExprMVar binderType
    let val' := mkApp val m
    let binderTypeType ← inferType binderType
    -- Only add as goal if binderType is Prop (i.e., this is a Lean implication)
    -- For type parameters (Sort u), we just use metavars without adding goals
    if binderTypeType.isProp then
      goals.modify (·.push m.mvarId!)
    return ← handleDependentArrows bi val' goals
  else
    -- Return the original type, not the whnf-reduced type
    -- (whnf may over-reduce things like entailment notation)
    return (val, p)

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
  -- Synthesize IntoEmpValid instance (handles base cases ⊢ P, P ⊢ Q, P ⊣⊢ Q)
  let _ ← try synthInstance q(@IntoEmpValid $p $prop $hyp $bi)
          catch _ => throwError "ipose: cannot find IntoEmpValid instance for {p}"
  return ← instantiateForalls bi hyp v terms

elab "ipose" colGt pmt:pmTerm "as" pat:(colGt icasesPat) : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    -- Accumulator for proof obligations from Lean implications
    let goals ← IO.mkRef #[]

    -- Elaborate the term and convert to Iris hypothesis
    let val ← elabTerm pmt.term none true
    let val ← instantiateMVars val
    let ⟨hyp, pf⟩ := ← iPoseCore bi val pmt.terms goals

    -- Destruct the hypothesis according to the pattern and add to context
    let m ← iCasesCore bi hyps goal q(false) hyp hyp ⟨⟩ pat (λ hyps => goalTracker goals .anonymous hyps goal)
    -- Complete the proof using the `pose` theorem
    mvar.assign <| ← mkAppM ``pose #[m, pf]
    -- Expose any proof obligations as new goals
    replaceMainGoal (← goals.get).toList
