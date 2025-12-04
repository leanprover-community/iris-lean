/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Cases
import Iris.Std

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pose [BI PROP] {P Q R : PROP}
    (H1 : P ∗ Q ⊢ R) (H2 : ⊢ Q) : P ⊢ R :=
  sep_emp.mpr.trans <| (sep_mono_r H2).trans H1

theorem pose_forall [BI PROP] (x : α) (P : α → PROP) {Q : PROP}
    [H1 : IntoForall Q P] (H2 : ⊢ Q) : ⊢ P x :=
  Entails.trans H2 <| H1.into_forall.trans <| forall_elim x

partial def instantiateForalls {prop : Q(Type u)} (bi : Q(BI $prop)) (hyp : Q($prop))
    (pf : Q(⊢ $hyp)) (terms : List Term) : TacticM (Expr × Expr) := do
  if let some t := terms.head? then
    let texpr ← mkAppM' (← elabTerm t none) #[]
    let ⟨_, ttype, texpr⟩ ← inferTypeQ texpr
    let Φ ← mkFreshExprMVarQ q($ttype → $prop)
    let _ ← synthInstanceQ q(IntoForall $hyp $Φ)
    let res ← mkAppM' Φ #[texpr]
    let pf' ← mkAppM ``pose_forall #[texpr, Φ, pf]
    return ← instantiateForalls bi res pf' terms.tail
  else
    let pf ← mkAppM ``as_emp_valid_1 #[hyp, pf]
    return ⟨hyp, pf⟩

partial def handleDependentArrows {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (goals : IO.Ref (Array MVarId)) : TacticM (Expr × Q(Prop)) := do
  let p : Q(Prop) ← inferType val
  if let .forallE _ binderType _ _ := p then
    let m ← mkFreshExprMVar binderType
    let val' := mkApp val m
    goals.modify (·.push m.mvarId!)
    return ← handleDependentArrows bi val' goals
  else
    return (val, p)

def iPoseCore {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (terms : List Term)
    (goals : IO.Ref (Array MVarId)) : TacticM (Q($prop) × Expr) := do
  let hyp ← mkFreshExprMVarQ q($prop)
  let (v, p) ← handleDependentArrows bi val goals
  if let some _ ← try? <| synthInstanceQ q(IntoEmpValid $p $hyp) then
    return ← instantiateForalls bi hyp v terms
  else
    throwError "ipose: {val} is not an entailment"

elab "ipose" colGt pmt:pmTerm "as" pat:(colGt icasesPat) : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let goals ← IO.mkRef #[]

    let f ← getFVarId pmt.term
    let ⟨hyp, pf⟩ := ← iPoseCore bi (.fvar f) pmt.terms goals

    let m ← iCasesCore bi hyps goal q(false) hyp hyp ⟨⟩ pat (λ hyps => goalTracker goals .anonymous hyps goal)
    mvar.assign <| ← mkAppM ``pose #[m, pf]
    replaceMainGoal (← goals.get).toList
