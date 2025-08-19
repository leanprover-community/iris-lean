/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Patterns.CasesPattern
import Iris.ProofMode.Tactics.Basic

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

def iPoseCore {prop : Q(Type u)} (bi : Q(BI $prop)) (val : Expr) (terms : List Term) : TacticM (Q($prop) × Expr) := do
  let valType : Q($prop) ← inferType val
  match valType with
  | .app (.app (.app (.app (.const ``Iris.BI.Entails _) _) _) P) Q =>
    let hyp : Q($prop) := ← match P with
    | .app (.app (.const ``Iris.BI.BIBase.emp _) _) _ => pure Q
    | _ => mkAppM ``Iris.BI.wand #[P, Q]
    return ← instantiateForalls bi hyp val terms
  | _ => throwError "ipose: {val} is not an entailment"

elab "ipose" colGt pmt:pmTerm "as" pat:(colGt icasesPat) : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let f ← getFVarId pmt.term
    let ⟨hyp, pf⟩ := ← iPoseCore bi (.fvar f) pmt.terms

    let uniq ← mkFreshId
    let name ← match pat with
    | .one name =>
      let (name, _) ← getFreshName name
      pure <| .str .anonymous name.toString
    -- handling general introduction patterns should be implemented in the future (using iCasesCore)
    | _ => throwError "ipose: pattern must be a single identifier"

    let hypsr := Hyps.mkHyp bi name uniq q(false) hyp hyp
    let hyps' := Hyps.mkSep hyps hypsr

    let goals ← IO.mkRef #[]
    let m ← goalTracker goals .anonymous hyps' goal
    mvar.assign <| ← mkAppM ``pose #[m, pf]
    replaceMainGoal (← goals.get).toList
