/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pose [BI PROP] {e hyp goal : PROP}
    (H1 : e ∗ hyp ⊢ goal) (H2 : ⊢ hyp) : e ⊢ goal :=
  sep_emp.mpr.trans <| (sep_mono_r H2).trans H1

def iPoseCore (prop : Q(Type u)) (f : FVarId) (ident : Ident) : MetaM (Q($prop) × Expr) := do
  let val := Expr.fvar f
  let some ldecl := (← getLCtx).find? f | throwError "ipose: {ident} not in scope"

  match ldecl.type with
  | .app (.app (.app (.app (.const ``Iris.BI.Entails _) _) _) P) Q =>
    let hyp : Q($prop) := ← match P with
    | .app (.app (.const ``Iris.BI.BIBase.emp _) _) _ => pure Q
    | _ => mkAppM ``Iris.BI.wand #[P, Q]
    let pf ← mkAppM ``as_emp_valid_1 #[hyp, val]

    return ⟨hyp, pf⟩
  | _ => throwError "ipose: {ident} is not an entailment"

elab "ipose" colGt ident:ident "as" colGt name:str : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let f ← getFVarId ident
    let ⟨hyp, pf⟩ := ← iPoseCore prop f ident

    let uniq ← mkFreshId
    let name := .str .anonymous name.getString
    let hypsr := Hyps.mkHyp bi name uniq q(false) hyp hyp
    let hyps' := Hyps.mkSep hyps hypsr

    let goals ← IO.mkRef #[]
    let m ← goalTracker goals .anonymous hyps' goal
    mvar.assign <| ← mkAppM ``pose #[m, pf]
    replaceMainGoal (← goals.get).toList
