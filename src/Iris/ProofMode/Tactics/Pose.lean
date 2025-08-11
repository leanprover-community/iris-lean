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

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
def iPoseCore
    (goal : Q($prop)) (hyps : Hyps bi e) (name : Name)
    (ident : TSyntax `ident) (f : FVarId)
    (addGoal : ∀ {e}, Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal))
    : MetaM Expr := do
  let val := Expr.fvar f

  let some ldecl := (← getLCtx).find? f | throwError "ipose: {ident} not in scope"

  match ldecl.type with
  | .app (.app (.app (.app (.const ``Iris.BI.Entails _) _) _) P) Q =>
    let hyp := ← match P with
    | .app (.app (.const ``Iris.BI.BIBase.emp _) _) _ => pure Q
    | _ => mkAppM ``Iris.BI.wand #[P, Q]
    let pf ← mkAppM ``as_emp_valid_1 #[hyp, val]

    let uniq ← mkFreshId
    let hyps' := .mkSep hyps (.mkHyp _ name uniq q(false) hyp)

    let m ← addGoal hyps' goal

    return ← mkAppM ``pose #[m, pf]
  | _ => throwError "ipose: {ident} is not an entailment"

elab "ipose" colGt ident:ident "as" colGt name:str : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let f ← getFVarId ident

    let goals ← IO.mkRef #[]
    mvar.assign <| ← iPoseCore goal hyps (.str .anonymous name.getString) ident f <| goalTracker goals .anonymous
    replaceMainGoal (← goals.get).toList
