/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem pose [BI PROP] {P Q : PROP}
    (h : P ⊢ Q -∗ R) : (⊢ Q) → P ⊢ R :=
  λ hq => h.trans <| wand_entails <| hq.trans <| wand_intro <| wand_elim_r

elab "ipose" colGt term:pmTerm : tactic => do
  let term ← liftMacroM <| PMTerm.parse term
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, e, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let f ← getFVarId term.ident
    let val : Q(Prop) := Expr.fvar f

    try
      let ls ← mvar.apply val
      replaceMainGoal ls
    catch _ =>
      let some ldecl := (← getLCtx).find? f | throwError "ipose: {term.ident.getId} not in scope"

      match ldecl.type with
      | .app (.app (.app (.app (.const ``Iris.BI.Entails _) _) _) P) Q =>
        let hyp : Q($prop) ← mkAppM ``Iris.BI.wand #[P, Q]
        let pf : Q(⊢ $hyp) ← mkAppM ``as_emp_valid_1 #[hyp, val]

        let m : Q($e ⊢ $hyp -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
            IrisGoal.toExpr { u, prop, bi, hyps, goal := q(wand $hyp $goal), .. }

        let pf' : Q($e ⊢ $goal) := q(pose $m $pf)

        mvar.assign pf'
        replaceMainGoal [m.mvarId!]
      | _ => throwError "ipose: {term.ident.getId} is not an entailment"
