/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

elab "ipose" colGt term:pmTerm : tactic => do
  let term ← liftMacroM <| PMTerm.parse term
  let mvar ← getMainGoal

  mvar.withContext do
    let f ← getFVarId term.ident
    let val := Expr.fvar f

    try
      let ls ← mvar.apply val
      replaceMainGoal ls
    catch _ =>
      let some ldecl := (← getLCtx).find? f | throwError "iapply: {term.ident.getId} not in scope"

      match ldecl.type with
      | .app (.app (.app (.app (.const ``Iris.BI.Entails _) _) _) P) Q =>
        let hyp ← mkAppM ``Iris.BI.wand #[P, Q]
        let pf ← mkAppM ``as_emp_valid_1 #[hyp, val]

        -- todo
      | _ => throwError "ipose: {term.ident.getId} is not an entailment"
