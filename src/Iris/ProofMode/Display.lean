/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI.Notation
import Iris.ProofMode.Expr

import Lean.PrettyPrinter.Delaborator

namespace Iris.ProofMode
open Iris.BI Qq
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/- This file generates the state display for the Iris Proof Mode. It is implemented as a
delaborator for the function `EnvsEntails`. An application of this function contains a separation
logic context as an object of `Envs` and a separation logic goal. The resulting display contains
the two separation logic contexts (intuitionistic and spatial), as well as the separation
logic goal. -/

syntax irisHyp := ("□" <|> "∗") ident " : " term

syntax irisGoalStx := ppDedent(ppLine irisHyp)* ppDedent(ppLine "⊢ " term)

open Lean.PrettyPrinter

@[delab app.Iris.ProofMode.Entails']
def delabIrisGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some { hyps, goal, .. } := parseIrisGoal? expr | failure

  -- delaborate
  let (_, hyps) ← delabHypotheses hyps ({}, #[])
  let goal ← unpackIprop (← delab goal)

  -- build syntax
  return ⟨← `(irisGoalStx| $hyps.reverse* ⊢ $goal:term)⟩
where
  delabHypotheses {prop bi s} (hyps : @Hyps prop bi s)
      (acc : NameMap Nat × Array (TSyntax ``irisHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``irisHyp)) := do
    match hyps with
    | .emp _ => pure acc
    | .hyp _ name _ p ty _ =>
      let mut (map, acc) := acc
      let (idx, name') ← if let some idx := map.find? name then
        pure (idx + 1, name.appendAfter <| if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
      else
        pure (0, name)
      let stx ← if isTrue p then
        `(irisHyp| □$(mkIdent name') : $(← unpackIprop (← delab ty)))
      else
        `(irisHyp| ∗$(mkIdent name') : $(← unpackIprop (← delab ty)))
      pure (map.insert name idx, acc.push stx)
    | .sep _ _ _ _ lhs rhs => delabHypotheses lhs (← delabHypotheses rhs acc)

@[delab app.Iris.ProofMode.HypMarker]
def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
