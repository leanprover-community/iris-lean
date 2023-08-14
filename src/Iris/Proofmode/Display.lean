/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.BI.Notation
import Iris.Proofmode.Expr

import Lean.PrettyPrinter.Delaborator

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/- This file generates the state display for the Iris Proof Mode. It is implemented as a
delaborator for the function `EnvsEntails`. An application of this function contains a separation
logic context as an object of `Envs` and a separation logic goal. The resulting display contains
the two separation logic contexts (intuitionistic and spatial), as well as the separation
logic goal. -/

syntax irisHyp := ("□" <|> "∗") ident " : " term

syntax irisGoalStx := ppDedent(ppLine irisHyp)* ppDedent(ppLine "⊢ " term)

abbrev delab := Lean.PrettyPrinter.delab

@[delab app.Iris.Proofmode.Entails']
def delabIrisGoal : Delab := do
  let expr ← instantiateMVars <| ← getExpr

  -- extract environment
  let some { hyps, goal, .. } := parseIrisGoal? expr | failure

  -- delaborate
  let hyps ← delabHypotheses hyps #[]
  let goal ← unpackIprop (← delab goal)

  -- build syntax
  return ⟨← `(irisGoalStx| $hyps* ⊢ $goal:term)⟩
where
  delabHypotheses {prop} (hyps : Hyps prop)
      (acc : Array (TSyntax ``irisHyp)) : DelabM (Array (TSyntax ``irisHyp)) := do
    match hyps with
    | .emp _ => pure acc
    | .hyp _ _ .spatial name ty =>
      acc.push <$> `(irisHyp| ∗$(mkIdent name) : $(← unpackIprop (← delab ty)))
    | .hyp _ _ .intuitionistic name ty =>
      acc.push <$> `(irisHyp| □$(mkIdent name) : $(← unpackIprop (← delab ty)))
    | .sep _ _ lhs rhs => delabHypotheses rhs (← delabHypotheses lhs acc)

end Iris.Proofmode
