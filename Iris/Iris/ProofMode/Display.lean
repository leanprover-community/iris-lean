/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.ProofMode.Expr

public meta section

namespace Iris.ProofMode
open Iris.BI Qq
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/-!
# IPM Proof State Display

This file generates the state display for the Iris Proof Mode. It is implemented as a
delaborator for the function `Entails'`. This function is definitionally equal to the `Entails`
predicate defined in `BI.BIBase`, its purpose is merely to serve as a marker for the delaboration
function. The hypothesis of the entailment are diplayed with a leading `□` or `∗` depending on
whether they are persistent or not.

NOTE: Hypothesis are assumed to have a specific shape so they can be displayed correctly.
In particular, hypothesis must have name annotations so they may be displayed appropiately.
-/

syntax irisHyp := ("□" <|> "∗") ident " : " term

syntax irisGoalStx := ppDedent(ppLine irisHyp)* ppDedent(ppLine "⊢ " term)

open Lean.PrettyPrinter.Delaborator SubExpr

def delabIProp : Delab := do
  annotateCurPos (← unpackIprop (← delab))

/-- Move from the position of a hypothesis node `□?p (IrisHyp ty)` to the position of `ty`. -/
def withHypType {α} [Inhabited α] (persistent : Bool) (d : DelabM α) : DelabM α :=
  let d := withMDataExpr <| withAppArg d
  if persistent then withNaryArg 2 d else d

@[delab app.Iris.ProofMode.IrisHyp]
def delabIrisHyp : Delab := withAppArg delab

@[delab app.Iris.ProofMode.Entails']
def delabIrisGoal : Delab := do
  let some { hyps, goal, .. } := parseIrisGoal? (← instantiateMVars (← getExpr)) | failure
  -- Delaboration for the hypotheses
  let ⟨_, hypStxs⟩ ← withNaryArg 2 <| delabHypotheses hyps ({}, #[])
  -- Delaboration for the proof goal
  let goalStx ← withNaryArg 3 delabIProp
  -- Conceal internal machinery (`Entails'`, `IrisHyp`) from user's view
  let stx ← annotateCurPos ⟨← `(irisGoalStx| $hypStxs.reverse* ⊢ $goalStx:term)⟩
  addTermInfo (← getPos) stx q(Entails $(clean hyps) $goal)
  return stx
where
  delabHypotheses {u prop bi s} (hyps : @Hyps u prop bi s)
      (acc : NameMap Nat × Array (TSyntax ``irisHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``irisHyp)) := do
    match hyps with
    | .emp _ => pure acc
    | .sep _ _ _ _ lhs rhs =>
      let acc ← withNaryArg 3 <| delabHypotheses rhs acc
      withNaryArg 2 <| delabHypotheses lhs acc
    | .hyp _ name ivar p ty _ =>
      let (map, acc) := acc
      -- For printing the name of the hypothesis, `✝` if anonymous
      let (idx, name') := match map.find? name with
        | some idx =>
          (idx + 1, name.appendAfter <|
            if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
        | none => (0, name)
      let pos ← getPos
      -- Delaboration of the proposition itself
      let tyStx ← withHypType (isTrue p) delabIProp
      let nameStx : Ident :=
        ⟨(mkIdent name').raw.setInfo (.synthetic ⟨pos.asNat⟩ ⟨pos.asNat⟩)⟩
      withLCtx ((← getLCtx).mkLocalDecl ⟨ivar.name⟩ name' q(HypMarker $ty))
          (← getLocalInstances) do
        addTermInfo pos nameStx (.fvar ⟨ivar.name⟩) (isBinder := true)
      -- Determine the prefix based on whether it is in the spatial or intuitionistic context
      let stx ← if isTrue p then
        `(irisHyp| □$nameStx : $tyStx)
      else
        `(irisHyp| ∗$nameStx : $tyStx)
      pure (map.insert name idx, acc.push stx)
  clean {u prop bi s} (hyps : @Hyps u prop bi s) : Q($prop) :=
    match hyps with
    | .emp _ => q(emp)
    | .sep _ _ _ _ lhs rhs => q(iprop($(clean lhs) ∗ $(clean rhs)))
    | .hyp _ _ _ p ty _ => (mkIntuitionisticIf bi p ty).val

@[delab app.Iris.ProofMode.HypMarker]
def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
