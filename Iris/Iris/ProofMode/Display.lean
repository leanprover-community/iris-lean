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

/- This file generates the state display for the Iris Proof Mode. It is implemented as a
delaborator for the function `Entails'`. This function is definitionally equal to the `Entails`
predicate defined in `BI.BIBase`, its purpose is merely to serve as a marker for the delaboration
function. The hypothesis of the entailment are diplayed with a leading `□` or `∗` depending on
whether they are persistent or not.

NOTE: Hypothesis are assumed to have a specific shape so they can be displayed correctly.
In particular, hypothesis must have name annotations so they may be displayed appropiately. -/

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
  let some { e, hyps, goal, .. } := parseIrisGoal? (← instantiateMVars (← getExpr)) | failure
  -- Delaboration for the hypotheses
  let ⟨_, hypStxs⟩ ← withNaryArg 2 <|
    delabHypotheses hyps.toArray (hyps.toArray.size - 1) ({}, #[])
  -- Delaboration for the proof goal
  let goalStx ← withNaryArg 3 delabIProp
  -- Conceal internal machinery (`Entails'`, `IrisHyp`) from user's view
  let stx ← annotateCurPos ⟨← `(irisGoalStx| $hypStxs.reverse* ⊢ $goalStx:term)⟩
  -- The index `e` of `Hyps bi e` is already the annotation-free context term,
  -- so the old `clean` traversal is unnecessary.
  addTermInfo (← getPos) stx q(Entails $e $goal)
  return stx
where
  /-- Delaborate `hs[0], …, hs[i]` in reverse order. On entry the current `SubExpr`
  position must be the canonical left-nested `∗`-fold of `hs[0…i]`. -/
  delabHypotheses {u : Level} {prop : Q(Type u)}
      (hs : Array (Hyp prop)) (i : Nat)
      (acc : NameMap Nat × Array (TSyntax ``irisHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``irisHyp)) := do
    -- empty context: the current position is `emp`, nothing to display
    let some h := hs[i]? | return acc
    match i with
    | 0 =>
      -- the position *is* `h₀`; there is no `∗` above it
      delabHyp h acc
    | n + 1 => do
      let acc ← withNaryArg 3 <| delabHyp h acc      -- rhs of the outermost `∗`
      withNaryArg 2 <| delabHypotheses hs n acc      -- lhs = fold of `hs[0…n]`

  /-- Delaborate a single hypothesis. The current `SubExpr` position must be the
  leaf `□?p (IrisHyp ty)`. -/
  delabHyp {u : Level} {prop : Q(Type u)} (h : Hyp prop)
      (acc : NameMap Nat × Array (TSyntax ``irisHyp)) :
      DelabM (NameMap Nat × Array (TSyntax ``irisHyp)) := do
    let (map, acc) := acc
    -- For printing the name of the hypothesis, `✝` if shadowed
    let (idx, name') := match map.find? h.name with
      | some idx =>
        (idx + 1, h.name.appendAfter <|
          if idx == 0 then "✝" else "✝" ++ idx.toSuperscriptString)
      | none => (0, h.name)
    let pos ← getPos
    -- Delaboration of the proposition itself
    let tyStx ← withHypType h.persistent? delabIProp
    let nameStx : Ident :=
      ⟨(mkIdent name').raw.setInfo (.synthetic ⟨pos.asNat⟩ ⟨pos.asNat⟩)⟩
    withLCtx ((← getLCtx).mkLocalDecl ⟨h.ivar.name⟩ name' q(HypMarker $(h.ty)))
        (← getLocalInstances) do
      addTermInfo pos nameStx (.fvar ⟨h.ivar.name⟩) (isBinder := true)
    -- Determine the prefix based on whether it is in the spatial or intuitionistic context
    let stx ← if h.persistent? then
      `(irisHyp| □$nameStx : $tyStx)
    else
      `(irisHyp| ∗$nameStx : $tyStx)
    pure (map.insert h.name idx, acc.push stx)

@[delab app.Iris.ProofMode.HypMarker]
def delabHypMarker : Delab := do unpackIprop (← withAppArg delab)
