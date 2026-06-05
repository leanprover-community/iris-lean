/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Leal
-/
module
public import Iris.ProofMode.Tactics.Intro
public import Iris.ProofMode.Tactics.Revert

namespace Iris.ProofMode

open Lean Meta Elab.Tactic Qq

public meta section

abbrev ProofModeContinuationIntro :=
  ∀ {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (_hyps : Hyps bi e) (goal: Q($prop)),
    ProofModeM Q($e ⊢ $goal)

abbrev ProofModeContinuationRevert :=
  ∀ {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (_hyps : Hyps bi e) (goal : Q($prop)), ProofModeContinuationIntro →
    ProofModeM Q($e ⊢ $goal)

def iRevertIntro
  {prop: Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)} (hyps : Hyps bi e) (goal: Q($prop))
  (hs : List SelTarget)
  (k : ∀ {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (_hyps : Hyps bi e) (goal: Q($prop)), ProofModeContinuationRevert →
    ProofModeM Q($e ⊢ $goal))
   : ProofModeM Q($e ⊢ $goal) := do
  let names : List (Syntax × IntroPat) ← hs.mapM fun
    | {kind := .pure id, ..} => do
      let name ← Lean.mkIdent <$> id.getUserName
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| .pure ident)
    | {kind := .ipm ivar, ..} =>  do
      let name ← Lean.mkIdent <$> (hyps.getUserName? ivar).getM
      let ident ← `(binderIdent| $name:ident)
      return (name, .intro <| (if ivar.persistent? then .intuitionistic else id) <| .one ident)
  trace[irevertintro] s!"Calling `iRevertIntro` with {names.map (·.1)} on context {←ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
  iRevertCore hs hyps goal fun hyps goal => do
    k hyps goal fun hyps goal k' => do
      iIntroCore hyps goal names k'

initialize registerTraceClass `irevertintro
