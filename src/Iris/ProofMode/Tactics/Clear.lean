/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Zongyuan Liu
-/
import Iris.ProofMode.Tactics.Remove
import Iris.ProofMode.Patterns.SelectPattern
import Iris.ProofMode.Tactics.ElaborateSelPat

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem clear_spatial [BI PROP] {P P' A Q : PROP} [TCOr (Affine A) (Absorbing Q)]
    (h_rem : P ⊣⊢ P' ∗ A) (h : P' ⊢ Q) : P ⊢ Q :=
  h_rem.1.trans <| (sep_mono_l h).trans sep_elim_l

theorem clear_intuitionistic [BI PROP] {P P' A Q : PROP}
    (h_rem : P ⊣⊢ P' ∗ □ A) (h : P' ⊢ Q) : P ⊢ Q := clear_spatial h_rem h

def clearCore {prop : Q(Type u)} (_bi : Q(BI $prop)) (p: Bool) (e e' out goal : Q($prop))
    (pf : Q($e ⊣⊢ $e' ∗ $out)) : MetaM Q(($e' ⊢ $goal) → $e ⊢ $goal) := do
  if p then
    have out' : Q($prop) := out.appArg!
    have : $out =Q iprop(□ $out') := ⟨⟩
    pure q(clear_intuitionistic (Q := $goal) $pf)
  else
    let _ ← synthInstanceQ q(TCOr (Affine $out) (Absorbing $goal))
    pure q(clear_spatial $pf)

structure ClearState {prop : Q(Type u)} {bi : Q(BI $prop)} where
    (mvar': MVarId) (e: Q($prop)) (hyps: Hyps bi e)

def clearCoreGo {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} (goal : Q($prop))
    (cs : @ClearState _ prop bi) (epats : List iElaboratedSelectPat): MetaM (@ClearState _ prop bi) := do
    epats.foldlM processPat cs
where processPat: (ClearState) → iElaboratedSelectPat → MetaM (ClearState)
  | { mvar', e, hyps}, epat => do
    match epat with
    | iElaboratedSelectPat.pure => do
        let newmvar ← mvar'.cleanup
        pure ({ mvar':= newmvar, e, hyps})
    | iElaboratedSelectPat.ident p uniq => do
      mvar'.withContext do
        let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove true uniq

        let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
          IrisGoal.toExpr { u, prop, bi, hyps := hyps', goal, .. }

        mvar'.assign ((← (clearCore bi p e e' out goal pf)).app m)
        pure ({ mvar':= m.mvarId!, e:= e', hyps := hyps'})

elab "iclear" selpat:iselectPat : tactic => do
  -- parse syntax
  let pats ← liftMacroM <| iSelectPat.parse selpat

  let mvar ← getMainGoal
  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u := u, prop := prop , bi, e := e, hyps, goal} := parseIrisGoal? g | throwError "not in proof mode"
    let epats ← elaborateSelPatsCore bi hyps pats

    -- Process all elaborated patterns
    let { mvar' := finalMvar, e:= _, hyps := _ } ← @clearCoreGo u prop bi goal { mvar':= mvar , e, hyps} epats
    replaceMainGoal [finalMvar]
