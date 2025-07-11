/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {P P' Q O A1 : PROP} {p : Bool}
    (h1 : P ⊣⊢ P' ∗ □?p O) (h2 : P' ⊢ A1) [h3 : IntoWand' p false O A1 A2]
    [h4 : FromAssumption false A2 Q] : P ⊢ Q :=
  h1.mp.trans (wand_elim (h2.trans (wand_intro ((sep_mono_r h3.1).trans (wand_elim_r.trans h4.1)))))

-- todo: hypothesis management
variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iApplyCore
    {P P'} (p : Q(Bool)) (hyps : Hyps bi P) (hyps' : Hyps bi P') (Q hyp : Q($prop))
    (pf : Q($P ⊣⊢ $P' ∗ □?$p $hyp)) (ls : List (TSyntax `Lean.Parser.Term.bracketedBinder))
    (k : ∀ {P}, Hyps bi P → (Q : Q($prop)) → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  let intoWand' ← try? do
    synthInstanceQ q(IntoWand' $p false $hyp $A1 $A2)

  if let some _ := intoWand' then
    let A1' ← mkFreshExprMVarQ q($prop)
    let A2' ← mkFreshExprMVarQ q($prop)

    let intoWand' ← try? do
      synthInstanceQ q(IntoWand' $p false $A2 $A1' $A2')

    if let some _ := intoWand' then
      if let some bind := ls.head? then
        let binderIdents ← match bind with
          | `(bracketedBinder| ($ids*)) => pure ids
          | _ => throwError "Unsupported binder format: {bind}"

        let hypsToRemove ← (binderIdents.toList.map (·.raw)).mapM fun id => do
          match id with
          | `(ident| $name:ident) => hyps'.findWithInfo name
          | `(Lean.Parser.Term.hole| _) => throwError "holes not supported in hypothesis binders"
          | _ => throwError "unsupported identifier format: {id}"

        -- todo: remove hypotheses

        let _ ← k (.mkEmp bi) A1 -- todo: use removed hypotheses
      else
        let _ ← k (.mkEmp bi) A1
      return ← iApplyCore p hyps hyps' Q A2 pf ls.tail k
    else
      let m ← k hyps' A1
      let _ ← synthInstanceQ q(FromAssumption false $A2 $Q)
      return q(apply $pf $m)
  else
    let _ ← synthInstanceQ q(FromAssumption $p $hyp $Q)
    let _ ← synthInstanceQ q(TCOr (Affine $P') (Absorbing $Q))

    return q(assumption $pf)

-- todo: hyp is a lean lemma (later)
elab "iapply" colGt hyp:ident ls:bracketedBinder* : tactic => do
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { u, prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let uniq ← hyps.findWithInfo hyp
    let ⟨_, hyps', out, _, p, _, pf⟩ := hyps.remove true uniq

    let goals ← IO.mkRef #[]
    let pf ← iApplyCore bi p hyps hyps' goal out pf ls.toList fun {P} hyps goal => do
      let m : Q($P ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { prop, bi, hyps, goal, .. }
      goals.modify (·.push m.mvarId!)
      pure m

    mvar.assign pf
    replaceMainGoal (← goals.get).toList
