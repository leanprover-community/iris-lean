/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.SpecPattern
import Iris.ProofMode.Tactics.Split

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {R P P' P1 P2 : PROP} {p : Bool}
    (h1 : P ⊣⊢ P' ∗ □?p R) (h2 : P' ⊢ P1) [h3 : IntoWand' p false R P1 P2] : P ⊢ P2 :=
  h1.mp.trans <| (sep_mono_l h2).trans <| wand_elim' h3.1

def binderIdentHasName (name : Name) (id : TSyntax ``binderIdent) : Bool :=
  match id with
  | `(binderIdent| $name':ident) => name'.getId == name
  | _ => false

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
def goalTracker {P} (goals : IO.Ref (Array MVarId)) (hyps : Hyps bi P) (goal : Q($prop)) : MetaM Q($P ⊢ $goal) := do
  let m : Q($P ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal, .. }
  goals.modify (·.push m.mvarId!)
  pure m

-- todo: complex spec patterns
variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def iApplyCore
    {P'} (p : Q(Bool)) (P : Q($prop)) (hyps : Hyps bi P') (Q hyp : Q($prop))
    (pf : Q($P ⊣⊢ $P' ∗ □?$p $hyp)) (pats : List SpecPat)
    (k : ∀ {P}, Hyps bi P → (Q : Q($prop)) → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  let intoWand ← try? do
    synthInstanceQ q(IntoWand' $p false $hyp $A1 $A2)

  if let some _ := intoWand then
    -- todo: this is unnecessarily hacky
    let A1' ← mkFreshExprMVarQ q($prop)
    let A2' ← mkFreshExprMVarQ q($prop)
    let intoWand' ← try? do
      synthInstanceQ q(IntoWand' $p false $A2 $A1' $A2')

    -- todo: could these cases be combined?
    if let some _ := intoWand' then
      let splitPat := fun name _ => match pats.head? with
        | some <| .idents ls => ls.any <| binderIdentHasName name | _ => false
      let ⟨el, er, hypsl, hypsr, h⟩ := Hyps.split bi splitPat hyps
      let _ ← k hypsr A1
      --let pf' : Q($P ⊣⊢ $el ∗ □?$p $A2) := sorry
      return ← iApplyCore p P hypsl Q A2 pf pats.tail k -- todo: update pf with h
    else
      let m ← k hyps A1
      let _ ← synthInstanceQ q(IntoWand' $p false $hyp $A1 $Q)
      return q(apply $pf $m)
  else
    let _ ← synthInstanceQ q(FromAssumption $p $hyp $Q)
    let _ ← synthInstanceQ q(TCOr (Affine $P') (Absorbing $Q))

    return q(assumption $pf)

-- todo: case when hyp is a lean lemma (later)
-- todo: macro for when no pat is supplied
elab "iapply" colGt hyp:ident pats:specPat,* : tactic => do
  let pats ← pats.elemsAndSeps.toList.mapM fun pat => liftMacroM <| SpecPat.parse pat
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { e, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    -- todo: could this be moved to iApplyCore?
    let uniq ← hyps.findWithInfo hyp
    let ⟨_, hyps', out, _, p, _, pf⟩ := hyps.remove true uniq

    let goals ← IO.mkRef #[]
    mvar.assign <| ← iApplyCore p e hyps' goal out pf pats <| goalTracker goals
    replaceMainGoal (← goals.get).toList
