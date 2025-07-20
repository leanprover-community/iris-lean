/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
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

theorem temp [BI PROP] {e' el er e out : PROP} (h : e' ⊣⊢ el ∗ er) (pf : e ⊣⊢ e' ∗ out) : e ⊣⊢ el ∗ (er ∗ out) :=
  pf.trans <| (sep_congr_l h).trans sep_assoc

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def iApplyCore
    {e} (hyps : Hyps bi e) (goal : Q($prop)) (remHyp : RemoveHyp bi e) (spats : List SpecPat)
    (k : ∀ {e}, Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($e ⊢ $goal)) := do
  let ⟨e', hyps', out, out', p, eq, pf⟩ := remHyp

  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  if let some _ ← try? (synthInstanceQ q(IntoWand' $p false $out' $A1 $A2)) then
    let splitPat := fun name _ => match spats.head? with
      | some <| .idents bIdents => bIdents.any <| binderIdentHasName name
      | none => false

    let splitHyp := Hyps.split bi splitPat hyps'
    let ⟨el, er, hypsl, hypsr, h⟩ := splitHyp

    let m ← k hypsr A1

    let newOut := q(sep $er $out)

    let p' ← mkFreshExprMVarQ q(Bool)
    let newOut' ← mkFreshExprMVarQ q($prop)

    let _ ← synthInstanceQ q(FromAssumption $p' $newOut' $newOut)
    let eq' := (← assertDefEqQ q($newOut) q(intuitionisticallyIf $p' $newOut')).down

    let pf' := q(temp $h $pf)

    let remHyps := ⟨el, hypsl, newOut, newOut', p', eq', pf'⟩

    return ← iApplyCore hyps goal remHyps spats.tail k
  else
    -- iexact case
    let _ ← synthInstanceQ q(FromAssumption $p $out' $goal)
    let _ ← synthInstanceQ q(TCOr (Affine $e') (Absorbing $goal))
    return q(assumption $pf)

-- todo: case when hyp is a lean lemma (later)
elab "iapply" colGt term:pmTerm : tactic => do
  let term ← liftMacroM <| PMTerm.parse term
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    let remHyp := hyps.remove true <| ← hyps.findWithInfo term.ident

    let goals ← IO.mkRef #[]
    mvar.assign <| ← iApplyCore hyps goal remHyp term.spats <| goalTracker goals
    replaceMainGoal (← goals.get).toList
