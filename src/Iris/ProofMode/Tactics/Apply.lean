/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Split

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {R P' P1 P2 : PROP}
    (h : P' ⊢ P1) [inst : IntoWand false false R P1 P2] : P' ∗ R ⊢ P2 :=
  (sep_mono h inst.1).trans wand_elim_r

theorem rec_apply [BI PROP] {el er el' er' A1 A2 : PROP}
    (h1 : el ⊣⊢ el' ∗ er') (h2 : er' ⊢ A1) [IntoWand false false er A1 A2] : el ∗ er ⊢ el' ∗ A2 :=
  (sep_congr h1 .rfl).mp.trans <| sep_assoc.mp.trans <| sep_mono_r <| apply h2

variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def iApplyCore
    (goal el er : Q($prop)) (hypsl : Hyps bi el) (spats : List SpecPat)
    (addGoal : ∀ {e}, Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($el ∗ $er ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  if let some _ ← try? (synthInstanceQ q(IntoWand false false $er $A1 $goal)) then
    let m ← addGoal hypsl A1
    return q(apply $m)
  if let some _ ← try? (synthInstanceQ q(IntoWand false false $er $A1 $A2)) then
    let splitPat := fun name _ => match spats.head? with
      | some <| .idents bIdents => bIdents.any <| binderIdentHasName name
      | none => false

    let ⟨el', er', hypsl', hypsr', h'⟩ := Hyps.split bi splitPat hypsl
    let m ← addGoal hypsr' A1

    let pf : Q($el ∗ $er ⊢ $el' ∗ $A2) := q(rec_apply $h' $m)
    let res : Q($el' ∗ $A2 ⊢ $goal) ← iApplyCore goal el' A2 hypsl' spats.tail addGoal

    return q(.trans $pf $res)
  else
    let _ ← synthInstanceQ q(FromAssumption false $er $goal)
    let _ ← synthInstanceQ q(TCOr (Affine $el) (Absorbing $goal))
    return q(assumption (p := false) .rfl)

-- todo: case when hyp is a lean lemma
elab "iapply" colGt term:pmTerm : tactic => do
  let term ← liftMacroM <| PMTerm.parse term
  let (mvar, { hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    if let some uniq ← try? do pure (← hyps.findWithInfo term.ident) then
      let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove false uniq

      let goals ← IO.mkRef #[]
      let res ← iApplyCore goal e' out hyps' term.spats <| goalTracker goals
      mvar.assign <| q(($pf).mp.trans $res)
      replaceMainGoal (← goals.get).toList
