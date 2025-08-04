/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Split

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem apply [BI PROP] {R P P' P1 P2 : PROP}
    (h1 : P ⊢ P' ∗ R) (h2 : P' ⊢ P1) [h3 : IntoWand false false R P1 P2] : P ⊢ P2 :=
  h1.trans <| (sep_mono_l h2).trans <| wand_elim' h3.1

theorem temp [BI PROP] {e e' out el er : PROP} (pf : e ⊢ e' ∗ out) (h : e' ⊢ el ∗ er) :
    e ⊢ er ∗ □?false (el ∗ out) :=
  pf.trans <| (sep_mono_l h).trans <| (sep_mono_l sep_symm).trans <| sep_assoc.mp.trans .rfl

theorem temp' [BI PROP] {el out A1 A2 : PROP} (h : out ⊢ A1 -∗ A2) : el ∗ out ⊢ A1 -∗ (el ∗ A2) :=
  (sep_mono_r h).trans <| wand_intro' <| sep_symm.trans <| sep_assoc.mp.trans <| sep_mono .rfl wand_elim_l

-- todo: deal with intuitionistic modality properly
variable {prop : Q(Type u)} {bi : Q(BI $prop)} in
partial def iApplyCore
    (goal el er : Q($prop)) (hypsl : Hyps bi el) (spats : List SpecPat)
    (k : ∀ {e}, Hyps bi e → (goal : Q($prop)) → MetaM Q($e ⊢ $goal)) :
    MetaM (Q($el ∗ $er ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)

  if let some _ ← try? (synthInstanceQ q(IntoWand false false $er $A1 $goal)) then
    let m ← k hypsl A1
    return q(apply .rfl $m)
  if let some inst ← try? (synthInstanceQ q(IntoWand false false $er $A1 $A2)) then
    let splitPat := fun name _ => match spats.head? with
      | some <| .idents bIdents => bIdents.any <| binderIdentHasName name
      | none => false

    let ⟨el', er', hypsl', hypsr', h'⟩ := Hyps.split bi splitPat hypsl
    let m ← k hypsr' A1

    let inst' : Q(IntoWand false false iprop(□?false ($el' ∗ $er)) $A1 iprop($el' ∗ $A2))
      := q({into_wand := temp' ($inst).into_wand})

    let pf : Q($el ∗ $er ⊢ $el' ∗ $A2) := q(apply (temp .rfl ($h').mp) $m)
    let res ← iApplyCore goal el' A2 hypsl' spats.tail k
    return q(($pf).trans $res)
  else
    let _ ← synthInstanceQ q(FromAssumption false $er $goal)
    let _ ← synthInstanceQ q(TCOr (Affine $el) (Absorbing $goal))
    return q(assumption (p := false) .rfl)

-- todo: case when hyp is a lean lemma (later)
elab "iapply" colGt term:pmTerm : tactic => do
  let term ← liftMacroM <| PMTerm.parse term
  let mvar ← getMainGoal

  mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some { hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"
    let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove true <| ← hyps.findWithInfo term.ident

    let goals ← IO.mkRef #[]
    let res ← iApplyCore goal e' out hyps' term.spats <| goalTracker goals
    mvar.assign <| q(($pf).mp.trans $res)
    replaceMainGoal (← goals.get).toList
