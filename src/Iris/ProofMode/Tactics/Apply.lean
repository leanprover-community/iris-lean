/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Patterns.SpecPattern
import Iris.ProofMode.Tactics.Split

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

-- todo: simplify in line with tac_apply
theorem apply [BI PROP] {P P' Q O A1 A2 : PROP} {p : Bool}
    (h1 : P ⊢ P' ∗ □?p O) (h2 : P' ⊢ A1) [h3 : IntoWand' p false O A1 A2]
    [h4 : FromAssumption false A2 Q] : P ⊢ Q :=
  h1.trans <| (sep_mono_l h2).trans <| (sep_mono_r h3.1).trans <| wand_elim_r.trans h4.1

-- todo: complex spec patterns
variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iApplyCore
    {P P'} (p : Q(Bool)) (hyps : Hyps bi P) (hyps' : Hyps bi P') (Q hyp : Q($prop))
    (pf : Q($P ⊣⊢ $P' ∗ □?$p $hyp)) (pat : List SpecPat)
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

    if let some _ := intoWand' then
      -- todo: use Hyps.split
      let _ ← k (.mkEmp bi) A1
      return ← iApplyCore p hyps hyps' Q A2 pf [] k
    else
      let m ← k hyps' A1
      let _ ← synthInstanceQ q(FromAssumption false $A2 $Q)
      return q(apply ($pf).mp $m)
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
    let some { u, prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

    let uniq ← hyps.findWithInfo hyp
    let ⟨_, hyps', out, _, p, _, pf⟩ := hyps.remove true uniq

    let goals ← IO.mkRef #[]
    let pf ← iApplyCore bi p hyps hyps' goal out pf pats fun {P} hyps goal => do
      let m : Q($P ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { prop, bi, hyps, goal, .. }
      goals.modify (·.push m.mvarId!)
      pure m

    mvar.assign pf
    replaceMainGoal (← goals.get).toList
