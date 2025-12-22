/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Specialize

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem have_asEmpValid [BI PROP] {φ} {P Q : PROP}
    [h1 : AsEmpValid .into φ P] (h : φ) : Q ⊢ Q ∗ P :=
  sep_emp.2.trans (sep_mono_r (asEmpValid_1 _ h))

private def iHaveCore {e} (hyps : @Hyps u prop bi e)
  (tm : Term) (name : TSyntax ``binderIdent) (keep : Bool) (mayPostpone : Bool) : ProofModeM (Name × (e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  if let some uniq ← try? <| hyps.findWithInfo ⟨tm⟩ then
    -- assertion from the Iris context
    let ⟨_, hyps, _, out', p, _, pf⟩ := hyps.remove (!keep) uniq
    let ⟨uniq', hyps⟩ ← Hyps.addWithInfo bi name p out' hyps
    return ⟨uniq', _, hyps, q($pf.1)⟩
  else
    -- lean hypothesis
    let val ← instantiateMVars <| ← elabTerm tm none mayPostpone
    let ty ← instantiateMVars <| ← inferType val

    let ⟨newMVars, _, _⟩ ← forallMetaTelescopeReducing ty
    let val := mkAppN val newMVars
    -- TOOD: should we call postprocessAppMVars?
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed val
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    for mvar in newMVarIds ++ otherMVarIds do
      addMVarGoal mvar

    -- TODO: can we do this without re typechecking?
    let ⟨0, ty, val⟩ ← inferTypeQ val | throwError m!"{val} is not a Prop"

    let hyp ← mkFreshExprMVarQ q($prop)
    let some _ ← ProofModeM.trySynthInstanceQ q(AsEmpValid .into $ty $hyp) | throwError m!"{ty} is not an entailment"

    let ⟨uniq', hyps⟩ ← Hyps.addWithInfo bi name q(false) hyp hyps
    return ⟨uniq', _, hyps, q(have_asEmpValid $val)⟩

def iHave{e} (hyps : @Hyps u prop bi e)
  (pmt : PMTerm) (name : TSyntax ``binderIdent) (keep : Bool) (mayPostpone := false) : ProofModeM (Name × (e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let ⟨uniq, _, hyps', pf⟩ ← iHaveCore hyps pmt.term name keep mayPostpone
  let ⟨_, hyps'', pf'⟩ ← iSpecializeCore hyps' uniq pmt.spats
  return ⟨uniq, _, hyps'', q($(pf).trans $pf')⟩

elab "ihave" colGt name:binderIdent " := " pmt:pmTerm  : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  let ⟨_, _, hyps, pf⟩ ← iHave hyps pmt name true
  let pf' ← addBIGoal hyps goal
  mvar.assign q(($pf).trans $pf')
