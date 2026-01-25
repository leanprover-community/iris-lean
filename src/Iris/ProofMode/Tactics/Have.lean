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

private theorem have_asEmpValid [BI PROP] {φ} {P Q : PROP}
    [h1 : AsEmpValid .into φ P] (h : φ) : Q ⊢ Q ∗ P :=
  sep_emp.2.trans (sep_mono_r (asEmpValid_1 _ h))

/--
Assert a hypothesis from either a hypothesis name or a Lean proof term `tm`.

## Parameters
- `hyps`: Current proof mode hypothesis context
- `keep`: If `true` and `tm` is an Iris hypothesis, keep it in the context;
  if `false`, remove it
- `mayPostpone`: If `true`, allow postponing elaboration of metavariables in `tm`

## Returns
A tuple containing:
- `e'`: Proposition for `hyps'`
- `hyps'`: Updated hypothesis context
- `p`: Persistence flag for the output (always `false` for Lean terms, inherited for Iris hypotheses)
- `out`: Asserted proposition
- `pf`: Proof of `hyps ⊢ hyps' ∗ □?p out`
-/
private def iHaveCore {e} (hyps : @Hyps u prop bi e)
  (tm : Term) (keep : Bool) (mayPostpone : Bool) :
  ProofModeM ((e' : _) × Hyps bi e' × (p : Q(Bool)) × (out : Q($prop)) × Q($e ⊢ $e' ∗ □?$p $out)) := do
  if let some uniq ← try? <| hyps.findWithInfo ⟨tm⟩ then
    -- assertion from the Iris context
    let ⟨_, hyps, _, out', p, _, pf⟩ := hyps.remove (!keep) uniq
    return ⟨_, hyps, p, out', q($pf.1)⟩
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
    let some _ ← ProofModeM.trySynthInstanceQ q(AsEmpValid .into $ty $hyp)
      | throwError m!"{ty} is not an entailment"

    return ⟨_, hyps, q(false), hyp, q(have_asEmpValid $val)⟩

def iHave {e} (hyps : @Hyps u prop bi e)
  (pmt : PMTerm) (keep : Bool) (mayPostpone := false) :
  ProofModeM ((e' : _) × Hyps bi e' × (p : Q(Bool)) × (out : Q($prop)) × Q($e ⊢ $e' ∗ □?$p $out)) := do
  -- assert `term` as hypothesis `A`
  let ⟨_, hyps', p, A, pf⟩ ← iHaveCore hyps pmt.term keep mayPostpone
  -- specialize `A` with `spats`
  let ⟨_, hyps'', pb, B, pf'⟩ ← iSpecializeCore hyps' p A pmt.spats
  return ⟨_, hyps'', pb, B, q($(pf).trans $pf')⟩

elab "ihave" colGt name:binderIdent " := " pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
  let ⟨_, hyps', p, out, pf⟩ ← iHave hyps pmt true
  let ⟨_, hyps''⟩ ← Hyps.addWithInfo bi name p out hyps'
  let pf' ← addBIGoal hyps'' goal
  mvar.assign q(($pf).trans $pf')

private theorem ihave_assert [BI PROP] {A B C : PROP}
  (h1 : A ∗ □ (B -∗ B) ⊢ C) : A ⊢ C :=
    (and_intro .rfl (persistently_emp_intro.trans (persistently_mono $ wand_intro emp_sep.1))).trans
      $ persistently_and_intuitionistically_sep_r.1.trans h1

elab "ihave" colGt name:binderIdent " : " P:term "$$" spat:specPat : tactic => do
  let spat ← liftMacroM <| SpecPat.parse spat
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do
  let P ← elabTermEnsuringTypeQ (← `(iprop($P))) prop
  --  establish `P` with `spat`, get `out := P`
  let ⟨_, hyps', p, out, pf⟩ ← iSpecializeCore hyps q(true) q(iprop($P -∗ $P)) [spat]
  let ⟨_, hyps''⟩ ← Hyps.addWithInfo bi name p out hyps'
  let pf' ← addBIGoal hyps'' goal
  mvar.assign q(ihave_assert (($pf).trans $pf'))
