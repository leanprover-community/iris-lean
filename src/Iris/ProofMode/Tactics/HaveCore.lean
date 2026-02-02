/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Specialize

/- This file contains the `iHave` function for asserting a ProofModeTerm.
   It is separate from the implementation of `ihave` in `Have.lean` since
   the `ihave` tactic in (`Have.lean`) depends on `Cases.lean`, which in turn
   depends on `iHave` in this file.
-/

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem have_asEmpValid [BI PROP] {φ} {P Q : PROP}
    [h1 : AsEmpValid .into φ P] (h : φ) : Q ⊢ Q ∗ □ P :=
  sep_emp.2.trans (sep_mono_r $ intuitionistically_emp.2.trans (intuitionistically_mono (asEmpValid_1 _ h)))

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

    let ⟨newMVars, _, _⟩ ← forallMetaTelescope ty
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

    return ⟨_, hyps, q(true), hyp, q(have_asEmpValid $val)⟩

def iHave {e} (hyps : @Hyps u prop bi e)
  (pmt : PMTerm) (keep : Bool) (try_dup_context : Bool := false) (mayPostpone := false) :
  ProofModeM ((e' : _) × Hyps bi e' × (p : Q(Bool)) × (out : Q($prop)) × Q($e ⊢ $e' ∗ □?$p $out)) := do
  -- assert `term` as hypothesis `A`
  let ⟨_, hyps', p, A, pf⟩ ← iHaveCore hyps pmt.term keep mayPostpone
  -- specialize `A` with `spats`
  let ⟨_, hyps'', pb, B, pf'⟩ ← iSpecializeCore hyps' p A pmt.spats (try_dup_context := try_dup_context)
  return ⟨_, hyps'', pb, B, q($(pf).trans $pf')⟩
