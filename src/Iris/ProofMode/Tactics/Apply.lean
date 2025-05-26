/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

-- iApply
-- - How to get the correct top-level syntax
-- - Do we already have an analogue of tac_assumption?
-- - What is our analouge of tac_apply?

-- Like tac_apply
theorem apply [BI PROP] (R P P1 Q D : PROP) [HW : InferIntoWand false false R P1 Q]
    (Hc : P ⊣⊢ D ∗ R) (Hap : D ⊢ P1) : P ⊢ Q :=
  Hc.mp.trans <| (sep_mono_l Hap).trans <| sep_symm.trans <| wand_elim (HW.into_wand)

-- Right now, this tactic does not try to do iExact

elab "iapply" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { u, prop, bi, e := _, hyps, goal} := parseIrisGoal? g | throwError "not in proof mode"
  let uniq ← hyps.findWithInfo hyp
  let ⟨context', hyps', thm, _, _, _, Hcontext'⟩ := hyps.remove true uniq
  let prec ← mkFreshExprMVarQ prop
  let tc_inst ← synthInstanceQ q(InferIntoWand false false $thm $prec $goal)
  let m : Q($context' ⊢ $prec) := ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { u, prop, bi, e := context', hyps := hyps', goal := q($prec) }
  mvar.assign q(apply (HW := $tc_inst) (Hc := $Hcontext') (Hap := $m))
  replaceMainGoal [m.mvarId!]
