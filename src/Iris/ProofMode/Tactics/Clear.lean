/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem clear_spatial [BI PROP] {P P' A Q : PROP} [TCOr (Affine A) (Absorbing Q)]
    (h_rem : P ⊣⊢ P' ∗ A) (h : P' ⊢ Q) : P ⊢ Q :=
  h_rem.1.trans <| (sep_mono_l h).trans sep_elim_l

theorem clear_intuitionistic [BI PROP] {P P' A Q : PROP}
    (h_rem : P ⊣⊢ P' ∗ □ A) (h : P' ⊢ Q) : P ⊢ Q := clear_spatial h_rem h

def clearCore {prop : Q(Type)} (_bi : Q(BI $prop)) (e e' out goal : Q($prop))
    (pf : Q($e ⊣⊢ $e' ∗ $out)) : MetaM Q(($e' ⊢ $goal) → $e ⊢ $goal) := do
  if out.isAppOfArity ``intuitionistically 3 then
    have out' : Q($prop) := out.appArg!
    have : $out =Q iprop(□ $out') := ⟨⟩
    pure q(clear_intuitionistic (Q := $goal) $pf)
  else
    let _ ← synthInstanceQ q(TCOr (Affine $out) (Absorbing $goal))
    pure q(clear_spatial $pf)

elab "iclear" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  let uniq ← hyps.findWithInfo hyp
  let ⟨e', hyps', out, _, _, _, pf⟩ := hyps.remove true uniq

  let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps := hyps', goal }

  mvar.assign ((← clearCore bi e e' out goal pf).app m)
  replaceMainGoal [m.mvarId!]
