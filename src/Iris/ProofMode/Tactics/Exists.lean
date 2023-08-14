/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI

theorem exists_intro' [BI PROP] {Φ : α → PROP} {P Q : PROP} [inst : FromExists Q Φ]
    (a : α) (h : P ⊢ Φ a) : P ⊢ Q :=
  h.trans <| (exists_intro a).trans inst.1

elab "iexists" x:term : tactic => do
  -- resolve existential quantifier with the given argument

  let (mvar, { prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  let α ← mkFreshExprMVarQ q(Type)
  let Φ ← mkFreshExprMVarQ q($α → $prop)
  let _ ← synthInstanceQ q(FromExists $goal $Φ)
  let x ← elabTermEnsuringTypeQ (u := .succ .zero) x α
  let m : Quoted q($e ⊢ $Φ $x) ← mkFreshExprSyntheticOpaqueMVar <|
    IrisGoal.toExpr { prop, bi, hyps, goal := Expr.headBeta q($Φ $x) }

  mvar.assign q(exists_intro' (Q := $goal) $x $m)
  replaceMainGoal [m.mvarId!]
