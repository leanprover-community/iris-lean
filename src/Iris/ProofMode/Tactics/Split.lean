/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI

private theorem from_and_intro [BI PROP] {P Q A1 A2 : PROP} [inst : FromAnd Q A1 A2]
    (h1 : P ⊢ A1) (h2 : P ⊢ A2) : P ⊢ Q :=
  (and_intro h1 h2).trans inst.1

elab "isplit" : tactic => do
  ProofModeM.runTactic λ mvar { prop, hyps, goal, .. } => do

  let A1 ← mkFreshExprMVarQ prop
  let A2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromAnd $goal $A1 $A2) | throwError "isplit: {goal} is not a conjunction"
  let m1 ← addBIGoal hyps A1
  let m2 ← addBIGoal hyps A2
  mvar.assign q(from_and_intro (Q := $goal) $m1 $m2)

private theorem sep_split [BI PROP] {P P1 P2 Q Q1 Q2 : PROP} [inst : FromSep Q Q1 Q2]
    (h : P ⊣⊢ P1 ∗ P2) (h1 : P1 ⊢ Q1) (h2 : P2 ⊢ Q2) : P ⊢ Q :=
  h.1.trans <| (sep_mono h1 h2).trans inst.1

inductive splitSide where
| splitLeft | splitRight

def isplitCore (side : splitSide) (names : Array (TSyntax `ident)) : TacticM Unit := do
  let splitRight := match side with
    | .splitLeft => false
    | .splitRight => true

  -- extract environment
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do

  let mut uniqs : NameSet := {}
  for name in names do
    uniqs := uniqs.insert (← hyps.findWithInfo name)

  let Q1 ← mkFreshExprMVarQ prop
  let Q2 ← mkFreshExprMVarQ prop
  let some _ ← ProofModeM.trySynthInstanceQ q(FromSep $goal $Q1 $Q2) |
    throwError "isplit: {goal} is not a separating conjunction"

  -- split conjunction
  let ⟨_, _, lhs, rhs, pf⟩ := hyps.split bi (fun _ uniq => uniqs.contains uniq == splitRight)

  let m1 ← addBIGoal lhs Q1
  let m2 ← addBIGoal rhs Q2
  mvar.assign q(sep_split (Q := $goal) $pf $m1 $m2)

elab "isplitl" "[" names:(colGt ident)* "]": tactic => do
  isplitCore .splitLeft names

elab "isplitr" "[" names:(colGt ident)* "]": tactic => do
  isplitCore .splitRight names

macro "isplitl" : tactic => `(tactic| isplitr [])
macro "isplitr" : tactic => `(tactic| isplitl [])
