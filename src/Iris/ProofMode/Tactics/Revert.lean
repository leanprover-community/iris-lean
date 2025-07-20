/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem wand_revert [BI PROP] {P Q A1 A2 : PROP}
    (h1 : P ⊣⊢ A1 ∗ A2) (h2 : A1 ⊢ A2 -∗ Q) : P ⊢ Q :=
  h1.mp.trans (wand_elim h2)

theorem forall_revert [BI PROP] {P : PROP} {Ψ : α → PROP}
    (h : P ⊢ ∀ x, Ψ x) : ∀ x, P ⊢ Ψ x :=
  λ x => h.trans (forall_elim x)

theorem pure_revert [BI PROP] {P Q : PROP} {φ : Prop}
    (h : P ⊢ ⌜φ⌝ -∗ Q) : φ → P ⊢ Q :=
  λ hp => (sep_emp.mpr.trans (sep_mono .rfl (pure_intro hp))).trans (wand_elim h)

elab "irevert" colGt hyp:ident : tactic => do
  let (mvar, { u, prop, bi, e, hyps, goal, .. }) ← istart (← getMainGoal)

  mvar.withContext do
    let uniq? ← try? do pure (← hyps.findWithInfo hyp)
    if let (some uniq) := uniq? then
      let ⟨e', hyps', out, _, _, _, h⟩ := hyps.remove true uniq
      let m : Q($e' ⊢ $out -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
        IrisGoal.toExpr { hyps := hyps', goal := q(wand $out $goal), .. }

      let pf : Q($e ⊢ $goal) := q(wand_revert $h $m)

      mvar.assign pf
      replaceMainGoal [m.mvarId!]
    else
      let f ← getFVarId hyp
      let (some ldecl) := ((← getLCtx).find? f) | throwError "unknown identifier"

      let bibase : Q(BIBase $prop) := q(@BI.toBIBase $prop $bi)

      let v : Level ← Meta.getLevel ldecl.type
      have α : Q(Sort v) := ldecl.type

      let (_, mvarId) ← mvar.revert #[f]
      mvarId.withContext do
        if ← Meta.isProp α then
          have φ : Q(Prop) := α
          let p : Q($prop) := q(@BI.pure $prop $bibase $φ)

          let m : Q($e ⊢ $p -∗ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
            IrisGoal.toExpr { u, prop, bi, hyps, goal := q(wand $p $goal), .. }

          let pf : Q($φ → ($e ⊢ $goal)) := q(pure_revert $m)

          mvarId.assign pf
          replaceMainGoal [m.mvarId!]
        else
          let Φ : Q($α → $prop) ← mapForallTelescope' (λ t _ => do
            let (some ig) := parseIrisGoal? t | throwError "not in proof mode"
            return ig.goal
          ) (Expr.mvar mvarId)
          let m : Q($e ⊢ ∀ x, $Φ x) ← mkFreshExprSyntheticOpaqueMVar <|
            IrisGoal.toExpr { u, prop, bi, hyps, goal := q(BI.forall $Φ), ..}

          let pf : Q(∀ (x : $α), $e ⊢ $Φ x) := q(forall_revert $m)

          mvarId.assign pf
          replaceMainGoal [m.mvarId!]
