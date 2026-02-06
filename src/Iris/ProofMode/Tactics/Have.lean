/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Patterns.CasesPattern
import Iris.ProofMode.Tactics.HaveCore
import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

macro "ihave" colGt pat:icasesPat " := " pmt:pmTerm : tactic => `(tactic | icases $pmt with $pat)

private theorem ihave_assert [BI PROP] {A B C : PROP}
  (h1 : A ∗ □ (B -∗ B) ⊢ C) : A ⊢ C :=
    (and_intro .rfl (persistently_emp_intro.trans (persistently_mono $ wand_intro emp_sep.1))).trans
      $ persistently_and_intuitionistically_sep_r.1.trans h1

elab "ihave" colGt pat:icasesPat " : " P:term "$$" spat:specPat : tactic => do
  let spat ← liftMacroM <| SpecPat.parse spat
  let pat ← liftMacroM <| iCasesPat.parse pat
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do
  let P ← elabTermEnsuringTypeQ (← `(iprop($P))) prop
  --  establish `P` with `spat`
  let ⟨_, hyps', p, A, pf⟩ ← iSpecializeCore hyps q(true) q(iprop($P -∗ $P)) [spat]
  have ⟨B, eq⟩ := mkIntuitionisticIf bi p A
  let pf2 ← iCasesCore bi hyps' goal p B A eq pat (λ hyps => addBIGoal hyps goal)
  mvar.assign q(ihave_assert (($pf).trans $pf2))
