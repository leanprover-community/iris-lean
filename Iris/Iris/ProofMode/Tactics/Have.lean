/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

import Iris.BI
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Tactics.HaveCore
public meta import Iris.ProofMode.Tactics.Cases

namespace Iris.ProofMode

public section
open BI

theorem ihave_assert [BI PROP] {A B C : PROP}
  (h1 : A ∗ □ (B -∗ B) ⊢ C) : A ⊢ C :=
    (and_intro .rfl (persistently_emp_intro.trans (persistently_mono $ wand_intro emp_sep.1))).trans
      $ persistently_and_intuitionistically_sep_right.1.trans h1

public meta section
open Lean Elab Tactic Meta Qq

/--
  `ihave pat := pmt` brings `pmt : pmTerm` into the context and destructs it
  with the case pattern `pat` without consuming the original hypotheses.
-/
macro "ihave " colGt pat:icasesPat " := " pmt:pmTerm : tactic => `(tactic | icases +keep $pmt with $pat)

/--
  `ihave pat : P $$ spat` asserts `P`, proves it with a subgoal built from the
  specification pattern `spat` and destructs it with the case pattern `pat`.
-/
elab "ihave " colGt pat:icasesPat " : " P:term " $$ " spat:specPat : tactic => do
  let spat ← liftMacroM <| SpecPat.parse spat
  let pat ← liftMacroM <| iCasesPat.parse pat
  ProofModeM.runTactic λ mvar { prop, bi, hyps, goal, .. } => do
  let P ← elabTermEnsuringTypeQ (← `(iprop($P))) prop
  --  establish `P` with `spat`
  let ⟨_, hyps', p, A, pf, _⟩ ← iSpecializeCore hyps q(true) q(iprop($P -∗ $P)) goal [spat] (try_dup_context := pat.should_try_dup_context)
  let pf2 ← iCasesCore bi hyps' goal pat p A
  mvar.assign q(ihave_assert ($pf $pf2))
