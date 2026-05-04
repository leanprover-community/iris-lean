/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

theorem combine [BI PROP] {out1 out2 e1 e2 goal e : PROP}
  (pf : □?false (out1 ∗ out2) ∗ e2 ⊢ goal)
  (pf1 : e ⊣⊢ e1 ∗ out1)
  (pf2 : e1 ⊣⊢ e2 ∗ out2) : e ⊢ goal := by
  refine Entails.trans ?_ pf
  have h0 : out1 ⊢ out1 := by simp
  have h1 : e2 ⊢ e2 := by simp
  have h2 : e ⊢ (out1 ∗ out2) ∗ e2 :=
    calc
      e ⊢ e1 ∗ out1 := pf1.mp
      _ ⊢ (e2 ∗ out2) ∗ out1 := sep_mono pf2.mp h0
      _ ⊢ e2 ∗ (out2 ∗ out1) := sep_assoc.mp
      _ ⊢ (out2 ∗ out1) ∗ e2 := sep_comm.mp
      _ ⊢ (out1 ∗ out2) ∗ e2 := sep_mono sep_comm.mp h1
  exact h2

-- An extremely simplified version of icombine for combining two propositions
-- into one, connected by the separating conjunction
private def iCombineCore (hyp1 hyp2 : Ident) : TacticM Unit := do
  /- TODO: generalisation with type classes -/
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
    let uniq1 ← hyps.findWithInfo hyp1
    let uniq2 ← hyps.findWithInfo hyp2

    -- Remove the original two hypotheses
    let ⟨_, hyps1, out1, _, _, _, pf1⟩ := hyps.remove true uniq1
    let ⟨_, hyps2, out2, _, _, _, pf2⟩ := hyps1.remove true uniq2

    let freshName := `Hnew
    let freshUniq ← mkFreshId

    -- Introduce the new hypothesis that combines the two original hypotheses
    let newHyp := Hyps.mkHyp bi freshName freshUniq q(false) q(BI.sep $out1 $out2)

    -- Add the new hypothesis into the set of hypotheses
    let newHyps := Hyps.mkSep newHyp hyps2

    -- New proof goal for the tactic user
    let pf ← addBIGoal newHyps goal

    mvar.assign q(combine $pf $pf1 $pf2)

elab "icombine" hyp1:ident hyp2:ident "as" pat:icasesPat : tactic => do
  /- TODO: case pattern destruction -/
  iCombineCore hyp1 hyp2
