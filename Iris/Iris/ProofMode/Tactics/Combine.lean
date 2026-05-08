/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

theorem combine_nil [BI PROP] {e goal : PROP}
  (pf : e ∗ □ emp ⊢ goal) : e ⊢ goal := by
  calc
    e ⊢ e ∗ emp   := sep_emp.mpr
    _ ⊢ e ∗ □ emp := sep_mono refl intuitionistically_emp.mpr
    _ ⊢ goal      := pf

theorem combine_singleton [BI PROP] {e e1 goal : PROP}
  (pf1 : e ⊣⊢ e1 ∗ out)
  (pf2 : e1 ∗ out ⊢ goal) : e ⊢ goal := pf1.mp.trans pf2

theorem combine_step [BI PROP] {out1 out2 out e1 e2 goal e : PROP}
  (pf1 : e ⊣⊢ e1 ∗ □?b1 out1)
  (pf2 : e1 ⊣⊢ e2 ∗ □?b2 out2)
  (pf3 : e2 ∗ □?b out ⊢ goal)
  (pf4 : b = (b1 && b2))
  (inst : CombineSepAs out1 out2 out)
  : e ⊢ goal := by
    calc
      e ⊢ e1 ∗ □?b1 out1               := pf1.mp
      _ ⊢ (e2 ∗ □?b2 out2) ∗ □?b1 out1 := sep_mono pf2.mp refl
      _ ⊢ e2 ∗ □?b2 out2 ∗ □?b1 out1   := sep_assoc.mp
      _ ⊢ e2 ∗ □?b1 out1 ∗ □?b2 out2   := sep_mono refl sep_comm.mp
      _ ⊢ e2 ∗ □?b (out1 ∗ out2)       := sep_mono refl (intuitionisticallyIf_sep_conj pf4)
      _ ⊢ e2 ∗ □?b out                 := sep_mono refl (intuitionisticallyIf_mono inst.combine_sep_as)
      _ ⊢ goal                         := pf3

theorem dummy_thm {p p1 p2 : Bool} : p = (p1 && p2) := sorry

/-- The tactic `icombine` combines two propositions into one using the type
    class `CombineSepAs` or, by default, the separating conjunction -/
private def iCombineCore {u} {prop : Q(Type u)} {bi e}
  (hyps : Hyps bi e) (goal : Q($prop)) (hs : List Ident)
  (pat : iCasesPat) (recCall : Bool := false) :
  ProofModeM Q($e ⊢ $goal) := do
    match hs with
    -- Introduce `emp` if no hypothesis is given as `icombine` arguments
    | [] => do
      let pf ← iCasesCore bi hyps goal pat q(true) q(emp) addBIGoal
      return q(combine_nil $pf)

    -- No hypothesis combined if exactly one hypothesis is given as an `icombine` argument
    | [h1] => do
      let uniq ← hyps.findWithInfo h1
      -- The second argument to `hyps.remove` is set as `false`
      let ⟨e, hyps, out, out', p, _, pf1⟩ := hyps.remove false uniq
      let pf2 ← iCasesCore bi hyps goal pat p out' addBIGoal
      return q(combine_singleton $pf1 $pf2)

    -- Combine the hypotheses if two or more are given as `icombine` arguments
    | h1 :: h2 :: htail => do
      let uniq1 ← hyps.findWithInfo h1
      let uniq2 ← hyps.findWithInfo h2

      -- The Boolean value `recCall` indicates that `iCombineCore` is currently
      -- is called recursively. In this case, the first hypothesis in the list
      -- is temporary and should be removed even if it is in the non-spatial
      -- context.
      let ⟨e1, hyps1, out1, out1', p1, eq1, pf1⟩ := hyps.remove recCall uniq1
      let ⟨e2, hyps2, out2, out2', p2, eq2, pf2⟩ := hyps1.remove false uniq2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out1' $out2' $out)
      -- The error should not happen as the default option is always available
      | throwError "icombine: no type class instance to combine propositions"

      let p := if ((p1 == q(true) && p2 == q(true))) then q(true) else q(false)

      match htail with
      | [] =>
        -- Introduce the new hypothesis that combines the two original hypotheses
        -- New proof goal for the tactic user
        let pf3 ← iCasesCore bi hyps2 goal pat p out addBIGoal
        let pf4 : Q($casesOn_1 = ($p1 && $p2)) := by simpa

        return q(combine_step $pf1 $pf2 $pf3 $pf4 $inst)
      | htail =>
        -- Create a temporary identifier for the combined hypothesis
        let freshId ← mkFreshId
        let h := mkIdent freshId

        -- Add the combined hypothesis to the context
        let newHyps := Hyps.mkSep hyps2 (Hyps.mkHyp bi freshId freshId p out)

        -- Add the combined proposition into the remaining list
        let pf3 ← iCombineCore newHyps goal (h :: htail) pat true
        let pf4 : Q($casesOn_1 = ($p1 && $p2)) := by simpa

        return q(combine_step $pf1 $pf2 $pf3 $pf4 $inst)
  termination_by hs.length

elab "icombine" hs:(colGt ident)* "as" colGt pat:icasesPat : tactic => do
  -- Parse syntax
  let pat ← liftMacroM <| iCasesPat.parse pat

  -- Generate new proof goals and fill in the original metavariable
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let proof ← iCombineCore hyps goal hs.toList pat
    mvar.assign proof
