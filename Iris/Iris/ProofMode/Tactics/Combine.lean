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

theorem combine_as_nil [BI PROP] {e goal : PROP}
  (pf : e ∗ □ emp ⊢ goal) : e ⊢ goal := by
  calc
    e ⊢ e ∗ emp   := sep_emp.mpr
    _ ⊢ e ∗ □ emp := sep_mono refl intuitionistically_emp.mpr
    _ ⊢ goal      := pf

theorem combine_as_singleton [BI PROP] {e e1 goal out : PROP}
  (pf1 : e ⊣⊢ e1 ∗ out)
  (pf2 : e1 ∗ out ⊢ goal) : e ⊢ goal := pf1.mp.trans pf2

theorem combine_as_step [BI PROP] {out1 out2 out e1 e2 e goal : PROP}
  {b1 b2 : Bool}
  (pf1 : e ⊣⊢ e1 ∗ □?b1 out1)
  (pf2 : e1 ⊣⊢ e2 ∗ □?b2 out2)
  (pf3 : e2 ∗ □?(b1 ∧ b2) out ⊢ goal)
  (inst : CombineSepAs out1 out2 out) : e ⊢ goal := by
    calc
      e ⊢ e1 ∗ □?b1 out1                 := pf1.mp
      _ ⊢ (e2 ∗ □?b2 out2) ∗ □?b1 out1   := sep_mono pf2.mp refl
      _ ⊢ e2 ∗ □?b2 out2 ∗ □?b1 out1     := sep_assoc.mp
      _ ⊢ e2 ∗ □?b1 out1 ∗ □?b2 out2     := sep_mono refl sep_comm.mp
      _ ⊢ e2 ∗ □?(b1 ∧ b2) (out1 ∗ out2) := sep_mono refl intuitionisticallyIf_sep_conj
      _ ⊢ e2 ∗ □?(b1 ∧ b2) out           := sep_mono refl (intuitionisticallyIf_mono inst.combine_sep_as)
      _ ⊢ goal                           := pf3

theorem combine_nil_singleton_gives [BI PROP] {e goal : PROP}
  (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := by
    calc
      e ⊢ e ∗ emp    := sep_emp.mpr
      _ ⊢ e ∗ □ True := sep_mono refl intuitionistically_true.mpr
      _ ⊢ goal       := pf

theorem combine_step_gives [BI PROP] {out1 out2 out e goal : PROP}
  (inst : CombineSepGives out1 out2 out) : e ⊢ goal := sorry

/-- The tactic `icombine` combines two propositions into one using the type
    class `CombineSepAs` or, by default, the separating conjunction -/
private def iCombineAsCore {u} {prop : Q(Type u)} {bi e}
  (hyps : Hyps bi e) (goal : Q($prop)) (hs : List Ident)
  (pat : iCasesPat) (recCall : Bool := false) :
  ProofModeM Q($e ⊢ $goal) := do
    match hs with
    -- Introduce `emp` if no hypothesis is given as `icombine` arguments
    | [] => do
      let pf ← iCasesCore _ hyps goal pat q(true) q(emp) addBIGoal
      return q(combine_as_nil $pf)

    -- No hypothesis combined if exactly one hypothesis is given as an `icombine` argument
    | [h1] => do
      let uniq ← hyps.findWithInfo h1
      -- The second argument to `hyps.remove` is set as `false`
      let ⟨_, hyps, _, out', p, _, pf1⟩ := hyps.remove false uniq
      let pf2 ← iCasesCore _ hyps goal pat p out' addBIGoal
      return q(combine_as_singleton $pf1 $pf2)

    -- Combine the hypotheses if two or more are given as `icombine` arguments
    | h1 :: h2 :: htail => do
      let uniq1 ← hyps.findWithInfo h1
      let uniq2 ← hyps.findWithInfo h2

      -- The Boolean value `recCall` indicates that `iCombineAsCore` is currently
      -- is called recursively. In this case, the first hypothesis in the list
      -- is temporary and should be removed even if it is in the non-spatial
      -- context.
      let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove recCall uniq1

      if (h2 :: htail).contains h1 ∧ ¬isTrue p1 then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨_, hyps2, _, out2', p2, _, pf2⟩ := hyps1.remove false uniq2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out1' $out2' $out)
      -- The error should not happen as the default option is always available
      | throwError "icombine: no type class instance to combine propositions"

      match htail with
      | [] =>
        -- Introduce the new hypothesis that combines the two original hypotheses
        -- New proof goal for the tactic user
        match matchBool p1, matchBool p2 with
        | .inl _, .inl _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(true) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inl _, .inr _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(false) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, .inl _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(false) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, .inr _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(false) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
      | htail =>
        -- Create a temporary identifier for the combined hypothesis
        let id ← mkFreshId
        let h := mkIdent id

        -- Add the combined hypothesis to the context and into the list `hs`
        match matchBool p1, matchBool p2 with
        | .inl _, .inl _ =>
          let newHyps := hyps2.add bi id id q(true) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inl _, .inr _ =>
          let newHyps := hyps2.add bi id id q(false) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, .inl _ =>
          let newHyps := hyps2.add bi id id q(false) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, .inr _ =>
          let newHyps := hyps2.add bi id id q(false) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
  termination_by hs.length

/-- Use the type class `CombineSepGives` to derive a new proposition in the
    the intutitionistic context and retain the original hypotheses  -/
private def iCombineGivesCore {u} {prop : Q(Type u)} {bi e}
  (hyps : Hyps bi e) (goal : Q($prop)) (hs : List Ident)
  (pat : iCasesPat) (recCall : Bool := false) :
  ProofModeM Q($e ⊢ $goal) := do
    match hs with
    -- Introduce `True` if no hypothesis is given as `icombine` arguments
    | [] => do
      let pf ← iCasesCore _ hyps goal pat q(true) q(iprop(True)) addBIGoal
      return q(combine_nil_singleton_gives $pf)

    -- Introduce `True` if exactly one hypothesis is given as an `icombine` argument
    | [_] => do
      let pf ← iCasesCore _ hyps goal pat q(true) q(iprop(True)) addBIGoal
      return q(combine_nil_singleton_gives $pf)

    -- Combine the hypotheses if two or more are given as `icombine` arguments
    | h1 :: h2 :: htail => do
      let uniq1 ← hyps.findWithInfo h1
      let uniq2 ← hyps.findWithInfo h2

      let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove recCall uniq1

      if (h2 :: htail).contains h1 ∧ ¬isTrue p1 then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨_, hyps2, _, out2', p2, _, pf2⟩ := hyps1.remove false uniq2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1' $out2' $out)
      -- Throw an error if a non-trivial fact is not found
      | throwError "icombine: no type class instance to combine propositions"

      match htail with
      | [] =>
        -- Introduce the new hypothesis into the
        -- New proof goal for the tactic user
        let pf3 ← iCasesCore _ hyps goal pat q(true) out addBIGoal
        return q(combine_step_gives $inst)

      | _ => throwUnsupportedSyntax
  termination_by hs.length

elab "icombine" hs:(colGt ident)* "as" colGt pat:icasesPat : tactic => do
  -- Parse syntax
  let pat ← liftMacroM <| iCasesPat.parse pat

  -- Generate new proof goals and fill in the original metavariable
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let proof ← iCombineAsCore hyps goal hs.toList pat
    mvar.assign proof

elab "icombine" hs:(colGt ident)* "gives" colGt pat:icasesPat : tactic => do
  -- Parse syntax
  let pat ← liftMacroM <| iCasesPat.parse pat

  -- Generate new proof goals and fill in the original metavariable
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let proof ← iCombineGivesCore hyps goal hs.toList pat
    mvar.assign proof
