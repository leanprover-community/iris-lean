/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

/-- Auxilary lemma for `iCombineAsCore` (base case with no hypotheses) -/
theorem combine_as_nil [BI PROP] {e goal : PROP}
  (pf : e ∗ □ emp ⊢ goal) : e ⊢ goal := by
  calc
    e ⊢ e ∗ emp   := sep_emp.mpr
    _ ⊢ e ∗ □ emp := sep_mono refl intuitionistically_emp.mpr
    _ ⊢ goal      := pf

/-- Auxilary lemma for `iCombineAsCore` (base case with one hypothesis) -/
theorem combine_as_singleton [BI PROP] {e e1 goal out : PROP}
  (pf1 : e ⊣⊢ e1 ∗ out)
  (pf2 : e1 ∗ out ⊢ goal) : e ⊢ goal := pf1.mp.trans pf2

/-- Auxilary lemma for `iCombineAsCore` (step case with two or more hypotheses) -/
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

/-- Auxilary lemma for `iCombineGivesCore` (base case with up to one hypothesis) -/
theorem combine_nil_singleton_gives [BI PROP] {e goal : PROP}
  (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := by
    calc
      e ⊢ e ∗ emp    := sep_emp.mpr
      _ ⊢ e ∗ □ True := sep_mono refl intuitionistically_true.mpr
      _ ⊢ goal       := pf

/-- Auxilary lemma for `iCombineGivesCore` (step case with two or more hypotheses) -/
theorem combine_step_gives [BI PROP] {out1 out2 out e1 e2 e goal : PROP}
  (pf1 : e ⊣⊢ e1 ∗ out1)
  (pf2 : e1 ⊣⊢ e2 ∗ out2)
  (pf3 : e ∗ □ out ⊢ goal)
  (inst : CombineSepGives out1 out2 out) : e ⊢ goal :=
    have pf4 : e ⊣⊢ e2 ∗ out1 ∗ out2 := by calc
      e ⊣⊢ e1 ∗ out1          := pf1
      _ ⊣⊢ (e2 ∗ out2) ∗ out1 := sep_congr pf2 .rfl
      _ ⊣⊢ e2 ∗ out2 ∗ out1   := sep_assoc
      _ ⊣⊢ e2 ∗ out1 ∗ out2   := sep_congr .rfl sep_comm
    calc
      e ⊢ e2 ∗ out1 ∗ out2 := pf4.mp
      _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ out1 ∗ out2) := and_intro refl refl
      _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ <pers> out)  := and_mono refl (sep_mono refl inst.combine_sep_gives)
      _ ⊢ (e2 ∗ out1 ∗ out2) ∧ <pers> out         := and_mono refl sep_elim_r
      _ ⊢ (e2 ∗ out1 ∗ out2) ∗ □ out              := persistently_and_intuitionistically_sep_r.mp
      _ ⊢ e ∗ □ out                               := sep_mono pf4.mpr refl
      _ ⊢ goal                                    := pf3

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
  (hyps : Hyps bi e) (goal : Q($prop)) (hs : List Ident) (pat : iCasesPat)
  (recCall : Bool := false) :
  ProofModeM Q($e ⊢ $goal) := do
    match hs with
    -- Combine the hypotheses if two or more are given as `icombine` arguments
    | h1 :: h2 :: htail => do
      let uniq1 ← hyps.findWithInfo h1
      let uniq2 ← hyps.findWithInfo h2

      -- We use `hyps.remove` to extract `out1` and `out2` for `CombineSepGives`
      -- The resultant
      let ⟨e1, hyps1, out1, out1', p1, _, pf1⟩ := hyps.remove recCall uniq1

      if (h2 :: htail).contains h1 ∧ ¬isTrue p1 then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨_, _, out2, _, _, _, pf2⟩ := hyps1.remove false uniq2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1 $out2 $out)
      -- Throw an error if a non-trivial fact is not found
      | throwError "icombine: no type class instance to combine propositions"

      match htail, recCall with
      | [], true =>
        -- Introduce the new hypothesis into the intuitionistic context and the new proof goal
        -- Note that we use the original set of hypothesis (`hyps`)
        let pf3 ← iCasesCore _ hyps1 goal pat q(true) out addBIGoal

        match matchBool p1 with
        | .inl _ =>
          let pf4 := q(sep_mono ($(pf1).mp.trans sep_elim_l) (refl : □ $out ⊢ □ $out))
          let pf5 := q($(pf4).trans $pf3)
          return q(combine_step_gives $pf1 $pf2 $pf5 $inst)
        | .inr _ =>
          throwError "icombine: not possible"
      | [], false =>
        let pf3 ← iCasesCore _ hyps goal pat q(true) out addBIGoal
        return q(combine_step_gives $pf1 $pf2 $pf3 $inst)
      | htail, _ =>
        -- Create a temporary identifier for the combined hypothesis
        let id ← mkFreshId
        let h := mkIdent id

        let newHyps := hyps.add bi id id q(true) out
        let pf3 ← iCombineGivesCore newHyps goal (h :: htail) pat true

        return q(combine_step_gives $pf1 $pf2 $pf3 $inst)
    | _ => do
      -- Introduce `True` if less than two hypotheses are given as an `icombine` argument
      let pf ← iCasesCore _ hyps goal pat q(true) q(iprop(True)) addBIGoal
      return q(combine_nil_singleton_gives $pf)
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

elab "icombine" hs:(colGt ident)* "as" colGt pat1:icasesPat "gives" colGt pat2:icasesPat : tactic => do
  let pat1 ← liftMacroM <| iCasesPat.parse pat1
  let pat2 ← liftMacroM <| iCasesPat.parse pat2

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let proof ← iCombineGivesCore hyps goal hs.toList pat2
    mvar.assign proof

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let proof ← iCombineAsCore hyps goal hs.toList pat1
    mvar.assign proof
