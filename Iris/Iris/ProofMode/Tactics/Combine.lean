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

theorem combine_as_nil [BI PROP] {e goal : PROP}
    (pf : e ∗ □ emp ⊢ goal) :
    e ⊢ goal := calc
  e ⊢ e ∗ emp   := sep_emp.mpr
  _ ⊢ e ∗ □ emp := sep_mono refl intuitionistically_emp.mpr
  _ ⊢ goal      := pf

theorem combine_as_singleton [BI PROP] {e e1 : PROP}
    (pf1 : e ⊢ e1 ∗ □?true emp)
    (pf2 : e1 ⊣⊢ e2 ∗ out2) : e ⊢ e2 ∗ out2 := calc
  e ⊢ e1 ∗ □?true emp := pf1
  _ ⊢ e1 ∗ emp        := sep_mono_r intuitionisticallyIf_emp.mp
  _ ⊢ e1              := sep_emp.mp
  _ ⊢ e2 ∗ out2       := pf2.mp

theorem combine_as_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1' out2' out : PROP}
    (pf1 : e ⊢ e1 ∗ □?p1 out1')
    (pf2 : e1 ⊢ e2 ∗ □?p2 out2')
    (inst : CombineSepAs out1' out2' out) :
    e ⊢ e2 ∗ □?(p1 && p2) out := calc
  e ⊢ e1 ∗ □?p1 out1'                   := pf1
  _ ⊢ (e2 ∗ □?p2 out2') ∗ □?p1 out1'    := sep_mono_l pf2
  _ ⊢ e2 ∗ □?p2 out2' ∗ □?p1 out1'      := sep_assoc.mp
  _ ⊢ e2 ∗ □?p1 out1' ∗ □?p2 out2'      := sep_mono_r sep_comm.mp
  _ ⊢ e2 ∗ □?(p1 && p2) (out1' ∗ out2') := sep_mono_r intuitionisticallyIf_sep_conj
  _ ⊢ e2 ∗ □?(p1 && p2) out             := sep_mono_r (intuitionisticallyIf_mono inst.combine_sep_as)

/-- The proposition `□?p1 out1'` is the combined hypothesis, and `hyps1` is
    are remaining hypotheses. -/
private structure CombineState {u} {prop : Q(Type u)} {bi} (origE goal : Q($prop)) where
  (recCall : Bool)
  (e1 : Q($prop))
  (hyps1 : Hyps bi e1)
  (p1 : Q(Bool))
  (out1' : Q($prop))
  (pf1 : Q($origE ⊢ $e1 ∗ □?$p1 $out1'))
  pf : Q(($e1 ∗ □?$p1 $out1' ⊢ $goal) → ($origE ⊢ $goal))

/-- The tactic `icombine` combines two propositions into one using the type
    class `CombineSepAs` or, by default, the separating conjunction.
    The Boolean value `recCall` indicates whether this function is currently
    being called recursively. -/
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
      let ivar ← hyps.findWithInfo h1
      -- The second argument to `hyps.remove` is set as `false`
      let ⟨_, hyps, _, out', p, _, pf1⟩ := hyps.remove false ivar
      let pf2 ← iCasesCore _ hyps goal pat p out' addBIGoal
      return q(combine_as_singleton $pf1 $pf2)

    -- Combine the hypotheses if two or more are given as `icombine` arguments
    | h1 :: h2 :: htail => do
      let ivar1 ← hyps.findWithInfo h1
      let ivar2 ← hyps.findWithInfo h2

      /- The Boolean value `recCall` indicates that `iCombineAsCore` is
         currently is called recursively. In this case, the first hypothesis in
         the list is temporary and should be removed even if it is in the
         non-spatial context. -/
      let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove recCall ivar1
      if (h2 :: htail).contains h1 ∧ ¬isTrue p1 then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
      let ⟨_, hyps2, _, out2', p2, _, pf2⟩ := hyps1.remove false ivar2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out1' $out2' $out)
      -- The error should not happen as the default option is always available
      | throwError "icombine: no type class instance to combine propositions"

      match htail with
      | [] =>
        /- Introduce the new hypothesis that combines the two original
           hypotheses into the proof state, and generate the new proof goal for
           the tactic user. The combined proposition is introduced into the
           intuitionistic context if `p1` and `p2` are true. -/
        match matchBool p1, matchBool p2 with
        | .inl _, .inl _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(true) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inl _, .inr _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(false) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, _ =>
          let pf3 ← iCasesCore _ hyps2 goal pat q(false) out addBIGoal
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
      | htail =>
        -- Create a temporary identifier for the combined hypothesis
        let id ← mkFreshId
        let h := mkIdent id

        /- Add the combined hypothesis to the proof state and into the list
           `hs` for the recursive function call. -/
        match matchBool p1, matchBool p2 with
        | .inl _, .inl _ =>
          let newHyps := hyps2.add bi id id q(true) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inl _, .inr _ =>
          let newHyps := hyps2.add bi id id q(false) out
          let pf3 ← iCombineAsCore newHyps goal (h :: htail) pat true
          return q(combine_as_step $pf1 $pf2 $pf3 $inst)
        | .inr _, _ =>
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
      let ivar1 ← hyps.findWithInfo h1
      let ivar2 ← hyps.findWithInfo h2

      -- USe `hyps.remove` to extract `out1` and `out2` for `CombineSepGives`
      let ⟨e1, hyps1, out1, _, p1, _, pf1⟩ := hyps.remove recCall ivar1

      if (h2 :: htail).contains h1 ∧ ¬isTrue p1 then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨_, _, out2, _, _, _, pf2⟩ := hyps1.remove false ivar2

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
          let pf4 := q($(pf1).mp.trans sep_elim_l)
          return q(combine_step_gives $pf1 $pf2 $pf3 $pf4 $inst)
        | .inr _ =>
          -- This should never happen as the intermediate proposition generated
          -- by `iCombineGivesCore` exists in the intuitionistic context
          throwAbortTactic
      | [], false =>
        let pf3 ← iCasesCore _ hyps goal pat q(true) out addBIGoal
        return q(combine_step_gives $pf1 $pf2 $pf3 refl $inst)
      | htail, _ =>
        -- Create a temporary identifier for the combined hypothesis
        let id ← mkFreshId
        let h := mkIdent id

        let newHyps := hyps.add bi id id q(true) out
        let pf3 ← iCombineGivesCore newHyps goal (h :: htail) pat true

        return q(combine_step_gives $pf1 $pf2 $pf3 refl $inst)
    | _ => do
      -- Introduce `True` if less than two hypotheses are given as an `icombine` argument
      let pf ← iCasesCore _ hyps goal pat q(true) q(iprop(True)) addBIGoal
      return q(combine_nil_singleton_gives $pf)
  termination_by hs.length

theorem dummy [BI PROP] {a b c : PROP} : a ⊢ b ∗ c := sorry

private def CombineState.combineAsProofModeHyp {u prop bi origE goal} :
    @CombineState u prop bi origE goal → IVarId  →
    ProofModeM (@CombineState u prop bi origE goal)
  | { e1, hyps1, out1', p1, pf1, pf, recCall }, ivar => do
      match p1, out1' with
      | ~q(true), ~q(emp) =>
        let ⟨e2, hyps2, out2, out2', p2, _, pf2⟩ := hyps1.remove false ivar
        let pf'' : Q($origE ⊢ $e2 ∗ □?$p2 $out2') := q(combine_as_singleton $pf1 $pf2)
        return {
          e1 := e2, hyps1 := hyps2, out1' := q($out2'), p1 := q($p2),
          pf1 := q(combine_as_singleton $pf1 $pf2),
          recCall := true,
          pf := q(fun pf => $(pf'').trans pf)
        }
      | _, _ =>
        let ⟨e2, hyps2, out2, out2', p2, _, pf2⟩ := hyps1.remove false ivar
        let out ← mkFreshExprMVarQ _
        let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out1' $out2' $out)
        -- The error should not happen as the default option is always available
        | throwError "icombine: no type class instance to combine propositions"

        match matchBool p1, matchBool p2 with
        | .inl _, .inl _ =>
            let pf'' : Q($origE ⊢ $e2 ∗ □?true $out) :=
              q(combine_as_step $pf1 $(pf2).mp $inst)
            return {
              e1 := e2, hyps1 := hyps2, p1 := q(true), out1' := out, pf1 := pf'',
              recCall := true
              pf := q(fun pf' => $(pf'').trans pf')
            }
        | .inl _, .inr _ =>
            let pf'' : Q($origE ⊢ $e2 ∗ □?false $out) :=
              q(combine_as_step $pf1 $(pf2).mp $inst)
            return {
              e1 := e2, hyps1 := hyps2, p1 := q(false), out1' := out, pf1 := pf'',
              recCall := true
              pf := q(fun pf' => $(pf'').trans pf')
            }
        | .inr _, _ =>
          let pf'' : Q($origE ⊢ $e2 ∗ □?false $out) :=
            q(combine_as_step $pf1 $(pf2).mp $inst)
          return {
            e1 := e2, hyps1 := hyps2, p1 := q(false), out1' := out, pf1 := pf'',
            recCall := true
            pf := q(fun pf' => $(pf'').trans pf')
          }

/-- The tactic `icombine` combines two propositions into one using the type
    class `CombineSepAs` or, by default, the separating conjunction. -/
elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList

    let mut st : CombineState e goal := {
      e1 := q($e), hyps1 := hyps, out1' := q(iprop(emp)), p1 := q(true),
      pf1 := q(sep_emp.mpr.trans <| sep_mono_r intuitionistically_emp.mpr),
      recCall := false
      pf := q(combine_as_nil)
    }

    for h in hs do
      let ivar ← hyps.findWithInfo h
      let ⟨_, _, _, _, p, _, _⟩ := hyps.remove false ivar

      -- Hypothesis in the spatial context should not be used multiple times
      if hs.count h ≥ 2 ∧ ¬isTrue p then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      st ← st.combineAsProofModeHyp ivar

    let pf' ← iCasesCore _ st.hyps1 goal pat q($(st.p1)) st.out1' addBIGoal
    mvar.assign q($(st.pf) $pf')
