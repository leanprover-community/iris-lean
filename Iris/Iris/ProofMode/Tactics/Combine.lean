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

/-- Auxilary lemma for the base case where no hypothesis is given -/
theorem combine_as_nil [BI PROP] {e goal : PROP} (pf : e ∗ □ emp ⊢ goal) : e ⊢ goal := calc
  e ⊢ e ∗ emp   := sep_emp.mpr
  _ ⊢ e ∗ □ emp := sep_mono_r intuitionistically_emp.mpr
  _ ⊢ goal      := pf

/-- Auxilary lemma for the base case with one hypothesis -/
theorem combine_as_singleton [BI PROP] {e e1 e2 out2 : PROP}
    (pf1 : e ⊢ e1 ∗ □?true emp)
    (pf2 : e1 ⊣⊢ e2 ∗ out2) : e ⊢ e2 ∗ out2 := calc
  e ⊢ e1 ∗ □?true emp := pf1
  _ ⊢ e1 ∗ emp        := sep_mono_r intuitionisticallyIf_emp.mp
  _ ⊢ e1              := sep_emp.mp
  _ ⊢ e2 ∗ out2       := pf2.mp

/-- Auxilary lemma for the step case with two or more hypotheses -/
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

/-- Auxilary lemma for the base case where no hypothesis is given -/
theorem combine_gives_nil [BI PROP] {e goal : PROP} (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := calc
  e ⊢ e ∗ emp    := sep_emp.mpr
  _ ⊢ e ∗ □ True := sep_mono_r intuitionistically_true.mpr
  _ ⊢ goal       := pf

theorem combine_gives_step [BI PROP] {e : PROP}
    (pf1 : e ⊣⊢ e1 ∗ □?p1 out1')
    (pf2 : e1 ⊣⊢ e2 ∗ □?p2 out2')
    (inst : CombineSepGives out1' out2' out) : e ⊣⊢ e ∗ □?true out := sorry

/--
  Given any Iris proposition `origE` and `goal`, the structure
  `CombineState origE goal` consists of a collection of hypotheses
  `newHyps` (representing `newE`), a Boolean value `p` and a proposition
  `out'` such that `origE` is equivalent to `newE ∗ □?p out'`.

  The Boolean expression `init` indicates whether the structure is in its
  initial state. When `p` is `q(true)` and `out'` is `q(emp)`, the Boolean
  expression implicitly indicates whether `□ emp` is the first hypothesis
  provided as an argument to `icombine` or simply the initial value of the
  structure. This is necessary because one, for example, should be able to
  combine `□HP : emp` with `∗HQ : Q` to get `emp ∗ Q` instead of just `Q`.
-/
private structure CombineState {u} {prop : Q(Type u)} {bi} (origE goal : Q($prop)) where
  {newE : Q($prop)}
  {p : Q(Bool)}
  {out' : Q($prop)}
  (newHyps : Hyps bi newE)
  (init : Q(Bool) := q(false))
  (pf1 : Q($origE ⊢ $newE ∗ □?$p $out'))
  pf : Q(($newE ∗ □?$p $out' ⊢ $goal) → ($origE ⊢ $goal))

private def updateSt {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {p1 p2 : Q(Bool)}
    {origE e1 e2 out1' out2' out' : Q($prop)}
    (pf1 : Q($origE ⊢ $e1 ∗ □?$p1 $out1'))
    (pf2 : Q($e1 ⊣⊢ $e2 ∗ □?$p2 $out2'))
    (newHyps : Hyps bi e2)
    (goal : Q($prop))
    (inst : Q(CombineSepAs $out1' $out2' $out')) :
    @CombineState u prop bi origE goal :=
  let pf' := q(combine_as_step $pf1 $(pf2).mp $inst)
  match matchBool p1, matchBool p2 with
  | .inl _, .inl _ => { newHyps, p := q(true), out', pf1 := q($pf'), pf := q(($pf').trans)}
  | .inl _, .inr _ => { newHyps, p := q(false), out', pf1 := q($pf'), pf := q(($pf').trans)}
  | .inr _, _ => { newHyps, p := q(false), out', pf1 := q($pf'), pf := q(($pf').trans)}

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
  | { newE, newHyps, p, out', pf1, init .. }, ivar => do
      let ⟨e2, hyps2, _, out2', p2, _, pf2⟩ := newHyps.remove false ivar
      match matchBool p, out', matchBool init with
      | .inl _, ~q(emp), .inl _ =>
        let pf'' : Q($origE ⊢ $e2 ∗ □?$p2 $out2') := q(combine_as_singleton $pf1 $pf2)
        return {
          newE := e2, newHyps := hyps2, p := q($p2), out' := q($out2'),
          pf1 := q(combine_as_singleton $pf1 $pf2),
          pf := q(fun pf => $(pf'').trans pf)
        }
      | _, _, _ =>
        let out ← mkFreshExprMVarQ _
        let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepAs $out' $out2' $out)
        -- The error should not happen as the default option is always available
        | throwError "icombine: no type class instance to combine propositions"
        let pf2 : Q($newE ⊣⊢ $e2 ∗ □?$p2 $out2') := pf2
        return updateSt pf1 pf2 hyps2 goal inst

private def CombineState.combineGivesProofModeHyp {u prop bi origE goal} :
    @CombineState u prop bi origE goal → IVarId  →
    ProofModeM (@CombineState u prop bi origE goal)
  | { newE, newHyps, p, out', pf1, init .. }, ivar => do
      let ⟨e2, hyps2, _, out2', p2, _, pf2⟩ := newHyps.remove false ivar
      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out' $out2' $out)
      | throwError "icombine: no type class instance to combine propositions"
      let pf2 : Q($newE ⊣⊢ $e2 ∗ □?$p2 $out2') := pf2
      return updateSt pf1 pf2 hyps2 goal inst (out' := out)

/-- The tactic `icombine` combines propositions into one using the type
    class `CombineSepAs`. By default, the separating conjunction is used
    as the connective. -/
elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList

    -- Initialise a mutable instance of `CombineState`
    let mut st : CombineState e goal := {
      -- Nothing is part of the combined hypothesis initially
      newE := q($e),
      newHyps := hyps,
      -- The initial combined hypothesis is `□ emp`
      p := q(true),
      out' := q(iprop(emp)),
      -- The proposition `e` is always equivalent to `e ∗ □ emp`
      pf1 := q(sep_emp.mpr.trans <| sep_mono_r intuitionistically_emp.mpr),
      -- No hypothesis is combined initially
      init := q(true)
      pf := q(combine_as_nil)
    }

    for h in hs do
      -- Find the `IVarId` of the hypothesis
      let ivar ← hyps.findWithInfo h

      -- Hypothesis in the spatial context should not be used multiple times
      if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      st ← st.combineAsProofModeHyp ivar

    -- Generate the new proof goal for the user and fill in the metavariable
    let pf' ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.out' addBIGoal
    mvar.assign q($(st.pf) $pf')

/-- The tactic `icombine` with `gives` syntax combines propositions to derive
    new information in the intutionisitic context using the type class
    `CombineSepGives`. It is possible that no type class instance is
    applicable -/
elab "icombine" idents:(colGt ident)* "gives" colGt patGives:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList

    match hs with
    | h1 :: h2 :: htail =>
      -- Find the `IVarId` of the hypothesis
      let ivar1 ← hyps.findWithInfo h1
      let ivar2 ← hyps.findWithInfo h2

      -- Hypothesis in the spatial context should not be used multiple times
      if hs.count h1 > 1 ∧ ¬isTrue (← hyps.findP h1) then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨e1, hyps1, out1, out1', p1, eq1, pf1⟩ := hyps.remove false ivar1
      let ⟨e2, hyps2, out2, out2', p2, eq2, pf2⟩ := hyps1.remove false ivar2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1' $out2' $out)
      | throwError "icombine: no type class instance to combine propositions"

      let pf' : Q($e ⊣⊢ $e ∗ □?true $out) := q(combine_gives_step $pf1 $pf2 $inst)

      let mut st : CombineState e goal := {
        newE := q($e),
        newHyps := hyps,
        p := q(true),
        out' := out,
        pf1 := q($(pf').mp),
        pf := q($(pf').mp.trans)
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h

        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

        st ← st.combineGivesProofModeHyp ivar

      -- Generate the new proof goal for the user and fill in the metavariable
      let pf' ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.out' addBIGoal
      mvar.assign q($(st.pf) $pf')

    | _ =>
      -- Initialise a mutable instance of `CombineState`
      let mut st : CombineState e goal := {
        -- Nothing is part of the combined hypothesis initially
        newE := q($e),
        newHyps := hyps,
        -- The initial combined hypothesis is `□ True`
        p := q(true),
        out' := q(iprop(True)),
        -- The proposition `e` is always equivalent to `e ∗ □ True`
        pf1 := q(sep_emp.mpr.trans <| sep_mono_r intuitionistically_true.mpr),
        -- No hypothesis is combined initially
        init := q(true)
        pf := q(combine_gives_nil)
      }

      -- Generate the new proof goal for the user and fill in the metavariable
      let pf' ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.out' addBIGoal
      mvar.assign q($(st.pf) $pf')
