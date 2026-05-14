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

/-- Auxilary lemma for the base case where up to one hypothesis is given -/
theorem combine_gives_nil [BI PROP] {e goal : PROP} (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := calc
  e ⊢ e ∗ emp    := sep_emp.mpr
  _ ⊢ e ∗ □ True := sep_mono_r intuitionistically_true.mpr
  _ ⊢ goal       := pf

/-- Auxilary lemma for the step case where multiple hypotheses are given -/
theorem combine_gives_step [BI PROP] {e e1 e2 out1 out2 out : PROP}
    (pf1 : e ⊣⊢ e1 ∗ out1)
    (pf2 : e1 ⊣⊢ e2 ∗ out2)
    (inst : CombineSepGives out1 out2 out) : e ⊢ e ∗ □ out :=
  have pf3 : e ⊣⊢ e2 ∗ out1 ∗ out2 := calc
    e ⊣⊢ e1 ∗ out1          := pf1
    _ ⊣⊢ (e2 ∗ out2) ∗ out1 := sep_congr pf2 .rfl
    _ ⊣⊢ e2 ∗ out2 ∗ out1   := sep_assoc
    _ ⊣⊢ e2 ∗ out1 ∗ out2   := sep_congr .rfl sep_comm
  calc
    e ⊢ e2 ∗ out1 ∗ out2                        := pf3.mp
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ out1 ∗ out2) := and_intro refl refl
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ <pers> out)  := and_mono refl (sep_mono refl inst.combine_sep_gives)
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ <pers> out         := and_mono refl sep_elim_r
    _ ⊢ (e2 ∗ out1 ∗ out2) ∗ □ out              := persistently_and_intuitionistically_sep_r.mp
    _ ⊢ e ∗ □ out                               := sep_mono_l pf3.mpr

/--
  Given any Iris proposition `origE` and `goal`, the structure
  `CombineAsState origE goal` consists of a collection of hypotheses
  `newHyps` (representing `newE`), a Boolean value `p` and a proposition
  `out'` such that `origE` is equivalent to `newE ∗ □?p out'`.

  The Boolean expression `init` indicates whether the structure is in its
  initial state. When `p` is `q(true)` and `out'` is `q(emp)`, the Boolean
  expression implicitly indicates whether `□ emp` is the first hypothesis
  provided as an argument to `icombine` or simply the initial value of the
  structure. This is necessary because one, for example, should be able to
  combine `□HP : emp` with `∗HQ : Q` to get `emp ∗ Q` instead of just `Q`.
-/
private structure CombineAsState {u} {prop : Q(Type u)} {bi} (origE goal : Q($prop)) where
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
    @CombineAsState u prop bi origE goal :=
  let pf' := q(combine_as_step $pf1 $(pf2).mp $inst)
  match matchBool p1, matchBool p2 with
  | .inl _, .inl _ => { newHyps, p := q(true), out', pf1 := q($pf'), pf := q(($pf').trans)}
  | .inl _, .inr _ => { newHyps, p := q(false), out', pf1 := q($pf'), pf := q(($pf').trans)}
  | .inr _, _ => { newHyps, p := q(false), out', pf1 := q($pf'), pf := q(($pf').trans)}

private def CombineAsState.combineAsProofModeHyp {u prop bi origE goal} :
    @CombineAsState u prop bi origE goal → IVarId  →
    ProofModeM (@CombineAsState u prop bi origE goal)
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

private structure CombineGivesState {u} {prop : Q(Type u)} {bi} (e goal : Q($prop)) where
  {out' : Q($prop)}
  (hyps : Hyps bi e)
  (pf1 : Q($e ⊢ $e ∗ □ $out'))
  pf : Q(($e ∗ □ $out' ⊢ $goal) → ($e ⊢ $goal))

private def CombineGivesState.combineGivesProofModeHyp {u prop bi e goal} :
    @CombineGivesState u prop bi e goal → IVarId →
    ProofModeM (@CombineGivesState u prop bi e goal)
  | { out', hyps, pf1, .. }, ivar => do
      let ⟨_, _, out2, _, _, _, pf2⟩ := hyps.remove false ivar
      let newOut ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives iprop(□ $out') $out2 $newOut)
      | throwError "icombine: no type class instance to combine propositions"
      let pf1 : Q($e ⊢ $e ∗ □ $newOut) := q(combine_gives_step ⟨$pf1, sep_elim_l⟩ $pf2 $inst)
      let pf : Q(($e ∗ □ $newOut ⊢ $goal) → ($e ⊢ $goal)) := q($(pf1).trans)
      return { hyps, out' := newOut, pf1, pf }

/-- The tactic `icombine` combines propositions into one using the type
    class `CombineSepAs`. By default, the separating conjunction is used
    as the connective. -/
elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList

    -- Initialise a mutable instance of `CombineAsState`
    let mut st : CombineAsState e goal := {
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
      if (hs.count h1 > 1 ∧ ¬isTrue (← hyps.findP h1)) ∨ (hs.count h2 > 1 ∧ ¬isTrue (← hyps.findP h2)) then
        throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

      let ⟨_, hyps1, out1, _, _, _, pf1⟩ := hyps.remove false ivar1
      let ⟨_, _, out2, _, _, _, pf2⟩ := hyps1.remove false ivar2

      let out ← mkFreshExprMVarQ _
      let some inst ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1 $out2 $out)
      | throwError "icombine: no type class instance to combine propositions"

      let pf' : Q($e ⊢ $e ∗ □ $out) := q(combine_gives_step $pf1 $pf2 $inst)

      -- Initialise the mutable `CombineGivesState` instance
      let mut st : CombineGivesState e goal := {
        hyps, out' := out, pf1 := q($pf'), pf := q($(pf').trans)
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h
        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
        -- Iteratively handle the remaining hypotheses
        st ← st.combineGivesProofModeHyp ivar

      -- Generate the new proof goal for the user and fill in the metavariable
      let pf' ← iCasesCore _ st.hyps goal pat q(true) st.out' addBIGoal
      mvar.assign q($(st.pf) $pf')
    | _ =>
      -- Introduce `True` into the intuitionistic context if less than two hypotheses are given
      let pf' ← iCasesCore _ hyps goal pat q(true) q(iprop(True)) addBIGoal
      mvar.assign q(combine_gives_nil $pf')

macro "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat "gives" colGt patGives:icasesPat : tactic =>
  `(tactic| (icombine $idents* gives $patGives; icombine $idents* as $patAs))
