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

/-- Auxilary lemma for the step case with two or more hypotheses -/
theorem combine_as_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1' out2' out goal : PROP}
    (inst : CombineSepAs out1' out2' out)
    (pf1 : (e1 ∗ □?p1 out1' ⊢ goal) → e ⊢ goal)
    (pf2 : e1 ⊢ e2 ∗ □?p2 out2')
    (pf3 : e2 ∗ □?(p1 && p2) out ⊢ goal) : e ⊢ goal := by
  apply pf1
  calc
    _ ⊢ (e2 ∗ □?p2 out2') ∗ □?p1 out1'    := sep_mono_l pf2
    _ ⊢ e2 ∗ □?p2 out2' ∗ □?p1 out1'      := sep_assoc.mp
    _ ⊢ e2 ∗ □?p1 out1' ∗ □?p2 out2'      := sep_mono_r sep_comm.mp
    _ ⊢ e2 ∗ □?(p1 && p2) (out1' ∗ out2') := sep_mono_r intuitionisticallyIf_sep_conj
    _ ⊢ e2 ∗ □?(p1 && p2) out             := sep_mono_r <| intuitionisticallyIf_mono inst.combine_sep_as
    _ ⊢ goal                              := pf3

/-- Auxilary lemma for the base case where up to one hypothesis is given -/
theorem combine_gives_nil [BI PROP] {e goal : PROP} (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := calc
  e ⊢ e ∗ emp    := sep_emp.mpr
  _ ⊢ e ∗ □ True := sep_mono_r intuitionistically_true.mpr
  _ ⊢ goal       := pf


theorem dummy [BI PROP] {e1 e2 e3 e4 : PROP} (pf : e1 ⊢ e2) : e3 ⊢ e4 := sorry

theorem dummy1 [BI PROP] {e1 e2 : PROP} : e1 ⊢ e2 := sorry

/-- Auxilary lemma for the step case where multiple hypotheses are given -/
theorem combine_gives_step [BI PROP] {e e1 e2 out1 out2 out goal : PROP}
    (inst : CombineSepGives out1 out2 out)
    (pf0 : e1 ∗ out1 ⊢ e)
    (pf1 : (e1 ∗ out1 ⊢ goal) → e ⊢ goal)
    (pf2 : e1 ⊣⊢ e2 ∗ out2)
    (pf3 : e ∗ □ out ⊢ goal) : e ⊢ goal := by
  apply pf1
  calc
    _ ⊢ (e2 ∗ out2) ∗ out1                      := sep_mono_l pf2.mp
    _ ⊢ e2 ∗ out2 ∗ out1                        := sep_assoc.mp
    _ ⊢ e2 ∗ out1 ∗ out2                        := sep_mono_r sep_comm.mp
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ out1 ∗ out2) := and_intro refl refl
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ (e2 ∗ <pers> out)  := and_mono_r <| sep_mono_r inst.combine_sep_gives
    _ ⊢ (e2 ∗ out1 ∗ out2) ∧ <pers> out         := and_mono_r sep_elim_r
    _ ⊢ (e2 ∗ out1 ∗ out2) ∗ □ out              := persistently_and_intuitionistically_sep_r.mp
    _ ⊢ (e2 ∗ out2 ∗ out1) ∗ □ out              := sep_mono_l <| sep_mono_r sep_comm.mp
    _ ⊢ ((e2 ∗ out2) ∗ out1) ∗ □ out            := sep_mono_l sep_assoc.mpr
    _ ⊢ (e1 ∗ out1) ∗ □ out                     := sep_mono_l <| sep_mono_l pf2.mpr
    _ ⊢ e ∗ □ out                               := sep_mono_l pf0
    _ ⊢ goal                                    := pf3

/- NEW CODE -/

private structure CombineState {u} {prop : Q(Type u)} {bi} (origE goal : Q($prop)) where
  -- The original set of hypotheses
  (origHyps : Hyps bi origE)
  -- The remaining hypotheses after combining hypotheses
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  -- The combined hypothesis for the `as` syntax
  {p : Q(Bool)}
  {outAs' : Q($prop)}
  -- The proof for the `as` syntax
  (pfAs : Q(($newE ∗ □?$p $outAs' ⊢ $goal) → ($origE ⊢ $goal)))
  -- The derived additional hypothesis for the `gives` syntax
  (outGives' : Option Q($prop))
  -- The proof for the `gives` syntax
  (pfGives : match outGives' with
    | none => PUnit
    | some outGives' => Q(($origE ∗ □ $outGives' ⊢ $goal) → ($origE ⊢ $goal)))

private def CombineState.combineProofModeHyp {u prop bi origE goal} :
    @CombineState u prop bi origE goal → IVarId →
    ProofModeM (@CombineState u prop bi origE goal)
  | { origHyps, newE, newHyps, p, outAs', pfAs, outGives', pfGives }, ivar => do
    let ⟨e2, hyps2, out2, out2', p2, eq2, pf2⟩ := newHyps.remove false ivar

    let newOutAs ← mkFreshExprMVarQ _
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $outAs' $out2' $newOutAs)


    let pf2 : Q($newE ⊣⊢ $e2 ∗ $out2) := pf2
    let newPfAs := q(combine_as_step $instAs $pfAs $(pf2).mp)

    match outGives', pfGives with
    | none, _ =>
      match matchBool p, matchBool p2 with
      | .inl _, .inl _ => return { origHyps, newHyps := hyps2, p := q(true), outAs' := newOutAs, pfAs := newPfAs, outGives' := none, pfGives := ⟨⟩ }
      | _,      _      => return { origHyps, newHyps := hyps2, p := q(false), outAs' := newOutAs, pfAs := newPfAs, outGives' := none, pfGives := ⟨⟩ }

    | some outGives', pfGives =>
      let pfGives : Q(($newE ∗ □ $outGives' ⊢ $goal) → $newE ⊢ $goal) := pfGives

      let newOutGives1 ← mkFreshExprMVarQ _
      let newOutGives2 ← mkFreshExprMVarQ _

      let instGives1 ← ProofModeM.trySynthInstanceQ q(CombineSepGives iprop(□ $outGives') $out2 $newOutGives1)
      let instGives2 ← ProofModeM.trySynthInstanceQ q(CombineSepGives iprop(□ $outAs') $out2 $newOutGives2)

      match instGives1, instGives2 with
      | none, none =>
        match matchBool p, matchBool p2 with
        | .inl _, .inl _ => return { origHyps, newHyps := hyps2, p := q(true), outAs' := newOutAs, pfAs := newPfAs, outGives' := none, pfGives := ⟨⟩ }
        | _,      _      => return { origHyps, newHyps := hyps2, p := q(false), outAs' := newOutAs, pfAs := newPfAs, outGives' := none, pfGives := ⟨⟩ }

      | some instGives1, _ =>
        let pf : Q(($newE ∗ □ $newOutGives1 ⊢ $goal) → ($newE ⊢ $goal)) := q(combine_gives_step $instGives1 sep_elim_l $pfGives $pf2)

        match matchBool p, matchBool p2 with
        | .inl _, .inl _ => return { origHyps, newHyps := hyps2, p := q(true), outAs' := newOutAs, pfAs := newPfAs, outGives' := some newOutGives1, pfGives := q(dummy) }
        | _,      _      => return { origHyps, newHyps := hyps2, p := q(false), outAs' := newOutAs, pfAs := newPfAs, outGives' := some newOutGives1, pfGives := q(dummy) }

      | none, some instGives2 =>
        let pf' : Q(($newE ∗ □ $outAs' ⊢ $goal) → ($newE ⊢ $goal)) := q(dummy)
        let pf : Q(($newE ∗ □ $newOutGives2 ⊢ $goal) → ($newE ⊢ $goal)) := q(combine_gives_step $instGives2 sep_elim_l $pf' $pf2)

        match matchBool p, matchBool p2 with
        | .inl _, .inl _ => return { origHyps, newHyps := hyps2, p := q(true), outAs' := newOutAs, pfAs := newPfAs, outGives' := some newOutGives2, pfGives := q(dummy) }
        | _,      _      => return { origHyps, newHyps := hyps2, p := q(false), outAs' := newOutAs, pfAs := newPfAs, outGives' := some newOutGives2, pfGives := q(dummy) }

private def iCombineCore {u} {prop : Q(Type $u)} {bi}
    (hs : List (TSyntax `ident))
    (e : Q($prop))
    (hyps : Hyps bi e)
    (goal : Q($prop)) :
    ProofModeM (@CombineState u prop bi e goal) := do
  match hs with
  | h1 :: h2 :: htail =>
    -- Find the `IVarId` of the hypothesis
    let ivar1 ← hyps.findWithInfo h1
    let ivar2 ← hyps.findWithInfo h2

    -- Hypothesis in the spatial context should not be used multiple times
    if (hs.count h1 > 1 ∧ ¬isTrue (← hyps.findP h1)) ∨ (hs.count h2 > 1 ∧ ¬isTrue (← hyps.findP h2)) then
      throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

    let ⟨_, hyps1, out1, out1', p1, _, pf1⟩ := hyps.remove false ivar1
    let ⟨e2, hyps2, out2, out2', p2, _, pf2⟩ := hyps1.remove false ivar2

    let newOutAs ← mkFreshExprMVarQ _
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $out1' $out2' $newOutAs)

    let newOutGives ← mkFreshExprMVarQ _
    let instGives ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1 $out2 $newOutGives)

    -- let pf2 : Q($newE ⊣⊢ $e2 ∗ $out2) := pf2

    match matchBool p1, matchBool p2, instGives with
    | .inl _, .inl _, some instGives =>

      -- Initialise the mutable `CombineGivesState` instance
      let mut st : CombineState e goal := {
        p := q(true),
        outAs' := newOutAs,
        pfAs := q(dummy)
        newE := e2,
        origHyps := hyps,
        newHyps := hyps2,
        outGives' := some newOutGives,
        pfGives := q(combine_gives_step $instGives $(pf1).mpr $(pf1).mp.trans $pf2)
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h
        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
        -- Iteratively handle the remaining hypotheses
        st ← st.combineProofModeHyp ivar

      return st

    | .inl _, .inl _, none =>

      -- Initialise the mutable `CombineGivesState` instance
      let mut st : CombineState e goal := {
        p := q(true),
        outAs' := newOutAs,
        pfAs := q(dummy)
        newE := e2,
        origHyps := hyps,
        newHyps := hyps2,
        outGives' := none,
        pfGives := ⟨⟩
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h
        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
        -- Iteratively handle the remaining hypotheses
        st ← st.combineProofModeHyp ivar

      return st

    | _, _, some instGives =>

      -- Initialise the mutable `CombineGivesState` instance
      let mut st : CombineState e goal := {
        p := q(false),
        outAs' := newOutAs,
        pfAs := q(dummy)
        newE := e2,
        origHyps := hyps,
        newHyps := hyps2,
        outGives' := some newOutGives,
        pfGives := q(combine_gives_step $instGives $(pf1).mpr $(pf1).mp.trans $pf2)
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h
        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
        -- Iteratively handle the remaining hypotheses
        st ← st.combineProofModeHyp ivar

      return st

    | _, _, none =>

      -- Initialise the mutable `CombineGivesState` instance
      let mut st : CombineState e goal := {
        p := q(false),
        outAs' := newOutAs,
        pfAs := q(dummy)
        newE := e2,
        origHyps := hyps,
        newHyps := hyps2,
        outGives' := none,
        pfGives := ⟨⟩
      }

      for h in htail do
        -- Find the `IVarId` of the hypothesis
        let ivar ← hyps.findWithInfo h
        -- Hypothesis in the spatial context should not be used multiple times
        if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
          throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"
        -- Iteratively handle the remaining hypotheses
        st ← st.combineProofModeHyp ivar

      return st

  | [h1] =>
    let ivar ← hyps.findWithInfo h1
    let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove false ivar

    if (hs.count h1 > 1 ∧ ¬isTrue (← hyps.findP h1)) then
      throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

    -- Initialise a mutable instance of `CombineAsState`
    let mut st : CombineState e goal :=
      { origHyps := hyps, newHyps := hyps1, p := p1, outAs' := out1', pfAs := q($(pf1).mp.trans), outGives' := some q(iprop(True)), pfGives := q(dummy) }

    return st

  | _ =>
    let mut st : CombineState e goal :=
    { origHyps := hyps, newHyps := hyps, p := q(true), outAs' := q(emp), pfAs := q(combine_as_nil), outGives' := some q(iprop(True)), pfGives := q(dummy) }

    return st

/-- The tactic `icombine` combines propositions into one using the type
    class `CombineSepAs`. By default, the separating conjunction is used
    as the connective. -/
elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs e hyps goal
    let pf' ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.outAs' addBIGoal
    mvar.assign q($(st.pfAs) $pf')

/-- The tactic `icombine` with `gives` syntax combines propositions to derive
    new information in the intutionisitic context using the type class
    `CombineSepGives`. It is possible that no type class instance is
    applicable -/
elab "icombine" idents:(colGt ident)* "gives" colGt patGives:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { e, hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs e hyps goal

    match st.outGives', st.pfGives with
    | some outGives', pfGives =>
      let pf' ← iCasesCore _ st.origHyps goal pat q(true) outGives' addBIGoal
      mvar.assign q($pfGives $pf')
    | none, _ => throwError "icombine: no type class instance to combine propositions"

elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat "gives" colGt patGives:icasesPat : tactic => do
  let pat1 ← liftMacroM <| iCasesPat.parse patAs
  let pat2 ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { prop, e, hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs e hyps goal

    match st.outGives', st.pfGives with
    | some outGives', pfGives =>

      let pf'' ← iCasesCore _ st.newHyps goal pat1 q($(st.p)) st.outAs'
        (fun myHyps myGoal => iCasesCore _ myHyps myGoal pat2 q(true) outGives' addBIGoal)

      mvar.assign q($st.pfAs $pf'')

    | none, _ => throwError "icombine: no type class instance to combine propositions"
