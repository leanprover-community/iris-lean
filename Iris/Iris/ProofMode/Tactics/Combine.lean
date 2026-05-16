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
theorem combine_gives_nil_singleton [BI PROP] {e goal : PROP} (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := calc
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

/--
  This function takes in an instance of `CombineState` and handles one
  hypothesis at a time. This function is called by `iCombineCore` iteratively
  for every hypotheses being combined.
-/
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

/--
  A hypothesis in the spatial context should not be used as an argument of
  the `icombine` tactic multiple times. This function ensures this is satisfied
  and prints a pretty error otherwise.
-/
private def checkSpatialContextHyp {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (hs : List (TSyntax `ident)) (hyps : Hyps bi e) (h : TSyntax `ident) :
    ProofModeM Unit := do
  if hs.count h > 1 ∧ ¬isTrue (← hyps.findP h) then
    throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

/--
  The `iCombineCore` function takes the hypotheses (`hyps`) and the goal
  (`goal`) of an Iris proof state, as well as the idents of hypotheses
  to be combined (`hs`). It then initialises an instance of `CombineState`,
  iteratively calls `CombineState.combineProofMode` for each hypothesis in `hs`
  and returns the instance.
-/
private def iCombineCore {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (hs : List (TSyntax `ident))
    (hyps : Hyps bi e)
    (goal : Q($prop)) :
    ProofModeM (@CombineState u prop bi e goal) := do
  match hs with
  /-
    Trivial case when no hypothesis is given as an argument for the tactic:
    introduce `□ emp` for the `as` syntax and `□ True` for the `gives` syntax.
  -/
  | [] =>
    return { origHyps := hyps, newHyps := hyps,
             p := q(true), outAs' := q(emp), pfAs := q(combine_as_nil),
             outGives' := some q(iprop(True)), pfGives := q(combine_gives_nil_singleton) }
  /-
    Trivial case when one hypothesis is given as an argument for the tactic:
    introduce the combined hypothesis unchanged for the `as` syntax and
    `□ True` for the `gives` syntax.
  -/
  | [h1] =>
    let ivar ← hyps.findWithInfo h1
    let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove false ivar
    return { origHyps := hyps, newHyps := hyps1,
             p := p1, outAs' := out1', pfAs := q($(pf1).mp.trans),
             outGives' := some q(iprop(True)), pfGives := q(combine_gives_nil_singleton) }
  /-
    Non-trivial case when two or more hypotheses are given as arguments for
    the tactic.
  -/
  | h1 :: h2 :: htail =>
    -- Find the `IVarId` values of the hypotheses and apply removal
    let ivar1 ← hyps.findWithInfo h1
    let ivar2 ← hyps.findWithInfo h2
    checkSpatialContextHyp hs hyps h1
    checkSpatialContextHyp hs hyps h2
    let ⟨_, hyps1, out1, out1', p1, _, pf1⟩ := hyps.remove false ivar1
    let ⟨e2, hyps2, out2, out2', p2, _, pf2⟩ := hyps1.remove false ivar2

    -- Search for the type class instance for the `as` syntax
    let newOutAs ← mkFreshExprMVarQ _
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $out1' $out2' $newOutAs)
    let pfAs : Q(($e2 ∗ □?($p1 && $p2) $newOutAs ⊢ $goal) → $e ⊢ $goal) :=
      q(combine_as_step $instAs $(pf1).mp.trans $(pf2).mp)

    -- Search for the type class instance for the `gives` syntax
    let newOutGives ← mkFreshExprMVarQ _
    let instGives ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out1 $out2 $newOutGives)

    -- Initialise the mutable `CombineState` instance with the first two hypotheses combined
    let mut st : CombineState e goal :=
      match matchBool p1, matchBool p2, instGives with
      | .inl _, .inl _, some instGives =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(true), outAs' := newOutAs, pfAs,
          outGives' := some newOutGives,
          pfGives := q(combine_gives_step $instGives $(pf1).mpr $(pf1).mp.trans $pf2) }
      | .inl _, .inl _, none =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(true), outAs' := newOutAs, pfAs,
          outGives' := none, pfGives := ⟨⟩ }
      | _, _, some instGives =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(false), outAs' := newOutAs, pfAs,
          outGives' := some newOutGives,
          pfGives := q(combine_gives_step $instGives $(pf1).mpr $(pf1).mp.trans $pf2) }
      | _, _, none =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(false), outAs' := newOutAs, pfAs,
          outGives' := none, pfGives := ⟨⟩ }

    -- Handle the remaining hypotheses that are given as tactic arguments
    for h in htail do
      -- Find the `IVarId` of the hypothesis
      let ivar ← hyps.findWithInfo h
      -- Hypothesis in the spatial context should not be used multiple times
      checkSpatialContextHyp hs hyps h
      -- Iteratively handle the remaining hypotheses
      st ← st.combineProofModeHyp ivar

    return st

/-- The tactic `icombine` combines propositions into one using the type
    class `CombineSepAs`. By default, the separating conjunction is used
    as the connective. -/
elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs hyps goal
    let pf' ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.outAs' addBIGoal
    mvar.assign q($(st.pfAs) $pf')

/-- The tactic `icombine` with `gives` syntax combines propositions to derive
    new information in the intutionisitic context using the type class
    `CombineSepGives`. It is possible that no type class instance is
    applicable -/
elab "icombine" idents:(colGt ident)* "gives" colGt patGives:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs hyps goal

    match st.outGives', st.pfGives with
    | some outGives', pfGives =>
      let pf' ← iCasesCore _ st.origHyps goal pat q(true) outGives' addBIGoal
      mvar.assign q($pfGives $pf')
    | none, _ => throwError "icombine: no type class instance to combine propositions"

elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat "gives" colGt patGives:icasesPat : tactic => do
  let pat1 ← liftMacroM <| iCasesPat.parse patAs
  let pat2 ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs hyps goal

    match st.outGives', st.pfGives with
    | some outGives', _ =>
      let pf'' ← iCasesCore _ st.newHyps goal pat1 q($(st.p)) st.outAs'
        (fun myHyps myGoal => iCasesCore _ myHyps myGoal pat2 q(true) outGives' addBIGoal)
      -- TODO: find the correct proof to fill in the metavariable
      mvar.assign q($st.pfAs $pf'')
    | none, _ => throwError "icombine: no type class instance to combine propositions"
