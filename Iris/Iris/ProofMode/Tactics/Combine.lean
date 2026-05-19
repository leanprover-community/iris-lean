/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

/-- Auxilary lemma for the step case with two or more hypotheses -/
theorem combine_as_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1' out2' out : PROP}
    (inst : CombineSepAs out2' out1' out)
    (pf1 : e ⊢ e1 ∗ □?p1 out1')
    (pf2 : e1 ⊢ e2 ∗ □?p2 out2') :
    e ⊢ e2 ∗ □?(p1 && p2) out := calc
  e ⊢ e1 ∗ □?p1 out1' := pf1
  _ ⊢ (e2 ∗ □?p2 out2') ∗ □?p1 out1'    := sep_mono_l pf2
  _ ⊢ e2 ∗ □?p2 out2' ∗ □?p1 out1'      := sep_assoc.mp
  _ ⊢ e2 ∗ □?p1 out1' ∗ □?p2 out2'      := sep_mono_r sep_comm.mp
  _ ⊢ e2 ∗ □?(p1 && p2) (out1' ∗ out2') := sep_mono_r intuitionisticallyIf_sep_conj
  _ ⊢ e2 ∗ □?(p1 && p2) out             := sep_mono_r <| intuitionisticallyIf_mono <| sep_comm.mp.trans inst.combine_sep_as

/-- Auxilary lemma for the base case where up to one hypothesis is given -/
theorem combine_gives_nil_singleton [BI PROP] {e goal : PROP} (pf : e ∗ □ True ⊢ goal) : e ⊢ goal := calc
  e ⊢ e ∗ emp    := sep_emp.mpr
  _ ⊢ e ∗ □ True := sep_mono_r intuitionistically_true.mpr
  _ ⊢ goal       := pf

/-- Auxilary lemma for the step case where multiple hypotheses are given -/
theorem combine_gives_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1' out2' out goal : PROP}
    (inst : CombineSepGives out2' out1' out)
    (pf1 : e ⊣⊢ e1 ∗ □?p1 out1')
    (pf2 : e1 ⊣⊢ e2 ∗ □?p2 out2')
    (pf3 : e ∗ □ out ⊢ goal) : e ⊢ goal := by
  have pf4 : □?p1 out1' ∗ □?p2 out2' ⊢ <pers> out := calc
    _ ⊢ □?(p1 && p2) (out1' ∗ out2') := intuitionisticallyIf_sep_conj
    _ ⊢ □?(p1 && p2) <pers> out      := intuitionisticallyIf_mono <| sep_comm.mp.trans inst.combine_sep_gives
    _ ⊢ <pers> out                   := intuitionisticallyIf_elim
  calc
    e ⊢ e1 ∗ □?p1 out1'                                     := pf1.mp
    _ ⊢ (e2 ∗ □?p2 out2') ∗ □?p1 out1'                      := sep_mono_l pf2.mp
    _ ⊢ e2 ∗ □?p2 out2' ∗ □?p1 out1'                        := sep_assoc.mp
    _ ⊢ e2 ∗ □?p1 out1' ∗ □?p2 out2'                        := sep_mono_r sep_comm.mp
    _ ⊢ (e2 ∗ □?p1 out1' ∗ □?p2 out2') ∧ (e2 ∗ <pers> out)  := and_intro refl <| sep_mono_r pf4
    _ ⊢ (e2 ∗ □?p1 out1' ∗ □?p2 out2') ∧ <pers> out         := and_mono_r sep_elim_r
    _ ⊢ (e2 ∗ □?p1 out1' ∗ □?p2 out2') ∗ □ out              := persistently_and_intuitionistically_sep_r.mp
    _ ⊢ (e2 ∗ □?p2 out2' ∗ □?p1 out1') ∗ □ out              := sep_mono_l <| sep_mono_r sep_comm.mp
    _ ⊢ ((e2 ∗ □?p2 out2') ∗ □?p1 out1') ∗ □ out            := sep_mono_l sep_assoc.mpr
    _ ⊢ (e1 ∗ □?p1 out1') ∗ □ out                           := sep_mono_l <| sep_mono_l pf2.mpr
    _ ⊢ e ∗ □ out                                           := sep_mono_l pf1.mpr
    _ ⊢ goal                                                := pf3

theorem combine_gives_step_conj [BI PROP] {p1 p2 : Bool}
    {e e1 e2 outGives newOutGives outGivesCombined out1' out2' : PROP}
    (instGives : CombineSepGives out2' out1' newOutGives)
    (instGivesCombined : MakeAnd outGives newOutGives outGivesCombined)
    (pf1 : (e ∗ □ outGives ⊢ goal) → e ⊢ goal)
    (pf2 : e ⊢ e1 ∗ □?p1 out1')
    (pf3 : e1 ⊣⊢ e2 ∗ □?p2 out2')
    (pf4 : e ∗ □ outGivesCombined ⊢ goal) : e ⊢ goal := by
  apply pf1
  have pf5 : e ∗ □ outGives ⊢ <pers> outGives := calc
    _ ⊢ e ∗ <pers> outGives := sep_mono_r persistently_of_intuitionistically
    _ ⊢ <pers> outGives     := persistently_absorb_r
  have pf6 : e ∗ □ outGives ⊢ <pers> newOutGives := calc
    _ ⊢ e                              := sep_elim_l
    _ ⊢ e1 ∗ □?p1 out1'                := pf2
    _ ⊢ (e2 ∗ □?p2 out2') ∗ □?p1 out1' := sep_mono_l pf3.mp
    _ ⊢ e2 ∗ □?p2 out2' ∗ □?p1 out1'   := sep_assoc.mp
    _ ⊢ e2 ∗ out2' ∗ out1'             := sep_mono_r <| sep_mono intuitionisticallyIf_elim intuitionisticallyIf_elim
    _ ⊢ e2 ∗ <pers> newOutGives        := sep_mono_r instGives.combine_sep_gives
    _ ⊢ <pers> newOutGives             := persistently_absorb_r
  calc
    _ ⊢ (e ∗ □ outGives) ∧ <pers> outGives ∧ <pers> newOutGives := and_intro refl <| and_intro pf5 pf6
    _ ⊢ (e ∗ □ outGives) ∧ <pers> (outGives ∧ newOutGives)      := and_mono_r <| persistently_and.mpr
    _ ⊢ (e ∗ □ outGives) ∧ <pers> outGivesCombined              := and_mono_r <| persistently_mono instGivesCombined.make_and.mp
    _ ⊢ (e ∗ □ outGives) ∗ □ outGivesCombined                   := persistently_and_intuitionistically_sep_r.mp
    _ ⊢ e ∗ □ outGivesCombined                                  := sep_mono_l sep_elim_l
    _ ⊢ goal                                                    := pf4

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
  (pfAs : Q($origE ⊢ $newE ∗ □?$p $outAs'))
  -- The derived additional hypothesis for the `gives` syntax
  (outGives' : Option Q($prop))
  -- The proof for the `gives` syntax
  (pfGives : match outGives' with
    | none => PUnit
    | some outGives' => Q(($origE ∗ □ $outGives' ⊢ $goal) → $origE ⊢ $goal))

/--
  Given two values `p1` and `p2`, check whether both are syntactically
  `q(true)` and, if so, return `q(true)`. Otherwise, return `q(false)`.
  This is useful for determining whether the combined hypothesis should
  exist in the intuitionistic context or the spatial context.
-/
private def pConj (p1 p2 : Q(Bool)) : Q(Bool) :=
  match matchBool p1, matchBool p2 with
  | .inl _, .inl _ => q(true)
  | _, _           => q(false)

/--
  This function takes in an instance of `CombineState` and handles one
  hypothesis at a time. This function is called by `iCombineCore` iteratively
  for every hypotheses being combined.
-/
private def CombineState.combineProofModeHyp {u prop bi origE goal} :
    @CombineState u prop bi origE goal → IVarId →
    ProofModeM (@CombineState u prop bi origE goal)
  | { origHyps, newHyps, p, outAs', pfAs, outGives', pfGives, .. }, ivar => do
    let ⟨_, hyps2, _, out2', p2, _, pf2⟩ := newHyps.remove false ivar

    -- Type class instance search for the `as` syntax
    let newOutAs ← mkFreshExprMVarQ _
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $out2' $outAs' $newOutAs)
    let newPfAs := q(combine_as_step $instAs $pfAs $(pf2).mp)

    -- Type class instance search for the `gives` syntax
    let newOutGives ← mkFreshExprMVarQ _
    let instGives ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out2' $outAs' $newOutGives)

    match instGives, outGives', pfGives with
    -- No additional persistent information derived, `outGives'` remains unchanged
    | none, _, _ =>
      return {
        origHyps, newHyps := hyps2,
        p := pConj p p2, outAs' := newOutAs, pfAs := newPfAs,
        -- The `gives` syntax should fail
        outGives' := none, pfGives := ⟨⟩
      }
    -- Persistent information derived at this step but not in the previous step
    | _, none, _ =>
      return {
        origHyps, newHyps := hyps2,
        p := pConj p p2, outAs' := newOutAs, pfAs := newPfAs,
        -- The `gives` syntax should fail
        outGives' := none, pfGives := ⟨⟩
      }
    -- Persistent information derived in addition to the existing `outGives'`
    | some instGives, some outGives', pfGives =>

      -- Combine the existing and new persistent information using the conjunction
      let newOutGivesCombined ← mkFreshExprMVarQ _
      let instGivesCombined ← ProofModeM.synthInstanceQ q(MakeAnd $outGives' $newOutGives $newOutGivesCombined)

      return {
        origHyps, newHyps := hyps2,
        p := pConj p p2, outAs' := newOutAs, pfAs := newPfAs,
        -- The `gives` syntax produces the conjunction of the two pieces of persistent information
        outGives' := some newOutGivesCombined,
        pfGives := q(combine_gives_step_conj $instGives $instGivesCombined $pfGives $pfAs $pf2)
      }

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
  match hs.reverse with
  /-
    Trivial case when no hypothesis is given as an argument for the tactic:
    introduce `□ emp` for the `as` syntax and `□ True` for the `gives` syntax.
  -/
  | [] =>
    return { origHyps := hyps, newHyps := hyps,
             p := q(true), outAs' := q(emp),
             pfAs := q(sep_emp.mpr.trans <| sep_mono_r intuitionistically_emp.mpr),
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
             p := p1, outAs' := out1', pfAs := q($(pf1).mp),
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
    let ⟨_, hyps1, _, out1', p1, _, pf1⟩ := hyps.remove false ivar1
    let ⟨e2, hyps2, _, out2', p2, _, pf2⟩ := hyps1.remove false ivar2

    -- Search for the type class instance for the `as` syntax
    let newOutAs ← mkFreshExprMVarQ _
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $out2' $out1' $newOutAs)
    let pfAs : Q($e ⊢ ($e2 ∗ □?($p1 && $p2) $newOutAs)) :=
      q(combine_as_step $instAs $(pf1).mp $(pf2).mp)

    -- Search for the type class instance for the `gives` syntax
    let newOutGives ← mkFreshExprMVarQ _
    let instGives ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out2' $out1' $newOutGives)

    -- Initialise the mutable `CombineState` instance with the first two hypotheses combined
    let mut st : CombineState e goal :=
      match matchBool p1, matchBool p2, instGives with
      | .inl _, .inl _, some instGives =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(true), outAs' := newOutAs, pfAs,
          outGives' := some newOutGives,
          pfGives := q(combine_gives_step $instGives $pf1 $pf2) }
      | .inl _, .inl _, none =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(true), outAs' := newOutAs, pfAs,
          outGives' := none, pfGives := ⟨⟩ }
      | _, _, some instGives =>
        { origHyps := hyps, newHyps := hyps2,
          p := q(false), outAs' := newOutAs, pfAs,
          outGives' := some newOutGives,
          pfGives := q(combine_gives_step $instGives $pf1 $pf2) }
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
    mvar.assign q($(st.pfAs).trans $pf')

private def throwNoInstanceForGives : ProofModeM Unit := do
  throwError "icombine: no type class instance to combine propositions"

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
    | none, _ => throwNoInstanceForGives

theorem pfAsGives_combine [BI PROP] {p : Bool} {newE e outAs' outGives' goal : PROP}
    (pfAs : e ⊢ newE ∗ □?p outAs')
    (pfGives : (e ∗ □ outGives' ⊢ goal) → e ⊢ goal)
    (pfAsGives : newE ∗ □?p (outAs' ∗ □ outGives') ⊢ goal) :
    e ⊢ goal := by
  apply pfGives
  calc
    _ ⊢ (newE ∗ □?p outAs') ∗ □ outGives'   := sep_mono_l pfAs
    _ ⊢ newE ∗ □?p outAs' ∗ □ outGives'     := sep_assoc.mp
    _ ⊢ newE ∗ □?p outAs' ∗ □?p □ outGives' := sep_mono_r <| sep_mono_r intuitionisticallyIf_intutitionistically.mpr
    _ ⊢ newE ∗ □?p (outAs' ∗ □ outGives')   := sep_mono_r intuitionisticallyIf_sep_2
    _ ⊢ goal := pfAsGives

elab "icombine" idents:(colGt ident)* "as" colGt patAs:icasesPat "gives" colGt patGives:icasesPat : tactic => do
  let pat1 ← liftMacroM <| iCasesPat.parse patAs
  let pat2 ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs := idents.toList
    let st ← iCombineCore hs hyps goal

    let outAs' := st.outAs'
    let pfAs := st.pfAs

    match st.outGives', st.pfGives with
    | some outGives', pfGives =>
      let pf' ← iCasesCore _ st.newHyps goal (.conjunction [pat1, .intuitionistic pat2])
        q($st.p) q(iprop($outAs' ∗ □ $outGives')) addBIGoal
      mvar.assign q(pfAsGives_combine $pfAs $pfGives $pf')
    | none, _ => throwNoInstanceForGives
