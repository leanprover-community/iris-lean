/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang, Michael Sammler
-/
module

public meta import Iris.ProofMode.Tactics.Assumption
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.ClassesMake

namespace Iris.ProofMode

public meta section
open Lean Elab Tactic Meta Qq BI Std

/-- Auxiliary lemma for combining two hypotheses using `CombineSepAs` -/
theorem combine_as_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1 out2 out : PROP}
    (inst : CombineSepAs out2 out1 out)
    (pf1 : e ⊢ e1 ∗ □?p1 out1)
    (pf2 : e1 ⊢ e2 ∗ □?p2 out2) :
    e ⊢ e2 ∗ □?(p1 && p2) out := calc
  e ⊢ e1 ∗ □?p1 out1 := pf1
  _ ⊢ (e2 ∗ □?p2 out2) ∗ □?p1 out1    := sep_mono_left pf2
  _ ⊢ e2 ∗ □?p2 out2 ∗ □?p1 out1      := sep_assoc.mp
  _ ⊢ e2 ∗ □?p1 out1 ∗ □?p2 out2      := sep_mono_right sep_comm.mp
  _ ⊢ e2 ∗ □?(p1 && p2) (out1 ∗ out2) := sep_mono_right intuitionisticallyIf_sep_conj
  _ ⊢ e2 ∗ □?(p1 && p2) out           := sep_mono_right <| intuitionisticallyIf_mono <| sep_comm.mp.trans inst.combine_sep_as

/-- Auxiliary lemma for the base case where up to one hypothesis is given -/
theorem combine_gives_nil_singleton [BI PROP] {e : PROP} : e ⊢ e ∗ □ True :=
  sep_emp.mpr.trans <| sep_mono_right intuitionistically_true.mpr

/-- Auxiliary lemma for the step case for combining two hypotheses using `CombineSepGives` -/
theorem combine_gives_step [BI PROP] {p1 p2 : Bool} {e e1 e2 out1 out2 out : PROP}
    (inst : CombineSepGives out2 out1 out)
    (pf1 : e ⊣⊢ e1 ∗ □?p1 out1)
    (pf2 : e1 ⊣⊢ e2 ∗ □?p2 out2) :
    e ⊢ e ∗ □ out :=
  have pf3 : □?p1 out1 ∗ □?p2 out2 ⊢ <pers> out := calc
    _ ⊢ □?(p1 && p2) (out1 ∗ out2) := intuitionisticallyIf_sep_conj
    _ ⊢ □?(p1 && p2) <pers> out    := intuitionisticallyIf_mono <| sep_comm.mp.trans inst.combine_sep_gives
    _ ⊢ <pers> out                 := intuitionisticallyIf_elim
  calc
    e ⊢ e1 ∗ □?p1 out1                                   := pf1.mp
    _ ⊢ (e2 ∗ □?p2 out2) ∗ □?p1 out1                     := sep_mono_left pf2.mp
    _ ⊢ e2 ∗ □?p2 out2 ∗ □?p1 out1                       := sep_assoc.mp
    _ ⊢ e2 ∗ □?p1 out1 ∗ □?p2 out2                       := sep_mono_right sep_comm.mp
    _ ⊢ (e2 ∗ □?p1 out1 ∗ □?p2 out2) ∧ (e2 ∗ <pers> out) := and_intro refl <| sep_mono_right pf3
    _ ⊢ (e2 ∗ □?p1 out1 ∗ □?p2 out2) ∧ <pers> out        := and_mono_right sep_elim_right
    _ ⊢ (e2 ∗ □?p1 out1 ∗ □?p2 out2) ∗ □ out             := persistently_and_intuitionistically_sep_right.mp
    _ ⊢ (e2 ∗ □?p2 out2 ∗ □?p1 out1) ∗ □ out             := sep_mono_left <| sep_mono_right sep_comm.mp
    _ ⊢ ((e2 ∗ □?p2 out2) ∗ □?p1 out1) ∗ □ out           := sep_mono_left sep_assoc.mpr
    _ ⊢ (e1 ∗ □?p1 out1) ∗ □ out                         := sep_mono_left <| sep_mono_left pf2.mpr
    _ ⊢ e ∗ □ out                                        := sep_mono_left pf1.mpr

/-- Auxiliary lemma for combining hypotheses derived using `CombineSepGives`
    by conjunction -/
theorem combine_gives_step_conj [BI PROP] {p1 p2 : Bool}
    {e e1 e2 outGives newOutGives outGivesCombined out1 out2 : PROP}
    (instGives : CombineSepGives out2 out1 newOutGives)
    (instGivesCombined : MakeAnd outGives newOutGives outGivesCombined)
    (pf1 : e ⊢ e ∗ □ outGives)
    (pf2 : e ⊢ e1 ∗ □?p1 out1)
    (pf3 : e1 ⊣⊢ e2 ∗ □?p2 out2) :
    e ⊢ e ∗ □ outGivesCombined :=
  have pf4 : e ∗ □ outGives ⊢ <pers> outGives :=
    (sep_mono_right persistently_of_intuitionistically).trans persistently_absorb_right
  have pf5 : e ∗ □ outGives ⊢ <pers> newOutGives := calc
    _ ⊢ e                            := sep_elim_left
    _ ⊢ e1 ∗ □?p1 out1               := pf2
    _ ⊢ (e2 ∗ □?p2 out2) ∗ □?p1 out1 := sep_mono_left pf3.mp
    _ ⊢ e2 ∗ □?p2 out2 ∗ □?p1 out1   := sep_assoc.mp
    _ ⊢ e2 ∗ out2 ∗ out1             := sep_mono_right <| sep_mono intuitionisticallyIf_elim intuitionisticallyIf_elim
    _ ⊢ e2 ∗ <pers> newOutGives      := sep_mono_right instGives.combine_sep_gives
    _ ⊢ <pers> newOutGives           := persistently_absorb_right
  calc
    _ ⊢ e ∗ □ outGives                                          := pf1
    _ ⊢ (e ∗ □ outGives) ∧ <pers> outGives ∧ <pers> newOutGives := and_intro refl <| and_intro pf4 pf5
    _ ⊢ (e ∗ □ outGives) ∧ <pers> (outGives ∧ newOutGives)      := and_mono_right <| persistently_and.mpr
    _ ⊢ (e ∗ □ outGives) ∧ <pers> outGivesCombined              := and_mono_right <| persistently_mono instGivesCombined.make_and.mp
    _ ⊢ (e ∗ □ outGives) ∗ □ outGivesCombined                   := persistently_and_intuitionistically_sep_right.mp
    _ ⊢ e ∗ □ outGivesCombined                                  := sep_mono_left sep_elim_left

theorem combine_as_gives [BI PROP] {p : Bool} {newE e outAs outGives goal : PROP}
    (pfAs : e ⊢ newE ∗ □?p outAs)
    (pfGives : e ⊢ e ∗ □ outGives)
    (pfAsGives : newE ∗ □?p (outAs ∗ □ outGives) ⊢ goal) :
    e ⊢ goal := calc
  e ⊢ e ∗ □ outGives := pfGives
  _ ⊢ (newE ∗ □?p outAs) ∗ □ outGives   := sep_mono_left pfAs
  _ ⊢ newE ∗ □?p outAs ∗ □ outGives     := sep_assoc.mp
  _ ⊢ newE ∗ □?p outAs ∗ □?p □ outGives := sep_mono_right <| sep_mono_right intuitionisticallyIf_intutitionistically.mpr
  _ ⊢ newE ∗ □?p (outAs ∗ □ outGives)   := sep_mono_right intuitionisticallyIf_sep_mpr
  _ ⊢ goal := pfAsGives

/--
  The `icombine` tactic with the `as` syntax transforms the hypotheses
  corresponding to `origE` into `newE ∗ □?$p $outAs`, where `outAs` is the
  combined hypotheses and `newE` corresponds to all remaining hypotheses.
  The value of `p` should be `q(true)` if and only if all hypotheses
  given as arguments for the tactic exist in the intuitionistic context.
  The tactic with the `gives` syntax allows one to derive an additional
  hypothesis in the intuitionistic context without changing existing hypotheses.
-/
private structure CombineState {u} {prop : Q(Type u)} {bi} (origE goal : Q($prop)) where
  -- The remaining hypotheses after combining hypotheses
  {newE : Q($prop)}
  (newHyps : Hyps bi newE)
  -- The combined hypothesis for the `as` syntax
  {p : Q(Bool)}
  {outAs : Q($prop)}
  -- The proof for the `as` syntax
  (pfAs : Q($origE ⊢ $newE ∗ □?$p $outAs))
  -- The additional persistent hypothesis for the `gives` syntax
  (outGives : Option Q($prop))
  -- The proof for the `gives` syntax
  (pfGives : match outGives with
    | none => PUnit
    | some outGives => Q($origE ⊢ $origE ∗ □ $outGives))

/--
  This function takes in an instance of `CombineState` and handles one
  hypothesis at a time. This function is called by `iCombineCore` iteratively
  for every hypotheses being combined.
-/
private def CombineState.combineProofModeHyp {u prop bi origE goal} :
    @CombineState u prop bi origE goal → IVarId →
    ProofModeM (@CombineState u prop bi origE goal)
  | { newHyps, p := p1, outAs, pfAs, outGives, pfGives, .. }, ivar => do
    let some (_, ⟨_, hyps2, _, out2, p2, _, pf2⟩) ←
        newHyps.removeG false <| fun _ ivar' _ _ => return guard <| ivar' == ivar
    | throwError "icombine: propositions in the spatial context cannot be used as arguments multiple times"

    -- Type class instance search for the `as` syntax
    let newOutAs ← mkFreshExprMVarQ q($prop)
    let instAs ← ProofModeM.synthInstanceQ q(CombineSepAs $out2 $outAs $newOutAs)
    let newPfAs := q(combine_as_step $instAs $pfAs $(pf2).mp)

    match outGives, pfGives with
    -- No persistent information derived in the previous step: `gives` syntax fails
    | none, _ =>
      return {
        newHyps := hyps2, p := conj p1 p2, outAs := newOutAs, pfAs := newPfAs,
        outGives := none, pfGives := ⟨⟩
      }
    | some outGives, pfGives =>
      -- Type class instance search for the `gives` syntax
      let newOutGives ← mkFreshExprMVarQ q($prop)
      let instGives ← ProofModeM.trySynthInstanceQ q(CombineSepGives $out2 $outAs $newOutGives)

      match instGives with
      -- No persistent information derived in the current step: `gives` syntax fails
      | none =>
        return {
          newHyps := hyps2, p := conj p1 p2, outAs := newOutAs, pfAs := newPfAs,
          outGives := none, pfGives := ⟨⟩
        }
      -- Combine the existing and new persistent information using the conjunction
      | some instGives =>
        let newOutGivesCombined ← mkFreshExprMVarQ q($prop)
        let instGivesCombined ← ProofModeM.synthInstanceQ q(MakeAnd $outGives $newOutGives $newOutGivesCombined)
        return {
          newHyps := hyps2, p := conj p1 p2, outAs := newOutAs, pfAs := newPfAs,
          -- The `gives` syntax produces the conjunction of the two pieces of persistent information
          outGives := some newOutGivesCombined,
          pfGives := q(combine_gives_step_conj $instGives $instGivesCombined $pfGives $pfAs $pf2)
        }

/--
  The `iCombineCore` function takes the hypotheses (`hyps`) and the goal
  (`goal`) of an Iris proof state, as well as the idents of hypotheses
  to be combined (`hs`). It then initialises an instance of `CombineState`,
  iteratively calls `CombineState.combineProofMode` for each hypothesis in `hs`
  and returns the instance.
-/
private def iCombineCore {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (ivars : List IVarId) (hyps : Hyps bi e) (goal : Q($prop)) :
    ProofModeM (@CombineState u prop bi e goal) := do
  match ivars.reverse with
  | [] =>
    return { newHyps := hyps, p := q(true), outAs := q(emp),
             pfAs := q(sep_emp.mpr.trans <| sep_mono_right intuitionistically_emp.mpr),
             outGives := some q(iprop(True)), pfGives := q(combine_gives_nil_singleton) }
  | ivar :: ivars =>
    -- Apply removal of the hypotheses
    let ⟨_, hyps1, _, out1, p1, _, pf1⟩ := hyps.remove false ivar

    -- Initialise the mutable `CombineState` instance
    let mut st : CombineState e goal :=
      { newHyps := hyps1, p := p1, outAs := out1, pfAs := q($(pf1).mp),
        outGives := some q(iprop(True)), pfGives := q(combine_gives_nil_singleton) }

    -- Iteratively handle the remaining hypotheses that are given as tactic arguments
    for i in ivars do
      st ← st.combineProofModeHyp i

    return st

/-- Parse the selection patterns and return a list of `IVarID` values. -/
private def iCombineParseSelPats {u} {prop : Q(Type $u)} {bi} {e : Q($prop)}
    (hyps : Hyps bi e) (patSels : TSyntaxArray `selPat) :
    ProofModeM (List IVarId) := do
  let selPats ← liftMacroM <| SelPat.parse patSels
  let targets ← SelPat.resolve hyps selPats
  targets.mapM fun t =>
    match t.kind with
    | .ipm iVarId => pure iVarId
    | .pure _      => throwError "icombine: invalid selection pattern with pure propositions"

private def throwNoInstanceForGives : ProofModeM Unit := do
  throwError "icombine: no type class instance to combine propositions"

/--
  `icombine patSels as patAs` combines the hypotheses specified by the selection
  pattern `patSels` into one using the `CombineSepAs` type class. The combined
  hypothesis is then destructed using the case pattern `patAs`

  If no other type class instance for `CombineSepAs` is found, the separating
  conjunction is used as the connective.
-/
elab "icombine" patSels:(colGt selPat)* "as" colGt patAs:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patAs

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs ← iCombineParseSelPats hyps patSels
    let st ← iCombineCore hs hyps goal

    let pf ← iCasesCore _ st.newHyps goal pat q($(st.p)) st.outAs addBIGoal
    mvar.assign q($(st.pfAs).trans $pf)

/--
  `icombine patSels gives patAs` combines the hypotheses specified by the
  selection pattern `patSels` to derive new information into the intuitionistic
  context using the type class `CombineSepGives`. The new intuitionistic
  hypothesis is then destructed using the case pattern `patGives`.

  The tactic fails if no applicable type class instance of `CombineSepGives` is
  found.
-/
elab "icombine" patSels:(colGt selPat)* "gives" colGt patGives:icasesPat : tactic => do
  let pat ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs ← iCombineParseSelPats hyps patSels
    let st ← iCombineCore hs hyps goal

    match st.outGives, st.pfGives with
    | some outGives, pfGives =>
      let pf ← iCasesCore _ hyps goal pat q(true) outGives addBIGoal
      mvar.assign q($(pfGives).trans $pf)
    | none, _ => throwNoInstanceForGives

/--
  `icombine patSels as patAs gives patGives` combines the hypotheses specified
  by the selection pattern `patSels` into one using the `CombineSepAs` type
  class. The combined hypothesis is then destructed using the case pattern
  `patAs`. Meanwhile, it also combines the hypotheses to derive new information
  into the intuitionistic context using the type class `CombineSepGives` and
  destructs the new intuitionistic hypothesis using the case pattern `patGives`.

  This is equivalent to using the tactic `icombine patSels gives patGives` and
  then `icombine patSels as patAs`.

  The tactic fails if no applicable type class instance of `CombineSepGives` is
  found.
-/
elab "icombine" patSels:(colGt selPat)* "as" colGt patAs:icasesPat "gives" colGt patGives:icasesPat : tactic => do
  let pat1 ← liftMacroM <| iCasesPat.parse patAs
  let pat2 ← liftMacroM <| iCasesPat.parse patGives

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    let hs ← iCombineParseSelPats hyps patSels
    let st ← iCombineCore hs hyps goal

    match st.outGives, st.pfGives with
    | some outGives, pfGives =>
      let pf ← iCasesCore _ st.newHyps goal (.conjunction [pat1, .intuitionistic pat2])
        q($st.p) q(iprop($st.outAs ∗ □ $outGives)) addBIGoal
      mvar.assign q(combine_as_gives $st.pfAs $pfGives $pf)
    | none, _ => throwNoInstanceForGives
