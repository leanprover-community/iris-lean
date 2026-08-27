/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.SpecPattern
public import Iris.ProofMode.Patterns.CasesPattern
public import Iris.ProofMode.Tactics.Trivial
public import Iris.ProofMode.Tactics.Frame

namespace Iris.ProofMode

public section
open BI

theorem specialize_wand [BI PROP] {q p : Bool} {A Q P1 P2 : PROP}
    (inst : IntoWand q p Q (.matching .argument) P1 P2) :
    (A ∗ □?p P1) ∗ □?q Q ⊢ A ∗ □?(p && q) P2 := by
  refine sep_assoc.mp.trans (sep_mono_right ?_)
  cases p with
  | false => exact (sep_mono_right inst.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □?q □ P1 ∗ □?q Q     := sep_mono_left intuitionisticallyIf_intutitionistically.mpr
    _ ⊢ □?q □ P1 ∗ □?q □?q Q := sep_mono_right intuitionisticallyIf_idem.mpr
    _ ⊢ □?q (□ P1 ∗ □?q Q)   := intuitionisticallyIf_sep_mpr
    _ ⊢ □?q P2               := intuitionisticallyIf_mono <| wand_elim_swap inst.into_wand

@[rocq_alias tac_specialize]
theorem specialize_wand_nest [BI PROP] {e e' e'' goal out out1' Q out2 : PROP}
    {p p1 q : Bool} (inst : IntoWand p q out (.matching .argument) Q out2)
    (h1 : e ⊣⊢ e' ∗ □?p1 out1')
    (h2 : (e'' ∗ □?q Q ⊢ □?p out -∗ goal) → e' ∗ □?p1 out1' ⊢ □?p out -∗ goal)
    (h3 : e'' ∗ □?(q && p) out2 ⊢ goal) : e ∗ □?p out ⊢ goal := by
  apply wand_elim_left_trans
  refine h1.mp.trans ?_
  refine h2 <| wand_intro ?_
  exact (specialize_wand inst).trans h3


/-
  TODO: if `p` is `true` and `e'` does not contain spatial hyps and `AddModal`
  is trivial, this proof can guarantee `□ P2` instead of `P2` in `h2`.
-/
-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/846ed45/iris/proofmode/coq_tactics.v#L336
@[rocq_alias tac_specialize_assert]
theorem specialize_wand_modal [BI PROP] {e e' goal R P1 P1' P2 : PROP} {p : Bool}
    (h1 : e ⊢ e' ∗ P1') (h2 : e' ∗ P2 ⊢ goal)
    (instWand : IntoWand p false R .unknown P1 P2)
    (instModal : AddModal P1' P1 goal) :
    e ∗ □?p R ⊢ goal := calc
  _ ⊢ (e' ∗ P1') ∗ □?p R                := sep_mono_left h1
  _ ⊢ (P1' ∗ e') ∗ □?p R                := sep_mono_left sep_comm.mp
  _ ⊢ P1' ∗ (e' ∗ □?p R)                := sep_assoc.mp
  _ ⊢ P1' ∗ (e' ∗ (P1 -∗ P2))           := sep_mono_right <| sep_mono_right instWand.into_wand
  _ ⊢ P1' ∗ ((P2 -∗ goal) ∗ (P1 -∗ P2)) := sep_mono_right <| sep_mono_left <| wand_intro h2
  _ ⊢ P1' ∗ (P1 -∗ goal)                := sep_mono_right <| sep_comm.mp.trans wand_trans
  _ ⊢ goal                              := instModal.add_modal

@[rocq_alias tac_specialize_assert_intuitionistic]
theorem specialize_wand_intuitionistic [BI PROP] {q : Bool} {A2 A3 Q P1' : PROP} P1 P2
    (instWand : IntoWand q true Q .unknown P1 P2) (instPers : Persistent P1)
    (instAbsorb : IntoAbsorbingly P1' P1) (h1 : A2 ⊢ A3 ∗ P1') : A2 ∗ □?q Q ⊢ A2 ∗ □?q P2 := by
  have h2 : □ P1 ∗ □?q Q ⊢ □?q P2 := by cases q with
  | false => exact (sep_mono_right instWand.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □ □ P1 ∗ □ □ Q          := sep_mono intuitionistically_idem.mpr intuitionistically_idem.mpr
    _ ⊢ □ (□ P1 ∗ □ Q)          := intuitionistically_sep_mpr
    _ ⊢ □ (□ P1 ∗ (□ P1 -∗ P2)) := intuitionistically_mono <| sep_mono_right instWand.into_wand
    _ ⊢ □?true P2               := intuitionistically_mono wand_elim_right
  have h3 : A2 ⊢ A2 ∗ □ P1 := calc
    _ ⊢ A2 ∧ A2                 := and_intro .rfl .rfl
    _ ⊢ A2 ∧ A3 ∗ P1'           := and_mono_right h1
    _ ⊢ A2 ∧ A3 ∗ <absorb> P1   := and_mono_right <| sep_mono_right into_absorbingly
    _ ⊢ A2 ∧ <absorb> P1        := and_mono_right <| sep_elim_right
    _ ⊢ A2 ∧ <absorb> <pers> P1 := and_mono_right <| absorbingly_mono Persistent.persistent
    _ ⊢ A2 ∧ <pers> P1          := and_mono_right absorbingly_persistently.mp
    _ ⊢ A2 ∗ □ P1               := persistently_and_intuitionistically_sep_right.mp
  calc
    _ ⊢ (A2 ∗ □ P1) ∗ □?q Q := sep_mono_left h3
    _ ⊢ A2 ∗ □ P1 ∗ □?q Q   := sep_assoc.mp
    _ ⊢ A2 ∗ □?q P2         := sep_mono_right h2

@[rocq_alias tac_forall_specialize, rocq_alias tac_specialize_assert_pure]
theorem specialize_forall [BI PROP] {p : Bool} {A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    (inst : IntoForall P Φ) (a : α) : A2 ∗ □?p P ⊢ A2 ∗ □?p (Φ a) :=
  sep_mono_right <| intuitionisticallyIf_mono <| inst.into_forall.trans (forall_elim a)

theorem specialize_dup_context [BI PROP] {P : PROP} {pa A P' pb B B'}
    (inst : IntoPersistently pb B B') (h1 : P ∗ □?pa A ⊢ P' ∗ □?pb B)
    (h2 : pa = true ∨ Affine A) : P ∗ □?pa A ⊢ P ∗ □ B' := by
  apply Entails.trans _ persistently_and_intuitionistically_sep_right.mp
  apply and_intro
  · cases h2 <;> subst_eqs <;> apply sep_elim_left
  · calc
      _ ⊢ P' ∗ □?pb B    := h1
      _ ⊢ P' ∗ <pers> B' :=
          sep_mono_right <| persistentlyIf_of_intuitionisticallyIf.trans into_persistently
      _ ⊢ <pers> B'      := sep_elim_right

#rocq_ignore tac_specialize_frame "Not needed as there is no locked in Lean"
#rocq_ignore tac_specialize_intuitionistic_helper
  "Functionality provided by Expr.lean infrastructure"
#rocq_ignore tac_specialize_intuitionistic_helper_done
  "Functionality provided by Expr.lean infrastructure"

public meta section
open Lean Elab Tactic Meta Qq Std

structure SpecializeState {prop : Q(Type u)} {bi : Q(BI $prop)} (orig goal : Q($prop)) where
  {e : Q($prop)} (hyps : Hyps bi e) (p : Q(Bool)) (out : Q($prop))
  pf : Q(($e ∗ □?$p $out ⊢ $goal) → $orig ⊢ $goal)

private def SpecializeState.updateCont {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {orig goal : Q($prop)} (st : @SpecializeState u prop bi orig goal)
    {e' : Q($prop)} (hyps' : Hyps bi e') (p' : Q(Bool)) (out' : Q($prop))
    (pfStep : Q(($e' ∗ □?$p' $out' ⊢ $goal) → $(st.e) ∗ □?$(st.p) $(st.out) ⊢ $goal)) :
    @SpecializeState u prop bi orig goal :=
  { hyps := hyps', p := p', out := out', pf := q(fun h => $(st.pf) ($pfStep h)) }

private def SpecializeState.update {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {orig goal : Q($prop)} (st : @SpecializeState u prop bi orig goal)
    {e' : Q($prop)} (hyps' : Hyps bi e') (p' : Q(Bool)) (out' : Q($prop))
    (pfStep : Q($(st.e) ∗ □?$(st.p) $(st.out) ⊢ $e' ∗ □?$p' $out')) :
    @SpecializeState u prop bi orig goal :=
  st.updateCont hyps' p' out' q($(pfStep).trans)

-- TODO: move this somewhere else?
private def synthIntoWand {u} {prop : Q(Type u)} (bi : Q(BI $prop))
    (p : Q(Bool)) (out : Q($prop)) (persistent : Bool) :
    ProofModeM <| (out1 : Q($prop)) × (out2 : Q($prop)) ×
      Q(IntoWand $p $persistent $out .unknown $out1 $out2) := do
  let out1 ← mkFreshExprMVarQ prop
  let out2 ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $persistent $out .unknown $out1 $out2)
    | throwIPMError "{out} is not a wand"
  return ⟨out1, out2, inst⟩

private def finishSubgoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (spec : Option <| SpecGoal × Name) :
    ProofModeM ((e' : Q($prop)) × Hyps bi e' × Q($e ⊢ $e' ∗ $goal)) := do
  match spec with
  -- Generate a subgoal, apply `itrivial` if `//` exists in the pattern
  | some ⟨{ negate, trivial, frame := frameIdents, hyps := hypIdents, .. }, name⟩ =>
    -- Hypotheses to be pass to the subgoal
    let ivars : IVarIdSet ← hypIdents.foldlM (return ·.insert <| ← hyps.findWithInfo ·) {}
    -- Hypotheses to be framed in the subgoal
    let mut frameIVars : List IVarId := []
    for i in frameIdents do
      let ivar ← hyps.findWithInfo i
      if frameIVars.contains ivar then
        throwIPMError "{i} used twice for framing"
      if ivars.contains ivar then
        throwIPMError "{i} cannot be used for both the subgoal and framing"
      frameIVars := ivar :: frameIVars
    frameIVars := frameIVars.reverse

    let ⟨el, _, hypsl, hypsr, pf'⟩ := Hyps.split bi
      (λ _ ivar => (negate ^^ ivars.contains ivar) || frameIVars.contains ivar) hyps
      -- let ⟨el, _, hypsl, hypsr, pf', frameIVars⟩ ← splitFrameHyps hyps hs f negate
    let res ← iFrame hypsr goal <| frameIVars.map (⟨.ipm ·, true⟩)
    let pf'' ← res.finish λ hyps goal => do
      if trivial then
        let some r ← iTrivial hyps goal
          | throwIPMError "itrivial could not solve\
              {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
        return r
      else addBIGoal hyps goal name
    return ⟨el, hypsl, q($(pf').mp.trans <| sep_mono_right $pf'')⟩
  -- Auto-framing: `[$]`, `[#$]` and `[>$]`
  | none =>
    let res ←
      (SelPat.resolve hyps [.spatial, .intuitionistic] .bottomToTop) >>=
      (iFrame hyps goal ·)
    let ⟨e', hyps', pf⟩ ← res.finishClose
    return ⟨e', hyps', pf⟩

/--
  For handling the specialisation patterns that generate subgoals.
  The argument `spec` is `none` for auto-framing (`[$]`, `[>$]` and `[#$]`).
  Otherwise, it is the `SpecGoal` value paired with the name for the subgoal.
  Keeping this function outside of the `mutual` block improves compilation time of this file.
-/
private def processSpecGoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {orig goal : Q($prop)}
    (specState : @SpecializeState u prop bi orig goal) (kind : SpecGoalKind)
    (spec : Option <| SpecGoal × Name) : ProofModeM (@SpecializeState u prop bi orig goal) := do
  let { hyps, p, out, .. } := specState
  match kind with
  -- Handle `[ H₁ … Hₙ ]`, `[- H₁ … Hₙ ]`, `[$]`, `[> H₁ … Hₙ ]`, `[>- H₁ … Hₙ ]` and `[>$]`
  | .spatial | .modal =>
    let ⟨out1, out2, inst⟩ ← synthIntoWand bi p out false
    -- add a modality using `AddModal` for the .modal case
    let ⟨out1', instModal⟩ : ((out1' : Q($prop)) × Q(AddModal $out1' $out1 $goal)) ←
      match kind with
      | .modal =>
        let out1' ← mkFreshExprMVarQ prop
        let some instModal ← ProofModeM.trySynthInstanceQ q(AddModal $out1' $out1 $goal)
          | throwIPMError "AddModal type class synthesis failed with {out1} and {goal}"
        pure ⟨out1', instModal⟩
      | _ /- .spatial -/ => pure ⟨out1, q(addModal_id _ _)⟩

    let ⟨_, hyps', pf⟩ ← finishSubgoal hyps out1' spec
    let pfStep := q((specialize_wand_modal $pf · $inst $instModal))
    return specState.updateCont hyps' q(false) out2 pfStep
  -- Handle `[# H₁ … Hₙ ]` and `[#$]`
  | .intuitionistic =>
    let spec : Option (SpecGoal × Name) ← spec.mapM fun ⟨sg, name⟩ => do
      unless sg.hyps.isEmpty do
        throwIPMError "cannot select hypotheses for intuitionistic premise"
      return ({ sg with negate := true }, name)
    let ⟨out1, out2, instWand⟩ ← synthIntoWand bi p out true
    let some instPers ← ProofModeM.trySynthInstanceQ q(Persistent $out1)
      | throwIPMError "{out1} is not persistent"
    let out1' ← mkFreshExprMVarQ prop
    let some instAbsorb ← ProofModeM.trySynthInstanceQ q(IntoAbsorbingly $out1' $out1)
      | throwIPMError "IntoAbsorbingly type class synthesis failed with {out1}"
    let ⟨_, _, pf⟩ ← finishSubgoal hyps out1' spec
    let pfStep := q(specialize_wand_intuitionistic $out1 $out2 $instWand $instPers $instAbsorb $pf)
    return specState.update hyps p out2 pfStep

mutual

partial def processWand {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {orig goal : Q($prop)}
    (specState : @SpecializeState u prop bi orig goal) (spat : SpecPat) :
    ProofModeM (@SpecializeState u prop bi orig goal) := do
  let { e, hyps, p, out, .. } := specState
  let ⟨ref, spat⟩ := spat
  withRef ref do
  match spat with
  -- A hypothesis name, possibly with nested specialisation patterns
  | .ident pmt =>
    let some ivar ← try? <| hyps.findWithInfo ⟨pmt.term⟩
      | throwIPMError "invalid hypothesis {pmt.term}"
    let ⟨_, hyps', _, out1', p1, _, pf'⟩ := hyps.remove false ivar
    let ⟨_, hyps'', pNest, outNest, pfContNest⟩ ←
      iSpecializeCore hyps' p1 out1' q(iprop(□?$p $out -∗ $goal)) pmt.spats
    let p2 := if isTrue pNest then p else q(false)
    let out2 ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ
        q(IntoWand $p $pNest $out (.matching .argument) $outNest $out2)
      | throwIPMError "IntoWand type class synthesis failed with {out} and {outNest}"
    let pfStep := q(specialize_wand_nest $inst $pf' $pfContNest)
    return specState.updateCont hyps'' p2 out2 pfStep
  -- A pure Lean hypothesis
  | .pure t => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
      | throwIPMError "{out} is not a Lean premise"
    let x ← elabTermEnsuringTypeQ t α
    let out' : Q($prop) := Expr.headBeta q($Φ $x)
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    let pfStep := q(specialize_forall (A2 := $e) (p := $p) $inst $x)
    return specState.update hyps p out' pfStep
  -- Subgoal with `[ H₁ … Hₙ ]`, `[> H₁ … Hₙ ]`, `[# H₁ … Hₙ ]`, `[- H₁ … Hₙ ]` or `[>- H₁ … Hₙ ]`
  | .goal specGoal name => processSpecGoal specState specGoal.kind (specGoal, name)
  -- Auto-framing with `[$]`, `[>$]` or `[#$]`
  | .autoframe kind => processSpecGoal specState kind none

/--
Specialize a proposition `A` by applying a sequence of specialization patterns.

## Parameters
- `hyps`: Current proof mode hypothesis context
- `pa`: Persistence flag for `A`
- `spats`: List of specialization patterns to apply sequentially
- `try_dup_context`: Boolean whether specialize should try to duplicate the context.
                     See `iCasesPat.should_try_dup_context`.

## Returns
A tuple containing:
- `e`: Proposition for `hyps'`
- `hyps'`: Updated hypothesis context, =`hyps` if context duplication succeeds
- `pb`: Persistence flag for `B`, =`true` if context duplication succeeds
- `B`: Resulting proposition after applying all patterns
- `pf`: Proof of `(e' ∗ □?pb B ⊢ goal) → e ∗ □?pa $A ⊢ goal`
-/
partial def iSpecializeCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (pa : Q(Bool)) (A : Q($prop)) (goal : Q($prop))
    (spats : List SpecPat) (try_dup_context : Bool := false) :
    ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) ×
      Q(($e' ∗ □?$pb $B ⊢ $goal) → $e ∗ □?$pa $A ⊢ $goal)) := do
  if !try_dup_context || spats.any (·.anyModal) then
    let st ← spats.foldlM processWand { hyps, p := pa, out := A, pf := q(id) }
    return ⟨_, st.hyps, st.p, st.out, st.pf⟩
  let ⟨_, hyps', pb, B, pf⟩ ← iSpecializeCoreNoModal hyps pa A spats try_dup_context
  return ⟨_, hyps', pb, B, q($(pf).trans)⟩

/--
  For cases where no modality-related specialisation pattern involved.
  This returns the proof `e ∗ □?pa $A ⊢ e' ∗ □?pb B`.
-/
partial def iSpecializeCoreNoModal {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (pa : Q(Bool)) (A : Q($prop))
    (spats : List SpecPat) (try_dup_context : Bool := false) :
    ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) ×
      Q($e ∗ □?$pa $A ⊢ $e' ∗ □?$pb $B)) := do
  -- Return the result directly when there is no specialisation pattern
  if spats.isEmpty then
    return ⟨_, hyps, pa, A, q(.rfl)⟩

  -- replacing the goal with an mvar breaks `>` specialization patterns,
  -- but this is fine since this function assumes that there are no such
  -- patterns in spats
  let goal : Q($prop) ← mkFreshExprMVarQ prop
  let st ← spats.foldlM processWand
    { hyps, p := pa, out := A, pf := q(id (α := $e ∗ □?$pa $A ⊢ $goal)) }
  unless ← isDefEq goal q(iprop($(st.e) ∗ □?$(st.p) $(st.out))) do
    throwIPMError "internal error, goal does not match the proof"
  let stPf : Q(($(st.e) ∗ □?$(st.p) $(st.out) ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) →
    $e ∗ □?$pa $A ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) := st.pf
  let pf : Q($e ∗ □?$pa $A ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) := q($stPf .rfl)

  -- Duplicate the context if requested and possible
  unless try_dup_context do
    return ⟨_, st.hyps, st.p, st.out, pf⟩
  let af : Option Q($pa = true ∨ Affine $A) ← match matchBool pa with
    | .inl _ => pure <| some q(Or.inl (.refl $pa))
    | .inr _ => do
      let .some h ← trySynthInstanceQ q(Affine $A) | pure none
      pure <| some q(Or.inr (a := $pa = true) $h)
  let some af := af | return ⟨_, st.hyps, st.p, st.out, pf⟩
  let B' : Q($prop) ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ q(IntoPersistently $(st.p) $(st.out) $B')
    | return ⟨_, st.hyps, st.p, st.out, pf⟩
  return ⟨_, hyps, q(true), B', q(specialize_dup_context $inst $pf $af)⟩

end

/--
`iCasesPat.should_try_dup_context` determines when iSpecializeCore should try to
duplicate the separation context.
-/
@[rocq_alias intro_pat_intuitionistic, rocq_alias use_tac_specialize_intuitionistic_helper]
partial def iCasesPat.should_try_dup_context (pat : iCasesPat) : Bool :=
  match pat.case with
  | .conjunction args | .disjunction args => args.all (·.should_try_dup_context)
  | .intuitionistic _ => true
  | .pure _ => true
  | _ => false

/--
  `ispecialize pmt` specialises a hypothesis according to `pmt : pmTerm`.
-/
elab "ispecialize " colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic `ispecialize λ mvar { bi, hyps, goal, .. } => do
  -- Hypothesis must be in the context, otherwise use `ihave`
  let name := ⟨pmt.term⟩
  let some ivar ← try? <| hyps.findWithInfo name
    | throwIPMError "{name} should be a hypothesis, use ihave instead"
  let some ⟨name, _, hyps', _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name ivar' _ _ => if ivar == ivar' then some name else none
    | throwIPMError "cannot find argument {name}"

  let ⟨_, hyps'', pb, B, pf'⟩ ← iSpecializeCore hyps' p out goal pmt.spats
  let ⟨_, hyps''', pfEq⟩ := Hyps.add bi name ivar pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).1.trans <| $(pf') <| $(pfEq).mp.trans $pf'')
