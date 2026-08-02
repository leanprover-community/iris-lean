/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.SpecPattern
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Tactics.Basic
public import Iris.ProofMode.Tactics.Trivial
public import Iris.ProofMode.Tactics.Frame

namespace Iris.ProofMode

public section
open BI

theorem specialize_wand [BI PROP] {q p : Bool} {A Q P1 P2 : PROP}
    (inst : IntoWand q p Q .in P1 .out P2) :
    (A ∗ □?p P1) ∗ □?q Q ⊢ A ∗ □?(p && q) P2 := by
  refine sep_assoc.mp.trans (sep_mono_right ?_)
  cases p with
  | false => exact (sep_mono_right inst.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □?q □ P1 ∗ □?q Q     := sep_mono_left intuitionisticallyIf_intutitionistically.mpr
    _ ⊢ □?q □ P1 ∗ □?q □?q Q := sep_mono_right intuitionisticallyIf_idem.mpr
    _ ⊢ □?q (□ P1 ∗ □?q Q)   := intuitionisticallyIf_sep_mpr
    _ ⊢ □?q P2               := intuitionisticallyIf_mono <| wand_elim_swap inst.into_wand

-- TODO: if q is true and A1 is persistent, this proof can guarantee □ P2 instead of P2
-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/846ed45bed6951035c6204fef365d9a344022ae6/iris/proofmode/coq_tactics.v#L336
theorem specialize_wand_subgoal [BI PROP] {q : Bool} {A2 A3 A4 Q P1 : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1) : A2 ∗ □?q Q ⊢ A3 ∗ P2 := by
  refine (sep_mono_left h2.mp).trans <| sep_assoc.mp.trans
    (sep_mono_right ((sep_mono_left h3).trans ?_))
  exact (sep_mono_right inst.into_wand).trans wand_elim_right

theorem specialize_wand_nest [BI PROP] {e e' e'' goal out out1' Q out2 : PROP}
    {p p1 q : Bool} (inst : IntoWand p q out .in Q .out out2)
    (h1 : e ⊣⊢ e' ∗ □?p1 out1')
    (h2 : (e'' ∗ □?q Q ⊢ □?p out -∗ goal) → e' ∗ □?p1 out1' ⊢ □?p out -∗ goal)
    (h3 : e'' ∗ □?(q && p) out2 ⊢ goal) : e ∗ □?p out ⊢ goal := by
  apply wand_elim_left_trans
  refine h1.mp.trans ?_
  refine h2 <| wand_intro ?_
  exact (specialize_wand inst).trans h3

theorem specialize_wand_autoframe_spatial [BI PROP] {q : Bool} {A2 A3 Q P1 : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h2 : A2 ⊢ A3 ∗ P1) : A2 ∗ □?q Q ⊢ A3 ∗ P2 := calc
  _ ⊢ (A3 ∗ P1) ∗ □?q Q := sep_mono_left h2
  _ ⊢ A3 ∗ P1 ∗ □?q Q   := sep_assoc.mp
  _ ⊢ A3 ∗ P2           := sep_mono_right <| (sep_mono_right inst.into_wand).trans wand_elim_right

theorem specialize_wand_persistent [BI PROP] {q : Bool} {A2 Q P1' : PROP} P1 P2
    (instWand : IntoWand q true Q .out P1 .out P2) (instPers : Persistent P1)
    (instAbsorb : IntoAbsorbingly P1' P1) (h1 : A2 ⊢ P1') : A2 ∗ □?q Q ⊢ A2 ∗ □?q P2 := by
  have h2 : □ P1 ∗ □?q Q ⊢ □?q P2 := by cases q with
  | false => exact (sep_mono_right instWand.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □ □ P1 ∗ □ □ Q          := sep_mono intuitionistically_idem.mpr intuitionistically_idem.mpr
    _ ⊢ □ (□ P1 ∗ □ Q)          := intuitionistically_sep_mpr
    _ ⊢ □ (□ P1 ∗ (□ P1 -∗ P2)) := intuitionistically_mono <| sep_mono_right instWand.into_wand
    _ ⊢ □?true P2               := intuitionistically_mono wand_elim_right
  have h3 : A2 ⊢ A2 ∗ □ P1 := calc
    _ ⊢ (A2 ∧ A2)                 := and_intro .rfl .rfl
    _ ⊢ (A2 ∧ P1')                := and_mono_right h1
    _ ⊢ (A2 ∧ <absorb> P1)        := and_mono_right into_absorbingly
    _ ⊢ (A2 ∧ <absorb> <pers> P1) := and_mono_right <| absorbingly_mono Persistent.persistent
    _ ⊢ (A2 ∧ <pers> P1)          := and_mono_right absorbingly_persistently.mp
    _ ⊢ (A2 ∗ □ P1)               := persistently_and_intuitionistically_sep_right.mp
  calc
    _ ⊢ (A2 ∗ □ P1) ∗ □?q Q := sep_mono_left h3
    _ ⊢ A2 ∗ □ P1 ∗ □?q Q   := sep_assoc.mp
    _ ⊢ A2 ∗ □?q P2         := sep_mono_right h2

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
      _ ⊢ P' ∗ <pers> B' := sep_mono_right <| persistentlyIf_of_intuitionisticallyIf.trans into_persistently
      _ ⊢ <pers> B'      := sep_elim_right

theorem specialize_modal [BI PROP] {e e' goal R P1 P1' P2 : PROP} {p : Bool}
    (h1 : e ⊢ e' ∗ P1') (h2 : e' ∗ P2 ⊢ goal)
    (instWand : IntoWand p false R .out P1 .out P2)
    (instModal : AddModal P1' P1 goal) :
    e ∗ □?p R ⊢ goal := calc
  _ ⊢ (e' ∗ P1') ∗ □?p R                := sep_mono_left h1
  _ ⊢ P1' ∗ (e' ∗ □?p R)                := sep_assoc.mp.trans sep_left_comm.mp
  _ ⊢ P1' ∗ (e' ∗ (P1 -∗ P2))           := sep_mono_right (sep_mono_right instWand.into_wand)
  _ ⊢ P1' ∗ ((P2 -∗ goal) ∗ (P1 -∗ P2)) := sep_mono_right (sep_mono_left (wand_intro h2))
  _ ⊢ P1' ∗ (P1 -∗ goal)                := sep_mono_right (sep_comm.mp.trans wand_trans)
  _ ⊢ goal                              := instModal.add_modal

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

/--
  Returns `IVarId` values of hypotheses to be included in a subgoal and those to be framed.
  Used by all `.goal` cases in `processWand`.
-/
private def findFrameIVars {u}  {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (subgoalIdents frameIdents : List Ident) :
    ProofModeM <| IVarIdSet × List IVarId := do
  -- Hypotheses to be included in the subgoal
  let subgoalIVars ← subgoalIdents.foldlM (return ·.insert <| ← hyps.findWithInfo ·) {}
  -- Hypotheses to be framed
  let mut frameIVars : List IVarId := []
  for i in frameIdents do
    let ivar ← hyps.findWithInfo i
    if frameIVars.contains ivar then
      throwError "ispecialize: {i} used twice for framing"
    if subgoalIVars.contains ivar then
      throwError "ispecialize: {i} cannot be used for both the subgoal and framing"
    frameIVars := ivar :: frameIVars
  return ⟨subgoalIVars, frameIVars.reverse⟩

/--
  Split hypotheses into those to be included in a subgoal and those to be framed.
  Used by the `.goal` cases with the `.spatial` or `.modal` kind.
-/
private def splitFrameHyps {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (subgoalIdents frameIdents : List Ident) (negate : Bool) :
    ProofModeM <| (el : Q($prop)) × (er : Q($prop)) ×
      Hyps bi el × Hyps bi er × Q($e ⊣⊢ $el ∗ $er) × List IVarId := do
  let ⟨ivars, frameIVars⟩ ← findFrameIVars hyps subgoalIdents frameIdents
  let ⟨el, er, hypsl, hypsr, pf⟩ := Hyps.split bi
    (λ _ ivar => (negate ^^ ivars.contains ivar) || frameIVars.contains ivar) hyps
  return ⟨el, er, hypsl, hypsr, pf, frameIVars⟩

/--
  Applying framing and then solve the goal using `itrivial` (when `trivial` is
  `true`) or add the goal into the proof state (when `trivial` is `false`).
  Used by all `.goal` cases and the `.autoframe persistent` case in `processWand`.
-/
private def finishFrameSubgoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (trivial : Bool) (g : Option Name)
    (frameIVars : Option <| List IVarId) : ProofModeM Q($e ⊢ $goal) := do
  let targets ← do match frameIVars with
  -- For auto-framing
  | none => SelPat.resolve hyps [.spatial, .intuitionistic]
  -- For framing with the specified hypotheses
  | some frameIVars => pure (frameIVars.map (⟨.ipm ·, true⟩))
  let res ← iFrame hyps goal targets
  res.finish λ hyps goal => do
    if trivial then
      let some r ← iTrivial hyps goal
        | throwError "ispecialize: itrivial could not solve\
            {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
      return r
    else addBIGoal hyps goal <| g.getD .anonymous

private def synthIntoWand {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (out : Q($prop)) (persistent : Bool) :
    ProofModeM <| (out1 : Q($prop)) × (out2 : Q($prop)) ×
      Q(IntoWand $p $persistent $out .out $out1 .out $out2) := do
  let out1 ← mkFreshExprMVarQ prop
  let out2 ← mkFreshExprMVarQ prop
  let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $persistent $out .out $out1 .out $out2)
    | throwError m!"ispecialize: {out} is not a wand"
  return ⟨out1, out2, inst⟩

/-- Used by the cases `.autoframe` and `.goal` in `processWand` with the `.persistent` kind. -/
private def synthIntoWandPersistent {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (out : Q($prop)) :
    ProofModeM ((out1 : Q($prop)) × (out2 : Q($prop)) × (out1' : Q($prop)) ×
      Q(IntoWand $p true $out .out $out1 .out $out2) ×
      Q(Persistent $out1) × Q(IntoAbsorbingly $out1' $out1)) := do
  let ⟨out1, out2, instWand⟩ : (out1 : Q($prop)) × (out2 : Q($prop)) ×
    Q(IntoWand $p true $out .out $out1 .out $out2) ← @synthIntoWand u prop bi p out true
  let some intoPers ← ProofModeM.trySynthInstanceQ q(Persistent $out1)
    | throwError m!"ispecialize: {out1} is not persistent"
  let out1' ← mkFreshExprMVarQ prop
  let some instAbsorb ← ProofModeM.trySynthInstanceQ q(IntoAbsorbingly $out1' $out1)
    | throwError m!"ispecialize: IntoAbsorbingly type class synthesis failed with {out1}"
  return ⟨out1, out2, out1', instWand, intoPers, instAbsorb⟩

/-- Used by the cases `.autoframe` and `.goal` in `processWand` with the `.modal` kind. -/
private def synthIntoWandModal {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (p : Q(Bool)) (out goal : Q($prop)) :
    ProofModeM ((out1 : Q($prop)) × (out2 : Q($prop)) × (out1' : Q($prop)) ×
      Q(IntoWand $p false $out .out $out1 .out $out2) × Q(AddModal $out1' $out1 $goal)) := do
  let ⟨out1, out2, instWand⟩ : (out1 : Q($prop)) × (out2 : Q($prop)) ×
    Q(IntoWand $p false $out .out $out1 .out $out2) ← @synthIntoWand u prop bi p out false
  let out1' ← mkFreshExprMVarQ prop
  let some instModal ← ProofModeM.trySynthInstanceQ q(AddModal $out1' $out1 $goal)
    | throwError m!"ispecialize: AddModal type class synthesis failed with {out1} and {goal}"
  pure ⟨out1, out2, out1', instWand, instModal⟩

mutual

partial def processWand {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {orig goal : Q($prop)}
    (specState : @SpecializeState u prop bi orig goal) (spat : Syntax × SpecPat) :
    ProofModeM (@SpecializeState u prop bi orig goal) := do
  let { e, hyps, p, out, .. } := specState
  let ⟨ref, spat⟩ := spat
  withRef ref do
  match spat with
  -- A hypothesis name, possibly with nested specialisation patterns
  | .ident pmt =>
    let ivar ← hyps.findWithInfo ⟨pmt.term⟩
    let ⟨_, hyps', _, out1', p1, _, pf'⟩ := hyps.remove false ivar
    let ⟨e'', hyps'', pNest, outNest, pfContNest, _⟩ ←
      iSpecializeCore hyps' p1 out1' q(iprop(□?$p $out -∗ $goal)) pmt.spats
    let p2 := if pNest.constName! == ``true then p else q(false)
    let out2 ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $pNest $out .in $outNest .out $out2)
      | throwError m!"ispecialize: IntoWand type class synthesis failed with {out} and {outNest}"
    let pfStep : Q((($e'' ∗ □?($pNest && $p) $out2 ⊢ $goal) → $e ∗ □?$p $out ⊢ $goal)) :=
      q(specialize_wand_nest $inst $pf' $pfContNest)
    return specState.updateCont hyps'' p2 out2 pfStep
  -- A pure Lean hypothesis
  | .pure t => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
      | throwError "ispecialize: {out} is not a Lean premise"
    let x ← elabTermEnsuringTypeQ t α
    let out' : Q($prop) := Expr.headBeta q($Φ $x)
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    let pfStep : Q($e ∗ □?$p $out ⊢ $e ∗ □?$p $Φ $x) :=
      q(specialize_forall (A2 := $e) (p := $p) $inst $x)
    return specState.update hyps p out' pfStep
  -- Subgoal with `[ H₁ … Hₙ ]` or `[- H₁ … Hₙ ]`
  | .goal { kind := .spatial, negate, trivial, frame := f, hyps := hs } g => do
    let ⟨_, _, hypsl, hypsr, pf', frameIVars⟩ ← splitFrameHyps hyps hs f negate
    let ⟨out1, out2, inst⟩ ← synthIntoWand p out false
    let pf'' ← finishFrameSubgoal hypsr out1 trivial g frameIVars
    let pfStep := q(specialize_wand_subgoal $out2 $inst $pf' $pf'')
    return specState.update hypsl q(false) out2 pfStep
  -- Subgoal with `[# H₁ … Hₙ ]` or `[#- H₁ … Hₙ ]`
  | .goal { kind := .intuitionistic, trivial, frame := f, hyps := hs, .. } g => do
    if !hs.isEmpty then
      throwError "ispecialize: the subgoal for the persistent premise should not consume hypotheses"
    let ⟨out1, out2, out1', instWand, instPers, instAbsorb⟩ ← synthIntoWandPersistent p out
    let ⟨_, frameIVars⟩ ← findFrameIVars hyps [] f
    let pf' ← finishFrameSubgoal hyps out1' trivial g frameIVars
    let pfStep := q(specialize_wand_persistent $out1 $out2 $instWand $instPers $instAbsorb $pf')
    return specState.update hyps p out2 pfStep
  -- Subgoal with `[> H₁ … Hₙ ]` or `[>- H₁ … Hₙ ]`
  | .goal { kind := .modal, negate, trivial, frame := f, hyps := hs, .. } g =>
    let ⟨el, _, hypsl', hypsr', pf', frameIVars⟩ ← splitFrameHyps hyps hs f negate
    let ⟨_, out2, out1', instWand, instModal⟩ ← synthIntoWandModal p out goal
    let pf'' ← finishFrameSubgoal hypsr' out1' trivial g frameIVars
    let h : Q($e ⊢ $el ∗ $out1') := q($(pf').mp.trans (sep_mono_right $pf''))
    let pfStep : Q(($el ∗ □?false $out2 ⊢ $goal) → $e ∗ □?$p $out ⊢ $goal) :=
      q(fun k => specialize_modal $h k $instWand $instModal)
    return specState.updateCont hypsl' q(false) out2 pfStep
  -- Auto-framing with `[$]`
  | .autoframe .spatial => do
    let ⟨out1, out2, inst⟩ ← synthIntoWand p out false
    let res ← iFrame hyps out1 (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    let pfStep := q(specialize_wand_autoframe_spatial $out2 $inst $pf')
    return specState.update hyps' q(false) out2 pfStep
  -- Auto-framing with `[#$]`
  | .autoframe .intuitionistic =>
    let ⟨out1, out2, out1', instWand, instPers, instAbsorb⟩ ← synthIntoWandPersistent p out
    let pf' ← finishFrameSubgoal hyps out1' true none none
    let pfStep := q(specialize_wand_persistent $out1 $out2 $instWand $instPers $instAbsorb $pf')
    return specState.update hyps p out2 pfStep
  -- Auto-framing with `[>$]`
  | .autoframe .modal =>
    let ⟨_, out2, out1', instWand, instModal⟩ ← synthIntoWandModal p out goal
    let res ← iFrame hyps out1' (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨e', hyps', pf'⟩ ← res.finishClose
    let pfStep : Q(($e' ∗ □?false $out2 ⊢ $goal) → $e ∗ □?$p $out ⊢ $goal) :=
      q(fun k => specialize_modal $pf' k $instWand $instModal)
    return specState.updateCont hyps' q(false) out2 pfStep

/-- Specialize a proposition `A` by applying a sequence of specialization patterns.

## Parameters
- `hyps`: Current proof mode hypothesis context
- `pa`: Persistence flag for `A`
- `spats`: List of specialization patterns to apply sequentially
- `try_dup_context`: Boolean whether specialize should try to duplicate the context. See [iCasesPat.should_try_dup_context]

## Returns
A tuple containing:
- `e`: Proposition for `hyps'`
- `hyps'`: Updated hypothesis context, =`hyps` if context duplication succeeds
- `pb`: Persistence flag for `B`, =`true` if context duplication succeeds
- `B`: Resulting proposition after applying all patterns
- `pf`: Proof of `hyps ∗ □?pa A ⊢ hyps' ∗ □?pb B`, =`hyps ∗ □?pa A ⊢ hyps ∗ □ B` if context duplication succeeds
-/
partial def iSpecializeCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (pa : Q(Bool)) (A : Q($prop)) (goal : Q($prop))
    (spats : List (Syntax × SpecPat)) (try_dup_context : Bool := false) :
    ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) ×
      Q(($e' ∗ □?$pb $B ⊢ $goal) → $e ∗ □?$pa $A ⊢ $goal) ×
      Option Q($e ∗ □?$pa $A ⊢ $e' ∗ □?$pb $B)) := do
  -- Return the result directly when there are no nested specialisation patterns
  if spats.isEmpty then
    return ⟨_, hyps, pa, A, q(id), some q(.rfl)⟩

  -- Modality-related specialisation patterns involved
  if spats.any (·.snd.anyModal) then
    let st ← spats.foldlM processWand { hyps, p := pa, out := A, pf := q(id) }
    return ⟨_, st.hyps, st.p, st.out, st.pf, none⟩

  -- No modality-related specialisation pattern involved: create a metavariable for the goal
  let goal : Q($prop) ← mkFreshExprMVarQ prop
  let st ← spats.foldlM processWand
    { hyps, p := pa, out := A, pf := q(id (α := $e ∗ □?$pa $A ⊢ $goal)) }
  unless ← isDefEq goal q(iprop($(st.e) ∗ □?$(st.p) $(st.out))) do
    throwError "ispecialize: internal error, goal does not match the proof"
  let stPf : Q(($(st.e) ∗ □?$(st.p) $(st.out) ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) →
    $e ∗ □?$pa $A ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) := st.pf
  let pf : Q($e ∗ □?$pa $A ⊢ $(st.e) ∗ □?$(st.p) $(st.out)) := q($stPf .rfl)

  -- Duplicate the context if requested and possible
  if try_dup_context then
    let af : Option Q($pa = true ∨ Affine $A) ← match matchBool pa with
      | .inl _ => pure <| some q(Or.inl (.refl $pa))
      | .inr _ => do
        let .some h ← trySynthInstanceQ q(Affine $A) | pure none
        pure <| some q(Or.inr (a := $pa = true) $h)
    let some af := af | return ⟨_, st.hyps, st.p, st.out, q($(pf).trans), some pf⟩
    let B' : Q($prop) ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoPersistently $(st.p) $(st.out) $B')
      | return ⟨_, st.hyps, st.p, st.out, q($(pf).trans), some pf⟩
    let pfDup := q(specialize_dup_context $inst $pf $af)
    return ⟨_, hyps, q(true), B', q($(pfDup).trans), some pfDup⟩
  return ⟨_, st.hyps, st.p, st.out, q($(pf).trans), some pf⟩

end

/--
`iCasesPat.should_try_dup_context` determines when iSpecializeCore should try to
duplicate the separation context.
The duplication only works if the conclusion of the specialization is persistent.
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
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
  -- Hypothesis must be in the context, otherwise use `ihave`
  let name := ⟨pmt.term⟩
  let some ivar ← try? <| hyps.findWithInfo name
    | throwError "ispecialize: {name} should be a hypothesis, use ihave instead"
  let some ⟨name, _, hyps', _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name ivar' _ _ => if ivar == ivar' then some name else none
    | throwError "ispecialize: cannot find argument {name}"

  let ⟨_, hyps'', pb, B, pf', _⟩ ← iSpecializeCore hyps' p out goal pmt.spats
  let ⟨_, hyps''', pfEq⟩ := Hyps.add bi name ivar pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).1.trans <| $(pf') <| $(pfEq).mp.trans $pf'')
