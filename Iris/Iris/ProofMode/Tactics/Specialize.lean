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

theorem specialize_wand_nest [BI PROP] {e e' e'' out out1' Q out2 : PROP}
    {p p1 q : Bool} (inst : IntoWand p q out .in Q .out out2)
    (h1 : e ⊣⊢ e' ∗ □?p1 out1') (h2 : e' ∗ □?p1 out1' ⊢ e'' ∗ □?q Q) :
    e ∗ □?p out ⊢ e'' ∗ □?(q && p) out2 := calc
  _ ⊢ (e'' ∗ □?q Q) ∗ □?p out := sep_mono_left <| h1.mp.trans h2
  _ ⊢ e'' ∗ □?(q && p) out2   := specialize_wand inst

theorem specialize_wand_nest_modal [BI PROP]
    {orig e e' e'' goal out out1' Q out2 : PROP} {p p1 q : Bool}
    (inst : IntoWand p q out .in Q .out out2)
    (h1 : (e ∗ □?p out ⊢ goal) → orig ⊢ goal) (h2 : e ⊣⊢ e' ∗ □?p1 out1')
    (h3 : (e'' ∗ □?q Q ⊢ □?p out -∗ goal) → e' ∗ □?p1 out1' ⊢ □?p out -∗ goal)
    (h4 : e'' ∗ □?(q && p) out2 ⊢ goal) : orig ⊢ goal := by
  apply h1
  apply wand_elim_left_trans
  calc
    _ ⊢ e' ∗ □?p1 out1' := h2.mp
    _ ⊢ □?p out -∗ goal := h3 <| wand_intro <| (specialize_wand inst).trans h4

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
  -- A weaker proposition than `pf`, applicable even when the `.modal` kind is involved
  (pfCont : Q(($e ∗ □?$p $out ⊢ $goal) → $orig ⊢ $goal))
  -- Holds when the `.modal` kind is not involved, cannot duplicate context if `pf = none`
  pf : Option Q($orig ⊢ $e ∗ □?$p $out)

/--
  Updates a `SpecializeState` instance by one iteration.
  Used in all cases in `processWand` except those involving the `.modal` kind.
-/
private def SpecializeState.update {u} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {orig goal : Q($prop)} (st : @SpecializeState u prop bi orig goal)
    {e' : Q($prop)} (hyps' : Hyps bi e') (p' : Q(Bool)) (out' : Q($prop))
    (pfStep : Q($(st.e) ∗ □?$(st.p) $(st.out) ⊢ $e' ∗ □?$p' $out')) :
    @SpecializeState u prop bi orig goal :=
  { hyps := hyps', p := p', out := out',
    pfCont := q(fun pf => $(st.pfCont) ($(pfStep).trans pf)),
    pf := st.pf.map (fun pf => q($(pf).trans $pfStep)) }

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
  let res ← iFrame bi hyps goal targets
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

private def processWand {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {orig goal : Q($prop)}
    (specState : @SpecializeState u prop bi orig goal) (spat : Syntax × SpecPat) :
    ProofModeM (@SpecializeState u prop bi orig goal) := do
  let { e, hyps, p, out, pfCont, pf } := specState
  let ⟨ref, spat⟩ := spat
  withRef ref do
  match spat with
  -- A hypothesis name, possibly with nested specialisation patterns
  | .ident i spats =>
    let ivar ← hyps.findWithInfo i
    let ⟨_, hyps', _, out1', p1, _, pf'⟩ := hyps.remove false ivar
    let ⟨_, hyps'', pNest, outNest, pfContNest, pfNest⟩ ←
      if spats.isEmpty then
        -- No nested specialisation patterns
        pure ⟨_, hyps', p1, out1', q(id), some q(.rfl)⟩
      else
        -- There are nested specialisation patterns, requires recursive calls
        iSpecializeCore hyps' p1 out1' q(iprop(□?$p $out -∗ $goal)) spats
    let p2 := if pNest.constName! == ``true then p else q(false)
    let out2 ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $pNest $out .in $outNest .out $out2)
    | throwError m!"ispecialize: IntoWand type class synthesis failed with {out} and {outNest}"
    match pfNest with
    -- Nested specialisation pattern involves the `.modal` kind
    | none =>
      let pfCont := q(specialize_wand_nest_modal $inst $pfCont $pf' $pfContNest)
      return { hyps := hyps'', p := p2, out := out2, pfCont, pf := none }
    -- Nested specialisation pattern does not involve the `.modal` kind, or no nested pattern
    | some pfNest =>
      let pfStep := q(specialize_wand_nest $inst $pf' $pfNest)
      return specState.update hyps'' p2 out2 pfStep
  -- A pure Lean hypothesis
  | .pure t => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
    | throwError "ispecialize: {out} is not a Lean premise"
    let x ← elabTermEnsuringTypeQ t α
    have out' : Q($prop) := Expr.headBeta q($Φ $x)
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
  | .goal { kind := .persistent, trivial, frame := f, hyps := hs, .. } g => do
    if !hs.isEmpty then
      throwError "ispecialize: the subgoal for the persistent premise should not consume hypotheses"
    let ⟨out1, out2, out1', instWand, instPers, instAbsorb⟩ ← synthIntoWandPersistent p out
    let ⟨_, frameIVars⟩ ← findFrameIVars hyps [] f
    let pf' ← finishFrameSubgoal hyps out1' trivial g frameIVars
    let pfStep := q(specialize_wand_persistent $out1 $out2 $instWand $instPers $instAbsorb $pf')
    return specState.update hyps p out2 pfStep
  -- Subgoal with `[> H₁ … Hₙ ]` or `[>- H₁ … Hₙ ]`
  | .goal { kind := .modal, negate, trivial, frame := f, hyps := hs, .. } g =>
    let ⟨_, _, hypsl', hypsr', pf', frameIVars⟩ ← splitFrameHyps hyps hs f negate
    let ⟨out1, out2, out1', instWand, instModal⟩ ← synthIntoWandModal p out goal
    let pf'' ← finishFrameSubgoal hypsr' out1' trivial g frameIVars
    let h := q($(pf').mp.trans (sep_mono_right $pf''))
    let pfCont := q(fun pf => $pfCont (specialize_modal $h pf $instWand $instModal))
    return { hyps := hypsl', p := q(false), out := out2, pfCont, pf := none }
  -- Auto-framing with `[$]`
  | .autoframe .spatial => do
    let ⟨out1, out2, inst⟩ ← synthIntoWand p out false
    let res ← iFrame bi hyps out1 (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    let pfStep := q(specialize_wand_autoframe_spatial $out2 $inst $pf')
    return specState.update hyps' q(false) out2 pfStep
  -- Auto-framing with `[#$]`
  | .autoframe .persistent =>
    let ⟨out1, out2, out1', instWand, instPers, instAbsorb⟩ ← synthIntoWandPersistent p out
    let pf' ← finishFrameSubgoal hyps out1' true none none
    let pfStep := q(specialize_wand_persistent $out1 $out2 $instWand $instPers $instAbsorb $pf')
    return specState.update hyps p out2 pfStep
  -- Auto-framing with `[>$]`
  | .autoframe .modal =>
    let ⟨out1, out2, out1', instWand, instModal⟩ ← synthIntoWandModal p out goal
    let res ← iFrame bi hyps out1' (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    let pfCont := q(fun pf => $pfCont (specialize_modal $pf' pf $instWand $instModal))
    return { hyps := hyps', p := q(false), out := out2, pfCont, pf := none }

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
def iSpecializeCore {prop : Q(Type u)} {bi : Q(BI $prop)} {e}
    (hyps : Hyps bi e) (pa : Q(Bool)) (A : Q($prop)) (goal : Q($prop))
    (spats : List (Syntax × SpecPat)) (try_dup_context : Bool := false) :
    ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) ×
      Q(($e' ∗ □?$pb $B ⊢ $goal) → $e ∗ □?$pa $A ⊢ $goal) ×
      Option Q($e ∗ □?$pa $A ⊢ $e' ∗ □?$pb $B)) := do
  let state : SpecializeState _ goal :=
    { hyps, out := A, p := pa, pfCont := q(id), pf := some q(.rfl) }
  let ⟨hyps', pb, B, pfCont, pf⟩ ← spats.foldlM processWand state
  match try_dup_context, pf with
  | true, some pf =>
    -- Duplicate context if `B` is persistent and `A` is persistent/affine
    let B' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let af ← do match matchBool pa with
    | .inl _ => pure <| some q(Or.inl (.refl $pa))
    | .inr _ => do
      let .some h ← trySynthInstanceQ q(Affine $A) | pure none
      pure <| some q(Or.inr (a := $pa = true) $h)
    let inst ← ProofModeM.trySynthInstanceQ q(IntoPersistently $pb $B $B')
    match inst, af with
    -- Context duplication does not succeed
    | none, _ | _, none => return ⟨_, hyps', pb, B, q($(pf).trans), some q($pf)⟩
    -- Context duplication succeeds
    | some inst, some af =>
      let pf := q(specialize_dup_context $inst $pf $af)
      return ⟨_, hyps, q(true), B', q($(pf).trans), some q($pf)⟩
  -- No request to duplicate the context, or the `.modal` kind is involved
  | _, _ => return ⟨_, hyps', pb, B, pfCont, pf⟩

end

/--
`iCasesPat.should_try_dup_context` determines when iSpecializeCore should try to
duplicate the separation context.
The duplication only works if the conclusion of the specialization is persistent.
-/
@[rocq_alias intro_pat_intuitionistic, rocq_alias use_tac_specialize_intuitionistic_helper]
partial def iCasesPat.should_try_dup_context (pat : iCasesPat) : Bool :=
  match pat with
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
  let hyps''' := Hyps.add bi name ivar pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).mp.trans <| $pf' $pf'')
