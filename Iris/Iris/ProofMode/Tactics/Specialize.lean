/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Alvin Tang
-/
module

public meta import Iris.ProofMode.Patterns.ProofModeTerm
public meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Tactics.Basic
public import Iris.ProofMode.Tactics.Trivial
public import Iris.ProofMode.Tactics.Frame

namespace Iris.ProofMode

public section
open BI

theorem specialize_wand [BI PROP] {q p : Bool} {A1 A2 A3 Q P1 P2 : PROP}
    (inst : IntoWand q p Q .in P1 .out P2)
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊢ A3 ∗ □?p P1) :
    A1 ⊢ A3 ∗ □?(p && q) P2 := by
  refine h1.trans <| (sep_mono_left h2).trans <| sep_assoc.mp.trans (sep_mono_right ?_)
  cases p with
  | false => exact (sep_mono_right inst.into_wand).trans <| wand_elim_right
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.mpr intuitionisticallyIf_idem.mpr).trans <|
    intuitionisticallyIf_sep_mpr.trans <| intuitionisticallyIf_mono <| (wand_elim_swap inst.into_wand)

theorem specialize_wand_cont [BI PROP] {q p : Bool}
    {A1 A2 A3 Q P1 P2 goal : PROP}
    (inst : IntoWand q p Q .in P1 .out P2)
    (h1 : (A2 ∗ □?q Q ⊢ goal) → A1 ⊢ goal) (h2 : A2 ⊢ A3 ∗ □?p P1)
    (h3 : A3 ∗ □?(p && q) P2 ⊢ goal) :
    A1 ⊢ goal := by
  refine h1 (Entails.trans ?_ h3)
  refine (sep_mono_left h2).trans <| sep_assoc.1.trans (sep_mono_right ?_)
  cases p with
  | false => exact (sep_mono_right inst.into_wand).trans <| wand_elim_right
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.mpr intuitionisticallyIf_idem.mpr).trans <|
    intuitionisticallyIf_sep_mpr.trans <| intuitionisticallyIf_mono <| (wand_elim_swap inst.into_wand)

-- TODO: if q is true and A1 is persistent, this proof can guarantee □ P2 instead of P2
-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/846ed45bed6951035c6204fef365d9a344022ae6/iris/proofmode/coq_tactics.v#L336
theorem specialize_wand_subgoal [BI PROP] {q : Bool} {A1 A2 A3 A4 Q P1 : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1) : A1 ⊢ A3 ∗ P2 := by
  refine h1.trans <| (sep_mono_left h2.1).trans <| sep_assoc.1.trans (sep_mono_right ((sep_mono_left h3).trans ?_))
  exact (sep_mono_right inst.1).trans wand_elim_right

theorem specialize_wand_subgoal_cont [BI PROP] {q : Bool}
    {A1 A2 A3 A4 Q P1 goal : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h1 : (A2 ∗ □?q Q ⊢ goal) → A1 ⊢ goal) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1)
    (h4 : A3 ∗ P2 ⊢ goal) : A1 ⊢ goal := by
  refine h1 (Entails.trans ?_ h4)
  refine (sep_mono_left h2.1).trans <| sep_assoc.1.trans (sep_mono_right ((sep_mono_left h3).trans ?_))
  exact (sep_mono_right inst.1).trans wand_elim_right

theorem specialize_wand_autoframe_spatial [BI PROP] {q : Bool}
    {A1 A2 A3 Q P1 : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊢ A3 ∗ P1) : A1 ⊢ A3 ∗ P2 :=
  h1.trans <| (sep_mono_left h2).trans <| sep_assoc.1.trans
    (sep_mono_right ((sep_mono_right inst.into_wand).trans wand_elim_right))

theorem specialize_wand_autoframe_spatial_cont [BI PROP] {q : Bool}
    {A1 A2 A3 Q P1 goal : PROP} P2
    (inst : IntoWand q false Q .out P1 .out P2)
    (h1 : (A2 ∗ □?q Q ⊢ goal) → A1 ⊢ goal) (h2 : A2 ⊢ A3 ∗ P1) (h3 : A3 ∗ P2 ⊢ goal) :
    A1 ⊢ goal := by
  refine h1 (Entails.trans ?_ h3)
  exact (sep_mono_left h2).trans <| sep_assoc.1.trans
    (sep_mono_right ((sep_mono_right inst.into_wand).trans wand_elim_right))

theorem specialize_wand_persistent [BI PROP] {q : Bool}
    {A1 A2 Q P1' : PROP} P1 P2
    (inst3 : IntoWand q true Q .out P1 .out P2) (inst2 : Persistent P1)
    (inst1 : IntoAbsorbingly P1' P1)
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊢ P1') :
    A1 ⊢ A2 ∗ □?q P2 :=
  have h3 : □ P1 ∗ □?q Q ⊢ □?q P2 := by cases q with
  | false => exact (sep_mono_right inst3.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □ □ P1 ∗ □ □ Q          := sep_mono intuitionistically_idem.mpr intuitionistically_idem.mpr
    _ ⊢ □ (□ P1 ∗ □ Q)          := intuitionistically_sep_mpr
    _ ⊢ □ (□ P1 ∗ (□ P1 -∗ P2)) := intuitionistically_mono <| sep_mono_right <| inst3.into_wand
    _ ⊢ □?true P2               := intuitionistically_mono wand_elim_right
  calc
    _ ⊢ A2 ∗ □?q Q                        := h1
    _ ⊢ (A2 ∧ A2) ∗ □?q Q                 := sep_mono_left <| and_intro .rfl .rfl
    _ ⊢ (A2 ∧ P1') ∗ □?q Q                := sep_mono_left <| and_mono_right h2
    _ ⊢ (A2 ∧ <absorb> P1) ∗ □?q Q        := sep_mono_left <| and_mono_right into_absorbingly
    _ ⊢ (A2 ∧ <absorb> <pers> P1) ∗ □?q Q := sep_mono_left <| and_mono_right <| absorbingly_mono Persistent.persistent
    _ ⊢ (A2 ∧ <pers> P1) ∗ □?q Q          := sep_mono_left <| and_mono_right <| absorbingly_persistently.mp
    _ ⊢ (A2 ∗ □ P1) ∗ □?q Q               := sep_mono_left persistently_and_intuitionistically_sep_right.mp
    _ ⊢ A2 ∗ □ P1 ∗ □?q Q                 := sep_assoc.mp
    _ ⊢ A2 ∗ □?q P2                       := sep_mono_right h3

theorem specialize_wand_persistent_cont [BI PROP] {q : Bool}
    {A1 A2 Q P1' goal : PROP} P1 P2
    (inst3 : IntoWand q true Q .out P1 .out P2) (inst2 : Persistent P1)
    (inst1 : IntoAbsorbingly P1' P1)
    (h1 : (A2 ∗ □?q Q ⊢ goal) → A1 ⊢ goal) (h2 : A2 ⊢ P1') (h3 : A2 ∗ □?q P2 ⊢ goal) :
    A1 ⊢ goal := by
  refine h1 (Entails.trans ?_ h3)
  have h4 : □ P1 ∗ □?q Q ⊢ □?q P2 := by cases q with
  | false => exact (sep_mono_right inst3.into_wand).trans wand_elim_right
  | true => calc
    _ ⊢ □ □ P1 ∗ □ □ Q          := sep_mono intuitionistically_idem.mpr intuitionistically_idem.mpr
    _ ⊢ □ (□ P1 ∗ □ Q)          := intuitionistically_sep_mpr
    _ ⊢ □ (□ P1 ∗ (□ P1 -∗ P2)) := intuitionistically_mono <| sep_mono_right <| inst3.into_wand
    _ ⊢ □?true P2               := intuitionistically_mono wand_elim_right
  calc
    _ ⊢ (A2 ∧ A2) ∗ □?q Q                 := sep_mono_left <| and_intro .rfl .rfl
    _ ⊢ (A2 ∧ P1') ∗ □?q Q                := sep_mono_left <| and_mono_right h2
    _ ⊢ (A2 ∧ <absorb> P1) ∗ □?q Q        := sep_mono_left <| and_mono_right into_absorbingly
    _ ⊢ (A2 ∧ <absorb> <pers> P1) ∗ □?q Q := sep_mono_left <| and_mono_right <| absorbingly_mono Persistent.persistent
    _ ⊢ (A2 ∧ <pers> P1) ∗ □?q Q          := sep_mono_left <| and_mono_right <| absorbingly_persistently.mp
    _ ⊢ (A2 ∗ □ P1) ∗ □?q Q               := sep_mono_left persistently_and_intuitionistically_sep_right.mp
    _ ⊢ A2 ∗ □ P1 ∗ □?q Q                 := sep_assoc.mp
    _ ⊢ A2 ∗ □?q P2                       := sep_mono_right h4

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    (inst : IntoForall P Φ) (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_right <| intuitionisticallyIf_mono <| inst.into_forall.trans (forall_elim a)

theorem specialize_forall_cont [BI PROP] {p : Bool} {A1 A2 P goal : PROP} {α : Sort _} {Φ : α → PROP}
    (inst : IntoForall P Φ) (h : (A2 ∗ □?p P ⊢ goal) → A1 ⊢ goal) (a : α)
    (h2 : A2 ∗ □?p (Φ a) ⊢ goal) : A1 ⊢ goal := by
  refine h (Entails.trans ?_ h2)
  refine sep_mono_right <| intuitionisticallyIf_mono <| inst.into_forall.trans (forall_elim a)

theorem specialize_dup_context [BI PROP] {P : PROP} {pa A P' pb B B'}
  (h : P ∗ □?pa A ⊢ P' ∗ □?pb B)
  (h2 : pa = true ∨ Affine A)
  [IntoPersistently pb B B']
  : P ∗ □?pa A ⊢ P ∗ □ B' := by
    apply Entails.trans _ persistently_and_intuitionistically_sep_right.1
    apply and_intro
    · cases h2 <;> subst_eqs <;> apply sep_elim_left
    · apply h.trans $ (sep_mono_right (persistentlyIf_of_intuitionisticallyIf.trans into_persistently)).trans sep_elim_right

theorem specialize_modal [BI PROP] {e e' goal R P1 P1' P2 : PROP} {p : Bool}
    (h1 : e ⊢ e' ∗ P1') (h2 : e' ∗ P2 ⊢ goal)
    (inst1 : AddModal P1' P1 goal) (inst2 : IntoWand p false R .out P1 .out P2) :
    e ∗ □?p R ⊢ goal := calc
  _ ⊢ (e' ∗ P1') ∗ □?p R                := sep_mono_left h1
  _ ⊢ P1' ∗ (e' ∗ □?p R)                := sep_assoc.mp.trans sep_left_comm.mp
  _ ⊢ P1' ∗ (e' ∗ (P1 -∗ P2))           := sep_mono_right (sep_mono_right inst2.into_wand)
  _ ⊢ P1' ∗ ((P2 -∗ goal) ∗ (P1 -∗ P2)) := sep_mono_right (sep_mono_left (wand_intro h2))
  _ ⊢ P1' ∗ (P1 -∗ goal)                := sep_mono_right (sep_comm.mp.trans wand_trans)
  _ ⊢ goal                              := inst1.add_modal

public meta section
open Lean Elab Tactic Meta Qq Std

structure SpecializeState {prop : Q(Type u)} {bi : Q(BI $prop)} (orig goal : Q($prop)) where
  {e : Q($prop)} (hyps : Hyps bi e) (p : Q(Bool)) (out : Q($prop))
  (pfCont : Q(($e ∗ □?$p $out ⊢ $goal) → $orig ⊢ $goal))
  pf : Option Q($orig ⊢ $e ∗ □?$p $out)

set_option maxHeartbeats 300000 in
mutual

private def processWand {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {orig goal : Q($prop)}
    (specState : @SpecializeState u prop bi orig goal) (spat : Syntax × SpecPat) :
    ProofModeM (@SpecializeState u prop bi orig goal) := do
  let { e, hyps, p, out, pfCont, pf } := specState
  let ⟨ref, spat⟩ := spat
  withRef ref do
  match spat with
  | .ident i [] => do
    let ivar ← hyps.findWithInfo i
    let ⟨_, hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false ivar
    let p2 := if p1.constName! == ``true then p else q(false)
    have : $out₁ =Q iprop(□?$p1 $out₁') := ⟨⟩
    have : $p2 =Q ($p1 && $p) := ⟨⟩
    let out₂ ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $p1 $out .in $out₁' .out $out₂) |
      throwError m!"ispecialize: cannot instantiate {out} with {out₁'}"
    let pfCont := q(specialize_wand_cont $inst $pfCont $(pf').mp)
    let pf := pf.bind (fun pf => some q(specialize_wand $inst $pf $(pf').mp))
    return { hyps := hyps', p := p2, out := out₂, pfCont, pf }
  | .ident i spats =>
    let ivar ← hyps.findWithInfo i
    let ⟨_, hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false ivar
    let ⟨_, hyps'', pB, B, _, some pfNest⟩ ← iSpecializeCore hyps' p1 out₁' goal spats
    | throwError "ispecialize: nested specialisation pattern is not supported with modality handling"
    let p2 := if pB.constName! == ``true then p else q(false)
    have : $out₁ =Q iprop(□?$p1 $out₁') := ⟨⟩
    have : $p2 =Q ($pB && $p) := ⟨⟩
    let out₂ ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p $pB $out .in $B .out $out₂) |
      throwError m!"ispecialize: cannot instantiate {out} with {B}"
    let pfCont := q(specialize_wand_cont $inst $pfCont ($(pf').mp.trans $pfNest))
    let pf := pf.bind (fun pf => some q(specialize_wand $inst $pf ($(pf').mp.trans $pfNest)))
    return { hyps := hyps'', p := p2, out := out₂, pfCont, pf }
  | .pure t => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
    | throwError "ispecialize: {out} is not a Lean premise"
    let x ← elabTermEnsuringTypeQ (u := .succ .zero) t α
    have out' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $out' =Q $Φ $x := ⟨⟩
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    let pfCont := q(specialize_forall_cont $inst $pfCont $x)
    let pf := pf.bind (fun pf => some q(specialize_forall $inst $pf $x))
    return { e, hyps, p, out := out', pfCont, pf }
  | .goal { kind := .spatial, negate, trivial, frame := f, hyps := hs } g => do
    let mut ivars : IVarIdSet := {}
    for name in hs do
      ivars := ivars.insert (← hyps.findWithInfo name)
    let mut frameIVars : List IVarId := []
    for name in f do
      let ivar ← hyps.findWithInfo name
      frameIVars := ivar :: frameIVars
      if ivars.contains ivar then
        throwError "ispecialize: {name} used twice"
    frameIVars := frameIVars.reverse
    let ⟨_, _, hypsl', hypsr', pf'⟩ := Hyps.split bi
      (λ _ ivar => (negate ^^ ivars.contains ivar) || frameIVars.contains ivar) hyps
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let res ← iFrame bi _ hypsr' out₁ (frameIVars.map (⟨.ipm ·, true⟩))
    let pf'' ← res.finish λ hyps goal => do
      if trivial then
        let some r ← iTrivial hyps goal
        | throwError "ispecialize: itrivial could not solve {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
        return r
      else
        addBIGoal hyps goal g
    let pfCont := q(specialize_wand_subgoal_cont $out₂ $inst $pfCont $pf' $pf'')
    let pf := pf.bind (fun pf => some q(specialize_wand_subgoal $out₂ $inst $pf $pf' $pf''))
    return { hyps := hypsl', p := q(false), out := out₂, pfCont, pf }
  | .goal { kind := .persistent, trivial, frame := f, hyps := hs, .. } g => do
    if !hs.isEmpty then
      throwError "ispecialize: the subgoal for the persistent premise should not consume hypotheses"
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst1 ← ProofModeM.trySynthInstanceQ q(IntoWand $p true $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let some inst2 ← ProofModeM.trySynthInstanceQ q(Persistent $out₁)
    | throwError m!"ispecialize: {out₁} is not persistent"
    let out₁' ← mkFreshExprMVarQ prop
    let some inst3 ← ProofModeM.trySynthInstanceQ q(IntoAbsorbingly $out₁' $out₁)
    | throwError m!"ispecialize: type class synthesis failed for {out₁} with IntoAbsorbingly"
    let mut frameIVars : List IVarId := []
    for name in f do
      frameIVars := (← hyps.findWithInfo name) :: frameIVars
    frameIVars := frameIVars.reverse
    let res ← iFrame bi _ hyps out₁' (frameIVars.map (⟨.ipm ·, true⟩))
    let pf' ← res.finish λ hyps goal => do
      if trivial then
        let some r ← iTrivial hyps goal
        | throwError "ispecialize: itrivial could not solve {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
        return r
      else
        addBIGoal hyps goal g
    let pfCont := q(specialize_wand_persistent_cont $out₁ $out₂ $inst1 $inst2 $inst3 $pfCont $pf')
    let pf := pf.bind (fun pf => some q(specialize_wand_persistent $out₁ $out₂ $inst1 $inst2 $inst3 $pf $pf'))
    return { hyps, p, out := out₂, pfCont, pf }
  | .goal { kind := .modal, negate, trivial, frame := f, hyps := hs, .. } g =>
    let mut ivars : IVarIdSet := {}
    for name in hs do
      ivars := ivars.insert (← hyps.findWithInfo name)
    let mut frameIVars : List IVarId := []
    for name in f do
      let ivar ← hyps.findWithInfo name
      frameIVars := ivar :: frameIVars
      if ivars.contains ivar then
        throwError "ispecialize: {name} used twice"
    frameIVars := frameIVars.reverse
    let ⟨_, _, hypsl', hypsr', pf'⟩ := Hyps.split bi
      (λ _ ivar => (negate ^^ ivars.contains ivar) || frameIVars.contains ivar) hyps
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst1 ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let out₁' ← mkFreshExprMVarQ prop
    let some inst2 ← ProofModeM.trySynthInstanceQ q(AddModal $out₁' $out₁ $goal)
    | throwError "ispecialize: AddModal type class synthesis failed with {out₁} and {goal}"
    let res ← iFrame bi _ hypsr' out₁' (frameIVars.map (⟨.ipm ·, true⟩))
    let pf'' ← res.finish λ hyps goal => do
      if trivial then
        let some r ← iTrivial hyps goal
        | throwError "ispecialize: itrivial could not solve {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
        return r
      else
        addBIGoal hyps goal g
    let h := q($(pf').mp.trans (sep_mono_right $pf''))
    let pfCont := q(fun pf => $pfCont (specialize_modal $h pf $inst2 $inst1))
    return { hyps := hypsl', p := q(false), out := out₂, pfCont, pf := none }
  | .autoframe .spatial => do
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let res ← iFrame bi _ hyps out₁ (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    let pfCont := q(specialize_wand_autoframe_spatial_cont $out₂ $inst $pfCont $pf')
    let pf := pf.bind (fun pf => some q(specialize_wand_autoframe_spatial $out₂ $inst $pf $pf'))
    return { hyps := hyps', p := q(false), out := out₂, pfCont, pf }
  | .autoframe .persistent =>
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst1 ← ProofModeM.trySynthInstanceQ q(IntoWand $p true $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let some inst2 ← ProofModeM.trySynthInstanceQ q(Persistent $out₁)
    | throwError m!"ispecialize: {out₁} is not persistent"
    let out₁' ← mkFreshExprMVarQ prop
    let some inst3 ← ProofModeM.trySynthInstanceQ q(IntoAbsorbingly $out₁' $out₁)
    | throwError m!"ispecialize: type class synthessis failed for {out₁} with IntoAbsorbingly"
    let res ← iFrame bi _ hyps out₁' (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let pf' ← res.finish <| fun hyps goal => do
      let some pf ← iTrivial hyps goal
      | throwError "ispecialize: unable to solve premise by framing"
      return pf
    let pfCont := q(specialize_wand_persistent_cont $out₁ $out₂ $inst1 $inst2 $inst3 $pfCont $pf')
    let pf := pf.bind (fun pf => some q(specialize_wand_persistent $out₁ $out₂ $inst1 $inst2 $inst3 $pf $pf'))
    return { hyps, p, out := out₂, pfCont, pf }
  | .autoframe .modal =>
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some inst1 ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
    | throwError m!"ispecialize: {out} is not a wand"
    let out₁' ← mkFreshExprMVarQ prop
    let some inst2 ← ProofModeM.trySynthInstanceQ q(AddModal $out₁' $out₁ $goal)
    | throwError m!"ispecialize: AddModal type class synthesis failed with {out₁} and {goal}"
    let res ← iFrame bi _ hyps out₁' (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    let pfCont := q(fun pf => $pfCont (specialize_modal $pf' pf $inst2 $inst1))
    return { hyps := hyps', p := q(false), out := out₂, pfCont := q($pfCont), pf := none }

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
  let state : SpecializeState _ goal := { hyps, out := A, p := pa, pfCont := q(id), pf := some q(.rfl) }
  let ⟨hyps', pb, B, pfCont, pf⟩ ← spats.foldlM processWand state
  if try_dup_context then
    let pf ← do match pf with
    | some pf => pure pf
    | none => throwError "ispecialize: unable to duplicate context"
    -- context duplication succeeds if `B` is persistent, and `A` is persistent or affine
    let B' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently $pb $B $B')
    | return ⟨_, hyps', pb, B, q($(pf).trans), some q($pf)⟩
    have af : MetaM (Option Q($pa = true ∨ Affine $A)) :=
      match matchBool pa with
      | .inl _ => return some q(.inl (.refl _))
      | .inr _ => do
        let .some h ← trySynthInstanceQ q(Affine $A) | return none
        return some q(.inr $h)
    let some af ← af | return ⟨_, hyps', pb, B, q($(pf).trans), pf⟩
    return ⟨_, hyps, q(true), B', q((specialize_dup_context $pf $af).trans), some q(specialize_dup_context $pf $af)⟩
  else
    return ⟨_, hyps', pb, B, pfCont, pf⟩

end

/-- `iCasesPat.should_try_dup_context` determines when iSpecializeCore should try to duplicate the separation context.
The duplication only works if the conclusion of the specialization is persistent.

TODO: Should this also return true for lists of intuitionistic patterns? (check in Rocq)

TODO: This also needs to check that there are no modality addition patterns in `pat` once they are implemented.
-/
@[rocq_alias intro_pat_intuitionistic, rocq_alias use_tac_specialize_intuitionistic_helper]
def iCasesPat.should_try_dup_context (pat : iCasesPat) : Bool :=
  match pat with
  | .intuitionistic _ => true
  | .pure _ => true
  | _ => false

/--
  `ispecialize pmt` specialises a hypothesis according to `pmt : pmTerm`.
-/
elab "ispecialize " colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
  -- hypothesis must be in the context, otherwise use ihave
  let name := ⟨pmt.term⟩
  let some ivar ← try? <| hyps.findWithInfo name
    | throwError "{name} should be a hypothesis, use ihave instead"
  let some ⟨name, _, hyps', _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name ivar' _ _ => if ivar == ivar' then some name else none
    | throwError "ispecialize: cannot find argument"

  let ⟨_, hyps'', pb, B, pf', _⟩ ← iSpecializeCore hyps' p out goal pmt.spats
  let hyps''' := Hyps.add bi name ivar pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).1.trans <| $pf' $pf'')
