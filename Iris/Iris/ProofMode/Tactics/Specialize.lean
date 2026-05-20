/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
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
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ □?p P1)
    [h3 : IntoWand q p Q .in P1 .out P2] :
    A1 ⊢ A3 ∗ □?(p && q) P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ?_)
  cases p with
  | false => exact (sep_mono_r h3.1).trans <| wand_elim_r
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.2 intuitionisticallyIf_idem.2).trans <|
    intuitionisticallyIf_sep_2.trans <| intuitionisticallyIf_mono <| (wand_elim' h3.1)

-- TODO: if q is true and A1 is persistent, this proof can guarantee □ P2 instead of P2
-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/846ed45bed6951035c6204fef365d9a344022ae6/iris/proofmode/coq_tactics.v#L336
theorem specialize_wand_subgoal [BI PROP] {q : Bool} {A1 A2 A3 A4 Q P1 : PROP} P2
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1)
    [inst : IntoWand q false Q .out P1 .out P2] : A1 ⊢ A3 ∗ P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ((sep_mono_l h3).trans ?_))
  exact (sep_mono_r inst.1).trans wand_elim_r

theorem specialize_wand_autoframe [BI PROP] {q : Bool} {A1 A2 A3 Q P1 : PROP} P2
     (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊢ A3 ∗ P1)
     [inst : IntoWand q false Q .out P1 .out P2] : A1 ⊢ A3 ∗ P2 :=
  h1.trans <| (sep_mono_l h2).trans <| sep_assoc.1.trans
    (sep_mono_r ((sep_mono_r inst.into_wand).trans wand_elim_r))

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    [inst : IntoForall P Φ] (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim a)

theorem specialize_dup_context [BI PROP] {P : PROP} {pa A P' pb B}
  (h : P ∗ □?pa A ⊢ P' ∗ □?pb B)
  (h2 : pa = true ∨ Affine A)
  [IntoPersistently pb B B']
  : P ∗ □?pa A ⊢ P ∗ □ B' := by
    apply Entails.trans _ persistently_and_intuitionistically_sep_r.1
    apply and_intro
    · cases h2 <;> subst_eqs <;> apply sep_elim_l
    · apply h.trans $ (sep_mono_r (persistentlyIf_of_intuitionisticallyIf.trans into_persistently)).trans sep_elim_r

public meta section
open Lean Elab Tactic Meta Qq Std

structure SpecializeState {prop : Q(Type u)} (bi : Q(BI $prop)) (orig : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (p : Q(Bool)) (out : Q($prop))
  pf : Q($orig ⊢ $e ∗ □?$p $out)

private def processWand :
    @SpecializeState u prop bi orig → SpecPat → ProofModeM (SpecializeState bi orig)
  | { hyps, p, out, pf, .. }, .ident i => do
    let ivar ← hyps.findWithInfo i
    let ⟨e', hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false ivar
    let p2 := if p1.constName! == ``true then p else q(false)
    have : $out₁ =Q iprop(□?$p1 $out₁') := ⟨⟩
    have : $p2 =Q ($p1 && $p) := ⟨⟩

    let out₂ ← mkFreshExprMVarQ prop
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p $p1 $out .in $out₁' .out $out₂) |
      throwError m!"ispecialize: cannot instantiate {out} with {out₁'}"
    let pf := q(specialize_wand $pf $pf')
    return { e := e', hyps := hyps', p := p2, out := out₂, pf }
  | { e, hyps, p, out, pf, .. }, .pure t => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ)
      | throwError "ispecialize: {out} is not a lean premise"
    let x ← elabTermEnsuringTypeQ (u := .succ .zero) t α
    have out' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $out' =Q $Φ $x := ⟨⟩
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    return { e, hyps, p, out := out', pf := q(specialize_forall $pf $x) }
  | { hyps, p, out, pf, .. }, .goal {kind, negate, trivial, frame := f, hyps := hs} g => do
    if kind != .spatial then
      -- TODO
      throwError "ispecialize: only spatial kind is supported at the moment"
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
    let ⟨el', _, hypsl', hypsr', pf'⟩ := Hyps.split bi
      (λ _ ivar => (negate ^^ ivars.contains ivar) || frameIVars.contains ivar) hyps
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
      | throwError m!"ispecialize: {out} is not a wand"
    let res ← iFrame bi _ hypsr' out₁ (frameIVars.map (⟨.ipm ·, true⟩))
    let pf'' ← res.finish λ hyps goal => do
      if trivial then
        let some r ← iTrivial hyps goal
          | throwError "ispecialize: itrivial could not solve {← ppExpr <| IrisGoal.toExpr {hyps, goal ..}}"
        return r
      else
        addBIGoal hyps goal g
    let pf := q(specialize_wand_subgoal $out₂ $pf $pf' $pf'')
    return { e := el', hyps := hypsl', p := q(false), out := out₂, pf }

  | { hyps, p, out, pf, .. }, .autoframe kind => do
    if kind != .spatial then
      -- TODO
      throwError "ispecialize: only spatial kind is supported at the moment"
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂)
      | throwError m!"ispecialize: {out} is not a wand"
    let res ← iFrame bi _ hyps out₁ (← SelPat.resolve hyps [.spatial, .intuitionistic])
    let ⟨_, hyps', pf'⟩ ← res.finishClose
    return { e := _, hyps := hyps', p := q(false), out := out₂, pf := q(specialize_wand_autoframe $out₂ $pf $pf') }

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
def iSpecializeCore {e} (hyps : @Hyps u prop bi e) (pa : Q(Bool)) (A : Q($prop)) (spats : List SpecPat) (try_dup_context : Bool := false) :
  ProofModeM ((e' : _) × Hyps bi e' × (pb : Q(Bool)) × (B : Q($prop)) × Q($e ∗ □?$pa $A ⊢ $e' ∗ □?$pb $B)) := do
  let state := { hyps, out := A, p := pa, pf := q(.rfl), .. }
  let ⟨_, hyps', pb, B, pf⟩ ← spats.foldlM processWand state
  if try_dup_context then
    -- context duplication succeeds if `B` is persistent, and `A` is persistent or affine
    let B' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let .some _ ← trySynthInstanceQ q(IntoPersistently $pb $B $B')
      | return ⟨_, hyps', pb, B, pf⟩
    have af : MetaM (Option Q($pa = true ∨ Affine $A)) :=
      match matchBool pa with
      | .inl _ => return some q(.inl (.refl _))
      | .inr _ => do
        let .some h ← trySynthInstanceQ q(Affine $A) | return none
        return some q(.inr $h)
    let some af ← af | return ⟨_, hyps', pb, B, pf⟩
    return ⟨_, hyps, q(true), B', q(specialize_dup_context $pf $af)⟩
  return ⟨_, hyps', pb, B, pf⟩

elab "ispecialize" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { bi, hyps, goal, .. } => do
  -- hypothesis must be in the context, otherwise use ihave
  let name := ⟨pmt.term⟩
  let some ivar ← try? <| hyps.findWithInfo name
    | throwError "{name} should be a hypothesis, use ihave instead"
  let some ⟨name, _, hyps', _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name ivar' _ _ => if ivar == ivar' then some name else none
    | throwError "ispecialize: cannot find argument"

  let ⟨_, hyps'', pb, B, pf'⟩ ← iSpecializeCore hyps' p out pmt.spats
  let hyps''' := Hyps.add bi name ivar pb B hyps''
  let pf'' ← addBIGoal hyps''' goal
  mvar.assign q(($pf).1.trans <| $(pf').trans <| $pf'')
