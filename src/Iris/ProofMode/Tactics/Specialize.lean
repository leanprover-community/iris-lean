/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove
import Iris.ProofMode.Tactics.Split

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

structure SpecializeState {prop : Q(Type u)} (bi : Q(BI $prop)) (orig : Q($prop)) where
  (e : Q($prop)) (hyps : Hyps bi e) (p : Q(Bool)) (out : Q($prop))
  pf : Q($orig ⊢ $e ∗ □?$p $out)

theorem specialize_wand [BI PROP] {q p : Bool} {A1 A2 A3 Q P1 P2 P3 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ □?p P1)
    [h3 : IntoWand q false Q P2 P3] [h4 : FromAssumption p P1 P2] :
    A1 ⊢ A3 ∗ □?(p && q) P3 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ?_)
  cases p with
  | false => exact (sep_mono_r h3.1).trans <| (sep_mono_l h4.1).trans wand_elim_r
  | true => exact
    (sep_mono intuitionisticallyIf_intutitionistically.2 intuitionisticallyIf_idem.2).trans <|
    intuitionisticallyIf_sep_2.trans <| intuitionisticallyIf_mono <| (sep_mono_l h4.1).trans (wand_elim' h3.1)

-- TODO: if q is true and A1 is persistent, this proof can guarantee □ P2 instead of P2
-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/846ed45bed6951035c6204fef365d9a344022ae6/iris/proofmode/coq_tactics.v#L336
theorem specialize_wand_subgoal [BI PROP] {q : Bool} {A1 A2 A3 A4 Q P1 P2 : PROP}
    (h1 : A1 ⊢ A2 ∗ □?q Q) (h2 : A2 ⊣⊢ A3 ∗ A4) (h3 : A4 ⊢ P1)
    [inst : IntoWand q false Q P1 P2] : A1 ⊢ A3 ∗ P2 := by
  refine h1.trans <| (sep_mono_l h2.1).trans <| sep_assoc.1.trans (sep_mono_r ((sep_mono_l h3).trans ?_))
  exact (sep_mono_r inst.1).trans wand_elim_r

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    [inst : IntoForall P Φ] (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim a)

def SpecializeState.process_forall :
    @SpecializeState u prop bi orig → Term → TermElabM (SpecializeState bi orig)
  | { e, hyps, p, out, pf }, arg => do
    let v ← mkFreshLevelMVar
    let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
    let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
    let _ ← synthInstanceQ q(IntoForall $out $Φ)
    let x ← elabTermEnsuringTypeQ (u := .succ .zero) arg α
    have out' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $out' =Q $Φ $x := ⟨⟩
    return { e, hyps, p, out := out', pf := q(specialize_forall $pf $x) }

def SpecializeState.process_wand (gs : @Goals u prop bi) :
    @SpecializeState u prop bi orig → SpecPat → TermElabM (SpecializeState bi orig)
  | { hyps, p, out, pf, .. }, .ident i => do
    let uniq ← hyps.findWithInfo i
    let ⟨e', hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false uniq
    let p2 := if p1.constName! == ``true then p else q(false)
    have : $out₁ =Q iprop(□?$p1 $out₁') := ⟨⟩
    have : $p2 =Q ($p1 && $p) := ⟨⟩

    let out₁'' ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let LOption.some _ ← trySynthInstanceQ q(IntoWand $p false $out $out₁'' $out₂) |
      throwError m!"ispecialize: {out} is not a wand"
    let LOption.some _ ← trySynthInstanceQ q(FromAssumption $p1 $out₁' $out₁'') |
      throwError m!"ispecialize: cannot instantiate {out} with {out₁'}"
    let pf := q(specialize_wand $pf $pf')
    return { e := e', hyps := hyps', p := p2, out := out₂, pf }
  | { hyps, p, out, pf, .. }, .goal ns g => do
    let mut uniqs : NameSet := {}
    for name in ns do
      uniqs := uniqs.insert (← hyps.findWithInfo name)
    let ⟨el', _, hypsl', hypsr', h'⟩ := Hyps.split bi (λ _ uniq => uniqs.contains uniq) hyps
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let LOption.some _ ← trySynthInstanceQ q(IntoWand $p false $out $out₁ $out₂) | throwError m!"ispecialize: {out} is not a wand"
    let pf' ← gs.addGoal hypsr' out₁ g
    let pf := q(specialize_wand_subgoal $pf $h' $pf')
    return { e := el', hyps := hypsl', p := q(false), out := out₂, pf }

def iSpecializeCore (gs : @Goals u prop bi) {e} (hyps : Hyps bi e)
  (uniq : Name) (alls : List Term) (spats : List SpecPat) : TacticM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let some ⟨name, _, hyps, _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name uniq' _ _ => if uniq == uniq' then some name else none
    | throwError "ispecialize: cannot find argument"
  let state := { hyps, out, p, pf := q(($pf).1), .. }
  let state ← liftM <| alls.foldlM SpecializeState.process_forall state
  let state ← liftM <| spats.foldlM (SpecializeState.process_wand gs) state

  let hyps' := Hyps.add bi name uniq state.p state.out state.hyps
  return ⟨_, hyps', state.pf⟩

elab "ispecialize" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let (mvar, { bi, hyps, goal, .. }) ← istart (← getMainGoal)
  mvar.withContext do
  let gs ← Goals.new bi
  -- hypothesis must be in the context, otherwise use pose proof
  let name := ⟨pmt.term⟩
  let some uniq ← try? <| hyps.findWithInfo name | throwError s!"{name} should be a hypothesis, use ihave instead"
  let ⟨_, hyps', pf⟩ ← iSpecializeCore gs hyps uniq pmt.terms pmt.spats
  let pf' ← gs.addGoal hyps' goal
  mvar.assign q(($pf).trans $pf')
  replaceMainGoal (← gs.getGoals)
