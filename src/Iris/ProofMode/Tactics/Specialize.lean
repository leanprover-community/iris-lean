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

theorem specialize_forall [BI PROP] {p : Bool} {A1 A2 P : PROP} {α : Sort _} {Φ : α → PROP}
    [inst : IntoForall P Φ] (h : A1 ⊢ A2 ∗ □?p P) (a : α) : A1 ⊢ A2 ∗ □?p (Φ a) := by
  refine h.trans <| sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim a)

def SpecializeState.process_wand :
    @SpecializeState u prop bi orig → SpecPat → ProofModeM (SpecializeState bi orig)
  | { hyps, p, out, pf, .. }, .ident i => do
    let uniq ← hyps.findWithInfo i
    let ⟨e', hyps', out₁, out₁', p1, _, pf'⟩ := hyps.remove false uniq
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
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoForall $out $Φ) | throwError "ispecialize: {out} is not a lean premise"
    let x ← elabTermEnsuringTypeQ (u := .succ .zero) t α
    have out' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $out' =Q $Φ $x := ⟨⟩
    let newMVarIds ← getMVarsNoDelayed x
    for mvar in newMVarIds do addMVarGoal mvar
    return { e, hyps, p, out := out', pf := q(specialize_forall $pf $x) }
  | { hyps, p, out, pf, .. }, .goal ns g => do
    let mut uniqs : NameSet := {}
    for name in ns do
      uniqs := uniqs.insert (← hyps.findWithInfo name)
    let ⟨el', _, hypsl', hypsr', h'⟩ := Hyps.split bi (λ _ uniq => uniqs.contains uniq) hyps
    let out₁ ← mkFreshExprMVarQ prop
    let out₂ ← mkFreshExprMVarQ prop
    let some _ ← ProofModeM.trySynthInstanceQ q(IntoWand $p false $out .out $out₁ .out $out₂) | throwError m!"ispecialize: {out} is not a wand"
    let pf' ← addBIGoal hypsr' out₁ g
    let pf := q(specialize_wand_subgoal $out₂ $pf $h' $pf')
    return { e := el', hyps := hypsl', p := q(false), out := out₂, pf }

def iSpecializeCore {e} (hyps : @Hyps u prop bi e)
  (uniq : Name) (spats : List SpecPat) : ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let some ⟨name, _, hyps, _, out, p, _, pf⟩ := Id.run <|
    hyps.removeG true λ name uniq' _ _ => if uniq == uniq' then some name else none
    | throwError "ispecialize: cannot find argument"
  let state := { hyps, out, p, pf := q(($pf).1), .. }
  let state ← spats.foldlM (SpecializeState.process_wand) state

  let hyps' := Hyps.add bi name uniq state.p state.out state.hyps
  return ⟨_, hyps', state.pf⟩

elab "ispecialize" colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
  -- hypothesis must be in the context, otherwise use pose proof
  let name := ⟨pmt.term⟩
  let some uniq ← try? <| hyps.findWithInfo name | throwError s!"{name} should be a hypothesis, use ihave instead"
  let ⟨_, hyps', pf⟩ ← iSpecializeCore hyps uniq pmt.spats
  let pf' ← addBIGoal hyps' goal
  mvar.assign q(($pf).trans $pf')
