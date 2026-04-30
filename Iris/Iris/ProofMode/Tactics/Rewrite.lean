module

import Iris.BI
public import Iris.BI.InternalEq
public import Iris.ProofMode.Classes
public import Iris.Std.TC
public import Iris.ProofMode.ProofModeM
meta import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode

public section
open BI Std

theorem rewrite_goal [BI PROP] [Sbi PROP] {P Q : PROP} {A : Type _} [OFE A] {a b : A}
    (Ψ : A → PROP) [OFE.NonExpansive Ψ]
    (h_eq : P ⊢ internalEq a b)
    (h_goal : Q ⊢ Ψ a)
    : P ∗ Q ⊢ Ψ b := by
  sorry

theorem rewrite_hyp [BI PROP] [Sbi PROP] {P Q : PROP} {A : Type _} [OFE A] {a b : A}
    (Φ : A → PROP) [OFE.NonExpansive Φ]
    (h_eq : P ⊢ internalEq a b)
    (h_hyp : Q ⊢ Φ a)
    [Affine P] :
    P ∗ Q ⊢ Φ b := by
    sorry

public meta section
open Lean Elab Tactic Meta Qq BI Std

inductive RewriteDirection
  | forward
  | backward

inductive RewriteLocation
  | goal
  | hyp (name : Ident)

#check Iris.internalEq
#check IntoInternalEq
#print IntoInternalEq

private def iRewriteGoalCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (goal : Q($prop))
    (eq_hyp_name : Ident) (direction : RewriteDirection) :
    ProofModeM Q($e ⊢ $goal) := do
  let uniq ← hyps.findWithInfo eq_hyp_name
  let ⟨_, hyps', out, out', peq, _, pf⟩ := hyps.remove true uniq

  let .some _ ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"
  let v ← mkFreshLevelMVar
  let A : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a : Q($A) ← mkFreshExprMVarQ q($A)
  let b : Q($A) ← mkFreshExprMVarQ q($A)
  let ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)
  let .some out'' ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $out)
    | throwError "irewrite: {out} is not an internal equality"
  let _ ← instantiateLevelMVars v
  let _ ← instantiateMVars A
  let _ ← instantiateMVars a
  let _ ← instantiateMVars b
  let _ ← instantiateMVars ofe
  let (search, target) := match direction with
    | .forward => (a, b)
    | .backward => (b, a)

  let x ← mkFreshExprMVar (.some A)
  let goalAbstracted ← kabstract goal search
  let goalWithX := goalAbstracted.instantiate1 x
  let Ψ : Q($A → $prop) ← mkLambdaFVars #[x] goalWithX
  let .some _ ← trySynthInstanceQ q(OFE.NonExpansive $Ψ)
    | throwError "irewrite: could not synthesize NonExpansive instance for {Ψ}"
  let goal' : Q($prop) := q($Ψ $search)
  let asm : Q($prop) := q($Ψ $target)

  dbg_trace f!"{goalAbstracted} {goalWithX} {Ψ} {goal'} {asm} {goal} {target} {search}"
  let ⟨_⟩ ← assertDefEqQ goal goal'
  let pf' ← addBIGoal hyps' asm
  let _ ← addBIGoal hyps' goal -- remove, also wtf
  let _ ← addBIGoal hyps' goal' -- remove, also wtf
  let _ ← addBIGoal hyps' out -- remove, also wtf
  let eq_pf : Q($out ⊢ internalEq $target $search) := q(sorry)
  return q(Entails.trans ($pf).mp (Entails.trans sep_comm.mp (rewrite_goal $Ψ $eq_pf $pf')))

private def iRewriteHypCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (_hyps : Hyps bi e)
    (_target_hyp_name : Ident) (_eq_hyp_name : Ident)
    (_direction : RewriteDirection) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  throwError "irewrite in hypothesis: not implemented"

syntax rewriteLocation := "in" ident

elab "irewrite" dir:"←"? colGt eq_hyp:ident loc:(rewriteLocation)? : tactic => do
  let direction := if dir.isSome then RewriteDirection.backward else RewriteDirection.forward

  let location ← match loc with
    | none => pure RewriteLocation.goal
    | some loc =>
      match loc with
      | `(rewriteLocation| in $hyp:ident) => pure (RewriteLocation.hyp hyp)
      | _ => throwUnsupportedSyntax

  ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
    match location with
    | RewriteLocation.goal => do
      let pf ← iRewriteGoalCore hyps goal eq_hyp direction
      mvar.assign pf

    | RewriteLocation.hyp target_hyp => do
      let ⟨e', hyps', pf⟩ ← iRewriteHypCore hyps target_hyp eq_hyp direction
      let pf' ← addBIGoal hyps' goal
      mvar.assign q(Entails.trans $pf $pf')
