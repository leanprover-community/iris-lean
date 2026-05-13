module

import Iris.BI
public import Iris.BI.InternalEq
public import Iris.ProofMode.Classes
public import Iris.Std.TC
public import Iris.ProofMode.ProofModeM
meta import Iris.ProofMode.Tactics.Basic
meta import Lean.Parser.Tactic

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
open Lean Elab Tactic Meta Qq BI Std Parser.Tactic

namespace IRewrite
structure Config where
  occs : Occurrences := .all
end IRewrite

declare_config_elab elabIRewriteConfig IRewrite.Config

inductive RewriteDirection
  | forward
  | backward

inductive RewriteLocation
  | goal
  | hyp (name : Ident)

private def iRewriteGoalCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (goal : Q($prop))
    (eq_hyp_name : Ident) (direction : RewriteDirection)
    (occs : Occurrences := Occurrences.all) :
    ProofModeM Q($e ⊢ $goal) := do
  let uniq ← hyps.findWithInfo eq_hyp_name
  let ⟨_, hyps', out, _, _, _, pf⟩ := hyps.remove true uniq

  let .some sbi ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"

  let v ← mkFreshLevelMVar
  let A : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a : Q($A) ← mkFreshExprMVarQ q($A)
  let b : Q($A) ← mkFreshExprMVarQ q($A)
  let ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)
  let .some out'' ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $out)
    | throwError "irewrite: {out} is not an internal equality"

  let A   : Q(Type v)  ← instantiateMVars A
  let a   : Q($A)      ← instantiateMVars a
  let b   : Q($A)      ← instantiateMVars b
  let ofe : Q(OFE $A)  ← instantiateMVars ofe
  let out'' : Q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $out) :=
    ← instantiateMVars out''

  let search := match direction with | .forward => a | .backward => b

  let goalAbstracted ← kabstract (occs := occs) goal search
  unless goalAbstracted.hasLooseBVars do
    let (tgt, pat) ← addPPExplicitToExposeDiff goal search
    throwError "irewrite: Could not find {indentExpr pat}\nin the target expression{indentExpr tgt}"
  have Ψ : Q($A → $prop) := mkLambda `x .default A goalAbstracted
  let inst ← trySynthInstanceQ q(OFE.NonExpansive $Ψ)
  let _ ← match inst with
    | .some x => pure x
    | _ =>
      let ne ← mkFreshExprMVarQ q(OFE.NonExpansive $Ψ)
      modify ({goals := ·.goals.push ne.mvarId!})
      pure ne

  match direction with
  | .forward => do
      -- FIXME: mkAppOptM is used to bypass Qq's BI-instance mismatch for internalEq.symm.
      let into_eq : Expr := q(($out'').into_internal_eq)
      let symm_app ← mkAppOptM ``internalEq.symm #[prop, sbi, A, ofe, a, b]
      let eq_pf_expr ← mkAppOptM ``Entails.trans #[prop, none, none, none, none, into_eq, symm_app]
      let eq_pf : Q($out ⊢ internalEq $b $a) := eq_pf_expr
      let pf' ← addBIGoal hyps' q($Ψ $b)
      let inner : Expr := q(Entails.trans ($pf).mp (Entails.trans sep_comm.mp (rewrite_goal $Ψ $eq_pf $pf')))
      return inner
  | .backward => do
      let eq_pf : Q($out ⊢ internalEq $a $b) := q(($out'').into_internal_eq)
      let pf' ← addBIGoal hyps' q($Ψ $a)
      let inner : Expr := q(Entails.trans ($pf).mp (Entails.trans sep_comm.mp (rewrite_goal $Ψ $eq_pf $pf')))
      return inner

private def iRewriteHypCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (_hyps : Hyps bi e)
    (_target_hyp_name : Ident) (_eq_hyp_name : Ident)
    (_direction : RewriteDirection) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  throwError "irewrite in hypothesis: not implemented"

syntax irwRule    := patternIgnore("← " <|> "<- ")? ident
syntax irwRuleSeq := " [" withoutPosition(irwRule,*,?) "]"

elab (name := irewriteSeq) "irewrite" cfg:optConfig "[" rules:(irwRule),* "]" loc:(location)? : tactic => do
  let config ← elabIRewriteConfig cfg
  let location : RewriteLocation ← match loc with
    | none => pure RewriteLocation.goal
    | some loc => match loc with
      | `(location| at ⊢) => pure RewriteLocation.goal
      | `(location| at $hyp:ident) => pure (RewriteLocation.hyp hyp)
      | _ => throwError "irewrite: unsupported location"
  for rule in rules.getElems do
    let direction : RewriteDirection :=
      if rule.raw[0].getArgs.isEmpty then .forward else .backward
    let eq_hyp : Ident := ⟨rule.raw[1]⟩
    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      match location with
      | RewriteLocation.goal =>
        let pf ← iRewriteGoalCore hyps goal eq_hyp direction config.occs
        mvar.assign pf
      | RewriteLocation.hyp target_hyp =>
        let ⟨_, hyps', pf⟩ ← iRewriteHypCore hyps target_hyp eq_hyp direction
        let pf' ← addBIGoal hyps' goal
        mvar.assign q(Entails.trans $pf $pf')
