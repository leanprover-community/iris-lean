module

import Iris.BI
public import Iris.BI.InternalEq
public import Iris.ProofMode.Classes
public import Iris.Std.TC
public import Iris.ProofMode.ProofModeM
public meta import Iris.ProofMode.Patterns.ProofModeTerm
public meta import Iris.ProofMode.Tactics.HaveCore
meta import Lean.Parser.Tactic

namespace Iris.ProofMode

public section
open BI Std

theorem rewrite_tac [Sbi PROP] {R P Q : PROP} {A : Type _} [OFE A] {a b : A}
    (Ψ : A → PROP) [OFE.NonExpansive Ψ]
    (h_eq : P ⊢ internalEq a b)
    (h_split : R ⊢ P ∗ Q)
    (h_goal : R ⊢ Ψ a)
    : R ⊢ Ψ b :=
  internalEq.rewrite' Ψ
    (h_split.trans ((sep_mono_l h_eq).trans sep_elim_l))
    h_goal

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
    (pmt : PMTerm) (direction : RewriteDirection)
    (occs : Occurrences := Occurrences.all) :
    ProofModeM Q($e ⊢ $goal) := do
  let ⟨e', _, p, inner, pf⟩ ← iHave hyps pmt false
  let out : Q($prop) := q(intuitionisticallyIf $p $inner)

  let .some sbi ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"

  let v ← mkFreshLevelMVar
  let A : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a : Q($A) ← mkFreshExprMVarQ q($A)
  let b : Q($A) ← mkFreshExprMVarQ q($A)
  let ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)

  let .some out'' ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner)
    | throwError "irewrite: {out} is not an internal equality"

  let A   : Q(Type v)  ← instantiateMVars A
  let a   : Q($A)      ← instantiateMVars a
  let b   : Q($A)      ← instantiateMVars b
  let ofe : Q(OFE $A)  ← instantiateMVars ofe

  let out'' : Q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner) :=
    ← instantiateMVars out''

  let search := match direction with | .forward => a | .backward => b

  let goalAbstracted ← kabstract (occs := occs) goal search
  unless goalAbstracted.hasLooseBVars do
    let (tgt, pat) ← addPPExplicitToExposeDiff goal search
    throwError "irewrite: Could not find {indentExpr pat}\nin the target expression{indentExpr tgt}"
  have Ψ : Q($A → $prop) := mkLambda `x .default A goalAbstracted
  let ne_inst ← match ← trySynthInstanceQ q(OFE.NonExpansive $Ψ) with
    | .some x => pure x
    | _ =>
      let ne ← mkFreshExprMVarQ q(OFE.NonExpansive $Ψ)
      modify ({goals := ·.goals.push ne.mvarId!})
      pure ne

  let eq_pf_direct : Q($out ⊢ internalEq $a $b) :=
    q(intuitionisticallyIf_elim.trans ($out'').into_internal_eq)

  let sc ← mkAppOptM ``sep_comm #[prop, bi, e', out]
  let sep_comm_mp ← mkAppOptM ``Iris.BI.BIBase.BiEntails.mp #[prop, none, none, none, sc]
  let h_split ← mkAppOptM ``Entails.trans #[prop, none, none, none, none, (pf : Expr), sep_comm_mp]
  match direction with
  | .forward => do
      let symm_app ← mkAppOptM ``internalEq.symm #[prop, sbi, A, ofe, a, b]
      let eq_pf_expr ← mkAppOptM ``Entails.trans #[prop, none, none, none, none, eq_pf_direct, symm_app]
      let eq_pf : Q($out ⊢ internalEq $b $a) := eq_pf_expr
      let h_goal ← addBIGoal hyps q($Ψ $b)
      let rw_pf ← mkAppOptM ``rewrite_tac
        #[prop, sbi, none, none, none, A, ofe, b, a, Ψ, ne_inst, eq_pf, h_split, h_goal]
      return rw_pf
  | .backward => do
      let eq_pf : Q($out ⊢ internalEq $a $b) := eq_pf_direct
      let h_goal ← addBIGoal hyps q($Ψ $a)
      let rw_pf ← mkAppOptM ``rewrite_tac
        #[prop, sbi, none, none, none, A, ofe, a, b, Ψ, ne_inst, eq_pf, h_split, h_goal]
      return rw_pf

private def iRewriteHypCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (_hyps : Hyps bi e)
    (_target_hyp_name : Ident) (_eq_pmt : PMTerm)
    (_direction : RewriteDirection) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  throwError "irewrite in hypothesis: not implemented"

syntax irwRule    := patternIgnore("← " <|> "<- ")? pmTerm
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
    let eq_pmt ← liftMacroM <| PMTerm.parse (⟨rule.raw[1]⟩ : TSyntax `pmTerm)
    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      match location with
      | RewriteLocation.goal =>
        let pf ← iRewriteGoalCore hyps goal eq_pmt direction config.occs
        mvar.assign pf
      | RewriteLocation.hyp target_hyp =>
        let ⟨_, hyps', pf⟩ ← iRewriteHypCore hyps target_hyp eq_pmt direction
        let pf' ← addBIGoal hyps' goal
        mvar.assign q(Entails.trans $pf $pf')
