module

import Iris.BI
public import Iris.BI.InternalEq
public import Iris.ProofMode.Classes
public import Iris.Std.TC
public import Iris.ProofMode.ProofModeM
public meta import Iris.ProofMode.Patterns.ProofModeTerm
public meta import Iris.ProofMode.Tactics.HaveCore
public meta import Iris.ProofMode.Tactics.Cases
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

theorem rewrite_tac_symm [Sbi PROP] {R P Q : PROP} {A : Type _} [OFE A] {a b : A}
    (Ψ : A → PROP) [OFE.NonExpansive Ψ]
    (h_eq : P ⊢ internalEq b a)
    (h_split : R ⊢ P ∗ Q)
    (h_goal : R ⊢ Ψ a)
    : R ⊢ Ψ b :=
  internalEq.rewrite' Ψ
    ((h_split.trans ((sep_mono_l h_eq).trans sep_elim_l)).trans internalEq.symm)
    h_goal

theorem rewrite_tac_hyp [Sbi PROP] {R P Q : PROP} {A : Type _} [OFE A] {a b : A}
    (Ψ : A → PROP) [OFE.NonExpansive Ψ]
    (h_eq : R ⊢ internalEq a b)
    (h_split : P ⊢ R ∗ (Q ∗ Ψ a))
    : P ⊢ R ∗ (Q ∗ Ψ b) :=
  letI _ : OFE.NonExpansive (fun x => iprop(R ∗ (Q ∗ Ψ x))) :=
    ⟨fun _ _ _ H => sep_ne.ne .rfl (sep_ne.ne .rfl (OFE.NonExpansive.ne H))⟩
  rewrite_tac (fun x => iprop(R ∗ (Q ∗ Ψ x))) h_eq h_split h_split

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
  let ⟨e', _, p, inner, pf⟩ ← iHave hyps pmt true (try_dup_context := true)
  let out : Q($prop) := q(intuitionisticallyIf $p $inner)

  let .some sbi ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"

  let v               ← mkFreshLevelMVar
  let A   : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a   : Q($A)     ← mkFreshExprMVarQ q($A)
  let b   : Q($A)     ← mkFreshExprMVarQ q($A)
  let ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)

  let .some out'' ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner)
    | throwError "irewrite: {out} is not an internal equality"

  let A   : Q(Type v)  ← instantiateMVars A
  let a   : Q($A)      ← instantiateMVars a
  let b   : Q($A)      ← instantiateMVars b
  let ofe : Q(OFE $A)  ← instantiateMVars ofe
  let out'' : Q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner)
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
  let h_split : Q($e ⊢ intuitionisticallyIf $p $inner ∗ $e') :=
    q(Entails.trans $pf (sep_comm (P := $e') (Q := intuitionisticallyIf $p $inner)).mp)
  match direction with
  | .forward => do
      let h_goal ← addBIGoal hyps q($Ψ $b)
      mkAppOptM ``rewrite_tac_symm
        #[prop, sbi, none, none, none, A, ofe, b, a, Ψ, ne_inst, eq_pf_direct, h_split, h_goal]
  | .backward => do
      let h_goal ← addBIGoal hyps q($Ψ $a)
      mkAppOptM ``rewrite_tac
        #[prop, sbi, none, none, none, A, ofe, a, b, Ψ, ne_inst, eq_pf_direct, h_split, h_goal]

private def iRewriteHypCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e)
    (target_hyp_name : Ident) (eq_pmt : PMTerm)
    (direction : RewriteDirection)
    (occs : Occurrences := Occurrences.all) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let ⟨e', hyps', p', inner', pf'⟩ ← iHave hyps eq_pmt true (try_dup_context := true)
  let some (uniq_target, _, _) := hyps'.find? target_hyp_name.getId
    | throwError "iRewriteHypCore: unknown target hypothesis {target_hyp_name}"
  let ⟨e'', hyps'', p'', inner'', pf''⟩ ← iHave hyps ⟨⟨target_hyp_name.raw⟩, []⟩ false
  let out : Q($prop) := q(intuitionisticallyIf $p' $inner')

  let .some sbi ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"

  let v               ← mkFreshLevelMVar
  let A   : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a   : Q($A)     ← mkFreshExprMVarQ q($A)
  let b   : Q($A)     ← mkFreshExprMVarQ q($A)
  let ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)

  let .some out' ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner')
    | throwError "irewrite: {out} is not an internal equality"

  let A   : Q(Type v)  ← instantiateMVars A
  let a   : Q($A)      ← instantiateMVars a
  let b   : Q($A)      ← instantiateMVars b
  let ofe : Q(OFE $A)  ← instantiateMVars ofe
  let out'' : Q(IntoInternalEq (PROP := $prop) (ofe := $ofe) (A := $A) (x := $a) (y := $b) $inner')
    ← instantiateMVars out'

  let search := match direction with | .forward => a | .backward => b

  let targetAbstracted ← kabstract (occs := occs) inner'' search
  unless targetAbstracted.hasLooseBVars do
    let (tgt, pat) ← addPPExplicitToExposeDiff inner'' search
    throwError "irewrite: Could not find {indentExpr pat}\nin the hypothesis{indentExpr tgt}"

  have Ψ : Q($A → $prop) := mkLambda `x .default A targetAbstracted
  let ne_inst ← match ← trySynthInstanceQ q(OFE.NonExpansive $Ψ) with
    | .some x => pure x
    | _ =>
      let ne ← mkFreshExprMVarQ q(OFE.NonExpansive $Ψ)
      modify ({goals := ·.goals.push ne.mvarId!})
      pure ne

  let eq_pf_direct : Q($out ⊢ internalEq $a $b) :=
    q(intuitionisticallyIf_elim.trans ($out'').into_internal_eq)
  let .some _ ← ProofModeM.trySynthInstanceQ q(Absorbing (internalEq (PROP := $prop) $a $b))
    | throwError "irewrite: you should not get this error"
  let pff : Q($e ⊢ internalEq $a $b) := q((($pf').trans (sep_mono_r $eq_pf_direct)).trans sep_elim_r)
  let h_split : Q($e ⊢ intuitionisticallyIf $p' $inner' ∗ ($e'' ∗ intuitionisticallyIf $p'' $inner'')) :=
    q($pf' |>.trans (sep_comm (P := $e') (Q := intuitionisticallyIf $p' $inner')).mp |>.trans (sep_mono_r $pf''))
  match direction with
  | .forward => do
      -- let symm_app ← mkAppOptM ``internalEq.symm #[prop, sbi, A, ofe, a, b]
      -- let eq_pf_expr ← mkAppOptM ``Entails.trans #[prop, none, none, none, none, eq_pf_direct, symm_app]
      -- let eq_pf : Q($out ⊢ internalEq $b $a) := eq_pf_expr
      let t ← mkAppOptM ``rewrite_tac_hyp
        #[prop, sbi, none, none, none, A, ofe, a, b, Ψ, ne_inst, eq_pf_direct, h_split]
      let hyps''' := Hyps.add bi target_hyp_name.getId uniq_target p'' q($Ψ $b) hyps''
      return ⟨q(sep $e'' (intuitionisticallyIf $p'' ($Ψ $b))), hyps''', t⟩
  | .backward => do
      throwError "A"

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
        let ⟨_, hyps', pf⟩ ← iRewriteHypCore hyps target_hyp eq_pmt direction config.occs
        let pf' ← addBIGoal hyps' goal
        mvar.assign q(Entails.trans $pf $pf')
