/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Iris.BI
public import Iris.BI.InternalEq
public import Iris.ProofMode.Classes
public import Iris.Std.TC
public import Iris.ProofMode.ProofModeM
public meta import Iris.ProofMode.Patterns.SpecPattern
public meta import Iris.ProofMode.Tactics.HaveCore
meta import Lean.Parser.Tactic

namespace Iris.ProofMode

public section
open BI Std

theorem rewrite_tac [Sbi PROP] {P P' Q : PROP} {A : Type _} [OFE A] {a b : A} {p}
    (Ψ : A → PROP) [ne : OFE.NonExpansive Ψ] [heq : IntoInternalEq Q a b]
    (h1 : P ⊢ P' ∗ □?p Q)
    : P ⊢ <pers> (Ψ a ∗-∗ Ψ b) :=
  calc P
  _ ⊢ P' ∗ internalEq a b := h1.trans (sep_mono_right (intuitionisticallyIf_elim.trans heq.1))
  _ ⊢ internalEq a b := sep_elim_right
  _ ⊢ internalEq (Ψ a) (Ψ b) := internalEq.of_internalEquiv_ne Ψ
  _ ⊢ <pers> internalEq (Ψ a) (Ψ b) := persistent
  _ ⊢ <pers> <affine> internalEq (Ψ a) (Ψ b) := persistently_affinely.2
  _ ⊢ <pers> (Ψ a ∗-∗ Ψ b) := persistently_mono (affinely_internalEq_wandIff _ _)

theorem rewrite_tac_symm [Sbi PROP] {P P' Q : PROP} {A : Type _} [OFE A] {a b : A} {p}
    (Ψ : A → PROP) [ne : OFE.NonExpansive Ψ] [IntoInternalEq Q a b]
    (h_eq : P ⊢ P' ∗ □?p Q)
    : P ⊢ <pers> (Ψ b ∗-∗ Ψ a) :=
      (rewrite_tac Ψ h_eq).trans (persistently_mono and_symm)

theorem rewrite_tac_goal [BI PROP] {P Q Q' : PROP}
    (h1 : P ⊢ <pers> (Q ∗-∗ Q'))
    (h2 : P ⊢ Q')
    : P ⊢ Q :=
    calc P
      _ ⊢ <pers> (Q ∗-∗ Q') ∧ Q' := and_intro h1 h2
      _ ⊢ (Q ∗-∗ Q') ∗ Q' := persistently_and_l
      _ ⊢ (Q' -∗ Q) ∗ Q' := sep_mono_left and_elim_r
      _ ⊢ Q := wand_elim_left

theorem rewrite_tac_hyp [BI PROP] {P Q Q' : PROP}
    (h1 : P ⊢ <pers> (Q ∗-∗ Q'))
    : P ⊢ <pers> (Q -∗ Q') :=
  h1.trans (persistently_mono and_elim_l)

public meta section
open Lean Elab Tactic Meta Qq BI Std Parser.Tactic


namespace IRewrite

section config

structure Config where
  occs : Occurrences := .all

declare_config_elab elabIRewriteConfig Config

end config

section location

inductive Location
  | goal
  | hyp (name : Ident)

def Location.parse (loc : Option (TSyntax `Lean.Parser.Tactic.location)) : MetaM Location := do
  let some loc := loc | return Location.goal
  match loc with
  | `(location| at ⊢) => pure Location.goal
  | `(location| at $hyp:ident) => pure (Location.hyp hyp)
  | _ => throwError "irewrite: only single location is supported (at ⊢ or at <hyp>)"

end location

section rule
syntax irwRule := patternIgnore("← " <|> "<- ")? pmTerm

inductive Direction
  | forward
  | backward

structure Rule where
  direction : Direction
  term : PMTerm

partial def Rule.parseOne (pat : TSyntax ``irwRule) : MacroM Rule := do
  match ← go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `irwRule → MacroM (Option Rule)
  | `(irwRule| ← $t) => do
    return some <| {direction := .backward, term := ← PMTerm.parse t}
  | `(irwRule| $t:pmTerm) => do
    return some <| {direction := .forward, term := ← PMTerm.parse t}
  | _ => return none

partial def Rule.parse (pats : TSyntaxArray ``irwRule) : MacroM (Array Rule) :=
  pats.mapM Rule.parseOne

end rule

end IRewrite

private def iRewriteCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (_goal : Q($prop)) (rule : IRewrite.Rule)
    (target : Q($prop))
    (occs : Occurrences := Occurrences.all) :
    ProofModeM ((target' : Q($prop)) × Q($e ⊢ <pers> ($target ∗-∗ $target'))) := do
  let g : Q($prop) ← mkFreshExprMVarQ q($prop)
  let ⟨e', _, p, eq, pf⟩ ← iHave hyps g rule.term true
  unless ← isDefEq g q(iprop($e' ∗ □?$p $eq)) do
    throwError "irewrite: could not pin the equality goal"
  have : $g =Q iprop($e' ∗ □?$p $eq) := ⟨⟩
  let pf' : Q($e ⊢ $e' ∗ □?$p $eq) := q($pf .rfl)

  let .some sbi ← trySynthInstanceQ q(Sbi $prop)
    | throwError "irewrite: could not synthesize Sbi instance"

  -- we assume that the SBI instance has bi as its BI instance
  have : $bi =Q ($sbi).toBI := ⟨⟩

  let v               ← mkFreshLevelMVar
  let A   : Q(Type v) ← mkFreshExprMVarQ q(Type v)
  let a   : Q($A)     ← mkFreshExprMVarQ q($A)
  let b   : Q($A)     ← mkFreshExprMVarQ q($A)
  let _ofe : Q(OFE $A) ← mkFreshExprMVarQ q(OFE $A)

  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoInternalEq (PROP := $prop) $eq $a $b)
    | throwError "irewrite: {eq} is not an internal equality"

  let ⟨a, _⟩ ← instantiateMVarsQ' a
  let ⟨b, _⟩ ← instantiateMVarsQ' b

  let search := match rule.direction with | .forward => a | .backward => b

  let goalAbstracted ← kabstract (occs := occs) target search
  unless goalAbstracted.hasLooseBVars do
    let (tgt, pat) ← addPPExplicitToExposeDiff target search
    throwError "irewrite: Could not find {indentExpr pat}\nin the target expression{indentExpr tgt}"
  have Ψ : Q($A → $prop) := mkLambda `x .default A goalAbstracted

  -- add OFE.NonExpansive to be solved by TC synthesis or left as a goal otherwise
  let _ ← match ← trySynthInstanceQ q(OFE.NonExpansive $Ψ) with
    | .some x => pure x
    | _ =>
      let ne ← mkFreshExprMVarQ q(OFE.NonExpansive $Ψ)
      addMVarGoal ne.mvarId!
      pure ne

  match rule.direction with
  | .forward =>
    have : $target =Q $Ψ $a := ⟨⟩
    return ⟨_, q(rewrite_tac $Ψ $pf')⟩
  | .backward => do
    have : $target =Q $Ψ $b := ⟨⟩
    return ⟨_, q(rewrite_tac_symm $Ψ $pf')⟩

def iRewriteGoal {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (rule : IRewrite.Rule) (goal : Q($prop))
    (occs : Occurrences := Occurrences.all) :
    ProofModeM Q($e ⊢ $goal) := do
  let ⟨goal', pf⟩ ← iRewriteCore hyps goal rule goal (occs := occs)
  let pf' ← addBIGoal hyps q($goal')
  return q(rewrite_tac_goal $pf $pf')

def iRewriteHyp {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (rule : IRewrite.Rule)
    (ivar : IVarId)
    (occs : Occurrences := Occurrences.all) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let some r ← hyps.replace ivar λ _ _ ty => do
    let ⟨ty', pf⟩ ← iRewriteCore hyps ty rule ty (occs := occs)
    return ⟨ty', q(rewrite_tac_hyp $pf)⟩
    | throwError "irewrite: cannot find hyp" -- should never happen
  return r

/--
  `irewrite [rules] at loc` applies a sequence `rules` of internal equalities
  (`≡`) to the locations (`loc`). The locations `loc` may contain hypothesis
  names and/or the goal, represented by `⊢`.

  Each rule is a proof mode term, optionally prefixed with `←` for
  right-to-left rewriting.

  Optionally, one can use `irewrite (occs := …) [rules] at H` to specify the occurrences.
-/
elab "irewrite " cfg:optConfig " [" rules:(IRewrite.irwRule),* "] " loc:(location)? : tactic => do
  let config ← IRewrite.elabIRewriteConfig cfg
  let location ← IRewrite.Location.parse loc
  let rules ← liftMacroM <| IRewrite.Rule.parse rules.getElems

  for rule in rules do
    ProofModeM.runTactic λ mvar { hyps, goal, .. } => do
      match location with
      | .goal =>
        let pf ← iRewriteGoal hyps rule goal config.occs
        mvar.assign pf
      | .hyp h =>
        let ivar ← hyps.findWithInfo h
        let ⟨_, hyps', pf⟩ ← iRewriteHyp hyps rule ivar config.occs
        let pf' ← addBIGoal hyps' goal
        mvar.assign q(Entails.trans $pf $pf')
