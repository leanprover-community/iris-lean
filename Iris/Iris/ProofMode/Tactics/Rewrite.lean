/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

import Iris.BI
public import Iris.ProofMode.Tactics.HaveCore

namespace Iris.ProofMode

public section
open BI Iris.Std

section
-- `PROP` first: it precedes the step index in the signatures below
variable {PROP : Type _} {SI : stepindex (Type _)} [SIdx SI]
local stepindex SI

@[indexed]
theorem rewrite_tac [BI PROP] [BIStepIndexed PROP] [Sbi PROP]
    {P P' Q : PROP} {A : Type _} [OFE A] {a b : A} {p}
    (Ψ : A → PROP) [ne : OFE.NonExpansive Ψ] [heq : IntoInternalEq Q a b]
    (h1 : P ⊢ P' ∗ □?p Q) : P ⊢ <pers> (Ψ a ∗-∗ Ψ b) := calc
  P ⊢ P' ∗ a ≡ b := h1.trans (sep_mono_right (intuitionisticallyIf_elim.trans heq.1))
  _ ⊢ a ≡ b := sep_elim_right
  _ ⊢ Ψ a ≡ Ψ b := internalEq.of_internalEquiv_ne Ψ
  _ ⊢ <pers> (Ψ a ≡ Ψ b) := persistent
  _ ⊢ <pers> <affine> Ψ a ≡ Ψ b := persistently_affinely.2
  _ ⊢ <pers> (Ψ a ∗-∗ Ψ b) := persistently_mono (affinely_internalEq_wandIff _ _)

@[indexed]
theorem rewrite_tac_symm [BI PROP] [BIStepIndexed PROP] [Sbi PROP]
    {P P' Q : PROP} {A : Type _} [OFE A] {a b : A} {p}
    (Ψ : A → PROP) [ne : OFE.NonExpansive Ψ] [IntoInternalEq Q a b]
    (h_eq : P ⊢ P' ∗ □?p Q) : P ⊢ <pers> (Ψ b ∗-∗ Ψ a) :=
  (rewrite_tac Ψ h_eq).trans (persistently_mono and_symm)

end

@[rocq_alias tac_rewrite]
theorem rewrite_tac_goal [BI PROP] {P Q Q' : PROP}
    (h1 : P ⊢ <pers> (Q ∗-∗ Q'))
    (h2 : P ⊢ Q') : P ⊢ Q :=
  calc
    _ ⊢ <pers> (Q ∗-∗ Q') ∧ Q' := and_intro h1 h2
    _ ⊢ (Q ∗-∗ Q') ∗ Q' := persistently_and_l
    _ ⊢ (Q' -∗ Q) ∗ Q' := sep_mono_left and_elim_r
    _ ⊢ Q := wand_elim_left

@[rocq_alias tac_rewrite_in]
theorem rewrite_tac_hyp [BI PROP] {P Q Q' : PROP}
    (h1 : P ⊢ <pers> (Q ∗-∗ Q')) : P ⊢ <pers> (Q -∗ Q') :=
  h1.trans (persistently_mono and_elim_l)

public meta section
open Lean Elab Tactic Meta Qq BI Iris.Std Parser.Tactic

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

def Location.parse (loc : Option (TSyntax `Lean.Parser.Tactic.location)) : ProofModeM Location := do
  let some loc := loc | return Location.goal
  match loc with
  | `(location| at ⊢) => pure Location.goal
  | `(location| at $hyp:ident) => pure (Location.hyp hyp)
  | _ => throwIPMError "only single location is supported (at ⊢ or at <hyp>)"

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

/-- Step-index candidates for `irewrite`: the `SI` of every `SIdx SI` instance occurring in the
equality `eq`, then of every local `SIdx SI` / `BIStepIndexed SI _` instance, then `Nat`. -/
private def rewriteSICandidates (eq : Expr) : MetaM (Array Expr) := do
  let mut cands : Array Expr := #[]
  let push (cands : Array Expr) (ty : Expr) : Array Expr :=
    let si? :=
      if ty.isAppOfArity ``SIdx 1 || ty.isAppOfArity ``BIStepIndexed 4 then some ty.getAppArgs[0]!
      else none
    match si? with
    | some si => if cands.contains si then cands else cands.push si
    | none => cands
  let mut todo : Array Expr := #[eq]
  let mut seen : Std.HashSet Expr := {}
  while h : todo.size > 0 do
    let t := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains t then continue
    seen := seen.insert t
    if !t.hasLooseBVars && (t.isApp || t.isConst || t.isFVar) then
      try cands := push cands (← whnfR (← inferType t)) catch _ => pure ()
    match t with
    | .app f x => todo := (todo.push f).push x
    | .mdata _ b => todo := todo.push b
    | .lam _ ty b _ | .forallE _ ty b _ => todo := (todo.push ty).push b
    | .letE _ ty v b _ => todo := ((todo.push ty).push v).push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  for inst in ← getLocalInstances do
    cands := push cands (← instantiateMVars (← inferType inst.fvar))
  unless cands.contains q(Nat) do cands := cands.push q(Nat)
  return cands

/-- `irewrite` at the step index `si`: fails (returns `none`) if `eq` is not an internal equality
over `si`. -/
private def iRewriteCoreAt {prop : Q(Type u)} {bi : Q(BI $prop)} {v : Level} (si : Q(Type v))
    (_sidx : Q(SIdx $si)) (_bsi : Q(BIStepIndexed $si $prop)) (_sbi : Q(Sbi $si $prop))
    {e e' : Q($prop)} (p : Q(Bool)) (eq : Q($prop)) (pf' : Q($e ⊢ $e' ∗ □?$p $eq))
    (rule : IRewrite.Rule) (target : Q($prop)) (occs : Occurrences) :
    ProofModeM (Option ((target' : Q($prop)) × Q($e ⊢ <pers> ($target ∗-∗ $target')))) := do
  let w               ← mkFreshLevelMVar
  let A   : Q(Type w) ← mkFreshExprMVarQ q(Type w)
  let a   : Q($A)     ← mkFreshExprMVarQ q($A)
  let b   : Q($A)     ← mkFreshExprMVarQ q($A)
  let _ofe : Q(OFE $si $A) ← mkFreshExprMVarQ q(OFE $si $A)

  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoInternalEq $si (PROP := $prop) $eq $a $b)
    | return none

  let ⟨a, _⟩ ← instantiateMVarsQ' a
  let ⟨b, _⟩ ← instantiateMVarsQ' b

  let search := match rule.direction with | .forward => a | .backward => b

  let goalAbstracted ← kabstract (occs := occs) target search
  unless goalAbstracted.hasLooseBVars do
    let (tgt, pat) ← addPPExplicitToExposeDiff target search
    throwIPMError "Could not find {indentExpr pat}\nin the target expression{indentExpr tgt}"
  have Ψ : Q($A → $prop) := mkLambda `x .default A goalAbstracted

  -- add OFE.NonExpansive to be solved by TC synthesis or left as a goal otherwise
  let _ ← match ← trySynthInstanceQ q(OFE.NonExpansive $si $Ψ) with
    | .some x => pure x
    | _ =>
      let ne ← mkFreshExprMVarQ q(OFE.NonExpansive $si $Ψ)
      addMVarGoal ne.mvarId!
      pure ne

  match rule.direction with
  | .forward =>
    have : $target =Q $Ψ $a := ⟨⟩
    return some ⟨_, q(rewrite_tac (SI := $si) $Ψ $pf')⟩
  | .backward => do
    have : $target =Q $Ψ $b := ⟨⟩
    return some ⟨_, q(rewrite_tac_symm (SI := $si) $Ψ $pf')⟩

private def iRewriteCore {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (rule : IRewrite.Rule)
    (target : Q($prop))
    (occs : Occurrences := Occurrences.all) :
    ProofModeM ((target' : Q($prop)) × Q($e ⊢ <pers> ($target ∗-∗ $target'))) := do
  let g : Q($prop) ← mkFreshExprMVarQ q($prop)
  let ⟨e', _, p, eq, pf⟩ ← iHave hyps g rule.term true
  unless ← isDefEq g q(iprop($e' ∗ □?$p $eq)) do
    throwIPMError "could not pin the equality goal"
  have : $g =Q iprop($e' ∗ □?$p $eq) := ⟨⟩
  let pf' : Q($e ⊢ $e' ∗ □?$p $eq) := q($pf .rfl)

  -- The step index is genuinely needed here: it is the one of the internal equality `eq`.
  for cand in ← rewriteSICandidates (← instantiateMVars eq) do
    let v ← getDecLevel cand
    have si : Q(Type v) := cand
    let some sidx ← synthInstance? q(SIdx $si) | continue
    have sidx : Q(SIdx $si) := sidx
    let some bsi ← synthInstance? q(BIStepIndexed $si $prop) | continue
    have bsi : Q(BIStepIndexed $si $prop) := bsi
    let some sbi ← synthInstance? q(Sbi $si $prop) | continue
    let s ← saveState
    if let some res ← iRewriteCoreAt si sidx bsi sbi p eq pf' rule target occs then
      return res
    s.restore
  throwIPMError "{eq} is not an internal equality"

def iRewriteGoal {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (rule : IRewrite.Rule) (goal : Q($prop))
    (occs : Occurrences := Occurrences.all) :
    ProofModeM Q($e ⊢ $goal) := do
  let ⟨goal', pf⟩ ← iRewriteCore hyps rule goal (occs := occs)
  let pf' ← addBIGoal hyps q($goal')
  return q(rewrite_tac_goal $pf $pf')

def iRewriteHyp {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e} (hyps : Hyps bi e) (rule : IRewrite.Rule)
    (ivar : IVarId)
    (occs : Occurrences := Occurrences.all) :
    ProofModeM ((e' : _) × Hyps bi e' × Q($e ⊢ $e')) := do
  let some r ← hyps.replace ivar fun _ _ ty => do
    let ⟨ty', pf⟩ ← iRewriteCore hyps rule ty (occs := occs)
    return ⟨ty', q(rewrite_tac_hyp $pf)⟩
    | throwIPMError "cannot find hyp" -- should never happen
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
  let rules ← liftMacroM <| IRewrite.Rule.parse rules.getElems

  for rule in rules do
    ProofModeM.runTactic `irewrite fun mvar { hyps, goal, .. } => do
      let location ← IRewrite.Location.parse loc
      match location with
      | .goal =>
        let pf ← iRewriteGoal hyps rule goal config.occs
        mvar.assign pf
      | .hyp h =>
        let ivar ← hyps.findWithInfo h
        let ⟨_, hyps', pf⟩ ← iRewriteHyp hyps rule ivar config.occs
        let pf' ← addBIGoal hyps' goal
        mvar.assign q(Entails.trans $pf $pf')

end

end

end ProofMode

end Iris
