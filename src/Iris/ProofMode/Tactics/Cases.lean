/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler, Yunsong Yang
-/
module

meta import Iris.ProofMode.Patterns.ProofModeTerm
meta import Iris.ProofMode.Patterns.CasesPattern
public meta import Iris.ProofMode.Tactics.Mod
public meta import Iris.ProofMode.Tactics.Pure
public meta import Iris.ProofMode.Tactics.Clear
public meta import Iris.ProofMode.Tactics.Basic
public meta import Iris.ProofMode.Tactics.HaveCore

namespace Iris.ProofMode

public section
open BI Std

theorem false_elim' [BI PROP] {P Q : PROP} : P ∗ □?p False ⊢ Q :=
  wand_elim' <| intuitionisticallyIf_elim.trans false_elim

theorem exists_elim' [BI PROP] {p} {P A Q : PROP} {Φ : α → PROP} [inst : IntoExists A Φ]
    (h : ∀ a, P ∗ □?p Φ a ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| (intuitionisticallyIf_mono inst.1).trans intuitionisticallyIf_exists.1).trans <| sep_exists_l.1.trans (exists_elim h)

theorem sep_and_elim_l [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A1 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_l).trans h

theorem sep_and_elim_r [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_r).trans h

theorem sep_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoSep A A1 A2]
    (h : P ∗ A1 ⊢ A2 -∗ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_assoc.2.trans <| wand_elim h

theorem and_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ □ A2 -∗ Q) : P ∗ □ A ⊢ Q :=
  (sep_mono_r <| inst.1.trans intuitionistically_and_sep.1).trans <|
  sep_assoc.2.trans <| wand_elim h

theorem or_elim' [BI PROP] {p} {P A Q A1 A2 : PROP} [inst : IntoOr A A1 A2]
    (h1 : P ∗ □?p A1 ⊢ Q) (h2 : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| (intuitionisticallyIf_mono inst.1).trans (intuitionisticallyIf_or _).1).trans <| BI.sep_or_l.1.trans <| or_elim h1 h2

theorem intuitionistic_elim_spatial [BI PROP] {A A' Q : PROP}
    [IntoPersistently false A A'] [TCOr (Affine A) (Absorbing Q)]
    (h : P ∗ □ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r to_persistent_spatial).apply h

theorem intuitionistic_elim_intuitionistic [BI PROP] {A A' Q : PROP} [IntoPersistently true A A']
    (h : P ∗ □ A' ⊢ Q) : P ∗ □ A ⊢ Q := intuitionistic_elim_spatial h

theorem spatial_elim [BI PROP] {p} {A A' Q : PROP} [FromAffinely A' A p]
    (h : P ∗ A' ⊢ Q) : P ∗ □?p A ⊢ Q :=
      (sep_mono_r <| (affinelyIf_of_intuitionisticallyIf).trans from_affinely).trans h

theorem of_emp_sep [BI PROP] {A Q : PROP} (h : A ⊢ Q) : emp ∗ A ⊢ Q := emp_sep.1.trans h

public meta section
open Lean Elab Tactic Meta Qq Std

private def iCasesEmptyConj {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (_hyps : Hyps bi P) (p : Q(Bool)) (A goal : Q($prop)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  if let .defEq _ ← isDefEqQ A q(iprop(False)) then
    return q(false_elim')
  else
    throwError "icases: cannot destruct {A} as an empty conjunct"

/-- Destruct an existential hypothesis [A] by introducing its witness and continuing with the body [B]. -/
private def iCasesExists {prop : Q(Type u)} (bi : Q(BI $prop)) (name : TSyntax ``binderIdent)
    (p : Q(Bool)) (P A goal : Q($prop))
    (k : (B : Q($prop)) → ProofModeM Q($P ∗ □?$p $B ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  let v ← mkFreshLevelMVar
  let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let Φ : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoExists $A $Φ)
    | throwError "icases: {A} is not an existential quantifier"
  let (name, ref) ← getFreshName name
  withLocalDeclDQ name α fun x => do
    addLocalVarInfo ref (← getLCtx) x α
    have B : Q($prop) := Expr.headBeta q($Φ $x)
    let pf : Q(∀ x, $P ∗ □?$p $Φ x ⊢ $goal) ← mkLambdaFVars #[x] <|← k B
    return q(exists_elim' $pf)

/-- Destruct a conjunction hypothesis [A] and continue with only its left or right component. -/
private def iCasesAndLR {prop : Q(Type u)} (bi : Q(BI $prop))
    (p : Q(Bool)) (P A goal : Q($prop)) (right : Bool)
    (k : (B : Q($prop)) → ProofModeM Q($P ∗ □?$p $B ⊢ $goal)) :
    ProofModeM (Option Q($P ∗ □?$p $A ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoAnd $p $A $A1 $A2)
    | return none
  if right then return some q(sep_and_elim_r $(← k A2))
  else return some q(sep_and_elim_l $(← k A1))

/-- Destruct a conjunction hypothesis [A] into two parts and continue with the left and right subpatterns in sequence. -/
private def iCasesSep {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (p : Q(Bool)) (A goal : Q($prop))
    (k : ∀ {P}, Hyps bi P → (goal : Q($prop)) → ProofModeM Q($P ⊢ $goal))
    (k1 k2 : ∀ {P}, Hyps bi P → (goal B : Q($prop)) →
      (∀ {P}, Hyps bi P → (goal : Q($prop)) → ProofModeM Q($P ⊢ $goal)) →
      ProofModeM Q($P ∗ □?$p $B ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  match matchBool p with
  | .inl _ =>
    let .some _ ← ProofModeM.trySynthInstanceQ q(IntoAnd $p $A $A1 $A2)
      | throwError "icases: cannot destruct {A}"
    let goal' := q(iprop(□ $A2 -∗ $goal))
    let pf ← k1 hyps goal' A1 fun hyps goal' => do
      let goal'' ← mkFreshExprMVarQ q($prop)
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $goal' iprop(□ $A2) $goal'')
        | throwError "icases: internal error: {goal'} is not a wand"
      let pf ← k2 hyps goal'' A2 k
      return q((wand_intro $pf).trans from_wand)
    return q(and_elim_intuitionistic $pf)
  | .inr _ =>
    let .some _ ← ProofModeM.trySynthInstanceQ q(IntoSep $A $A1 $A2)
      | throwError "icases: cannot destruct {A}"
    let goal' := q(iprop($A2 -∗ $goal))
    let pf ← k1 hyps goal' A1 fun hyps goal' => do
      let goal'' ← mkFreshExprMVarQ q($prop)
      let .some _ ← ProofModeM.trySynthInstanceQ q(FromWand $goal' $A2 $goal'')
        | throwError "icases: internal error: {goal'} is not a wand"
      let pf ← k2 hyps goal'' A2 k
      return q((wand_intro $pf).trans from_wand)
    return q(sep_elim_spatial (A := $A) $pf)

/-- Destruct a disjunction hypothesis [A] into two cases and continue separately on each branch. -/
private def iCasesOr {prop : Q(Type u)} (bi : Q(BI $prop))
    (p : Q(Bool)) (P A goal : Q($prop))
    (k1 k2 : (B : Q($prop)) → ProofModeM Q($P ∗ □?$p $B ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoOr $A $A1 $A2)
    | throwError "icases: {A} is not a disjunction"
  return q(or_elim' $(← k1 A1) $(← k2 A2))

/-- Destruct a persistent hypothesis [A] by turning it into an explicit [□ B] and continuing with the persistent body. -/
private def iCasesIntuitionistic {prop : Q(Type u)} (_bi : Q(BI $prop))
    (p : Q(Bool)) (P A goal : Q($prop))
    (k : (B : Q($prop)) → ProofModeM Q($P ∗ □ $B ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  let B ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently $p $A $B)
    | throwError "icases: {A} not persistent"
  match matchBool p with
  | .inl _ =>
    return q(intuitionistic_elim_intuitionistic $(← k B))
  | .inr _ =>
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $A) (Absorbing $goal))
      | throwError "icases: {A} not affine and the goal not absorbing"
    return q(intuitionistic_elim_spatial (A := $A) $(← k B))

/-- Destruct an affine/spatial hypothesis [A] by removing the affinely wrapper and continuing with the spatial body. -/
private def iCasesSpatial {prop : Q(Type u)} (_bi : Q(BI $prop))
    (p : Q(Bool)) (P A goal : Q($prop))
    (k : (B : Q($prop)) → ProofModeM Q($P ∗ $B ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) := do
  let B ← mkFreshExprMVarQ q($prop)
  -- this should always succeed
  let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B $A $p)
  return q(spatial_elim $(← k B))

variable {prop : Q(Type u)} (bi : Q(BI $prop)) in
/--
Recursively destruct the current hypothesis `□?p A` in the proof-mode context `hyps`
according to the cases pattern `pat`. After the pattern has been processed, the
continuation `k` is called with the updated context and, for modal patterns,
possibly an updated goal.

## Parameters
- `hyps`: The current proof mode hypothesis context
- `goal`: The current BI goal
- `pat`: The cases pattern describing how to destruct the current hypothesis
- `p`: Whether the current hypothesis is persistent
- `A`: The payload proposition of the current hypothesis
- `k`: The continuation representing the remaining proof after this destruct step

## Returns
A proof of `hyps ∗ □?p A ⊢ goal`.
-/
partial def iCasesCore {P} (hyps : Hyps bi P) (goal : Q($prop)) (pat : iCasesPat)
    (p : Q(Bool)) (A : Q($prop))
    (k : ∀ {P}, Hyps bi P → (goal' : Q($prop)) → ProofModeM Q($P ⊢ $goal)) :
    ProofModeM (Q($P ∗ □?$p $A ⊢ $goal)) :=
  match pat with
  | .one name => do
    -- TODO: use Hyps.addWithInfo here?
    let (name, ref) ← getFreshName name
    let uniq ← mkFreshId
    addHypInfo ref name uniq prop A (isBinder := true)
    let hyp := .mkHyp bi name uniq p A
    if let .emp _ := hyps then pure q(of_emp_sep $(← k hyp goal))
    else k (.mkSep hyps hyp) goal

  | .clear => do
    let pf ← iClearCore bi q(iprop($P ∗ □?$p $A)) P p A goal q(.rfl)
    pure q($pf $(← k hyps goal))

  | .conjunction [arg] | .disjunction [arg] => iCasesCore hyps goal arg p A @k

  | .disjunction [] => throwUnsupportedSyntax

  | .conjunction [] => iCasesEmptyConj bi hyps p A goal

  -- pure conjunctions are always handled as existentials. There is
  -- intoExist_and_pure and intoExist_sep_pure to make this work as
  -- expected for pure assertions that are not explicit existentials.
  | .conjunction (.pure arg :: args) => do
    iCasesExists bi arg p P A goal (iCasesCore hyps goal (.conjunction args) p · k)
  | .conjunction (arg :: args) => do
    if arg matches .clear then
      if let some pf ← iCasesAndLR bi p P A goal true λ B =>
        iCasesCore hyps goal (.conjunction args) p B @k then return pf
    if args matches [.clear] then
      if let some pf ← iCasesAndLR bi p P A goal false λ B =>
        iCasesCore hyps goal arg p B @k then return pf
    iCasesSep bi hyps p A goal @k (iCasesCore · · arg p · ·)
      (iCasesCore · · (.conjunction args) p · ·)

  | .disjunction (arg :: args) =>
    iCasesOr bi p P A goal (iCasesCore hyps goal arg p · k)
      (iCasesCore hyps goal (.disjunction args) p · k)

  | .pure arg => do
    iPureCore bi q(iprop($P ∗ □?$p $A)) P p A goal arg q(.rfl) λ _ _ => k hyps goal

  | .intuitionistic arg =>
    iCasesIntuitionistic bi p P A goal (iCasesCore hyps goal arg q(true) · @k)

  | .spatial arg =>
    iCasesSpatial bi p P A goal (iCasesCore hyps goal arg q(false) · @k)

  | .mod arg =>
    iModCore bi P goal p A λ p' A goal' =>
      iCasesCore hyps goal' arg p' A @k

elab "icases" keep:("+keep")? colGt pmt:pmTerm "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  ProofModeM.runTactic λ mvar { bi, goal, hyps, .. } => do

  -- We keep the persistent hypothesis if it is required by the user (+keep is set by ihave) or if we perform specialization
  let ⟨_, hyps, p, A, pf⟩ ← iHave hyps pmt (keep.isSome || pmt.is_nontrivial) (try_dup_context := pat.should_try_dup_context)

  -- process pattern
  let pf2 ← iCasesCore bi hyps goal pat p A λ hyps goal => addBIGoal hyps goal

  mvar.assign q(($pf).trans $pf2)

macro "imod" colGt pmt:pmTerm "with" colGt pat:icasesPat : tactic => `(tactic | icases $pmt with >$pat)
macro "imod" colGt hyp:ident : tactic => `(tactic | imod $hyp:ident with $hyp:ident)

-- TODO: remove these shortcuts if they are not used
macro "iintuitionistic" hyp:ident : tactic => `(tactic | icases $hyp:ident with #$hyp:ident)
macro "ispatial" hyp:ident : tactic => `(tactic | icases $hyp:ident with ∗$hyp:ident)
