/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Michael Sammler
-/
import Iris.ProofMode.Patterns.ProofModeTerm
import Iris.ProofMode.Patterns.CasesPattern
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Clear
import Iris.ProofMode.Tactics.Pure
import Iris.ProofMode.Tactics.HaveCore
import Iris.ProofMode.Tactics.Mod

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem false_elim' [BI PROP] {P Q : PROP} : P ∗ □?p False ⊢ Q :=
  wand_elim' <| intuitionisticallyIf_elim.trans false_elim

def iCasesEmptyConj {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (_hyps : Hyps bi P) (Q A' : Q($prop)) (p : Q(Bool))
    (_k : ∀ {P}, Hyps bi P → ProofModeM Q($P ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  if let .defEq _ ← isDefEqQ A' q(iprop(False)) then
    return q(false_elim')
  else
    throwError "icases: cannot destruct {A'} as an empty conjunct"


private theorem exists_elim' [BI PROP] {p} {P A Q : PROP} {Φ : α → PROP} [inst : IntoExists A Φ]
    (h : ∀ a, P ∗ □?p Φ a ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| (intuitionisticallyIf_mono inst.1).trans intuitionisticallyIf_exists.1).trans <| sep_exists_l.1.trans (exists_elim h)

def iCasesExists {prop : Q(Type u)} (bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (name : TSyntax ``binderIdent)
    (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → ProofModeM Q($P ∗ $B ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let v ← mkFreshLevelMVar
  let α : Quoted q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let Φ : Quoted q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoExists $A' $Φ)
    | throwError "icases: {A'} is not an existential quantifier"
  let (name, ref) ← getFreshName name
  withLocalDeclDQ name α fun x => do
    addLocalVarInfo ref (← getLCtx) x α
    have B' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $B' =Q $Φ $x := ⟨⟩
    have ⟨B, _⟩ := mkIntuitionisticIf bi p B'
    let pf : Q(∀ x, $P ∗ □?$p $Φ x ⊢ $Q) ← mkLambdaFVars #[x] <|← k B B' ⟨⟩
    return q(exists_elim' (A := $A') $pf)


private theorem sep_and_elim_l [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A1 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_l).trans h

private theorem sep_and_elim_r [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_r).trans h

def iCasesAndLR {prop : Q(Type u)} (bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool)) (right : Bool)
  (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → ProofModeM Q($P ∗ $B ⊢ $Q)) :
    ProofModeM (Option Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoAnd $p $A' $A1 $A2)
    | return none
  if right then
    have ⟨A2', _⟩ := mkIntuitionisticIf bi p A2
    return some q(sep_and_elim_r $(← k A2' A2 ⟨⟩))
  else
    have ⟨A1', _⟩ := mkIntuitionisticIf bi p A1
    return some q(sep_and_elim_l $(← k A1' A1 ⟨⟩))

private theorem sep_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoSep A A1 A2]
    (h : P ∗ A1 ⊢ A2 -∗ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_assoc.2.trans <| wand_elim h

private theorem and_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ □ A2 -∗ Q) : P ∗ □ A ⊢ Q :=
  (sep_mono_r <| inst.1.trans intuitionistically_and_sep.1).trans <|
  sep_assoc.2.trans <| wand_elim h

def iCasesSep {prop : Q(Type u)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (Q A' : Q($prop)) (p : Q(Bool))
    (k : ∀ {P}, Hyps bi P → ProofModeM Q($P ⊢ $Q))
    (k1 k2 : ∀ {P}, Hyps bi P → (Q B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) →
      (∀ {P}, Hyps bi P → ProofModeM Q($P ⊢ $Q)) → ProofModeM Q($P ∗ $B ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  match matchBool p with
  | .inl _ =>
    let .some _ ← ProofModeM.trySynthInstanceQ q(IntoAnd $p $A' $A1 $A2)
      | throwError "icases: cannot destruct {A'}"
    let Q' := q(iprop(□ $A2 -∗ $Q))
    let pf ← k1 hyps Q' q(iprop(□ $A1)) A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q q(iprop(□ $A2)) A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(and_elim_intuitionistic (A := $A') $pf)
  | .inr _ =>
    let .some _ ← ProofModeM.trySynthInstanceQ q(IntoSep $A' $A1 $A2)
      | throwError "icases: cannot destruct {A'}"
    let Q' := q(iprop($A2 -∗ $Q))
    let pf ← k1 hyps Q' A1 A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q A2 A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(sep_elim_spatial (A := $A') $pf)

private theorem or_elim' [BI PROP] {p} {P A Q A1 A2 : PROP} [inst : IntoOr A A1 A2]
    (h1 : P ∗ □?p A1 ⊢ Q) (h2 : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| (intuitionisticallyIf_mono inst.1).trans (intuitionisticallyIf_or _).1).trans <| BI.sep_or_l.1.trans <| or_elim h1 h2

def iCasesOr {prop : Q(Type u)} (bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k1 k2 : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → ProofModeM Q($P ∗ $B ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoOr $A' $A1 $A2)
    | throwError "icases: {A'} is not a disjunction"
  have ⟨A1', _⟩ := mkIntuitionisticIf bi p A1
  have ⟨A2', _⟩ := mkIntuitionisticIf bi p A2
  let pf1 ← k1 A1' A1 ⟨⟩
  let pf2 ← k2 A2' A2 ⟨⟩
  return q(or_elim' (A := $A') $pf1 $pf2)

private theorem intuitionistic_elim_spatial [BI PROP] {A A' Q : PROP}
    [IntoPersistently false A A'] [TCOr (Affine A) (Absorbing Q)]
    (h : P ∗ □ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r to_persistent_spatial).apply h

private theorem intuitionistic_elim_intuitionistic [BI PROP] {A A' Q : PROP} [IntoPersistently true A A']
    (h : P ∗ □ A' ⊢ Q) : P ∗ □ A ⊢ Q := intuitionistic_elim_spatial h

def iCasesIntuitionistic {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → ProofModeM Q($P ∗ □ $B' ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  let .some _ ← ProofModeM.trySynthInstanceQ q(IntoPersistently $p $A' $B')
    | throwError "icases: {A'} not persistent"
  match matchBool p with
  | .inl _ =>
    return q(intuitionistic_elim_intuitionistic $(← k B'))
  | .inr _ =>
    let .some _ ← trySynthInstanceQ q(TCOr (Affine $A') (Absorbing $Q))
      | throwError "icases: {A'} not affine and the goal not absorbing"
    return q(intuitionistic_elim_spatial (A := $A') $(← k B'))

private theorem spatial_elim [BI PROP] {p} {A A' Q : PROP} [FromAffinely A' A p]
    (h : P ∗ A' ⊢ Q) : P ∗ □?p A ⊢ Q :=
      (sep_mono_r <| (affinelyIf_of_intuitionisticallyIf).trans from_affinely).trans h

def iCasesSpatial {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → ProofModeM Q($P ∗ $B' ⊢ $Q)) :
    ProofModeM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  -- this should always succeed
  let _ ← ProofModeM.synthInstanceQ q(FromAffinely $B' $A' $p)
  return q(spatial_elim (A := $A') $(← k B'))

theorem of_emp_sep [BI PROP] {A Q : PROP} (h : A ⊢ Q) : emp ∗ A ⊢ Q := emp_sep.1.trans h

  -- TODO: Why does this function require both A and A' instead of just A'?
variable {u : Level} {prop : Q(Type u)} (bi : Q(BI $prop)) in
partial def iCasesCore
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (p : Q(Bool))
    (A A' : Q($prop)) (_ : $A =Q iprop(□?$p $A'))
    (pat : iCasesPat) (k : ∀ {P}, Hyps bi P → ProofModeM Q($P ⊢ $Q)) : ProofModeM (Q($P ∗ $A ⊢ $Q)) :=
  match pat with
  | .one name => do
    -- TODO: use Hyps.addWithInfo here?
    let (name, ref) ← getFreshName name
    let uniq ← mkFreshId
    addHypInfo ref name uniq prop A' (isBinder := true)
    let hyp := .mkHyp bi name uniq p A' A
    if let .emp _ := hyps then
      let pf : Q($A ⊢ $Q) ← k hyp
      pure q(of_emp_sep $pf)
    else
      k (.mkSep hyps hyp)

  | .clear => do
    let pf ← iClearCore bi q(iprop($P ∗ $A)) P p A' Q q(.rfl)
    pure q($pf $(← k hyps))

  | .conjunction [arg] | .disjunction [arg] => iCasesCore hyps Q p A A' ⟨⟩ arg @k

  | .disjunction [] => throwUnsupportedSyntax

  | .conjunction [] => iCasesEmptyConj bi hyps Q A' p @k

  -- pure conjunctions are always handled as existentials. There is
  -- intoExist_and_pure and intoExist_sep_pure to make this work as
  -- expected for pure assertions that are not explicit existentials.
  | .conjunction (.pure arg :: args) => do
    iCasesExists bi P Q A' p arg
      (iCasesCore hyps Q p · · · (.conjunction args) k)
  | .conjunction (arg :: args) => do
    if arg matches .clear then
      let pf ← iCasesAndLR bi P Q A' p (right := true) fun B B' h =>
        iCasesCore hyps Q p B B' h (.conjunction args) @k
      if let some pf := pf then return pf
    if args matches [.clear] then
      let pf ← iCasesAndLR bi P Q A' p (right := false) fun B B' h =>
        iCasesCore hyps Q p B B' h arg @k
      if let some pf := pf then return pf
    iCasesSep bi hyps Q A' p @k
      (iCasesCore · · p · · · arg)
      (iCasesCore · · p · · · (.conjunction args))

  | .disjunction (arg :: args) =>
    iCasesOr bi P Q A' p
      (iCasesCore hyps Q p · · · arg @k)
      (iCasesCore hyps Q p · · · (.disjunction args) @k)

  | .pure arg => do
    iPureCore bi q(iprop($P ∗ $A)) P p A' Q arg q(.rfl) fun _ _ => k hyps

  | .intuitionistic arg =>
    iCasesIntuitionistic bi P Q A' p fun B' =>
      iCasesCore hyps Q q(true) q(iprop(□ $B')) B' ⟨⟩ arg @k

  | .spatial arg =>
    iCasesSpatial bi P Q A' p fun B' =>
      iCasesCore hyps Q q(false) B' B' ⟨⟩ arg @k

  | .mod arg =>
    iModCore bi P Q p A' fun p' A' Q' =>
      have ⟨A'', eq⟩ := mkIntuitionisticIf bi p' A'
      iCasesCore hyps Q' p' A'' A' eq arg @k

elab "icases" colGt pmt:pmTerm "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let pmt ← liftMacroM <| PMTerm.parse pmt
  let pat ← liftMacroM <| iCasesPat.parse pat
  ProofModeM.runTactic λ mvar { bi, goal, hyps, .. } => do

  let ⟨_, hyps, p, A, pf⟩ ← iHave hyps pmt false

  -- process pattern
  have ⟨B, eq⟩ := mkIntuitionisticIf bi p A
  let pf2 ← iCasesCore bi hyps goal p B A eq pat (λ hyps => addBIGoal hyps goal)

  mvar.assign q(($pf).trans $pf2)

macro "imod" colGt pmt:pmTerm "with" colGt pat:icasesPat : tactic => `(tactic | icases $pmt with >$pat)
macro "imod" colGt hyp:ident : tactic => `(tactic | imod $hyp:ident with $hyp:ident)

-- TODO: remove these shortcuts if they are not used
macro "iintuitionistic" hyp:ident : tactic => `(tactic | icases $hyp:ident with □$hyp:ident)
macro "ispatial" hyp:ident : tactic => `(tactic | icases $hyp:ident with ∗$hyp:ident)
