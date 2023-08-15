/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Iris.ProofMode.Instances
import Iris.ProofMode.Patterns.CasesPattern
import Iris.ProofMode.Tactics.Clear
import Iris.ProofMode.Tactics.Move
import Iris.ProofMode.Tactics.Pure

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

theorem false_elim_spatial [BI PROP] {P Q : PROP} : P ∗ False ⊢ Q := wand_elim' false_elim

theorem false_elim_intuitionistic [BI PROP] {P Q : PROP} : P ∗ □ False ⊢ Q :=
  wand_elim' <| intuitionistically_elim.trans false_elim

theorem sep_emp_intro_spatial [BI PROP] {P Q : PROP} (h : P ⊢ Q) : P ∗ emp ⊢ Q := sep_emp.1.trans h

theorem sep_emp_intro_intuitionistic [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : P ∗ □ emp ⊢ Q := (sep_mono_r intuitionistically_emp.1).trans <| sep_emp.1.trans h

def iCasesEmptyConj {prop : Q(Type)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (Q A' : Q($prop)) (p : Q(Bool))
    (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  try
    let ⟨_⟩ ← assertDefEqQ A' q(iprop(False))
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩; return q(false_elim_intuitionistic)
    else
      have : $p =Q false := ⟨⟩; return q(false_elim_spatial)
  catch _ =>
    let ⟨_⟩ ← assertDefEqQ A' q(iprop(emp))
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩; return q(sep_emp_intro_intuitionistic $(← k hyps))
    else
      have : $p =Q false := ⟨⟩; return q(sep_emp_intro_spatial $(← k hyps))


theorem exists_elim_spatial [BI PROP] {P A Q : PROP} {Φ : α → PROP} [inst : IntoExists A Φ]
    (h : ∀ a, P ∗ Φ a ⊢ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_exists_l.1.trans (exists_elim h)

theorem exists_elim_intuitionistic [BI PROP] {P A Q : PROP} {Φ : α → PROP} [IntoExists A Φ]
    (h : ∀ a, P ∗ □ Φ a ⊢ Q) : P ∗ □ A ⊢ Q := exists_elim_spatial h

def iCasesExists {prop : Q(Type)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (name : Option Name) (α : Q(Type)) (Φ : Q(«$α» → «$prop»)) (_inst : Q(IntoExists «$A'» «$Φ»))
    (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  withLocalDeclDQ (← getFreshName name) α fun x => do
    have B' : Q($prop) := Expr.headBeta q($Φ $x)
    have : $B' =Q $Φ $x := ⟨⟩
    if p.constName! == ``true then
      have : $p =Q true := ⟨⟩
      let pf : Q(∀ x, $P ∗ □ $Φ x ⊢ $Q) ← mkLambdaFVars #[x] <|← k q(iprop(□ $B')) B' ⟨⟩
      return q(exists_elim_intuitionistic (A := $A') $pf)
    else
      have : $p =Q false := ⟨⟩
      let pf : Q(∀ x, $P ∗ $Φ x ⊢ $Q) ← mkLambdaFVars #[x] <|← k B' B' ⟨⟩
      return q(exists_elim_spatial (A := $A') $pf)

theorem sep_and_elim_l [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A1 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_l).trans h

theorem and_elim_l_spatial [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd false A A1 A2]
    (h : P ∗ A1 ⊢ Q) : P ∗ A ⊢ Q := sep_and_elim_l (p := false) h

theorem and_elim_l_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ Q) : P ∗ □ A ⊢ Q := sep_and_elim_l (p := true) h

theorem sep_and_elim_r [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd p A A1 A2]
    (h : P ∗ □?p A2 ⊢ Q) : P ∗ □?p A ⊢ Q :=
  (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono and_elim_r).trans h

theorem and_elim_r_spatial [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd false A A1 A2]
    (h : P ∗ A2 ⊢ Q) : P ∗ A ⊢ Q := sep_and_elim_r (p := false) h

theorem and_elim_r_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoAnd true A A1 A2]
    (h : P ∗ □ A2 ⊢ Q) : P ∗ □ A ⊢ Q := sep_and_elim_r (p := true) h

def iCasesAndLR {prop : Q(Type)} (_bi : Q(BI $prop)) (P Q A' A1 A2 : Q($prop)) (p : Q(Bool))
    (_inst : Q(IntoAnd $p $A' $A1 $A2)) (right : Bool)
    (k : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    if right then
      return q(and_elim_r_intuitionistic (A := $A') $(← k q(iprop(□ $A2)) A2 ⟨⟩))
    else
      return q(and_elim_l_intuitionistic (A := $A') $(← k q(iprop(□ $A1)) A1 ⟨⟩))
  else
    have : $p =Q false := ⟨⟩
    if right then
      return q(and_elim_r_spatial (A := $A') $(← k A2 A2 ⟨⟩))
    else
      return q(and_elim_l_spatial (A := $A') $(← k A1 A1 ⟨⟩))

theorem sep_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoSep A A1 A2]
    (h : P ∗ A1 ⊢ A2 -∗ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| sep_assoc.2.trans <| wand_elim h

theorem and_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoAnd true A A1 A2]
    (h : P ∗ □ A1 ⊢ □ A2 -∗ Q) : P ∗ □ A ⊢ Q :=
  (sep_mono_r <| inst.1.trans intuitionistically_and_sep.1).trans <|
  sep_assoc.2.trans <| wand_elim h

def iCasesSep {prop : Q(Type)} (bi : Q(BI $prop))
    {P} (hyps : Hyps bi P) (Q A' A1 A2 : Q($prop)) (p : Q(Bool))
    (inst : Option Q(IntoAnd $p $A' $A1 $A2))
    (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q))
    (k1 k2 : ∀ {P}, Hyps bi P → (Q B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) →
      (∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  if p.constName! == ``true then
    let some _ := inst | _ ← synthInstanceQ q(IntoAnd $p $A' $A1 $A2); unreachable!
    have : $p =Q true := ⟨⟩
    let Q' := q(iprop(□ $A2 -∗ $Q))
    let pf ← k1 hyps Q' q(iprop(□ $A1)) A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q q(iprop(□ $A2)) A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(and_elim_intuitionistic (A := $A') $pf)
  else
    let _ ← synthInstanceQ q(IntoSep $A' $A1 $A2)
    have : $p =Q false := ⟨⟩
    let Q' := q(iprop($A2 -∗ $Q))
    let pf ← k1 hyps Q' A1 A1 ⟨⟩ fun hyps => do
      let pf ← k2 hyps Q A2 A2 ⟨⟩ k
      return q(wand_intro $pf)
    return q(sep_elim_spatial (A := $A') $pf)

theorem or_elim_spatial [BI PROP] {P A Q A1 A2 : PROP} [inst : IntoOr A A1 A2]
    (h1 : P ∗ A1 ⊢ Q) (h2 : P ∗ A2 ⊢ Q) : P ∗ A ⊢ Q :=
  (sep_mono_r inst.1).trans <| BI.sep_or_l.1.trans <| or_elim h1 h2

theorem or_elim_intuitionistic [BI PROP] {P A Q A1 A2 : PROP} [IntoOr A A1 A2]
    (h1 : P ∗ □ A1 ⊢ Q) (h2 : P ∗ □ A2 ⊢ Q) : P ∗ □ A ⊢ Q := or_elim_spatial h1 h2

def iCasesOr {prop : Q(Type)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k1 k2 : (B B' : Q($prop)) → (_ : $B =Q iprop(□?$p $B')) → MetaM Q($P ∗ $B ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let A1 ← mkFreshExprMVarQ q($prop)
  let A2 ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(IntoOr $A' $A1 $A2)
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    let pf1 ← k1 q(iprop(□ $A1)) A1 ⟨⟩
    let pf2 ← k2 q(iprop(□ $A2)) A2 ⟨⟩
    return q(or_elim_intuitionistic (A := $A') $pf1 $pf2)
  else
    have : $p =Q false := ⟨⟩
    let pf1 ← k1 A1 A1 ⟨⟩
    let pf2 ← k2 A2 A2 ⟨⟩
    return q(or_elim_spatial (A := $A') $pf1 $pf2)

theorem intuitionistic_elim_spatial [BI PROP] {A A' Q : PROP}
    [IntoPersistently false A A'] [TCOr (Affine A) (Absorbing Q)]
    (h : P ∗ □ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r to_persistent_spatial).apply h

theorem intuitionistic_elim_intuitionistic [BI PROP] {A A' Q : PROP} [IntoPersistently true A A']
    (h : P ∗ □ A' ⊢ Q) : P ∗ □ A ⊢ Q := intuitionistic_elim_spatial h

def iCasesIntuitionistic {prop : Q(Type)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → MetaM Q($P ∗ □ $B' ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(IntoPersistently $p $A' $B')
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    return q(intuitionistic_elim_intuitionistic $(← k B'))
  else
    have : $p =Q false := ⟨⟩
    let _ ← synthInstanceQ q(TCOr (Affine $A') (Absorbing $Q))
    return q(intuitionistic_elim_spatial (A := $A') $(← k B'))

theorem spatial_elim_spatial [BI PROP] {A A' Q : PROP} [FromAffinely A' A false]
    (h : P ∗ A' ⊢ Q) : P ∗ A ⊢ Q := (replaces_r (from_affine (p := false))).apply h

theorem spatial_elim_intuitionistic [BI PROP] {A A' Q : PROP} [FromAffinely A' A true]
    (h : P ∗ A' ⊢ Q) : P ∗ □ A ⊢ Q := (replaces_r (from_affine (p := true))).apply h

def iCasesSpatial {prop : Q(Type)} (_bi : Q(BI $prop)) (P Q A' : Q($prop)) (p : Q(Bool))
    (k : (B' : Q($prop)) → MetaM Q($P ∗ $B' ⊢ $Q)) :
    MetaM (Q($P ∗ □?$p $A' ⊢ $Q)) := do
  let B' ← mkFreshExprMVarQ q($prop)
  let _ ← synthInstanceQ q(FromAffinely $B' $A' $p)
  if p.constName! == ``true then
    have : $p =Q true := ⟨⟩
    return q(spatial_elim_intuitionistic $(← k B'))
  else
    have : $p =Q false := ⟨⟩
    return q(spatial_elim_spatial (A := $A') $(← k B'))

theorem of_emp_sep [BI PROP] {A Q : PROP} (h : A ⊢ Q) : emp ∗ A ⊢ Q := emp_sep.1.trans h

variable {prop : Q(Type)} (bi : Q(BI $prop)) in
partial def iCasesCore
    {P} (hyps : Hyps bi P) (Q : Q($prop)) (p : Q(Bool))
    (A A' : Q($prop)) (_ : $A =Q iprop(□?$p $A'))
    (pat : iCasesPat) (k : ∀ {P}, Hyps bi P → MetaM Q($P ⊢ $Q)) : MetaM (Q($P ∗ $A ⊢ $Q)) :=
  match pat with
  | .one name => do
    let hyp := .mkHyp bi (← getFreshName name) (← mkFreshId) p A' A
    if let .emp _ := hyps then
      let pf : Q($A ⊢ $Q) ← k hyp
      pure q(of_emp_sep $pf)
    else
      k (.mkSep hyps hyp)

  | .clear => do
    let pf ← clearCore bi q(iprop($P ∗ $A)) P A Q q(.rfl)
    pure q($pf $(← k hyps))

  | .conjunction [arg] | .disjunction [arg] => iCasesCore hyps Q p A A' ⟨⟩ arg @k

  | .disjunction [] => throwUnsupportedSyntax

  | .conjunction [] => iCasesEmptyConj bi hyps Q A' p @k

  | .conjunction (arg :: args) => do
    let exres ← try? (α := _ × (α : Q(Type)) × (Φ : Q($α → $prop)) × Q(IntoExists $A' $Φ)) do
      let .one n := arg | failure
      let α ← mkFreshExprMVarQ q(Type)
      let Φ ← mkFreshExprMVarQ q($α → $prop)
      Pure.pure ⟨n, α, Φ, ← synthInstanceQ q(IntoExists $A' $Φ)⟩
    if let some ⟨n, α, Φ, inst⟩ := exres then
      iCasesExists bi P Q A' p n α Φ inst
        (iCasesCore hyps Q p · · · (.conjunction args) k)
    else
      let A1 ← mkFreshExprMVarQ q($prop)
      let A2 ← mkFreshExprMVarQ q($prop)
      let inst ← try? (α := Q(IntoAnd $p $A' $A1 $A2)) do
        unless arg matches .clear || args matches [.clear] || p.constName! == ``true do failure
        synthInstanceQ q(IntoAnd $p $A' $A1 $A2)
      if let (.clear, some inst) := (arg, inst) then
        iCasesAndLR bi P Q A' A1 A2 p inst (right := true) fun B B' h =>
          iCasesCore hyps Q p B B' h (.conjunction args) @k
      else if let ([.clear], some inst) := (args, inst) then
        iCasesAndLR bi P Q A' A1 A2 p inst (right := false) fun B B' h =>
          iCasesCore hyps Q p B B' h arg @k
      else
        iCasesSep bi hyps Q A' A1 A2 p inst @k
          (iCasesCore · · p · · · arg)
          (iCasesCore · · p · · · (.conjunction args))

  | .disjunction (arg :: args) =>
    iCasesOr bi P Q A' p
      (iCasesCore hyps Q p · · · arg @k)
      (iCasesCore hyps Q p · · · (.disjunction args) @k)

  | .pure arg => do
    let .one n := arg
      | throwError "cannot further destruct a hypothesis after moving it to the Lean context"
    (·.2) <$> ipureCore bi q(iprop($P ∗ $A)) P A Q (← getFreshName n) q(.rfl) fun _ _ =>
      ((), ·) <$> k hyps

  | .intuitionistic arg =>
    iCasesIntuitionistic bi P Q A' p fun B' =>
      iCasesCore hyps Q q(true) q(iprop(□ $B')) B' ⟨⟩ arg @k

  | .spatial arg =>
    iCasesSpatial bi P Q A' p fun B' =>
      iCasesCore hyps Q q(false) B' B' ⟨⟩ arg @k

elab "icases" colGt hyp:ident "with" colGt pat:icasesPat : tactic => do
  -- parse syntax
  let name := hyp.getId
  if name.isAnonymous then
    throwUnsupportedSyntax
  let pat ← liftMacroM <| iCasesPat.parse pat

  let (mvar, { prop, bi, e, hyps, goal }) ← istart (← getMainGoal)
  mvar.withContext do

  let some ⟨_, hyps', A, A', b, h, pf⟩ := hyps.remove true name | throwError "unknown hypothesis"

  -- process pattern
  let goals ← IO.mkRef #[]
  let pf2 ← iCasesCore bi hyps' goal b A A' h pat fun hyps => do
    let m : Q($e ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps, goal }
    goals.modify (·.push m.mvarId!)
    pure m

  mvar.assign q(($pf).1.trans $pf2)
  replaceMainGoal (← goals.get).toList
