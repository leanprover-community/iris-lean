/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public meta import Iris.BI.Notation
public import Iris.Std.Classes
public meta import Iris.Std.DelabRule
public meta import Iris.Std.Rewrite
public import Iris.Std.BigOp
public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris.BI
open Iris.Std
open Lean

/--
Require the definitions of the separation logic connectives and units on a carrier type `PROP`.
-/
class BIBase (PROP : Type u) where
  Entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  sForall : (PROP → Prop) → PROP
  sExists : (PROP → Prop) → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  persistently : PROP → PROP
  later : PROP → PROP

namespace BIBase

def «forall» [BIBase PROP] {α : Sort _} (P : α → PROP) : PROP := sForall fun p => ∃ a, P a = p
def «exists» [BIBase PROP] {α : Sort _} (P : α → PROP) : PROP := sExists fun p => ∃ a, P a = p

/-- Entailment on separation logic propositions. -/
macro:25 P:term:29 " ⊢ " Q:term:25 : term => ``(BIBase.Entails iprop($P) iprop($Q))

macro:25 P:term:29 " ⊢@{ " PROP:term "} " Q:term:25 : term => ``(BIBase.Entails (PROP:=$PROP) iprop($P) iprop($Q))

delab_rule BIBase.Entails
  | `($_ $P $Q) => do ``($(← unpackIprop P) ⊢ $(← unpackIprop Q))

/-- Embedding of pure Lean proposition as separation logic proposition.
Elaborates to `BIBase.pure` when inside an `iprop(...)` scope. -/
syntax (name := bi_pure) "⌜" term "⌝" : term
/-- Separating conjunction. Elaborates to `BIBase.sep` when inside an
`iprop(...)` scope; throws `unsupportedSyntax` otherwise. -/
syntax:35 (name := bi_sep) term:36 " ∗ " term:35 : term
/-- Separating implication. Elaborates to `BIBase.wand` when inside an
`iprop(...)` scope; throws `unsupportedSyntax` otherwise. -/
syntax:25 (name := bi_wand) term:26 " -∗ " term:25 : term
/-- Persistency modality. `persistently` is a primitive of BI.
Elaborates to `BIBase.persistently` inside an `iprop(...)` scope. -/
syntax:max (name := bi_pers) "<pers> " term:40 : term
/-- Later modality. `later` is a primitive of BI.
Elaborates to `BIBase.later` inside an `iprop(...)` scope. -/
syntax:max (name := bi_later) "▷ " term:40 : term

/-- Bidirectional implication on separation logic propositions. Shares the
`↔` token with core Lean's `Iff`; disambiguated by the `iprop(...)` macro
rule (see below). -/
syntax:27 term:28 " ↔ " term:28 : term
/-- Bidrectional separating implication on separation logic propositions.
Elaborates to `wandIff` inside an `iprop(...)` scope. -/
syntax:27 (name := bi_wandIff) term:28 " ∗-∗ " term:28 : term

/-- Existential quantification on separation logic propositions. -/
macro "∃" xs:explicitBinders ", " b:term : term => do
  return ⟨← expandExplicitBinders ``BIBase.exists xs b⟩

-- `iprop` syntax interpretation
macro_rules
  | `(iprop(emp))       => ``(BIBase.emp)
  | `(iprop($P ∧ $Q))   => ``(BIBase.and iprop($P) iprop($Q))
  | `(iprop($P ∨ $Q))   => ``(BIBase.or iprop($P) iprop($Q))
  | `(iprop($P → $Q))   => ``(BIBase.imp iprop($P) iprop($Q))
  | `(iprop(∃ $xs, $Ψ)) => do expandExplicitBinders ``BIBase.exists xs (← ``(iprop($Ψ)))

-- `∗` and `-∗` are handled by flag-based term elaborators rather than
-- `iprop(...)` macro_rules. This allows them to fire at any depth Lean's
-- elaborator descends into (including lambda bodies, match arms, and
-- function arguments at any nesting), without per-construct carry-through.
open Lean.Elab Lean.Elab.Term in
@[term_elab bi_sep]
meta def elabBiSep : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[0]⟩
  let Q : Term := ⟨stx[2]⟩
  elabTerm (← `(BIBase.sep iprop($P) iprop($Q))) expectedType?

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_wand]
meta def elabBiWand : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[0]⟩
  let Q : Term := ⟨stx[2]⟩
  elabTerm (← `(BIBase.wand iprop($P) iprop($Q))) expectedType?

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_pure]
meta def elabBiPure : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  -- `⌜ φ ⌝` parses as ⟨"⌜", φ, "⌝"⟩; argument index 1 is the embedded prop.
  let φ : Term := ⟨stx[1]⟩
  elabTerm (← `(BIBase.pure $φ)) expectedType?

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_pers]
meta def elabBiPers : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(BIBase.persistently iprop($P))) expectedType?

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_later]
meta def elabBiLater : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(BIBase.later iprop($P))) expectedType?

delab_rule BIBase.emp
  | `($_) => ``(iprop($(mkIdent `emp)))
delab_rule BIBase.pure
  | `($_ $φ) => ``(iprop(⌜$φ⌝))
delab_rule BIBase.and
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∧ $(← unpackIprop Q)))
delab_rule BIBase.or
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∨ $(← unpackIprop Q)))
delab_rule BIBase.imp
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) → $(← unpackIprop Q)))
delab_rule BIBase.forall
  | `($_ fun $x:ident => iprop(∀ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(iprop(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(iprop(∀ $x:ident, $(← unpackIprop Ψ)))
delab_rule BIBase.exists
  | `($_ fun $x:ident => iprop(∃ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(iprop(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(iprop(∃ $x:ident, $(← unpackIprop Ψ)))
delab_rule BIBase.sep
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗ $(← unpackIprop Q)))
delab_rule BIBase.wand
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -∗ $(← unpackIprop Q)))
delab_rule BIBase.persistently
  | `($_ $P) => do ``(iprop(<pers> $(← unpackIprop P)))
delab_rule BIBase.later
  | `($_ $P) => do ``(iprop(▷ $(← unpackIprop P)))

delab_rule BIBase.pure
  | `($_ True) => ``(iprop($(mkIdent `True)))
  | `($_ False) => ``(iprop($(mkIdent `False)))
delab_rule BIBase.imp
  | `($_ $P iprop(False)) => do ``(iprop(¬$(← unpackIprop P)))

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules
  | `(iprop(∀ _%$tk, $Ψ)) => ``(BIBase.forall (fun _%$tk => iprop($Ψ)))
macro_rules
  | `(iprop(∀ $x:ident, $Ψ)) => ``(BIBase.forall (fun $x => iprop($Ψ)))
macro_rules
  | `(iprop(∀ (_%$tk : $t), $Ψ)) => ``(BIBase.forall (fun (_%$tk : $t) => iprop($Ψ)))
  | `(iprop(∀ (_%$tk $xs* : $t), $Ψ)) =>
    ``(BIBase.forall (fun (_%$tk : $t) => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(iprop(∀ ($x:ident : $t), $Ψ)) => ``(BIBase.forall (fun ($x : $t) => iprop($Ψ)))
  | `(iprop(∀ ($x:ident $xs* : $t), $Ψ)) =>
    ``(BIBase.forall (fun ($x : $t) => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(iprop(∀ {_%$tk : $t}, $Ψ)) =>
    ``(BIBase.forall (fun {_%$tk : $t}  => iprop($Ψ)))
  | `(iprop(∀ {_%$tk $xs* : $t}, $Ψ)) =>
    ``(BIBase.forall (fun {_%$tk : $t}  => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(iprop(∀ {$x:ident : $t}, $Ψ)) =>
    ``(BIBase.forall (fun ($x : $t) => iprop($Ψ)))
  | `(iprop(∀ {$x:ident $xs* : $t}, $Ψ)) =>
    ``(BIBase.forall (fun ($x : $t) => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(iprop(∀ $x $y $xs*, $Ψ)) => ``(iprop(∀ $x, ∀ $y $xs*, $Ψ))

-- `iprop` macros
macro_rules
  | `(iprop(True))  => ``(BIBase.pure True)
  | `(iprop(False)) => ``(BIBase.pure False)
  | `(iprop(¬$P))   => ``(iprop($P → False))

def iff     [BIBase PROP] (P Q : PROP) : PROP := iprop((P → Q) ∧ (Q → P))
def wandIff [BIBase PROP] (P Q : PROP) : PROP := iprop((P -∗ Q) ∧ (Q -∗ P))

macro_rules
  | `(iprop($P ↔ $Q))   => ``(iff iprop($P) iprop($Q))

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_wandIff]
meta def elabBiWandIff : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[0]⟩
  let Q : Term := ⟨stx[2]⟩
  elabTerm (← `(wandIff iprop($P) iprop($Q))) expectedType?

delab_rule iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ↔ $(← unpackIprop Q)))
delab_rule wandIff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗-∗ $(← unpackIprop Q)))

/-- Affine modality.
```
def affinely (P) := emp ∧ P
```
-/
syntax:max (name := bi_affine) "<affine> " term:40 : term
/-- Absorbing modality, `absorbingly`.
```
def absorbingly (P) := True ∗ P
```
-/
syntax:max (name := bi_absorb) "<absorb> " term:40 : term

def affinely    [BIBase PROP] (P : PROP) : PROP := iprop(emp ∧ P)
def absorbingly [BIBase PROP] (P : PROP) : PROP := BIBase.sep iprop(True) P

structure BiEntails [BIBase PROP] (P Q : PROP) where
  mp : P ⊢ Q
  mpr : Q ⊢ P

def EmpValid [BIBase PROP] (P : PROP) : Prop := emp ⊢ P

/-- Entailment on separation logic propositions with an empty context. -/
macro:25 "⊢ " P:term:25 : term => ``(EmpValid iprop($P))
macro:25 "⊢@{ " PROP:term " } " P:term:25 : term =>
  ``(EmpValid (PROP:=$PROP) iprop($P))
/-- Bidirectional entailment on separation logic propositions. -/
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(BiEntails iprop($P) iprop($Q))
macro:25 P:term:29 " ⊣⊢@{ " PROP:term " } " Q:term:29 : term =>
  ``(BiEntails (PROP:=$PROP) iprop($P) iprop($Q))

delab_rule BIBase.EmpValid
  | `($_ $P) => do ``(⊢ $(← unpackIprop P))

delab_rule BIBase.BiEntails
  | `($_ $P $Q) => do ``($(← unpackIprop P) ⊣⊢ $(← unpackIprop Q))

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_affine]
meta def elabBiAffine : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(affinely iprop($P))) expectedType?

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_absorb]
meta def elabBiAbsorb : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(absorbingly iprop($P))) expectedType?

delab_rule affinely
  | `($_ $P) => do ``(iprop(<affine> $(← unpackIprop P)))
delab_rule absorbingly
  | `($_ $P) => do ``(iprop(<absorb> $(← unpackIprop P)))

/-- Intuitionistic modality.
```
def intuitionistically (P) := <affine> <pers> P
```
-/
syntax:max (name := bi_intuit) "□ " term:40 : term

def intuitionistically [BIBase PROP] (P : PROP) : PROP := iprop(<affine> <pers> P)

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_intuit]
meta def elabBiIntuit : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(intuitionistically iprop($P))) expectedType?

delab_rule intuitionistically
  | `($_ $P) => do ``(iprop(□ $(← unpackIprop P)))

/-- Conditional persistency modality.
```
def persistentlyIf (p : Bool) (P : PROP) := if p then <pers> P else P
```
-/
syntax:max (name := bi_persIf)   "<pers>?"   term:max ppHardSpace term:40 : term
/-- Conditional affine modality.
```
def affinelyIf (p : Bool) (P : PROP) := if p then <affine> P else P
```
-/
syntax:max (name := bi_affineIf) "<affine>?" term:max ppHardSpace term:40 : term
/-- Conditional absorbing modality.
```
def absorbinglyIf (p : Bool) (P : PROP) := if p then <absorb> P else P
```
-/
syntax:max (name := bi_absorbIf) "<absorb>?" term:max ppHardSpace term:40 : term
/-- Conditional intuitionistic modality.
```
def intuitionisticallyIf (p : Bool) (P : PROP) := if p then □ P else P
```
-/
syntax:max (name := bi_intuitIf) "□?"        term:max ppHardSpace term:40 : term
/-- Conditional later modality.
```
def laterIf (p : Bool) (P : PROP) := if p then ▷ P else P
```
-/
syntax:max (name := bi_laterIf)  "▷?"        term:max ppHardSpace term:40 : term

def persistentlyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <pers> P else P)
def affinelyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <affine> P else P)
def absorbinglyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <absorb> P else P)
def intuitionisticallyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then □ P else P)
def laterIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then ▷ P else P)

section
open Lean.Elab Lean.Elab.Term

@[term_elab bi_persIf]
meta def elabBiPersIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(persistentlyIf $p iprop($P))) expectedType?

@[term_elab bi_affineIf]
meta def elabBiAffineIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(affinelyIf $p iprop($P))) expectedType?

@[term_elab bi_absorbIf]
meta def elabBiAbsorbIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(absorbinglyIf $p iprop($P))) expectedType?

@[term_elab bi_intuitIf]
meta def elabBiIntuitIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(intuitionisticallyIf $p iprop($P))) expectedType?

@[term_elab bi_laterIf]
meta def elabBiLaterIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(laterIf $p iprop($P))) expectedType?

end

delab_rule persistentlyIf
  | `($_ $p $P) => do ``(iprop(<pers>?$p $(← unpackIprop P)))
delab_rule affinelyIf
  | `($_ $p $P) => do ``(iprop(<affine>?$p $(← unpackIprop P)))
delab_rule absorbinglyIf
  | `($_ $p $P) => do ``(iprop(<absorb>?$p $(← unpackIprop P)))
delab_rule intuitionisticallyIf
  | `($_ $p $P) => do ``(iprop(□?$p $(← unpackIprop P)))
delab_rule laterIf
  | `($_ $p $P) => do ``(iprop(▷?$p $(← unpackIprop P)))

/-- Fold the conjunction `∧` over a list of separation logic propositions. -/
def bigAnd [BIBase PROP] (Ps : List PROP) : PROP := bigOp and iprop(True) Ps
/-- Fold the disjunction `∨` over a list of separation logic propositions. -/
def bigOr [BIBase PROP] (Ps : List PROP) : PROP := bigOp or iprop(False) Ps
/-- Fold the separating conjunction `∗` over a list of separation logic propositions. -/
def bigSep [BIBase PROP] (Ps : List PROP) : PROP := bigOp sep iprop(emp) Ps

notation:40 "[∧] " Ps:max => bigAnd Ps
notation:40 "[∨] " Ps:max => bigOr Ps
notation:40 "[∗] " Ps:max => bigSep Ps


/-- Iterated later modality. -/
syntax:max (name := bi_laterN) "▷^[" term:45 "]" term:40 : term

def laterN [BIBase PROP] (n : Nat) (P : PROP) : PROP :=
  match n with | .zero => P | .succ n' => later <| laterN n' P

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_laterN]
meta def elabBiLaterN : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let n : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[3]⟩
  elabTerm (← `(laterN $n iprop($P))) expectedType?

delab_rule laterN
  | `($_ $n $P) => do ``(iprop(▷^[$n] $(← unpackIprop P)))


/-- Except-0 modality -/
syntax:max (name := bi_except0) "◇ " term:40 : term

def except0 [BIBase PROP] (P : PROP) := iprop(▷ False ∨ P)

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_except0]
meta def elabBiExcept0 : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(except0 iprop($P))) expectedType?

delab_rule except0
  | `($_ $P) => do ``(iprop(◇ $(← unpackIprop P)))


/-- Plainly modality -/
class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly (plainly)

syntax (name := bi_plainly) "■ " term:40 : term

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_plainly]
meta def elabBiPlainly : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let P : Term := ⟨stx[1]⟩
  elabTerm (← `(Plainly.plainly iprop($P))) expectedType?

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■ $(← Iris.BI.unpackIprop P)))

@[rocq_alias plainly_if]
def Plainly.plainlyIf [BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max (name := bi_plainlyIf) "■?" term:max ppHardSpace term:40 : term

open Lean.Elab Lean.Elab.Term in
@[term_elab bi_plainlyIf]
meta def elabBiPlainlyIf : TermElab := fun stx expectedType? => do
  unless ← inIpropScope do throwUnsupportedSyntax
  let p : Term := ⟨stx[1]⟩
  let P : Term := ⟨stx[2]⟩
  elabTerm (← `(Plainly.plainlyIf $p iprop($P))) expectedType?

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))
