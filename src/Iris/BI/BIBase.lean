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

/-- Embedding of pure Lean proposition as separation logic proposition. -/
syntax "⌜" term "⌝" : term
/-- Separating conjunction. -/
syntax:35 term:36 " ∗ " term:35 : term
/-- Separating implication. -/
syntax:25 term:26 " -∗ " term:25 : term
/-- Persistency modality. `persistently` is a primitive of BI. -/
syntax:max "<pers> " term:40 : term
/-- Later modality. `later` is a primitive of BI. -/
syntax:max "▷ " term:40 : term

/-- Bidirectional implication on separation logic propositions. -/
syntax:27 term:28 " ↔ " term:28 : term
/-- Bidrectional separating implication on separation logic propositions. -/
syntax:27 term:28 " ∗-∗ " term:28 : term

/-- Existential quantification on separation logic propositions. -/
macro "∃" xs:explicitBinders ", " b:term : term => do
  return ⟨← expandExplicitBinders ``BIBase.exists xs b⟩

-- `iprop` syntax interpretation
macro_rules
  | `(iprop(emp))       => ``(BIBase.emp)
  | `(iprop(⌜$φ⌝))      => ``(BIBase.pure $φ)
  | `(iprop($P ∧ $Q))   => ``(BIBase.and iprop($P) iprop($Q))
  | `(iprop($P ∨ $Q))   => ``(BIBase.or iprop($P) iprop($Q))
  | `(iprop($P → $Q))   => ``(BIBase.imp iprop($P) iprop($Q))
  | `(iprop(∃ $xs, $Ψ)) => do expandExplicitBinders ``BIBase.exists xs (← ``(iprop($Ψ)))
  | `(iprop($P ∗ $Q))   => ``(BIBase.sep iprop($P) iprop($Q))
  | `(iprop($P -∗ $Q))  => ``(BIBase.wand iprop($P) iprop($Q))
  | `(iprop(<pers> $P)) => ``(BIBase.persistently iprop($P))
  | `(iprop(▷ $P))      => ``(BIBase.later iprop($P))

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
  | `(iprop($P ∗-∗ $Q)) => ``(wandIff iprop($P) iprop($Q))

delab_rule iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ↔ $(← unpackIprop Q)))
delab_rule wandIff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗-∗ $(← unpackIprop Q)))

/-- Affine modality.
```
def affinely (P) := emp ∧ P
```
-/
syntax:max "<affine> " term:40 : term
/-- Absorbing modality, `absorbingly`.
```
def absorbingly (P) := True ∗ P
```
-/
syntax:max "<absorb> " term:40 : term

def affinely    [BIBase PROP] (P : PROP) : PROP := iprop(emp ∧ P)
def absorbingly [BIBase PROP] (P : PROP) : PROP := iprop(True ∗ P)

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

macro_rules
  | `(iprop(<affine> $P)) => ``(affinely iprop($P))
  | `(iprop(<absorb> $P)) => ``(absorbingly iprop($P))

delab_rule affinely
  | `($_ $P) => do ``(iprop(<affine> $(← unpackIprop P)))
delab_rule absorbingly
  | `($_ $P) => do ``(iprop(<absorb> $(← unpackIprop P)))

/-- Intuitionistic modality.
```
def intuitionistically (P) := <affine> <pers> P
```
-/
syntax:max "□ " term:40 : term

def intuitionistically [BIBase PROP] (P : PROP) : PROP := iprop(<affine> <pers> P)

macro_rules
  | `(iprop(□ $P)) => ``(intuitionistically iprop($P))

delab_rule intuitionistically
  | `($_ $P) => do ``(iprop(□ $(← unpackIprop P)))

/-- Conditional persistency modality.
```
def persistentlyIf (p : Bool) (P : PROP) := if p then <pers> P else P
```
-/
syntax:max "<pers>?"   term:max ppHardSpace term:40 : term
/-- Conditional affine modality.
```
def affinelyIf (p : Bool) (P : PROP) := if p then <affine> P else P
```
-/
syntax:max "<affine>?" term:max ppHardSpace term:40 : term
/-- Conditional absorbing modality.
```
def absorbinglyIf (p : Bool) (P : PROP) := if p then <absorb> P else P
```
-/
syntax:max "<absorb>?" term:max ppHardSpace term:40 : term
/-- Conditional intuitionistic modality.
```
def intuitionisticallyIf (p : Bool) (P : PROP) := if p then □ P else P
```
-/
syntax:max "□?"        term:max ppHardSpace term:40 : term
/-- Conditional later modality.
```
def laterIf (p : Bool) (P : PROP) := if p then ▷ P else P
```
-/
syntax:max "▷?"        term:max ppHardSpace term:40 : term

def persistentlyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <pers> P else P)
def affinelyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <affine> P else P)
def absorbinglyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <absorb> P else P)
def intuitionisticallyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then □ P else P)
def laterIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then ▷ P else P)

macro_rules
  | `(iprop(<pers>?$p $P))   => ``(persistentlyIf $p iprop($P))
  | `(iprop(<affine>?$p $P)) => ``(affinelyIf $p iprop($P))
  | `(iprop(<absorb>?$p $P)) => ``(absorbinglyIf $p iprop($P))
  | `(iprop(□?$p $P))        => ``(intuitionisticallyIf $p iprop($P))
  | `(iprop(▷?$p $P))        => ``(laterIf $p iprop($P))

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
syntax:max "▷^[" term:45 "]" term:40 : term

def laterN [BIBase PROP] (n : Nat) (P : PROP) : PROP :=
  match n with | .zero => P | .succ n' => later <| laterN n' P

macro_rules
  | `(iprop(▷^[$n] $P))   => ``(laterN $n iprop($P))

delab_rule laterN
  | `($_ $n $P) => do ``(iprop(▷^[$n] $(← unpackIprop P)))


/-- Except-0 modality -/
syntax:max "◇ " term:40 : term

def except0 [BIBase PROP] (P : PROP) := iprop(▷ False ∨ P)

macro_rules
  | `(iprop(◇ $P)) => ``(except0 iprop($P))

delab_rule except0
  | `($_ $P) => do ``(iprop(◇ $(← unpackIprop P)))


/-- Plainly modality -/
class Plainly (PROP : Type _) where
  plainly : PROP → PROP
export Plainly (plainly)

syntax "■ " term:40 : term

macro_rules
  | `(iprop(■ $P))  => ``(Plainly.plainly iprop($P))

delab_rule Plainly.plainly
  | `($_ $P) => do ``(iprop(■ $(← Iris.BI.unpackIprop P)))

def Plainly.plainlyIf [BIBase PROP] [Plainly PROP] (p : Bool) (P : PROP) : PROP :=
  iprop(if p then ■ P else P)

syntax:max "■?" term:max ppHardSpace term:40 : term

macro_rules
  | `(iprop(■? $p $P))  => ``(Plainly.plainlyIf $p iprop($P))

delab_rule Plainly.plainlyIf
  | `($_ $p $P) => do ``(iprop(■? $p $(← Iris.BI.unpackIprop P)))
