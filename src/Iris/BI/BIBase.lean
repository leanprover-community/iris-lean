/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Notation
import Iris.Std.Classes
import Iris.Std.DelabRule
import Iris.Std.Rewrite
import Iris.Std.BigOp

namespace Iris.BI
open Iris.Std
open Lean

/-- Require the definitions of the separation logic connectives and units on a carrier type `PROP`. -/
class BIBase (PROP : Type) where
  entails : PROP → PROP → Prop
  emp : PROP
  pure : Prop → PROP
  and : PROP → PROP → PROP
  or : PROP → PROP → PROP
  imp : PROP → PROP → PROP
  «forall» {α : Type} : (α → PROP) → PROP
  «exists» {α : Type} : (α → PROP) → PROP
  sep : PROP → PROP → PROP
  wand : PROP → PROP → PROP
  persistently : PROP → PROP

namespace BIBase

section Syntax

/-- Entailment on separation logic propositions. -/
macro:25 P:term:29 " ⊢ " Q:term:25 : term => ``(BIBase.entails iprop($P) iprop($Q))

/-- Embedding of pure Lean proposition as separation logic proposition. -/
syntax "⌜" term "⌝" : term
/-- Separating conjunction. -/
syntax:35 term:36 " ∗ " term:35 : term
/-- Separating implication. -/
syntax:25 term:26 " -∗ " term:25 : term
/-- Persistency modality. -/
syntax:max "<pers> " term:40 : term

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

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules | `(iprop(∀ _, $Ψ))                    => ``(BIBase.forall (fun _         => iprop($Ψ)))
macro_rules | `(iprop(∀ $x:ident, $Ψ))             => ``(BIBase.forall (fun $x        => iprop($Ψ)))
macro_rules | `(iprop(∀ (_ : $t), $Ψ))             => ``(BIBase.forall (fun (_ : $t)  => iprop($Ψ)))
macro_rules | `(iprop(∀ (_ $xs* : $t), $Ψ))        => ``(BIBase.forall (fun (_ : $t)  => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules | `(iprop(∀ ($x:ident : $t), $Ψ))      => ``(BIBase.forall (fun ($x : $t) => iprop($Ψ)))
macro_rules | `(iprop(∀ ($x:ident $xs* : $t), $Ψ)) => ``(BIBase.forall (fun ($x : $t) => iprop(∀ ($xs* : $t), $Ψ)))
macro_rules | `(iprop(∀ {_ : $t}, $Ψ))             => ``(BIBase.forall (fun {_ : $t}  => iprop($Ψ)))
macro_rules | `(iprop(∀ {_ $xs* : $t}, $Ψ))        => ``(BIBase.forall (fun {_ : $t}  => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules | `(iprop(∀ {$x:ident : $t}, $Ψ))      => ``(BIBase.forall (fun ($x : $t) => iprop($Ψ)))
macro_rules | `(iprop(∀ {$x:ident $xs* : $t}, $Ψ)) => ``(BIBase.forall (fun ($x : $t) => iprop(∀ {$xs* : $t}, $Ψ)))
macro_rules | `(iprop(∀ $x $y $xs*, $Ψ))           => ``(iprop(∀ $x, ∀ $y $xs*, $Ψ))

-- `iprop` macros
macro_rules
  | `(iprop(True))  => ``(BIBase.pure True)
  | `(iprop(False)) => ``(BIBase.pure False)
  | `(iprop(¬$P))   => ``(iprop($P → False))

end Syntax


-- delaboration rules
section Delab

delab_rule BIBase.entails
  | `($_ $P $Q) => do ``($(← unpackIprop P) ⊢ $(← unpackIprop Q))

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
  | `($_ fun $x:ident => iprop(∀ $y:ident $[$z:ident]*, $Ψ)) => do ``(iprop(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(iprop(∀ $x:ident, $(← unpackIprop Ψ)))
delab_rule BIBase.exists
  | `($_ fun $x:ident => iprop(∃ $y:ident $[$z:ident]*, $Ψ)) => do ``(iprop(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(iprop(∃ $x:ident, $(← unpackIprop Ψ)))
delab_rule BIBase.sep
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗ $(← unpackIprop Q)))
delab_rule BIBase.wand
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) -∗ $(← unpackIprop Q)))
delab_rule BIBase.persistently
  | `($_ $P) => do ``(iprop(<pers> $(← unpackIprop P)))

delab_rule BIBase.pure
  | `($_ True) => ``(iprop($(mkIdent `True)))
  | `($_ False) => ``(iprop($(mkIdent `False)))
delab_rule BIBase.imp
  | `($_ $P iprop(False)) => do ``(iprop(¬$(← unpackIprop P)))

end Delab

/-- Entailment on separation logic propositions with an empty context. -/
macro:25 "⊢ " P:term:25 : term => ``(iprop(emp) ⊢ iprop($P))
/-- Bidirectional entailment on separation logic propositions. -/
macro:25 P:term:29 " ⊣⊢ " Q:term:29 : term => ``(iprop($P) = iprop($Q))

delab_rule BIBase.entails
  | `($_ iprop(emp) $P) => do ``(⊢ $(← unpackIprop P))

/-- Bidirectional implication on separation logic propositions. -/
syntax:27 term:28 " ↔ " term:28 : term
/-- Bidrectional separating implication on separation logic propositions. -/
syntax:27 term:28 " ∗-∗ " term:28 : term

def iff     [BIBase PROP] (P Q : PROP) : PROP := iprop((P → Q) ∧ (Q → P))
def wandIff [BIBase PROP] (P Q : PROP) : PROP := iprop((P -∗ Q) ∧ (Q -∗ P))

macro_rules
  | `(iprop($P ↔ $Q))   => ``(iff iprop($P) iprop($Q))
  | `(iprop($P ∗-∗ $Q)) => ``(wandIff iprop($P) iprop($Q))

delab_rule iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ↔ $(← unpackIprop Q)))
delab_rule wandIff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗-∗ $(← unpackIprop Q)))

/-- Affine modality. -/
syntax:max "<affine> " term:40 : term
/-- Absorbing modality. -/
syntax:max "<absorb> " term:40 : term

def affinely    [BIBase PROP] (P : PROP) : PROP := iprop(emp ∧ P)
def absorbingly [BIBase PROP] (P : PROP) : PROP := iprop(True ∗ P)

macro_rules
  | `(iprop(<affine> $P)) => ``(affinely iprop($P))
  | `(iprop(<absorb> $P)) => ``(absorbingly iprop($P))

delab_rule affinely
  | `($_ $P) => do ``(iprop(<affine> $(← unpackIprop P)))
delab_rule absorbingly
  | `($_ $P) => do ``(iprop(<absorb> $(← unpackIprop P)))

/-- Intuitionistic modality. -/
syntax:max "□ " term:40 : term

def intuitionistically [BIBase PROP] (P : PROP) : PROP := iprop(<affine> <pers> P)

macro_rules
  | `(iprop(□ $P)) => ``(intuitionistically iprop($P))

delab_rule intuitionistically
  | `($_ $P) => do ``(iprop(□ $(← unpackIprop P)))

/-- Conditional persistency modality. -/
syntax:max "<pers>?"   term:max ppHardSpace term:40 : term
/-- Conditional affine modality. -/
syntax:max "<affine>?" term:max ppHardSpace term:40 : term
/-- Conditional absorbing modality. -/
syntax:max "<absorb>?" term:max ppHardSpace term:40 : term
/-- Conditional intuitionistic modality. -/
syntax:max "□?"        term:max ppHardSpace term:40 : term

def persistentlyIf       [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <pers> P else P)
def affinelyIf           [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <affine> P else P)
def absorbinglyIf        [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <absorb> P else P)
def intuitionisticallyIf [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then □ P else P)

macro_rules
  | `(iprop(<pers>?$p $P))   => ``(persistentlyIf $p iprop($P))
  | `(iprop(<affine>?$p $P)) => ``(affinelyIf $p iprop($P))
  | `(iprop(<absorb>?$p $P)) => ``(absorbinglyIf $p iprop($P))
  | `(iprop(□?$p $P))        => ``(intuitionisticallyIf $p iprop($P))

delab_rule persistentlyIf
  | `($_ $p $P) => do ``(iprop(<pers>?$p $(← unpackIprop P)))
delab_rule affinelyIf
  | `($_ $p $P) => do ``(iprop(<affine>?$p $(← unpackIprop P)))
delab_rule absorbinglyIf
  | `($_ $p $P) => do ``(iprop(<absorb>?$p $(← unpackIprop P)))
delab_rule intuitionisticallyIf
  | `($_ $p $P) => do ``(iprop(□?$p $(← unpackIprop P)))

/-- Fold the conjunction `∧` over a list of separation logic propositions. -/
syntax:40 "[∧] " term:max : term
/-- Fold the disjunction `∨` over a list of separation logic propositions. -/
syntax:40 "[∨] " term:max : term
/-- Fold the separating conjunction `∗` over a list of separation logic propositions. -/
syntax:40 "[∗] " term:max : term

macro_rules
  | `(iprop([∧] $Ps)) => ``(bigOp BIBase.and iprop(True) iprop($Ps))
  | `(iprop([∨] $Ps)) => ``(bigOp BIBase.or iprop(False) iprop($Ps))
  | `(iprop([∗] $Ps)) => ``(bigOp BIBase.sep iprop(emp) iprop($Ps))

delab_rule bigOp
  | `($_ BIBase.and iprop(True)  $Ps) => do ``(iprop([∧] $(← unpackIprop Ps)))
  | `($_ BIBase.or  iprop(False) $Ps) => do ``(iprop([∨] $(← unpackIprop Ps)))
  | `($_ BIBase.sep iprop(emp)   $Ps) => do ``(iprop([∗] $(← unpackIprop Ps)))
