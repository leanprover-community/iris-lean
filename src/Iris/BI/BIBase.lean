/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.Notation
import Iris.Std.Classes
import Iris.Std.DelabRule
import Iris.Std.Rewrite

namespace Iris.BI
open Iris.Std
open Lean

/-- Require the definitions of the separation logic connectives and units on a carrier type `car`. -/
class BIBase (car : Type) where
  entails : car → car → Prop
  emp : car
  pure : Prop → car
  and : car → car → car
  or : car → car → car
  impl : car → car → car
  «forall» {α : Type} : (α → car) → car
  exist {α : Type} : (α → car) → car
  sep : car → car → car
  wand : car → car → car
  persistently : car → car


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
  | `(iprop($P → $Q))   => ``(BIBase.impl iprop($P) iprop($Q))
  | `(iprop(∃ $xs, $Ψ)) => do expandExplicitBinders ``BIBase.exist xs (← ``(iprop($Ψ)))
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
delab_rule BIBase.impl
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) → $(← unpackIprop Q)))
delab_rule BIBase.forall
  | `($_ fun $x:ident => iprop(∀ $y:ident $[$z:ident]*, $Ψ)) => do ``(iprop(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ fun $x:ident => $Ψ) => do ``(iprop(∀ $x:ident, $(← unpackIprop Ψ)))
delab_rule BIBase.exist
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
delab_rule BIBase.impl
  | `($_ $P iprop(False)) => do ``(iprop(¬$(← unpackIprop P)))

end Delab

end Iris.BI
