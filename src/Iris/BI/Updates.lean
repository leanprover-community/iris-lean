/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.BI

--TODO: Which type should we use for sets of masks?
abbrev Set (α : Type _) := α → Prop
abbrev setT {α : Type _} : Set α := fun _ => True

class BUpd (PROP : Type _) where
  bupd : PROP → PROP
export BUpd (bupd)

syntax "|==> " term : term
syntax term " ==∗ " term : term

macro_rules
  | `(iprop(|==> $P))  => ``(iprop(bupd $P))
  | `(iprop($P ==∗ $Q))  => ``(iprop($P -∗ bupd $Q))

delab_rule BUpd.bupd
  | `($_ $P) => do ``(iprop(|==> $(← Iris.BI.unpackIprop P)))
-- delab_rule WandUpdate ??
--   | `($_ $P $Q) => ``(iprop($P ==∗ $Q))

class FUpd (PROP : Type _) (MASK : Type _) where
  fupd : Set MASK → Set MASK → PROP → PROP
export FUpd (fupd)

syntax "|={ " term " , " term " }=> " term : term
syntax term "={ " term " , " term " }=∗ " term : term
syntax "|={ " term " }=> " term : term
syntax term "={ " term " }=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 , $E2 }=> $P))  => ``(iprop(fupd $E1 $E2 $P))
  | `(iprop($P ={ $E1 , $E2 }=∗ $Q))  => ``(iprop($P -∗ fupd $E1 $E2 $Q))
  | `(iprop(|={ $E1 }=> $P))  => ``(iprop(fupd $E1 $P))
  | `(iprop($P ={ $E1 }=∗ $Q))  => ``(iprop($P -∗ fupd $E1 $Q))

-- Delab rules


syntax "|={ " term " }[ " term " ]▷=> " term : term
syntax term "={ " term " }[ " term " ]▷=∗ " term : term
syntax "|={ " term " }▷=> " term : term
syntax term "={ " term " }▷=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷=> $P))  => ``(iprop(|={$E1, $E2}=> ▷ (|={ $E2, $E1 }=> $P)))
  | `(iprop($P ={ $E1 }[ $E2 ]▷=∗ $Q))  => ``(iprop($P -∗ |={$E1}[$E2]▷=> $Q))
  | `(iprop(|={ $E1 }▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> $P))
  | `(iprop($P ={ $E1 }▷=∗ $Q))  => ``(iprop($P ={$E1}[$E1]▷=∗ $Q))

-- Delab rules


syntax "|={ " term " }[ " term " ]▷^" term "=> " term : term
syntax term "={ " term " }[ " term " ]▷^" term "=∗ " term : term
syntax "|={ " term " }▷^" term "=> " term : term
syntax term "={ " term " }▷^" term "=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷^$n=> $P))  => ``(iprop(|={$E1, $E2}=> ▷^[$n] (|={ $E2, $E1 }=> $P)))
  | `(iprop($P ={ $E1 }[ $E2 ]▷^$n=∗ $Q))  => ``(iprop($P -∗ |={$E1}[$E2]▷^$n=> $Q))
  | `(iprop(|={ $E1 }▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> $P))
  | `(iprop($P ={ $E1 }▷^$n=∗ $Q))  => ``(iprop($P ={$E1}[$E1]▷^$n=∗ $Q))

-- Delab rules

namespace Iris.BI
open Iris.Std BI



-- example [BI PROP] [BUpd PROP] (P Q : PROP) : ⊢ iprop(R ∗ P) := sorry
example [BI PROP] [BUpd PROP] (P : PROP) : ⊢ iprop(|==> P) := sorry
-- example [BI PROP] [BUpd PROP] (P : PROP) : ⊢ iprop(|==> P ∗ P) := sorry
example [BI PROP] [BUpd PROP] (P Q : PROP) : ⊢ iprop(R ∗ P ==∗ Q) := sorry
-- example [BI PROP] [BUpd PROP] (P Q R : PROP) : ⊢ iprop(R ∗ P ==∗ Q -∗ R) := sorry
example [BI PROP] [BUpd PROP] (P Q : PROP) : ⊢ iprop(P -∗ |==> P) := sorry
