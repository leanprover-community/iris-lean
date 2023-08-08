/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI.BI

namespace Iris.BI

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

def bi_iff      [BIBase PROP] (P Q : PROP) : PROP := iprop((P → Q) ∧ (Q → P))
def bi_wand_iff [BIBase PROP] (P Q : PROP) : PROP := iprop((P -∗ Q) ∧ (Q -∗ P))

macro_rules
  | `(iprop($P ↔ $Q))   => ``(bi_iff iprop($P) iprop($Q))
  | `(iprop($P ∗-∗ $Q)) => ``(bi_wand_iff iprop($P) iprop($Q))

delab_rule bi_iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ↔ $(← unpackIprop Q)))
delab_rule bi_wand_iff
  | `($_ $P $Q) => do ``(iprop($(← unpackIprop P) ∗-∗ $(← unpackIprop Q)))

/-- Affine modality. -/
syntax:max "<affine> " term:40 : term
/-- Absorbing modality. -/
syntax:max "<absorb> " term:40 : term

def bi_affinely    [BIBase PROP] (P : PROP) : PROP := iprop(emp ∧ P)
def bi_absorbingly [BIBase PROP] (P : PROP) : PROP := iprop(True ∗ P)

macro_rules
  | `(iprop(<affine> $P)) => ``(bi_affinely iprop($P))
  | `(iprop(<absorb> $P)) => ``(bi_absorbingly iprop($P))

delab_rule bi_affinely
  | `($_ $P) => do ``(iprop(<affine> $(← unpackIprop P)))
delab_rule bi_absorbingly
  | `($_ $P) => do ``(iprop(<absorb> $(← unpackIprop P)))

/-- Intuitionistic modality. -/
syntax:max "□ " term:40 : term

def bi_intuitionistically [BIBase PROP] (P : PROP) : PROP := iprop(<affine> <pers> P)

macro_rules
  | `(iprop(□ $P)) => ``(bi_intuitionistically iprop($P))

delab_rule bi_intuitionistically
  | `($_ $P) => do ``(iprop(□ $(← unpackIprop P)))

/-- Conditional persistency modality. -/
syntax:max "<pers>?"   term:max ppHardSpace term:40 : term
/-- Conditional affine modality. -/
syntax:max "<affine>?" term:max ppHardSpace term:40 : term
/-- Conditional absorbing modality. -/
syntax:max "<absorb>?" term:max ppHardSpace term:40 : term
/-- Conditional intuitionistic modality. -/
syntax:max "□?"        term:max ppHardSpace term:40 : term

def bi_persistently_if       [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <pers> P else P)
def bi_affinely_if           [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <affine> P else P)
def bi_absorbingly_if        [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then <absorb> P else P)
def bi_intuitionistically_if [BIBase PROP] (p : Bool) (P : PROP) : PROP := iprop(if p then □ P else P)

macro_rules
  | `(iprop(<pers>?$p $P))   => ``(bi_persistently_if $p iprop($P))
  | `(iprop(<affine>?$p $P)) => ``(bi_affinely_if $p iprop($P))
  | `(iprop(<absorb>?$p $P)) => ``(bi_absorbingly_if $p iprop($P))
  | `(iprop(□?$p $P))        => ``(bi_intuitionistically_if $p iprop($P))

delab_rule bi_persistently_if
  | `($_ $p $P) => do ``(iprop(<pers>?$p $(← unpackIprop P)))
delab_rule bi_affinely_if
  | `($_ $p $P) => do ``(iprop(<affine>?$p $(← unpackIprop P)))
delab_rule bi_absorbingly_if
  | `($_ $p $P) => do ``(iprop(<absorb>?$p $(← unpackIprop P)))
delab_rule bi_intuitionistically_if
  | `($_ $p $P) => do ``(iprop(□?$p $(← unpackIprop P)))

end Iris.BI
