/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Iris.Algebra.OFE

namespace Iris
open OFE

class CMRA (α : Type _) extends OFE α where
  pcore : α → Option α
  op : α → α → α
  validN : Nat → α → Prop
  valid : α → Prop

  op_ne : NonExpansive (op x)
  pcore_ne : x ≡{n}≡ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  validN_ne : x ≡{n}≡ y → validN n x → validN n y

  valid_validN : valid x ↔ ∀ n, validN n x
  validN_succ : validN n.succ x → validN n x
  assoc : op x (op y z) ≡ op (op x y) z
  comm : op x y ≡ op y x
  pcore_l : pcore x = some cx → op cx x ≡ x
  pcore_idem : pcore x = some cx → pcore cx ≡ some cx
  pcore_mono' : pcore x = some cx → ∃ cy, pcore (op x y) = some (op cx cy)
  validN_op_l : validN n (op x y) → validN n x
  extend : validN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

namespace CMRA
variable [CMRA α]

infix:60 " • " => op

def included (x y : α) : Prop := ∃ z, y ≡ x • z
infix:50 " ≼ " => included

def includedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
notation:50 x "≼{" n "}" y:51 => includedN n x y

def op? [CMRA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
infix:60 " •? " => op?

prefix:50 "✓" => valid
notation:50 "✓{" n "}" x:51 => validN n x

class CoreId (x : α) : Prop where
  core_id : pcore x ≡ some x

class Exclusive (x : α) : Prop where
  exclusive0_l : ¬✓{0} x • y

class Cancelable (x : α) : Prop where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z

class IdFree (x : α) : Prop where
  id_free0_r : ✓{0} x → ¬x • y ≡{0}≡ x

class IsTotal (α : Type _) [CMRA α] where
  total (x : α) : ∃ cx, pcore x = some cx

def core (x : α) := (pcore x).getD x

class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x

end CMRA

class UCMRA (α : Type _) extends CMRA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x ≡ x
  pcore_unit : pcore unit ≡ some unit
