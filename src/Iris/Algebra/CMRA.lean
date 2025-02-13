/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Iris.Algebra.OFE

namespace Iris
open OFE

class PreCMRA (α : Type _) extends OFE α where
  op : α → α → α
  validN : Nat → α → Prop
  valid : α → Prop

export PreCMRA (op validN valid)

namespace CMRA

infix:60 " • " => op

def included [PreCMRA α] (x y : α)  : Prop := ∃ z, y ≡ x • z
infix:50 " ≼ " => included

def includedN [PreCMRA α] (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
notation:50 x " ≼{" n "} " y:51 => includedN n x y

prefix:50 "✓" => valid
notation:50 "✓{" n "}" x:51 => validN n x

abbrev is_idempotentN_lb [PreCMRA α] (x : α) (n : Nat) (y : α) : Prop :=
  y ≼{n} x ∧ y • y ≡{n}≡ y

abbrev is_maximal_idempotentN_lb [PreCMRA α] (x : α) (n : Nat) (cx : α) : Prop :=
  is_idempotentN_lb x n cx ∧ ∀ m y, m ≤ n -> is_idempotentN_lb x m y -> y ≼{m} cx

abbrev no_maximal_idempotentN [PreCMRA α] (x : α) : Prop :=
  ∀ y, ¬ is_idempotentN_lb x 0 y

inductive MI [PreCMRA α] (x : α) (n : Nat) : Type _ where
| HasMI (cx : α) : is_maximal_idempotentN_lb x n cx -> MI x n
| NoMI : no_maximal_idempotentN x -> MI x n

end CMRA

class CMRA (α : Type _) extends PreCMRA α where
  op_ne : NonExpansive (op x)
  valid_imp_eqv : x₁ ≡{n}≡ x₂ -> validN n x₁ -> validN n x₂
  valid_validN : valid x ↔ ∀ n, validN n x
  validN_succ : validN n.succ x → validN n x
  assoc : op x (op y z) = op (op x y) z
  comm : op x y = op y x
  validN_l : validN n (op x y) -> validN n x
  extend : validN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  mi : validN n x -> CMRA.MI x n

namespace CMRA
variable [CMRA α]

def op? [CMRA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
infix:60 " •? " => op?

class CoreId (x : α) : Prop where
  core_id : x ≡ x • x

class Exclusive (x : α) : Prop where
  exclusive0_l : ¬✓{0} x • y

class Cancelable (x : α) : Prop where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z

class IdFree (x : α) : Prop where
  id_free0_r : ✓{0} x → ¬x • y ≡{0}≡ x

class IsTotal (α : Type _) [CMRA α] where
  total (x : α) : ∃ cx, cx ≼ x ∧ cx ≡ cx • cx

class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x

end CMRA

class UCMRA (α : Type _) extends CMRA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x ≡ x

class CMRATotal (α : Type _) extends CMRA α where
  total : ∀ x, ∃ (cx : α), cx ≼ x ∧ cx • cx ≡ cx
