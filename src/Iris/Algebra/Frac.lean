/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

-- TODO: The typeclasses generalize the fractional construction by paramaterizing by the operations we need,
-- but this could probably be simpified, and use an actual arithmetic type if we have access to it.
-- I want this to be generalized so I can use posreal from mathlib.

class One (T : Type _) where one : T
export One(one)

class CommMonoid (α : Type _) extends Add α, Zero α, One α where
  assoc  : ∀ a b c : α, (a + b) + c = a + (b + c)
  comm : ∀ a b : α, a + b = b + a
  id_law : ∀ a : α, a + 0 = a

class TotallyOrdered (α : Type _) extends LE α, LT α where
  le_refl : ∀ {a : α}, a ≤ a
  le_antisymm : ∀ {a b : α}, a ≤ b → ¬ b ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  le_total : ∀ {a b : α}, a ≤ b ∨ b ≤ a
  lt_def_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ a ≠ b

class Fractional (α : Type _) extends CommMonoid α, TotallyOrdered α where

  add_le_mono  : ∀ {a b c : α}, a + b ≤ c → a ≤ c
  lt_sum : ∀ {a b : α}, a < b ↔ ∃ r, a + r = b
  left_cancel : ∀ {a b c : α}, c + a = c + b → a = b
  positive : ∀ {a : α}, ¬∃ (b : α), a + b ≤ a



namespace Iris

abbrev Frac (T : Type _) [Fractional T] := LeibnizO T

-- TODO: How do I get rid of these instances?
-- I definitely do not want to use an abbrev for Frac (there are many different OFE's for numerical types)
-- so do we need to keep around all of these coercions?
instance [Fractional α] : Coe (Frac α) α := ⟨(·.car)⟩
instance [Fractional T] : Coe T (Frac T) := ⟨(⟨·⟩)⟩
@[simp] instance [Fractional T] : COFE (Frac T) := by unfold Frac; infer_instance
@[simp] instance [Fractional T] : One (Frac T) := ⟨⟨One.one⟩⟩
@[simp] instance [Fractional T] : LE (Frac T) := ⟨fun x y => x.1 ≤ y.1⟩
@[simp] instance [Fractional T] : LT (Frac T) := ⟨fun x y => x.1 < y.1⟩
@[simp] instance [Fractional T] : Add (Frac T) := ⟨fun x y => x.1 + y.1⟩

namespace Frac

variable [iF : Fractional α]

instance Frac_CMRA : CMRA (Frac α) where
  pcore _ := none
  op := Add.add
  ValidN _ x := x ≤ one
  Valid x := x ≤ one
  op_ne {x} := ⟨fun _ _ _ => congrArg (Add.add x)⟩
  pcore_ne := fun _ => (exists_eq_right'.mpr ·)
  validN_ne := (le_of_eq_of_le ∘ OFE.Dist.symm <| ·)
  valid_iff_validN := Iff.symm (forall_const Nat)
  validN_succ := (·)
  validN_op_left := Fractional.add_le_mono
  assoc := by simp [← iF.assoc]
  comm := by simp [← iF.comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  extend {_ _ y1 y2} _ _ := by exists y1; exists y2

-- TODO: Simplify
theorem frac_included {p q : Frac α} : p ≼ q ↔ p < q :=
  ⟨ by
      rintro ⟨r, Hr⟩
      apply Fractional.lt_sum.mpr
      exists r
      rw [Hr]
      rfl,
    by
      intro H
      rcases Fractional.lt_sum.mp H with ⟨r, Hr⟩
      exists r
      simp [Iris.Frac.Frac_CMRA]
      rw [Hr]
      rfl⟩

theorem frac_included_weak {p q : Frac α} (H : p ≼ q) : p ≤ q := by
  have h := iF.lt_def_le.mp (frac_included.mp H)
  simp [h]

instance : CMRA.Discrete (Frac α) where
  discrete_0 := id
  discrete_valid := id

instance : CMRA.Exclusive (one : Frac α) where
  exclusive0_l _ H := Fractional.positive ⟨_, H⟩

-- TODO: Simplify
instance {q : Frac α} : CMRA.Cancelable q where
  cancelableN {n x y} := by
    simp [CMRA.ValidN]
    intro _
    suffices q + x = q + y → x = y by apply this
    intro H
    simp at H
    have H' := @iF.left_cancel x.car y.car q.car
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases q with ⟨q⟩
    simp_all [Add.add]
    rw [H']
    simp [HAdd.hAdd] at H
    have H'' : ({ car := Add.add q x } : Frac α).car = ({ car := Add.add q y } : Frac α).car := by
      rw [H]
    exact H''

-- TODO: Simplify
instance {q : Frac α} : CMRA.IdFree q where
  id_free0_r y := by
    intro H H'
    apply @Fractional.positive (α) (a := q)
    exists y
    conv=>
      rhs
      rw [← H']
    apply iF.le_refl

end Frac
