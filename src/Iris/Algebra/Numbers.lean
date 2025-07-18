/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

/-!
## Numbers CMRA
This camera provides us a resource of numbers on which a total ordering compatible with an addition operationa are defined. This module defines Numbers as a commutative additive monoid which is totally ordered. The `Numbers` class extends `CommMonoid` and `TotallyOrdered` classes and includes a list of compatbility axioms between the addition operation and total ordering relation.
-/

class CommMonoid (α : Type _) extends Add α, Zero α, One α where
  add_assoc  : ∀ a b c : α, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  id_law : ∀ a : α, a + 0 = a

class TotallyOrdered (α : Type _) extends LE α, LT α where
  le_refl : ∀ {a : α}, a ≤ a
  le_antisymm : ∀ {a b : α}, a ≤ b ∧ b ≤ a → a = b
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  le_total : ∀ {a b : α}, a ≤ b ∨ b ≤ a

class Numbers (α : Type _) extends CommMonoid α, TotallyOrdered α where
  zero_lt_one : 0 < 1
  lt_def : ∀ {a b : α}, a < b ↔ a ≤ b ∧ a ≠ b
  add_le_compat : ∀ {a b c : α}, a ≤ b → a + c ≤ b + c
  add_left_cancel : ∀ {a b c : α}, c + a = c + b → a = b
  -- these two are theorems. remove them after replacing them with theorems
  add_le_mono  : ∀ {a b c : α}, a + b ≤ c → a ≤ c
  lt_sum : ∀ {a b : α}, a < b ↔ ∃ r, a + r = b

section NumbersAPI

variable [iNum : Numbers α]

theorem add_right_cancel : ∀ {a b : α}, a + c = b + c → a = b := by
  intro a b h
  conv at h => lhs; rw[iNum.add_comm]
  conv at h => rhs; rw[iNum.add_comm]
  apply iNum.add_left_cancel h

theorem lt_anti_symm : ∀ {a b : α}, a < b → ¬ b < a := by
  intro a b hlt hgt
  have hle : a ≤ b := by
    rw [iNum.lt_def] at hlt
    exact hlt.left
  have hge : b ≤ a := by
    rw [iNum.lt_def] at hgt
    exact hgt.left
  have heq : a = b := by
    apply iNum.le_antisymm
    exact ⟨hle, hge⟩
  simp[iNum.lt_def] at hlt
  exact hlt.right heq

theorem lt_order_compat :
  ∀ {a b c : α}, a < b → a + c < b + c := by
  intro a b c
  intro hab
  rw [iNum.lt_def] at *
  obtain ⟨hleq, hneq⟩ := hab
  constructor
  · apply iNum.add_le_compat hleq
  · simp_all only [ne_eq]
    intro h
    apply hneq (add_right_cancel h)


theorem lt_trans:
  ∀ {a b c : α}, a < b → b < c → a < c := by
  intro a b c hab hbc
  rw [iNum.lt_def] at *
  constructor
  · apply iNum.le_trans hab.left hbc.left
  · intro h
    rw [h] at hab
    have hbc_eq : b =c := by
      symm
      apply iNum.le_antisymm ⟨hab.left, hbc.left⟩
    exact hbc.right hbc_eq


theorem right_add_le_compat :
  ∀ a b c : α, a ≤ b → c + a ≤ c + b := by
  intro a b c h
  conv => lhs; rw[iNum.add_comm]
  conv => rhs; rw[iNum.add_comm]
  apply iNum.add_le_compat h

end NumbersAPI

namespace Iris


abbrev Numerical (α : Type _) [Numbers α] := LeibnizO α

-- TODO: How do I get rid of these instances?
-- I definitely do not want to use an abbrev for Frac (there are many different OFE's for numerical types)
-- so do we need to keep around all of these coercions?
instance [Numbers α] : Coe (Numerical α) α := ⟨(·.car)⟩
instance [Numbers T] : Coe T (Numerical T) := ⟨(⟨·⟩)⟩
@[simp] instance [Numbers T] : COFE (Numerical T) := by unfold Numerical; infer_instance
@[simp] instance [Numbers α] : Zero (Numerical α) := ⟨⟨Zero.zero⟩⟩
@[simp] instance [Numbers T] : One (Numerical T) := ⟨⟨One.one⟩⟩
@[simp] instance [Numbers T] : LE (Numerical T) := ⟨fun x y => x.1 ≤ y.1⟩
@[simp] instance [Numbers T] : LT (Numerical T) := ⟨fun x y => x.1 < y.1⟩
@[simp] instance [Numbers T] : Add (Numerical T) := ⟨fun x y => x.1 + y.1⟩



namespace NumbersCMRA

variable [iNum : Numbers α]

instance Num_CMRA : CMRA (Numerical α) where
  pcore _ := some (instZeroNumerical.zero)
  op := instAddNumerical.add
  ValidN _ x := True
  Valid x := True
  op_ne {x} := ⟨fun n a b => by apply congrArg (Add.add x)⟩
  pcore_ne := fun _ => (exists_eq_right'.mpr ·)
  validN_ne := fun _ _ => True.intro
  valid_iff_validN := Iff.symm (forall_const Nat)
  validN_succ := (·)
  validN_op_left := by simp only [imp_self, implies_true]
  assoc := by simp [← iNum.add_assoc]
  comm := by simp [← iNum.add_comm]
  pcore_op_left := by
    intro ⟨x⟩ ⟨y⟩ hxy
    cases hxy
    simp [iNum.add_comm]
    exact iNum.id_law x


  pcore_idem := by simp
  pcore_op_mono := by
    intro ⟨x⟩ ⟨cx⟩ cx_eq ⟨y⟩
    exists ⟨0⟩
    cases cx_eq
    ext
    simp [iNum.id_law]


  extend {_ _ y1 y2} _ _ := by exists y1; exists y2

-- TODO: Simplify

theorem num_included {p q : Numerical α} : p ≼ q ↔ p < q := by
  constructor
  · rintro ⟨r, Hr⟩
    apply Numbers.lt_sum.mpr
    exists r
    rw [Hr]
    rfl
  · intro H
    rcases Numbers.lt_sum.mp H with ⟨r, Hr⟩
    exists r
    simp [Iris.NumbersCMRA.Num_CMRA]
    rw [Hr]


theorem num_included_weak {p q : Numerical α} (H : p ≼ q) : p ≤ q := by
  have h := iNum.lt_def.mp (num_included.mp H)
  simp [h]

instance : CMRA.Discrete (Numerical α) where
  discrete_0 := id
  discrete_valid := id

instance : CMRA.Exclusive (one : Numerical α) where
  exclusive0_l x H := by
    simp [CMRA.ValidN, CMRA.op] at H
    sorry


-- TODO: Simplify
instance {q : Numerical α} : CMRA.Cancelable q where
  cancelableN {n x y} := by
    simp [CMRA.ValidN]
    intro _
    suffices q + x = q + y → x = y by sorry -- {apply this}
    intro H
    simp at H
    have H' := @iNum.add_left_cancel x.car y.car q.car
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases q with ⟨q⟩
    simp_all [Add.add]
    rw [H']
    simp [HAdd.hAdd] at H
    have H'' : ({ car := Add.add q x } : Numerical α).car = ({ car := Add.add q y } : Numerical α).car := by
      rw [H]
    exact H''
-- TODO: Simplify
instance {q : Numerical α} : CMRA.IdFree q where
  id_free0_r y := by
    intro H H'
    simp [CMRA.op, CMRA.toOFE.equiv_dist, CMRA.ValidN] at H' H
    sorry


end NumbersCMRA
