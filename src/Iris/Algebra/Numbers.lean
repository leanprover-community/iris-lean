/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
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
  lt_def : ∀ a b, a < b ↔ ∃ c : α, c > 0 ∧ a + c = b
  le_def : ∀ a b : α, a ≤ b ↔ a < b ∨ a = b
  lt_not_eq : ∀ {a : α}, a > 0 ↔ a ≠ 0
  add_order_compat : ∀ {a b c : α}, a ≤ b → a + c ≤ b + c
  positive  {a : α} : a ≥ 0
  left_cancel : ∀ {a b c : α}, c + a = c + b → a = b

  -- these two are theorems. remove them after replacing them with theorems
  add_le_mono  : ∀ {a b c : α}, a + b ≤ c → a ≤ c
  lt_sum : ∀ {a b : α}, a < b ↔ ∃ r, a + r = b

theorem lt_order_compat [iFrac : Numbers α] :
  ∀ {a b c : α}, a < b → a + c < b + c := by
  intro a b c
  intro hab
  rw [iFrac.lt_def] at *
  obtain ⟨d, hd_pos, hab⟩ := hab
  exists d
  constructor
  · exact hd_pos
  · conv =>
      lhs
      rw [iFrac.add_assoc]
      arg 2
      rw [iFrac.add_comm]
    conv =>
      lhs
      rw[←iFrac.add_assoc]
      rw[hab]


theorem lt_alt_def [iFrac : Numbers α] :
  ∀ {a b : α}, a < b ↔ a ≤ b ∧ a ≠ b := by
  intro a b
  constructor
  · intro h
    simp
    constructor
    · rw[iFrac.le_def]
      left
      exact h
    · rw[iFrac.lt_def] at h
      obtain ⟨c, hc_pos, hc_sum⟩ := h
      intro heq
      rw [heq] at hc_sum
      conv at hc_sum => rhs; rw [←iFrac.id_law b]

      sorry
  ·
    sorry



theorem le_alt_def [iFrac : Numbers α] :
  ∀ {a b : α}, a ≤ b ↔ ∃ c : α, a + c = b := by
  intro a b
  constructor
  · intro h
    rw [iFrac.le_def] at h
    obtain (left | right) := h
    rw [iFrac.lt_def] at left
    obtain ⟨c, hc⟩ := left
    exists c
    exact hc.right
    exists 0
    rw [iFrac.id_law]
    exact right
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [iFrac.le_def]
    by_cases hc_zero : c > 0
    left
    rw [iFrac.lt_def]
    exists c
    right
    have : c = 0 := by
      have h_int : 0 < c ∨ 0 = c:= (iFrac.le_def 0 c).mp iFrac.positive
      simp at hc_zero
      obtain (heq | hlt) := h_int
      exfalso
      exact hc_zero heq
      exact hlt.symm
    rw [this, iFrac.id_law] at hc
    exact hc

theorem lt_trans [iFrac : Numbers α] :
  ∀ {a b c : α}, a < b → b < c → a < c := by
  intro a b c hab hbc
  rw [iFrac.lt_def] at *
  obtain ⟨ad, had⟩ := hab
  obtain ⟨bd, hbd⟩ := hbc
  exists (ad + bd)
  sorry

theorem right_add_order_compat [iFrac : Numbers α] :
  ∀ a b c : α, a ≤ b → c + a ≤ c + b := by
  intro a b c h
  conv => lhs; rw[iFrac.add_comm]
  conv => rhs; rw[iFrac.add_comm]
  apply iFrac.add_order_compat h


theorem right_cancel [iFrac : Numbers α] : ∀ a b c : α, a + c = b + c → a = b := by
  intro a b c h
  conv at h => lhs; rw [iFrac.add_comm]
  conv at h => rhs; rw [iFrac.add_comm]
  apply iFrac.left_cancel h

theorem add_to_zero_is_zero [iFrac : Numbers α] :
  ∀ {a b : α}, a + b = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  constructor
  · have h' := (@le_alt_def α iFrac a 0).mpr
    have h_int : ∃ c, a + c = 0 := by
      exists b
    have h₃ : a ≤ 0 := h' h_int
    exact iFrac.le_antisymm ⟨h₃, iFrac.positive⟩
  · rw [iFrac.add_comm] at h
    have h' := (@le_alt_def α iFrac b 0).mpr
    have h_int : ∃ c, b + c = 0 := by
      exists a
    have h₃ : b ≤ 0 := h' h_int
    exact iFrac.le_antisymm ⟨h₃, iFrac.positive⟩

theorem positive [iFrac : Numbers α] : ∀ {a : α}, ¬∃ (b : α), a + b < a := by
  intro a ⟨b,hb⟩
  rw [iFrac.lt_def] at hb
  have ⟨c, hc_pos, hc_sum⟩ := hb
  rw [iFrac.add_assoc] at hc_sum
  conv at hc_sum => rhs; rw [←iFrac.id_law a]
  replace hc_sum := iFrac.left_cancel hc_sum
  have h' := add_to_zero_is_zero hc_sum
  simp at hc_pos
  exact iFrac.lt_not_eq.mp hc_pos h'.right

theorem add_le_mono [iFrac : Numbers α] : ∀ {a b c : α}, a + b ≤ c → a ≤ c := by
  intro a b c h
  rw[iFrac.le_def, iFrac.lt_def] at *
  obtain (⟨d,hd⟩ | ⟨d,hd⟩) := h
  · left
    exists (b + d)
    constructor
    · simp

      sorry
    · sorry
  ·

    left
    sorry


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

namespace Frac

variable [iF : Numbers α]

instance Frac_CMRA : CMRA (Numerical α) where
  pcore _ := some 0
  op := Add.add
  ValidN _ x := True
  Valid x := True
  op_ne {x} := ⟨fun n a b => by apply congrArg (Add.add x)⟩
  pcore_ne := fun _ => (exists_eq_right'.mpr ·)
  validN_ne := fun _ _ => True.intro
  valid_iff_validN := Iff.symm (forall_const Nat)
  validN_succ := (·)
  validN_op_left := by simp only [imp_self, implies_true]
  assoc := by simp [← iF.add_assoc]
  comm := by simp [← iF.add_comm]
  pcore_op_left := by
    intro ⟨x⟩ ⟨y⟩ hxy
    cases hxy 
    simp
    rw[iF.add_comm]
    simp[iF.id_law x]
  pcore_idem := by simp
  pcore_op_mono := by simp
  extend {_ _ y1 y2} _ _ := by exists y1; exists y2

-- TODO: Simplify
theorem num_included {p q : Numerical α} : p ≼ q ↔ p < q :=
  ⟨ by
      rintro ⟨r, Hr⟩
      apply Numbers.lt_sum.mpr
      exists r
      rw [Hr]
      rfl,
    by
      intro H
      rcases Numbers.lt_sum.mp H with ⟨r, Hr⟩
      exists r
      simp [Iris.Frac.Frac_CMRA]
      rw [Hr]
      rfl⟩

theorem frac_included_weak {p q : Numerical α} (H : p ≼ q) : p ≤ q := by
  have h := iF.lt_def_le.mp (num_included.mp H)
  simp [h]

instance : CMRA.Discrete (Numerical α) where
  discrete_0 := id
  discrete_valid := id

instance : CMRA.Exclusive (one : Numerical α) where
  exclusive0_l _ H := Numerical.positive ⟨_, H⟩

-- TODO: Simplify
instance {q : Numerical α} : CMRA.Cancelable q where
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
    have H'' : ({ car := Add.add q x } : Numerical α).car = ({ car := Add.add q y } : Numerical α).car := by
      rw [H]
    exact H''

-- TODO: Simplify
instance {q : Numerical α} : CMRA.IdFree q where
  id_free0_r y := by
    intro H H'
    apply @Numbers.positive (α) (a := q)
    exists y
    conv=>
      rhs
      rw [← H']
    apply iF.le_refl

end Frac
