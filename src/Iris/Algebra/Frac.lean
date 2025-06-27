/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

/-!
# The Frac CMRA

This resource captures the notion of fractional ownership of another resource.
Traditionally the underlying set is assumed to be the half open interval $$(0,1]$$. However this full generality is not necessary. We use a generic typeclass inspired by Dyadic rational numbers for which instances can be derived later for Rational numbers, real numbers, and any other types which are useful for representing fractional ownership.
-/

section Fractional
class Fractional (α : Type _) extends One α, Add α, LE α, LT α where
  add_comm : ∀ {a b : α}, a + b = b + a
  add_assoc : ∀ {a b c : α}, a + (b + c) = (a + b) + c
  add_left_cancel : ∀ {a b c : α}, a + b = a + c → b = c
  le_def : ∀ {a b : α}, a ≤ b ↔ a = b ∨ a < b
  lt_def : ∀ {a b : α}, a < b ↔ ∃ c : α, a + c = b
  lt_not_eq : ∀ {a b : α}, a < b → a ≠ b

variable {α} [iR : Fractional α]

theorem le_refl {a : α} : a ≤ a := by
  rw [iR.le_def]
  left
  rfl

theorem lt_trans {a b c : α} : a < b → b < c → a < c := by
  rw [iR.lt_def, iR.lt_def, iR.lt_def] at *
  intro ⟨ac, hac⟩ ⟨bc, hbc⟩
  exists (ac + bc)
  rw [←hac, ←iR.add_assoc] at hbc
  assumption

theorem le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  rw [iR.le_def, iR.le_def, iR.le_def]
  rintro (ha_eq_b | ha_lt_b) (hb_eq_c | hb_lt_c)
  case inl.inl =>
    left; apply Eq.trans; exact ha_eq_b; assumption
  case inl.inr =>
    right; rw[←ha_eq_b] at hb_lt_c; assumption
  case inr.inl =>
    right; rw [←hb_eq_c]; assumption
  case inr.inr =>
    right; apply lt_trans; exact ha_lt_b; assumption

theorem add_right_cancel {a b c : α} : b + a = c + a → b = c := by
  intro h
  conv at h => lhs; rw [iR.add_comm]
  conv at h => rhs; rw [iR.add_comm]
  apply @iR.add_left_cancel a b c
  assumption

theorem add_le_mono {a b c : α} : a + b ≤ c → a ≤ c := by
  simp[iR.le_def, iR.lt_def]
  rintro (heq | ⟨d, hltd⟩)
  · right
    exists b
  · right
    exists (b + d)
    rw[iR.add_assoc]
    assumption

theorem lt_le {a b : α} : a < b → a ≤ b := by
  rw[iR.le_def]
  intro h
  right
  assumption

theorem positive {a : α} : ¬ ∃ b : α, a + b = a := by
  rw[←iR.lt_def]
  intro hlt
  exact (iR.lt_not_eq hlt) rfl

theorem strictly_positive {a : α} : ¬ ∃ b : α, a + b < a := by
  intro ⟨c,H⟩
  rw [iR.lt_def] at H
  have ⟨c1, H⟩:= H
  rw [←iR.add_assoc] at H
  exact positive ⟨c + c1, H⟩

end Fractional

namespace Iris

def Frac (T : Type _) [Fractional T] := LeibnizO T

-- TODO: How do I get rid of these instances?
-- I definitely do not want to use an abbrev for Frac (there are many different OFE's for numerical types)
-- so do we need to keep around all of these coercions?
instance [Fractional T] : Coe (Frac T) T := ⟨(·.1)⟩
instance [Fractional T] : Coe T (Frac T) := ⟨(⟨·⟩)⟩
@[simp] instance [Fractional T] : COFE (Frac T) := by unfold Frac; infer_instance
@[simp] instance [Fractional T] : One (Frac T) := ⟨⟨One.one⟩⟩
@[simp] instance [Fractional T] : LE (Frac T) := ⟨fun x y => x.1 ≤ y.1⟩
@[simp] instance [Fractional T] : LT (Frac T) := ⟨fun x y => x.1 < y.1⟩
@[simp] instance [Fractional T] : Add (Frac T) := ⟨fun x y => x.1 + y.1⟩

namespace Frac

variable [iFrac : Fractional α]

instance Frac_CMRA : CMRA (Frac α) where
  pcore _ := none
  op := (Add.add)
  ValidN _ x := x ≤ 1
  Valid x := x ≤ 1
  op_ne {x} := ⟨fun _ _ _ => congrArg (Add.add x)⟩
  pcore_ne := fun _ => (exists_eq_right'.mpr ·)
  validN_ne := (le_of_eq_of_le ∘ OFE.Dist.symm <| ·)
  valid_iff_validN := Iff.symm (forall_const Nat)
  validN_succ := (·)
  validN_op_left := add_le_mono
  assoc := by simp [iFrac.add_assoc]
  comm := by simp [iFrac.add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  extend {_ _ y1 y2} _ _ := by exists y1; exists y2


theorem frac_included {p q : Frac α} : p ≼ q ↔ p < q :=
  ⟨ by
      rintro ⟨r, Hr⟩
      apply iFrac.lt_def.mpr
      exists r
      rw [Hr]
      rfl,
    by
      intro H
      rcases iFrac.lt_def.mp H with ⟨r, Hr⟩
      exists r
      simp [Iris.Frac.Frac_CMRA]
      rw [Hr]
      rfl⟩

theorem frac_included_weak {p q : Frac α} (H : p ≼ q) : p ≤ q :=
  lt_le (frac_included.mp H)

instance : CMRA.Discrete (Frac α) where
  discrete_0 := id
  discrete_valid := id

instance : CMRA.Exclusive (1 : Frac α) where
  exclusive0_l x H := by
    simp [CMRA.op, Frac_CMRA, iFrac.le_def] at H
    obtain (H | H) := H
    · exact positive ⟨x.car, H⟩
    · exact strictly_positive ⟨x.car, H⟩


-- TODO: Simplify
instance {q : Frac α} : CMRA.Cancelable q where
  cancelableN {n x y} := by
    simp [CMRA.ValidN]
    intro _
    suffices q + x = q + y → x = y by apply this
    intro H
    have H' := @iFrac.add_left_cancel x.car y.car q.car
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases q with ⟨q⟩
    simp_all [Add.add]
    rw [H']
    simp [HAdd.hAdd] at H
    have H'' : ({ car := Add.add q x } : Frac α).car = ({ car := Add.add q y } : Frac α).car := by
      rw [H]
    simp at H''
    exact H''


instance {q : Frac α} : CMRA.IdFree q where
  id_free0_r y := by
    intro H H'
    apply @positive α (a := q)
    exists y
    conv=>
      rhs
      rw [← H']
    unfold CMRA.op Frac_CMRA
    simp
    exact iFrac


end Frac
