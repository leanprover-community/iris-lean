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

/-- A type which can be used as a a fraction. -/
class Fractional (T : Type _) extends One T, Add T, LE T, LT T where
  add_le_mono {x y z : T} : x + y ≤ z → x ≤ z
  assoc {a b c : T} : (a + b) + c = a + (b + c)
  comm {a b : T} : a + b = b + a
  lt_sum {a b : T} : a < b ↔ ∃ r, a + r = b
  lt_le {a b : T} : a < b → a ≤ b
  positive {a : T} : ¬∃ (b : T), a + b ≤ a
  cancel {a b c : T} : c + a = c + b → a = b
  le_refl {a : T} : a ≤ a

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

variable [Fractional α]

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
  assoc := by simp [← Fractional.assoc]
  comm := by simp [← Fractional.comm]
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

theorem frac_included_weak {p q : Frac α} (H : p ≼ q) : p ≤ q :=
  Fractional.lt_le (frac_included.mp H)

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
    have H' := @Fractional.cancel α _ x.car y.car q.car
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
    apply @Fractional.positive (T := α) (a := q)
    exists y
    conv=>
      rhs
      rw [← H']
    apply Fractional.le_refl

end Frac
