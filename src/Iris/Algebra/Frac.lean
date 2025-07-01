/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Shreyas Srinivas
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

/-!
# The Frac CMRA

This CMRA captures the notion of fractional ownership of another resource.
Traditionally the underlying set is assumed to be the half open interval $$(0,1]$$.
-/

class Fraction (α : Type _) extends Add α where
  /-- Validity predicate on fractions. Generalizes the notion of `(· ≤ 1)` from rational fractions. -/
  Proper : α → Prop
  add_comm : ∀ {a b : α}, a + b = b + a
  add_assoc : ∀ {a b c : α}, a + (b + c) = (a + b) + c
  add_left_cancel : ∀ {a b c : α}, a + b = a + c → b = c
  /-- There does not exist a zero fraction. -/
  add_ne : ∀{a b : α}, a ≠ b + a
  proper_add_mono_left : ∀ {a b : α}, Proper (a + b) → Proper a

/-- A fraction does not represent the entire resource.
Generalizes the notion of `(· < 1)` from rational fractions. -/
def Fraction.Fractional [Fraction α] (a : α) : Prop := ∃ b, Fraction.Proper (a + b)

/-- A fraction that is tne entire resource.
Generalizes the notion of `1` from rational fractions. -/
def Fraction.Whole [Fraction α] (a : α) : Prop := Fraction.Proper a ∧ ¬Fraction.Fractional a

section Fractional

open Fraction

variable [Fraction α]

theorem Proper.fractional_or_whole {a : α} (H : Proper a) : Fractional a ∨ Whole a := by
  apply (Classical.em (∃ b, Proper (a + b))).elim
  · exact (Or.intro_left _ ·)
  · exact (Or.intro_right _ ⟨H, ·⟩)

theorem Proper.fractional_not_whole {a : α} (H : Fractional a) : ¬Whole a :=
  H.elim fun a' Ha' Hk => Hk.2 ⟨a', Ha'⟩

theorem Proper.whole_not_fractional {a : α} (H : Whole a) : ¬Fractional a :=
  H.elim fun _ Hk1 Hk2 => Hk1 Hk2

theorem add_right_cancel {a b c : α} (H : b + a = c + a) : b = c :=
  add_left_cancel <| add_comm (a := c) ▸ add_comm (a := b) ▸ H

theorem fractional_proper {a : α} : Fractional a → Proper a :=
  fun H => H.elim fun _ H' => Fraction.proper_add_mono_left H'

theorem Fractional_add_left {a a' : α} (H : Fractional (a + a')) : Fractional a := by
  rcases H with ⟨z, Hz⟩
  exists (a' + z)
  rw [add_assoc]
  exact Hz

theorem Fractional_add_right {a a' : α} (H : Fractional (a + a')) : Fractional a' := by
  rcases H with ⟨z, Hz⟩
  exists (a + z)
  rw [add_assoc, add_comm (a := a')]
  exact Hz

end Fractional

namespace Iris

open Fraction OFE CMRA

abbrev Frac (α : Type _) := LeibnizO α
instance [Fraction α] : Coe (Frac α) α := ⟨(·.1)⟩
instance [Fraction α] : Coe α (Frac α) := ⟨(⟨·⟩)⟩
@[simp] instance [Fraction α] : COFE (Frac α) := by unfold Frac; infer_instance
@[simp] instance [Fraction α] : Add (Frac α) := ⟨fun x y => x.1 + y.1⟩
instance : Leibniz (Frac α) := ⟨(·)⟩

instance Frac_CMRA [Fraction α] : CMRA (Frac α) where
  pcore _ := none
  op := (Add.add)
  ValidN _ x := Proper x.1
  Valid x := Proper x.1
  op_ne {x} := ⟨fun _ _ _ => congrArg <| Add.add x⟩
  pcore_ne _ := (exists_eq_right'.mpr ·)
  validN_ne H Hp := H ▸ Hp
  valid_iff_validN := forall_const _ |>.symm
  validN_succ := (·)
  validN_op_left := proper_add_mono_left
  assoc := Equiv.of_eq <| by simp only [Add.add]; rw [add_assoc]
  comm := Equiv.of_eq <| by simp only [Add.add]; rw [add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  extend {_ _ y1 y2} _ _ := by exists y1; exists y2

instance [Fraction α] : CMRA.Discrete (Frac α) where
  discrete_0 := id
  discrete_valid := id

instance [Fraction α] [CMRA α] {a : Frac α} (Hw : Whole a.1) : Exclusive a where
  exclusive0_l _ Hk := (not_exists.mp Hw.2) _ Hk

instance [Fraction α] {a : Frac α} : CMRA.Cancelable a where
  cancelableN {n x y} _ H := by
    refine Dist.of_eq <| LeibnizO.ext <| add_left_cancel (a := a.car) <| ?_
    suffices a • x = a • y by simp [CMRA.op] at this; exact this
    trivial

instance [Fraction α] {a : Frac α} : CMRA.IdFree a where
  id_free0_r b _ H := by
    suffices (b + a).car = a.car by exact add_ne this.symm
    refine LeibnizO.ext_iff.mp (Leibniz.eq_of_eqv ?_)
    exact CMRA.comm.trans (discrete_0 H)

end Iris

/-- A type of fractions with a unique whole element. -/
class UFraction (α : Type _) extends Fraction α, One α where
  whole_iff_one {a : α} : Fraction.Whole a ↔ a = 1

section NumericFraction

section NumericFraction
/-- Generic fractional instance for types with comparison and 1 operators. -/
class NumericFraction (α : Type _) extends One α, Add α, LE α, LT α where
  add_comm : ∀ {a b : α}, a + b = b + a
  add_assoc : ∀ {a b c : α}, a + (b + c) = (a + b) + c
  add_left_cancel : ∀ {a b c : α}, a + b = a + c → b = c
  le_def : ∀ {a b : α}, a ≤ b ↔ a = b ∨ a < b
  lt_def : ∀ {a b : α}, a < b ↔ ∃ c : α, a + c = b
  lt_not_eq : ∀ {a b : α}, a < b → a ≠ b

open Iris

@[simp] instance [NumericFraction T] : One (Frac T) := ⟨⟨One.one⟩⟩
@[simp] instance [NumericFraction T] : LE (Frac T) := ⟨fun x y => x.1 ≤ y.1⟩
@[simp] instance [NumericFraction T] : LT (Frac T) := ⟨fun x y => x.1 < y.1⟩

variable {α} [NumericFraction α]

open NumericFraction Iris

theorem le_refl {a : α} : a ≤ a := by
  rw [le_def]
  left
  rfl

theorem lt_trans {a b c : α} : a < b → b < c → a < c := by
  rw [lt_def, lt_def, lt_def] at *
  intro ⟨ac, hac⟩ ⟨bc, hbc⟩
  exists (ac + bc)
  rw [←hac, ←add_assoc] at hbc
  assumption

theorem le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  rw [le_def, le_def, le_def]
  rintro (ha_eq_b | ha_lt_b) (hb_eq_c | hb_lt_c)
  case inl.inl =>
    left; apply Eq.trans; exact ha_eq_b; assumption
  case inl.inr =>
    right; rw[←ha_eq_b] at hb_lt_c; assumption
  case inr.inl =>
    right; rw [←hb_eq_c]; assumption
  case inr.inr =>
    right; apply lt_trans; exact ha_lt_b; assumption

theorem add_le_mono {a b c : α} : a + b ≤ c → a ≤ c := by
  simp only [le_def, lt_def]
  rintro (heq | ⟨d, hltd⟩)
  · right
    exists b
  · right
    exists (b + d)
    rw[add_assoc]
    assumption

theorem lt_le {a b : α} : a < b → a ≤ b := by
  rw[le_def]
  intro h
  right
  assumption

theorem positive {a : α} : ¬ ∃ b : α, a + b = a := by
  rw[←lt_def]
  intro hlt
  exact (lt_not_eq hlt) rfl

theorem strictly_positive {a : α} : ¬ ∃ b : α, a + b < a := by
  intro ⟨c,H⟩
  rw [lt_def] at H
  have ⟨c1, H⟩:= H
  rw [←add_assoc] at H
  exact positive ⟨c + c1, H⟩

instance : UFraction α where
  Proper x := x ≤ 1
  add_comm := add_comm
  add_assoc := add_assoc
  add_left_cancel := add_left_cancel
  add_ne H := positive (α := α) ⟨_, add_comm.trans H.symm⟩
  proper_add_mono_left := add_le_mono
  whole_iff_one {a} := by
    constructor
    · intro H
      simp [Fraction.Whole] at H
      rcases H with ⟨Hp, Hdp⟩
      cases (le_def.mp Hp)
      · trivial
      · rename_i HK; exfalso
        rcases (lt_def.mp HK) with ⟨c, Hc⟩
        apply Hdp
        exists c
        rw [← Hc]
        exact le_refl
    · intro H; subst H
      refine ⟨le_refl, ?_⟩
      rintro ⟨b, H⟩
      simp [Fraction.Proper] at H
      cases (le_def.mp H)
      · rename_i H''
        apply positive ⟨b, H''⟩
      · rename_i H''
        apply strictly_positive ⟨b, H''⟩

theorem frac_included {p q : Frac α} : p ≼ q ↔ p < q :=
  ⟨ by rintro ⟨r, Hr⟩; exact lt_def.mpr ⟨r, Hr ▸ rfl⟩,
    by
      intro H
      rcases lt_def.mp H with ⟨r, Hr⟩
      exact ⟨r, OFE.Equiv.of_eq <| LeibnizO.ext_iff.mpr Hr.symm⟩⟩

theorem frac_included_weak {p q : Frac α} (H : p ≼ q) : p ≤ q :=
  lt_le (frac_included.mp H)

end NumericFraction
