/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Shreyas Srinivas, Mario Carneiro
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

/-!
# The Frac CMRA

This CMRA captures the notion of fractional ownership of another resource.
Traditionally the underlying set is assumed to be the half open interval $$(0,1]$$.
-/

namespace Iris

class Fraction (α : Type _) extends Add α where
  /-- Validity predicate on fractions. Generalizes the notion of `(· ≤ 1)` from rational
  fractions. -/
  Proper : α → Prop
  add_comm : ∀ a b : α, a + b = b + a
  add_assoc : ∀ a b c : α, a + (b + c) = (a + b) + c
  add_left_cancel : ∀ {a b c : α}, a + b = a + c → b = c
  /-- There does not exist a zero fraction. -/
  add_ne : ∀ {a b : α}, a ≠ b + a
  proper_add_mono_left : ∀ {a b : α}, Proper (a + b) → Proper a

class IsSplitFraction (α : Type _) [Fraction α] where
  split : α → α × α
  split_add {a : α} : (split a).1 + (split a).2 = a

namespace Fraction

/-- A fraction does not represent the entire resource.
Generalizes the notion of `(· < 1)` from rational fractions. -/
def Fractional [Fraction α] (a : α) : Prop := ∃ b, Proper (a + b)

/-- A fraction that is tne entire resource.
Generalizes the notion of `1` from rational fractions. -/
def Whole [Fraction α] (a : α) : Prop := Proper a ∧ ¬Fractional a

variable [Fraction α]

theorem Proper.fractional_or_whole {a : α} (H : Proper a) : Fractional a ∨ Whole a := by
  if h : ∃ b, Proper (a + b) then exact .inl h
  else exact .inr ⟨H, h⟩

theorem Fractional.not_whole {a : α} (H : Fractional a) : ¬Whole a :=
  H.elim fun a' Ha' Hk => Hk.2 ⟨a', Ha'⟩

theorem Whole.not_fractional {a : α} (H : Whole a) : ¬Fractional a :=
  H.elim fun _ Hk1 Hk2 => Hk1 Hk2

theorem add_right_cancel {a b c : α} (H : b + a = c + a) : b = c :=
  add_left_cancel <| add_comm c _ ▸ add_comm b _ ▸ H

theorem Fractional.proper {a : α} : Fractional a → Proper a :=
  fun H => H.elim fun _ H' => proper_add_mono_left H'

theorem Fractional.of_add_left {a a' : α} (H : Fractional (a + a')) : Fractional a := by
  let ⟨z, Hz⟩ := H
  exists a' + z
  rw [add_assoc]
  exact Hz

theorem Fractional.of_add_right {a a' : α} (H : Fractional (a + a')) : Fractional a' := by
  let ⟨z, Hz⟩ := H
  exists a + z
  rw [add_assoc, add_comm (a := a')]
  exact Hz

end Fraction

open Fraction OFE CMRA

def Frac (α : Type _) := LeibnizO α
instance [Fraction α] : Coe (Frac α) α := ⟨(·.1)⟩
instance [Fraction α] : Coe α (Frac α) := ⟨(⟨·⟩)⟩
@[simp] instance : COFE (Frac α) := inferInstanceAs (COFE (LeibnizO α))
@[simp] instance [Fraction α] : Add (Frac α) := ⟨fun x y => x.1 + y.1⟩
instance : Leibniz (Frac α) := inferInstanceAs (Leibniz (LeibnizO α))

instance Frac_CMRA [Fraction α] : CMRA (Frac α) where
  pcore _ := none
  op := Add.add
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
  cancelableN {n x y} _ (H : a • x = a • y) := by
    refine Dist.of_eq <| LeibnizO.ext <| add_left_cancel (a := a.car) <| ?_
    simpa [CMRA.op, Frac] using H

instance [Fraction α] {a : Frac α} : CMRA.IdFree a where
  id_free0_r b _ H := by
    suffices (b + a).car = a.car from add_ne this.symm
    refine LeibnizO.ext_iff.mp (Leibniz.eq_of_eqv (α := Frac _) ?_)
    exact CMRA.comm.trans (discrete_0 H)

/-- A type of fractions with a unique whole element. -/
class UFraction (α : Type _) extends Fraction α, One α where
  -- Experiment: I don't see why we need a unique One element. I wouldn't be surprised if it were
  -- necessary somewhere, but for now we will try relaxing the constraint to just assert the
  -- existence of a Whole element.
  -- whole_iff_one {a : α} : Fraction.Whole a ↔ a = 1
  one_whole : Fraction.Whole (1 : α)

section NumericFraction

/-- Generic fractional instance for types with comparison and 1 operators. -/
class NumericFraction (α : Type _) extends One α, Add α, LE α, LT α where
  add_comm : ∀ a b : α, a + b = b + a
  add_assoc : ∀ a b c : α, a + (b + c) = (a + b) + c
  add_left_cancel : ∀ {a b c : α}, a + b = a + c → b = c
  le_def : ∀ {a b : α}, a ≤ b ↔ a = b ∨ a < b
  lt_def : ∀ {a b : α}, a < b ↔ ∃ c : α, a + c = b
  lt_irrefl : ∀ {a : α}, ¬a < a

@[simp] instance [NumericFraction T] : One (Frac T) := ⟨⟨One.one⟩⟩
@[simp] instance [NumericFraction T] : LE (Frac T) := ⟨(·.1 ≤ ·.1)⟩
@[simp] instance [NumericFraction T] : LT (Frac T) := ⟨(·.1 < ·.1)⟩

variable {α} [NumericFraction α]

open NumericFraction

theorem le_rfl {a : α} : a ≤ a := le_def.2 (.inl rfl)

theorem lt_trans {a b c : α} : a < b → b < c → a < c := by
  simp only [lt_def] at *
  exact fun ⟨ac, hac⟩ ⟨bc, hbc⟩ => ⟨ac + bc, by rwa [← hac, ←add_assoc] at hbc⟩

theorem le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  simp only [le_def] at *
  intro
  | .inl ha_eq_b, .inl hb_eq_c => exact .inl (ha_eq_b.trans hb_eq_c)
  | .inl ha_eq_b, .inr hb_lt_c => exact .inr (ha_eq_b ▸ hb_lt_c)
  | .inr ha_lt_b, .inl hb_eq_c => exact .inr (hb_eq_c ▸ ha_lt_b)
  | .inr ha_lt_b, .inr hb_lt_c => exact .inr (lt_trans ha_lt_b hb_lt_c)

theorem add_le_mono {a b c : α} : a + b ≤ c → a ≤ c := by
  simp only [le_def, lt_def]
  rintro (rfl | ⟨d, hltd⟩)
  · exact .inr ⟨b, rfl⟩
  · exact .inr ⟨b + d, (add_assoc ..).trans hltd⟩

theorem lt_le {a b : α} : a < b → a ≤ b := by simp +contextual [le_def]

theorem add_ne_self {a b : α} : a + b ≠ a := mt (lt_def.2 ⟨b, ·⟩) lt_irrefl

theorem not_add_lt_self {a b : α} : ¬a + b < a := fun H => by
  have ⟨c1, H⟩ := lt_def.1 H
  exact add_ne_self ((add_assoc ..).trans H)

theorem not_add_le_self {a b : α} : ¬ a + b ≤ a := fun H => by
  obtain H | H := le_def.mp H
  · exact add_ne_self H
  · exact not_add_lt_self H

instance : UFraction α where
  Proper x := x ≤ 1
  add_comm := add_comm
  add_assoc := add_assoc
  add_left_cancel := add_left_cancel
  add_ne H := add_ne_self ((add_comm ..).trans H.symm)
  proper_add_mono_left := add_le_mono
  -- whole_iff_one {a} := by
  --   constructor
  --   · intro ⟨Hp, Hdp⟩
  --     refine (le_def.mp Hp).resolve_right fun HK => ?_
  --     let ⟨c, Hc⟩ := lt_def.mp HK
  --     exact Hdp ⟨c, Hc ▸ le_refl⟩
  --   · rintro rfl; exact ⟨le_refl, fun ⟨b, H⟩ => not_add_le_self H⟩
  one_whole := by
    simp [Fraction.Whole, Fraction.Fractional]
    exact ⟨le_rfl, fun _ => not_add_le_self⟩

theorem Frac.inc_iff_lt {p q : Frac α} : p ≼ q ↔ p < q := by
  constructor
  · intro ⟨r, Hr⟩; exact lt_def.mpr ⟨r, Hr ▸ rfl⟩
  · intro H
    let ⟨r, Hr⟩ := lt_def.mp H
    exact ⟨r, .of_eq <| LeibnizO.ext_iff.mpr Hr.symm⟩

theorem Frac.le_of_inc {p q : Frac α} (H : p ≼ q) : p ≤ q :=
  lt_le (inc_iff_lt.mp H)

end NumericFraction
