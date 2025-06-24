/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Frac

open Iris

/-- Knowledge about a discardable fraction. -/
inductive DFracK (F : Type _) where
/-- Ownership of `F` plus knowledge that no fraction has been discarded. -/
| Own (f : F) : DFracK F
/-- Knowledge that a fraction has been discarded. -/
| Discard : DFracK F
/-- Ownership of `F` plus knowledge that a fraction has been discarded. -/
| OwnDiscard (f : F) : DFracK F

abbrev DFrac F := LeibnizO (DFracK F)

-- TODO: Delete this class. I have it now because the Fractional class is being
-- changed concurrently. Also I'm certain that some of these fields will be derivable.
-- class DFractional (F : Type _) extends UFraction F where
  -- one_strict_max {y : F} : ¬(One.one + y ≤ One.one)
  -- lt_irrefl : ¬(One.one < (One.one : F))
  -- strict_pos {x y : F} : ¬(x + y = x)
  -- lt_op_mono {x y z : F} : x + y ≤ z → y < z -- OK because positive

section dfrac

open DFracK

open Fraction

variable {F : Type _} [UFraction F]

instance : Inhabited (DFrac F) := ⟨⟨Discard⟩⟩

abbrev valid : DFrac F → Prop
| ⟨Own f⟩        => Proper f
| ⟨Discard⟩      => True
| ⟨OwnDiscard f⟩ => Fractional f

abbrev pcore : DFrac F → Option (DFrac F)
| ⟨Own _⟩        => none
| ⟨Discard⟩      => some ⟨Discard⟩
| ⟨OwnDiscard _⟩ => some ⟨Discard⟩

abbrev op : DFrac F → DFrac F → DFrac F
| ⟨Own f⟩, ⟨Own f'⟩               => ⟨Own (f + f')⟩
| ⟨Own f⟩, ⟨Discard⟩              => ⟨OwnDiscard f⟩
| ⟨Own f⟩, ⟨OwnDiscard f'⟩        => ⟨OwnDiscard (f + f')⟩
| ⟨Discard⟩, ⟨Own f'⟩             => ⟨OwnDiscard f'⟩
| ⟨Discard⟩, ⟨Discard⟩            => ⟨Discard⟩
| ⟨Discard⟩, ⟨OwnDiscard f'⟩      => ⟨OwnDiscard f'⟩
| ⟨OwnDiscard f⟩, ⟨Own f'⟩        => ⟨OwnDiscard (f + f')⟩
| ⟨OwnDiscard f⟩, ⟨Discard⟩       => ⟨OwnDiscard f⟩
| ⟨OwnDiscard f⟩, ⟨OwnDiscard f'⟩ => ⟨OwnDiscard (f + f')⟩

instance DFrac_CMRA : CMRA (DFrac F) where
  pcore := pcore
  op := op
  Valid := valid
  ValidN _ := valid
  op_ne {x} := ⟨by intro _ f1 f2 H; cases x <;> cases f1 <;> cases f2; exact congrArg (op _) H⟩
  pcore_ne {n x y z} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    rcases z with ⟨z|_|z⟩ <;>
    simp
    all_goals intro H; have H' := LeibnizO.dist_inj H; simp at H'
  validN_ne {_ x y} H := by cases x <;> cases y; exact (H ▸ id)
  valid_iff_validN := ⟨fun x _ => x, fun x => x 0⟩
  validN_succ := id
  validN_op_left {_ x y} := by
    have Lleft {a' a : F} (H : Fractional (a' + a)) : Fractional a := by
      rcases H with ⟨b, Hb⟩
      exists (a' + b)
      suffices (a' + a + b) = (a + (a' + b)) by rw [←this]; exact Hb
      refine .trans ?_ Fraction.add_assoc.symm
      congr 1
      apply Fraction.add_comm
    rcases x with ⟨x|_|x⟩ <;> rcases y with ⟨y|_|y⟩ <;> simp [valid]
    · apply proper_add_mono_left
    · apply fractional_proper
    · exact fractional_proper ∘ Fractional_add_left
    · apply Fractional_add_left
    · apply Fractional_add_left
  assoc {x y z} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    rcases z with ⟨z|_|z⟩ <;>
    simp [op, Fraction.add_assoc]
  comm {x y} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    simp [op, Fraction.add_comm]
  pcore_op_left {x y} := by rcases x with ⟨x|_|x⟩ <;> rcases y with ⟨y|_|y⟩ <;> simp
  pcore_idem {x y} := by rcases x with ⟨x|_|x⟩ <;> rcases y with ⟨y|_|y⟩ <;> simp
  pcore_op_mono {x y} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    simp <;>
    intro z <;>
    exists ⟨Discard⟩ <;>
    rcases z with ⟨z|_|z⟩ <;>
    simp [op]
  extend {_ x y z} Hx Hxyz := by
    rcases x with ⟨x|_|x⟩
    · rcases y with ⟨y|_|y⟩ <;> rcases z with ⟨z|_|z⟩ <;> simp [op] at Hxyz
      all_goals have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz'
      exists ⟨Own y⟩
      exists ⟨Own z⟩
    · rcases y with ⟨y|_|y⟩ <;> rcases z with ⟨z|_|z⟩ <;> simp [op] at Hxyz
      all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
      exists ⟨Discard⟩
      exists ⟨Discard⟩
    · rcases y with ⟨y|_|y⟩ <;> rcases z with ⟨z|_|z⟩ <;> simp [op] at Hxyz
      all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
      all_goals subst Hxyz'
      · exists ⟨Own x⟩; exists ⟨Discard⟩
      · exists ⟨Own y⟩; exists ⟨OwnDiscard z⟩
      · exists ⟨Discard⟩; exists ⟨Own x⟩
      · exists ⟨Discard⟩; exists ⟨OwnDiscard x⟩
      · exists ⟨OwnDiscard y⟩; exists ⟨Own z⟩
      · exists ⟨OwnDiscard x⟩; exists ⟨Discard⟩
      · exists ⟨OwnDiscard y⟩; exists ⟨OwnDiscard z⟩

theorem own_whole_exclusive {w : F} (Hw : Whole w) : CMRA.Exclusive (α := DFrac F) ⟨Own w⟩ where
  exclusive0_l y := by
    rcases y with ⟨y|_|y⟩ <;>
    simp only [CMRA.ValidN, valid]
    · suffices ¬(Fractional w) by
        intro Hp
        unfold Fractional at this
        apply this ⟨y, Hp⟩
      apply Proper.whole_not_fractional Hw
    · apply Proper.whole_not_fractional Hw
    · suffices ¬(Fractional w) by
        intro Hk; apply this
        exact Fractional_add_left Hk
      apply Proper.whole_not_fractional Hw

instance : CMRA.Exclusive (α := DFrac F) ⟨Own (1 : F)⟩ :=
  own_whole_exclusive <| UFraction.one_whole

instance {f : F} : CMRA.Cancelable (α := DFrac F) ⟨Own f⟩ where
  cancelableN {_ x y} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    simp [CMRA.ValidN, CMRA.op, op]
    all_goals intro H Hxyz
    all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
    · exact congrArg (LeibnizO.mk ∘ Own) <| Fraction.add_left_cancel Hxyz'
    · exact (Fraction.add_ne (Fraction.add_comm (α := F) ▸ Hxyz')).elim
    · exact (Fraction.add_ne (Fraction.add_comm (α := F) ▸ Hxyz').symm).elim
    · exact congrArg (LeibnizO.mk ∘ OwnDiscard) <| Fraction.add_left_cancel Hxyz'

instance {f : F} : CMRA.IdFree (α := DFrac F) ⟨Own f⟩ where
  id_free0_r y := by
    rcases y with ⟨y|_|y⟩ <;> simp [CMRA.ValidN, CMRA.op, op] <;> intro H Hxyz
    all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
    exact (Fraction.add_ne (Fraction.add_comm (α := F) ▸ Hxyz').symm).elim

theorem valid_own_one : ✓ (LeibnizO.mk (Own (One.one : F))) := UFraction.one_whole.1

theorem valid_op_own_r {dq : DFrac F} {q : F} : ✓ (dq • ⟨Own q⟩) → Fractional q := by
  rcases dq with ⟨y|_|y⟩
  · exact (⟨y, Fraction.add_comm (α := F)▸·⟩)
  · exact id
  · exact Fractional_add_right

theorem valid_op_own_l {dq : DFrac F} {q : F} : ✓ (⟨Own q⟩ • dq) → (Fractional q) :=
  valid_op_own_r ∘ CMRA.valid_of_eqv (CMRA.comm (y := dq))

theorem valid_discarded : ✓ (LeibnizO.mk Discard : DFrac F) := by simp [CMRA.Valid, valid]

theorem valid_own_op_discarded {q : F} : ✓ (⟨Own q⟩ • ⟨Discard⟩ : DFrac F) ↔ (Fractional q) := by
  simp [CMRA.op, op, CMRA.Valid, valid]

instance : CMRA.Discrete (DFrac F) where
  discrete_valid {x} := by simp [CMRA.Valid, CMRA.ValidN]

end dfrac
