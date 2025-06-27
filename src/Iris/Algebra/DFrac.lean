/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Frac

open Iris

inductive DFracK (F : Type _) where
| Own : F → DFracK F
| Discard : DFracK F
| OwnDiscard : F → DFracK F

abbrev DFrac F := LeibnizO (DFracK F)

-- TODO: Delete this class. I have it now because the Fractional class is being
-- changed concurrently. Also I'm certain that some of these fields will be derivable.
class DFractional (F : Type _) extends Fractional F where
  -- one_strict_max {y : F} : ¬(One.one + y ≤ One.one)
  -- lt_irrefl : ¬(One.one < (One.one : F))
  -- strict_pos {x y : F} : ¬(x + y = x)
  -- lt_op_mono {x y z : F} : x + y ≤ z → y < z -- OK because positive

section dfrac

open DFracK

variable {F : Type _} [DFractional F]

instance : Inhabited (DFrac F) := ⟨⟨Discard⟩⟩

abbrev valid : DFrac F → Prop
| ⟨Own f⟩        => Fractional.proper f -- f ≤ One.one
| ⟨Discard⟩      => True
| ⟨OwnDiscard f⟩ => sorry -- Iris.fraction -- f < One.one

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
    sorry
    /-
    have Lleft {a' a : F} (H : a' + a < one) : a' < one := by
      rcases Fractional.lt_sum.mp H with ⟨r, Hr⟩
      exact (Fractional.lt_sum.mpr ⟨a + r, Hr.symm ▸ Fractional.assoc.symm⟩)
    rcases x with ⟨x|_|x⟩ <;> rcases y with ⟨y|_|y⟩ <;> simp
    · exact Fractional.add_le_mono
    · exact Fractional.lt_le
    · exact (Fractional.add_le_mono <| Fractional.lt_le ·)
    · exact Lleft
    · exact Lleft
    -/
  assoc {x y z} := by
    sorry
    /-
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    rcases z with ⟨z|_|z⟩ <;>
    simp [op, Fractional.assoc]
    -/
  comm {x y} := sorry -- by rcases x with ⟨x|_|x⟩ <;> rcases y with ⟨y|_|y⟩ <;> simp [op, Fractional.comm]
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

instance : CMRA.Exclusive (α := DFrac F) ⟨Own One.one⟩ where
  exclusive0_l y := by
    rcases y with ⟨y|_|y⟩ <;>
    simp only [CMRA.ValidN, valid]
    · sorry -- exact DFractional.one_strict_max
    · sorry -- exact DFractional.lt_irrefl
    · sorry -- exact DFractional.one_strict_max ∘ Fractional.lt_le

instance {f : F} : CMRA.Cancelable (α := DFrac F) ⟨Own f⟩ where
  cancelableN {_ x y} := by
    rcases x with ⟨x|_|x⟩ <;>
    rcases y with ⟨y|_|y⟩ <;>
    simp [CMRA.ValidN, CMRA.op, op]
    all_goals intro H Hxyz
    all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
    · sorry -- exact congrArg (LeibnizO.mk ∘ Own) (Fractional.cancel Hxyz')
    · sorry -- exact (DFractional.strict_pos (F := F) Hxyz'.symm).elim
    · sorry -- exact (DFractional.strict_pos (F := F) Hxyz').elim
    · sorry -- exact congrArg (LeibnizO.mk ∘ OwnDiscard) (Fractional.cancel Hxyz')

instance {f : F} : CMRA.IdFree (α := DFrac F) ⟨Own f⟩ where
  id_free0_r y := by
    rcases y with ⟨y|_|y⟩ <;> simp [CMRA.ValidN, CMRA.op, op] <;> intro H Hxyz
    all_goals (try have Hxyz' := LeibnizO.dist_inj Hxyz <;> simp at Hxyz')
    sorry -- exact (DFractional.strict_pos (F := F) Hxyz').elim

-- theorem valid_own_iff {f : F} : ✓ (LeibnizO.mk (Own f)) ↔ f ≤ One.one := by simp [CMRA.Valid]
-- theorem valid_own_one : ✓ (LeibnizO.mk (Own (One.one : F))) := valid_own_iff.mpr Fractional.le_refl

-- theorem valid_op_own_r {dq : DFrac F} {q : F} : ✓ (dq • ⟨Own q⟩) → (q < One.one) := by
--   rcases dq with ⟨y|_|y⟩ <;> simp [CMRA.ValidN, CMRA.op, op, CMRA.Valid]
--   · exact DFractional.lt_op_mono
--   · exact DFractional.lt_op_mono ∘ Fractional.lt_le

-- theorem valid_op_own_l {dq : DFrac F} {q : F} : ✓ (⟨Own q⟩ • dq) → (q < One.one) :=
--   valid_op_own_r ∘ CMRA.valid_of_eqv (CMRA.comm (y := dq))

theorem valid_discarded : ✓ (LeibnizO.mk Discard : DFrac F) := by simp [CMRA.Valid, valid]

-- theorem valid_own_op_discarded {q : F} : ✓ (⟨Own q⟩ • ⟨Discard⟩ : DFrac F) ↔ q < One.one := by
--   simp [CMRA.op, op, CMRA.Valid, valid]

end dfrac
