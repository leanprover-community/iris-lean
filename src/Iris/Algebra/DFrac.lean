/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Mario Carneiro
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Frac
import Iris.Algebra.Updates
import Iris.Algebra.LocalUpdates

namespace Iris

/-- Knowledge about a discardable fraction. -/
inductive DFrac (F : Type _) where
/-- Ownership of `F` plus knowledge that no fraction has been discarded. -/
| own (f : F) : DFrac F
/-- Knowledge that a fraction has been discarded. -/
| discard : DFrac F
/-- Ownership of `F` plus knowledge that a fraction has been discarded. -/
| ownDiscard (f : F) : DFrac F

@[simp] instance : COFE (DFrac F) := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Leibniz (DFrac F) := ⟨(·)⟩
instance : OFE.Discrete (DFrac F) := ⟨congrArg id⟩

section dfrac

open DFrac Fraction OFE.Discrete

variable [UFraction F]

instance : Inhabited (DFrac F) := ⟨discard⟩

def valid : DFrac F → Prop
  | .own f        => Proper f
  | .discard      => True
  | .ownDiscard f => Fractional f

def pcore : DFrac F → Option (DFrac F)
  | own _        => none
  | .discard     => some discard
  | ownDiscard _ => some discard

def op : DFrac F → DFrac F → DFrac F
  | .discard, .discard => discard
  | own f, .discard
  | ownDiscard f, .discard
  | .discard, own f
  | .discard, ownDiscard f => ownDiscard f
  | own f, own f' => own (f + f')
  | own f, ownDiscard f'
  | ownDiscard f, own f'
  | ownDiscard f, ownDiscard f' => ownDiscard (f + f')

instance DFrac_CMRA : CMRA (DFrac F) where
  pcore := pcore
  op := op
  Valid := valid
  ValidN _ := valid
  op_ne := { ne _ _ _ := congrArg (op _) }
  pcore_ne {_} := by rintro ⟨⟩ ⟨⟩ <;> simp [pcore] <;> nofun
  validN_ne H := H ▸ id
  valid_iff_validN := ⟨fun x _ => x, fun x => x 0⟩
  validN_succ := id
  validN_op_left {_} := by
    rintro ⟨⟩ ⟨⟩ <;> simp [valid, op]
    · exact proper_add_mono_left
    · exact Fractional.proper
    · exact Fractional.proper ∘ Fractional.of_add_left
    · exact Fractional.of_add_left
    · exact Fractional.of_add_left
  assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp [op, Fraction.add_assoc]
  comm := by rintro ⟨⟩ ⟨⟩ <;> simp [op, Fraction.add_comm]
  pcore_op_left := by rintro ⟨⟩ ⟨⟩ <;> simp [op, pcore]
  pcore_idem := by rintro ⟨⟩ ⟨⟩ <;> simp [pcore]
  pcore_op_mono := by
    rintro ⟨⟩ ⟨⟩ <;> simp [pcore] <;>
    · intro z
      exists discard
      rcases z with z|_|z <;> simp [op]
  extend {_} := by -- x y z} Hx Hxyz := by
    rintro (x|_|x)
    · rintro (y|_|y) (z|_|z) Hx Hxyz <;> simp [op] at Hxyz
      all_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
      exists own y, own z
    · rintro (y|_|y) (z|_|z) Hx Hxyz <;> simp [op] at Hxyz
      any_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
      exists discard, discard
    · rintro (y|_|y) (z|_|z) Hx Hxyz <;> simp [op] at Hxyz
      any_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
      all_goals subst Hxyz'
      · exists own x, discard
      · exists own y, ownDiscard z
      · exists discard, own x
      · exists discard, ownDiscard x
      · exists ownDiscard y, own z
      · exists ownDiscard x, discard
      · exists ownDiscard y, ownDiscard z

theorem own_whole_exclusive {w : F} (Hw : Whole w) : CMRA.Exclusive (own w) where
  exclusive0_l := by
    rintro (y|_|y) <;> simp only [CMRA.ValidN, valid, CMRA.op, op]
    · exact fun Hp => Hw.not_fractional ⟨y, Hp⟩
    · exact Hw.not_fractional
    · exact fun Hk => Hw.not_fractional Hk.of_add_left

instance : CMRA.Exclusive (own (1 : F)) :=
  own_whole_exclusive <| UFraction.one_whole

instance {f : F} : CMRA.Cancelable (own f) where
  cancelableN {_} := by
    rintro ⟨⟩ ⟨⟩ <;> simp [CMRA.ValidN, CMRA.op, op] <;> intro H Hxyz
    any_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
    · exact congrArg own <| add_left_cancel Hxyz'
    · cases add_ne (Hxyz'.trans (add_comm ..))
    · cases add_ne ((add_comm ..).trans Hxyz').symm
    · exact congrArg ownDiscard <| add_left_cancel Hxyz'

instance {f : F} : CMRA.IdFree (own f) where
  id_free0_r := by
    rintro (y|_|y) <;> simp [CMRA.ValidN, CMRA.op, op] <;> intro H Hxyz
    any_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
    exact (add_ne ((add_comm ..).trans Hxyz').symm).elim

theorem valid_own_one : ✓ own (One.one : F) := UFraction.one_whole.1

theorem valid_op_own {dq : DFrac F} {q : F} : ✓ dq • own q → Fractional q := by
  obtain y|_|y := dq
  · exact (⟨y, add_comm (α := F) .. ▸ ·⟩)
  · exact id
  · exact Fractional.of_add_right

theorem valid_own_op {dq : DFrac F} {q : F} : ✓ own q • dq → Fractional q :=
  valid_op_own ∘ CMRA.valid_of_eqv (CMRA.comm (y := dq))

theorem valid_discard : ✓ (discard : DFrac F) := by simp [CMRA.Valid, valid]

theorem valid_own_op_discard {q : F} : ✓ own q • discard ↔ Fractional q := by
  simp [CMRA.op, op, CMRA.Valid, valid]

instance : CMRA.Discrete (DFrac F) where
  discrete_valid {x} := by simp [CMRA.Valid, CMRA.ValidN]

theorem DFrac.is_discrete {q : DFrac F} : OFE.DiscreteE q := ⟨congrArg id⟩

instance : CMRA.Discrete (DFrac F) where
  discrete_valid {x} := by simp [CMRA.Valid, CMRA.ValidN]

instance : CMRA.Discrete (DFrac F) where
  discrete_valid {x} := by simp [CMRA.Valid, CMRA.ValidN]

theorem DFrac.update_discard {dq : DFrac F} : dq ~~> .discard := by
  intros n q H
  apply (CMRA.valid_iff_validN' n).mp
  have H' := (CMRA.valid_iff_validN' n).mpr H
  simp [CMRA.op?] at H' ⊢
  rcases q with (_|⟨q|_|q⟩) <;> simp [CMRA.Valid, valid, CMRA.op, op]
  · cases dq <;> first | exact valid_op_own H | exact H
  · cases dq <;> first | exact Fractional.of_add_right H | exact H

theorem DFrac.update_acquire [IsSplitFraction F] :
    (.discard : DFrac F) ~~>: fun k => ∃ q, k = .own q := by
  apply UpdateP.discrete.mpr
  rintro (_|q)
  · rintro _
    refine ⟨.own One.one, ⟨⟨One.one, rfl⟩, ?_⟩⟩
    simp [CMRA.Valid]
    apply UFraction.one_whole.1
  rcases q with (q|_|q)
  · rintro ⟨q', HP⟩
    refine ⟨(.own q'), ⟨⟨q', rfl⟩, ?_⟩⟩
    simp [CMRA.op?, CMRA.op, op]
    rw [add_comm]
    exact HP
  · intro _
    let q' : F := (IsSplitFraction.split One.one).1
    refine ⟨.own q', ⟨⟨q', rfl⟩, ?_⟩⟩
    simp [CMRA.op?, CMRA.op, op]
    refine ⟨(IsSplitFraction.split One.one).2, ?_⟩
    rw [IsSplitFraction.split_add]
    apply UFraction.one_whole.1
  · rintro ⟨q', HP⟩
    let q'' : F := (IsSplitFraction.split q').1
    refine ⟨(.own q''), ⟨⟨q'', rfl⟩, ?_⟩⟩
    simp only [CMRA.op?, CMRA.op, op, add_comm]
    refine ⟨(IsSplitFraction.split q').2, ?_⟩
    rw [← add_assoc, IsSplitFraction.split_add]
    exact HP

end dfrac
