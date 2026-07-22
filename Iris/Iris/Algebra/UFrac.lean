/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.Frac
public import Iris.Algebra.IsOp
meta import Iris.Std.RocqPorting

/-!
# The UFrac CMRA

A variant of the Frac CMRA with unbounded validity (>1).
-/

@[expose] public section

namespace Iris

@[rocq_alias ufrac]
structure UFrac where
  frac : Qp

#rocq_ignore ufracO "Use UFrac type with typeclass inference"

namespace UFrac

@[simp] theorem ext_iff {x y : UFrac} : x = y ↔ x.frac = y.frac := by
  cases x; cases y; simp

#rocq_ignore ufrac_op_instance "Use CMRA instance"
#rocq_ignore ufrac_pcore_instance "Use CMRA instance"
#rocq_ignore ufrac_valid_instance "Use CMRA instance"

@[simp] instance : COFE UFrac := COFE.ofDiscrete _
instance : OFE.Discrete UFrac := ⟨fun h => h⟩

@[simp] theorem dist_iff {n} {x y : UFrac} : x ≡{n}≡ y ↔ x = y := Iff.rfl
@[simp] theorem equiv_iff {x y : UFrac} : x ≡ y ↔ x = y := ⟨OFE.Equiv.to_eq, OFE.Equiv.of_eq⟩

@[rocq_alias ufracR]
instance : CMRA UFrac where
  pcore _ := none
  op x y := ⟨x.frac + y.frac⟩
  Valid _ := True
  ValidN _ _ := True
  op_ne.ne _ _ _ H := by rw [H]
  pcore_ne _ H := by rcases H
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => trivial, fun _ => trivial⟩
  validN_succ := id
  validN_op_left _ := trivial
  assoc := OFE.Equiv.of_eq <| ext_iff.mpr <| Subtype.ext (Rat.add_assoc ..).symm
  comm := OFE.Equiv.of_eq <| ext_iff.mpr <| Subtype.ext (Rat.add_comm ..)
  pcore_op_left H := by rcases H
  pcore_idem H := by rcases H
  pcore_op_mono H := by rcases H
  extend {_ x y z} := by rintro _ rfl; exists y; exists z

@[simp, grind =] theorem frac_op (x y : UFrac) : (x • y).frac = x.frac + y.frac := rfl
@[simp, grind =] theorem valid_iff {x : UFrac} : ✓ x ↔ True := Iff.rfl
@[simp, grind =] theorem validN_iff {n} {x : UFrac} : ✓{n} x ↔ True := Iff.rfl

@[rocq_alias ufrac_op]
theorem op_eq (p q : UFrac) : p • q = ⟨p.frac + q.frac⟩ := rfl

@[rocq_alias ufrac_included]
theorem inc_iff {x y : UFrac} : x ≼ y ↔ x.frac < y.frac := by
  refine ⟨fun ⟨r, Hr⟩ => ?_, fun H => ?_⟩
  · have := r.frac.2; simp only [equiv_iff, ext_iff, frac_op] at Hr; grind
  · refine ⟨⟨⟨y.frac.val - x.frac.val, by grind⟩⟩, ?_⟩
    simp only [equiv_iff, ext_iff, frac_op]; grind

@[rocq_alias ufrac_included_weak]
theorem le_of_inc {x y : UFrac} (H : x ≼ y) : x.frac ≤ y.frac := by
  have := inc_iff.mp H; grind

@[rocq_alias ufrac_cmra_discrete]
instance : CMRA.Discrete UFrac where
  discrete_0 := fun h => h
  discrete_valid := id

@[rocq_alias ufrac_cancelable]
instance {q : UFrac} : CMRA.Cancelable q where
  cancelableN {n x y} _ (H : q • x = q • y) := by
    simp only [dist_iff, ext_iff, frac_op] at *; grind

@[rocq_alias ufrac_id_free]
instance {q : UFrac} : CMRA.IdFree q where
  id_free0_r b _ H := by
    have := b.frac.2; simp only [dist_iff, ext_iff, frac_op] at H; grind

set_option synthInstance.checkSynthOrder false in
@[rocq_alias is_op_ufrac]
instance (q : UFrac) : IsOp io1 q io2 ⟨q.frac.half⟩ io3 ⟨q.frac.half⟩ where
  is_op := OFE.Equiv.of_eq <| ext_iff.mpr (Qp.half_add_half q.frac).symm

end UFrac
