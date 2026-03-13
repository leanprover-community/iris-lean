import Iris.Algebra.Frac
import Iris.Algebra.Numbers

namespace Iris

open Fraction OFE Add CMRA

/-- Unbounded fractions over the same carrier as `Frac`, but with trivial validity
and no core. This matches Coq's `ufracR`. -/
def UFrac (α : Type _) := LeibnizO α

instance [Add α] : Coe α (UFrac α) := ⟨(⟨·⟩)⟩
@[simp] instance : COFE (UFrac α) := inferInstanceAs (COFE (LeibnizO α))
instance : Leibniz (UFrac α) := inferInstanceAs (Leibniz (LeibnizO α))
instance : OFE.Discrete (UFrac α) := inferInstanceAs (OFE.Discrete (LeibnizO α))
@[simp] instance [Add α] : Add (UFrac α) := ⟨fun x y => x.1 + y.1⟩

instance [Fraction α] : LeftCancelAdd α where
  cancel_left := Fraction.add_left_cancel

instance [Fraction α] : IdentityFree α where
  id_free {a b} h := Fraction.add_ne (a := a) (b := b) <| by
    simpa [Fraction.add_comm] using h.symm

instance UFrac_CMRA [Fraction α] : CMRA (UFrac α) where
  pcore _ := none
  op := Add.add
  ValidN _ _ := True
  Valid _ := True
  op_ne {x} := ⟨fun _ _ _ => congrArg <| Add.add x⟩
  pcore_ne _ := by
    rintro ⟨rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc := OFE.Equiv.of_eq <| by
    simp only [Add.add]
    rw [Fraction.add_assoc]
  comm := OFE.Equiv.of_eq <| by
    simp only [Add.add]
    rw [Fraction.add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  extend _ h := ⟨_, _, OFE.Discrete.discrete h, .rfl, .rfl⟩

instance [Fraction α] : CMRA.Discrete (UFrac α) where
  discrete_valid := id

instance [Fraction α] {a : UFrac α} : CMRA.Cancelable a where
  cancelableN {n x y} _ (H : a • x = a • y) := by
    refine OFE.Dist.of_eq <| LeibnizO.ext <| Fraction.add_left_cancel (a := a.car) ?_
    simpa [CMRA.op, UFrac] using H

instance [Fraction α] {a : UFrac α} : CMRA.IdFree a where
  id_free0_r b _ H := by
    have hba : b + a = a := OFE.Leibniz.eq_of_eqv (α := UFrac α) <| CMRA.comm.trans <| discrete_0 H
    have : b.1 + a.1 = a.1 := congrArg (fun x : UFrac α => x.1) hba
    have hab : a.1 + b.1 = a.1 := by
      simpa [Fraction.add_comm] using this
    exact IdentityFree.id_free (a := a.1) (b := b.1) hab

end Iris
