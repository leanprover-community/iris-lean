/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqPorting

/-! ## Numbers CMRA
Simple CMRA's for commutative monoids.

There are three variants:
- "Constant core": the core is a fixed value such as 0 (eg. (ℕ, +))
- "Universal core": every element is a core (eg. (ℕ, max))
- "No core": there is no core (eg. (PNat, +))
-/

@[expose] public section

open Std

class IdentityFree (α : Type _) [Add α] where
  id_free {a b : α} : ¬ Add.add a b = a

class LeftCancelAdd (α : Type _) [Add α] where
  cancel_left {x₁ x₂ y : α} : y + x₁ = y + x₂ → x₁ = x₂

open Add Commutative in
theorem LeftCancelAdd.cancel_right {x₁ x₂ y : α} [Add α] [LeftCancelAdd α]
    [Commutative (add (α := α))] (h : add x₁ y = add x₂ y) : x₁ = x₂ := by
  refine cancel_left (y := y) ?_
  rw [← add_eq_hAdd, comm (op := Add.add) y x₁, h, comm (op := Add.add)]

/- Constant core -/
namespace CommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA

variable [OFE α] [Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [Zero α] [LawfulLeftIdentity (add (α := α)) zero]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := some zero
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [(discrete h).to_eq]
  pcore_ne _ := dist_some ∘ Dist.of_eq
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; rw [left_id (op := add) _]
  pcore_idem := by simp
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ _
    exists zero
    rw [left_id (op := add) _]
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩
#rocq_ignore natR "Use Nat with scoped CMRA instance"
#rocq_ignore ZR "Use Int with scoped CMRA instance"
#rocq_ignore nat_ra_mixin "Not needed"
#rocq_ignore Z_ra_mixin "Not needed"
#rocq_ignore nat_op_instance "Use CMRA instance"
#rocq_ignore nat_pcore_instance "Use CMRA instance"
#rocq_ignore nat_valid_instance "Use CMRA instance"
#rocq_ignore nat_validN_instance "Use CMRA instance"
#rocq_ignore Z_op_instance "Use CMRA instance"
#rocq_ignore Z_pcore_instance "Use CMRA instance"
#rocq_ignore Z_valid_instance "Use CMRA instance"
#rocq_ignore Z_validN_instance "Use CMRA instance"

scoped instance : CMRA.Discrete α where
  discrete_valid := id
#rocq_ignore nat_cmra_discrete "Use scoped Discrete instance"
#rocq_ignore Z_cmra_discrete "Use scoped Discrete instance"

scoped instance : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := pcore_op_left rfl
  pcore_unit := .symm .rfl

#rocq_ignore natUR "Use Nat with scoped UCMRA instance"
#rocq_ignore ZUR "Use Int with scoped UCMRA instance"
#rocq_ignore nat_ucmra_mixin "Not needed"
#rocq_ignore Z_ucmra_mixin "Not needed"
#rocq_ignore nat_unit_instance "Use UCMRA instance"
#rocq_ignore Z_unit_instance "Use UCMRA instance"

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete
#rocq_ignore nat_cancelable "Use scoped Cancelable instance"
#rocq_ignore Z_cancelable "Use scoped Cancelable instance"

/-- The CMRA operation is `add`. -/
@[rocq_alias nat_op, rocq_alias Z_op]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := by
  refine ⟨fun ⟨z, hz⟩ => ⟨z, leibniz.mp hz⟩, fun ⟨z, hz⟩ => ⟨z, .of_eq hz⟩⟩

/-- Sufficient condition for a local update on a LeftCancelAdd structure, such as (ℕ, +) -/
theorem leftCancelAdd_local_update [LeftCancelAdd α] (h : add x y' = add x' y) :
    (x, y) ~l~> (x', y') := by
  refine leibniz_discrete_unital_triv_local_update (fun _ => trivial) @fun z hz => ?_
  refine LeftCancelAdd.cancel_right (y := y) ?_
  calc
    add x' y = add x y' := h.symm
    _ = add (add y z) y' := by rw [hz]; rfl
    _ = add y' (add y z) := by rw [comm (op := add)]
    _ = add y' (add z y) := by rw [comm (op := add) z]
    _ = add (add y' z) y := by rw [assoc (op := add)]

scoped instance {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

scoped instance : CoreId (α := α) 0 where
  core_id := by rfl

end CommMonoidLike

/- Universal core -/
namespace OrdCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [OFE.Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [IdempotentOp (add (α := α))]
variable [Zero α]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore := some
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [(discrete h).to_eq]
  pcore_ne {_ y _ _} h := by
    rintro ⟨rfl⟩
    exact ⟨y, congrArg _ <| leibniz.mp (discrete h.symm), .rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by
    rintro ⟨rfl⟩
    refine .of_eq <| idempotent _
  pcore_idem := by simp
  pcore_op_mono {a b} := by
    rintro ⟨rfl⟩ z
    exists z
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

#rocq_ignore max_nat "Use Nat with IdempotentOp max"
#rocq_ignore min_nat "Uses Nat with IdempotentOp min"
#rocq_ignore max_Z "Uses Int with IdempotentOp max"
#rocq_ignore max_natO "Use LeibnizO Nat"
#rocq_ignore max_ZO "Use LeibnizO Int"
#rocq_ignore min_natO "Use LeibnizO Nat"
#rocq_ignore max_natR "Use Nat with scoped CMRA instance"
#rocq_ignore max_ZR "Use Int with scoped CMRA instance"
#rocq_ignore min_natR "Use Nat with scoped CMRA instance"
#rocq_ignore max_nat_ra_mixin "Not needed"
#rocq_ignore max_Z_ra_mixin "Not needed"
#rocq_ignore min_nat_ra_mixin "Not needed"
#rocq_ignore max_nat_op_instance "Use CMRA instance"
#rocq_ignore max_nat_pcore_instance "Use CMRA instance"
#rocq_ignore max_nat_valid_instance "Use CMRA instance"
#rocq_ignore max_nat_validN_instance "Use CMRA instance"
#rocq_ignore max_Z_op_instance "Use CMRA instance"
#rocq_ignore max_Z_pcore_instance "Use CMRA instance"
#rocq_ignore max_Z_valid_instance "Use CMRA instance"
#rocq_ignore max_Z_validN_instance "Use CMRA instance"
#rocq_ignore min_nat_op_instance "Use CMRA instance"
#rocq_ignore min_nat_pcore_instance "Use CMRA instance"
#rocq_ignore min_nat_valid_instance "Use CMRA instance"
#rocq_ignore min_nat_validN_instance "Use CMRA instance"

scoped instance : CMRA.Discrete α where
  discrete_valid := id
#rocq_ignore max_nat_cmra_discrete "Use scoped Discrete instance"
#rocq_ignore max_Z_cmra_discrete "Use scoped Discrete instance"
#rocq_ignore min_nat_cmra_discrete "Use scoped Discrete instance"

scoped instance (a : α) : CMRA.CoreId a where
  core_id := by simp [pcore]
#rocq_ignore max_nat_core_id "Use scoped CoreId instance"
#rocq_ignore max_Z_core_id "Use scoped CoreId instance"
#rocq_ignore min_nat_core_id "Use scoped CoreId instance"

scoped instance [LawfulLeftIdentity (add (α := α)) zero] : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := .of_eq <| left_id _
  pcore_unit := .symm .rfl
#rocq_ignore max_natUR "Use Nat with scoped UCMRA instance"
#rocq_ignore max_nat_ucmra_mixin "Not needed"
#rocq_ignore max_nat_unit_instance "Use UCMRA instance"
#rocq_ignore max_Z_unit_instance "Use UCMRA instance"

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

omit [Zero α] in
/-- The CMRA operation is `add` (which is `max`/`min` for max_nat/min_nat/max_Z). -/
@[rocq_alias max_nat_op, rocq_alias max_Z_op, rocq_alias min_nat_op_min]
theorem op_eq {x y : α} : x • y = x + y := rfl

scoped instance {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

end OrdCommMonoidLike

/- NoCore core -/
namespace PosCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [OFE.Discrete α] [Leibniz α]
variable [Add α] [Associative (add (α := α))] [Commutative (add (α := α))]
variable [IdempotentOp (add (α := α))]

variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := none
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [(discrete h).to_eq]
  pcore_ne _ := by rintro ⟨rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by rintro ⟨rfl⟩
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩
#rocq_ignore positiveR "Use PNat with scoped CMRA instance"
#rocq_ignore pos_ra_mixin "Not needed"
#rocq_ignore pos_op_instance "Use CMRA instance"
#rocq_ignore pos_pcore_instance "Use CMRA instance"
#rocq_ignore pos_valid_instance "Use CMRA instance"
#rocq_ignore pos_validN_instance "Use CMRA instance"

scoped instance : CMRA.Discrete α where
  discrete_valid := id
#rocq_ignore pos_cmra_discrete "Use Discrete instance"

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete
#rocq_ignore pos_cancelable "Use scoped Cancelable instance"

scoped instance [IdentityFree α] {a : α} : CMRA.IdFree a where
  id_free0_r _ _ h := IdentityFree.id_free (α := α) <| leibniz.mp (discrete h)
#rocq_ignore pos_id_free "Use scoped IdentityFree instance"

#rocq_ignore pos_op_add "Not needed"

end PosCommMonoidLike
