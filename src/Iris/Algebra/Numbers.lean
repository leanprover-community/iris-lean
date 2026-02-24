/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.LocalUpdates

/-! ## Numbers CMRA
Simple CMRA's for commutative monoids.

There are three variants:
- "Constant core": the core is a fixed value such as 0 (eg. (ℕ, +))
- "Universal core": every element is a core (eg. (ℕ, max))
- "No core": there is no core (eg. (PNat, +))
-/

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
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
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

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := pcore_op_left rfl
  pcore_unit := .symm .rfl

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

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
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
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

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance (a : α) : CMRA.CoreId a where
  core_id := by simp [pcore]

scoped instance [LawfulLeftIdentity (add (α := α)) zero] : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := .of_eq <| left_id _
  pcore_unit := .symm .rfl

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

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
  op_ne.ne _ _ _ h := by rw [eq_of_eqv (discrete h)]
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

scoped instance : CMRA.Discrete α where
  discrete_valid := id

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ eq_of_eqv ∘ discrete

scoped instance [IdentityFree α] {a : α} : CMRA.IdFree a where
  id_free0_r _ _ h := IdentityFree.id_free (α := α) <| leibniz.mp (discrete h)

end PosCommMonoidLike
