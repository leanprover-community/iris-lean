/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
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

variable [OFE α] [Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := some zero
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [discrete h]
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
  pcore_unit := rfl

#rocq_ignore natUR "Use Nat with scoped UCMRA instance"
#rocq_ignore ZUR "Use Int with scoped UCMRA instance"
#rocq_ignore nat_ucmra_mixin "Not needed"
#rocq_ignore Z_ucmra_mixin "Not needed"
#rocq_ignore nat_unit_instance "Use UCMRA instance"
#rocq_ignore Z_unit_instance "Use UCMRA instance"

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
#rocq_ignore nat_cancelable "Use scoped Cancelable instance"
#rocq_ignore Z_cancelable "Use scoped Cancelable instance"

/-- The CMRA operation is `add`. -/
@[rocq_alias nat_op, rocq_alias Z_op]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := by
  refine ⟨fun ⟨z, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz⟩⟩

/-- Sufficient condition for a local update on a LeftCancelAdd structure, such as (ℕ, +) -/
theorem leftCancelAdd_local_update [LeftCancelAdd α] (h : add x y' = add x' y) :
    (x, y) ~l~> (x', y') := by
  refine discrete_unital_triv_local_update (fun _ => trivial) @fun z hz => ?_
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

variable [OFE α] [OFE.Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [IdempotentOp (α := α) (· + ·)]
variable [Zero α]
variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore := some
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [discrete h]
  pcore_ne {_ y _ _} h := by
    rintro ⟨rfl⟩
    exact ⟨y, congrArg _ <| discrete h.symm, .rfl⟩
  validN_ne _ _ := .intro
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left := id
  assoc {_ _ _} := by rw [assoc (op := add)]
  comm {_ _} := by rw [comm (op := add)]
  pcore_op_left {_ _} := by
    rintro ⟨rfl⟩
    exact idempotent _
  pcore_idem := by simp
  pcore_op_mono {a b} := by
    rintro ⟨rfl⟩ z
    exists z
  extend _ h := ⟨_, _, discrete h, .rfl, .rfl⟩

#rocq_ignore max_natO "Use scoped COFE instance"
#rocq_ignore max_ZO "Use scoped COFE instance"
#rocq_ignore min_natO "Use scoped COFE instance"
#rocq_ignore max_natR "Use Nat with scoped CMRA instance"
#rocq_ignore max_ZR "Use Int with scoped CMRA instance"
#rocq_ignore min_natR "Use scoped CMRA instance"
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

scoped instance : CMRA.IsTotal α where
  total x := ⟨x, rfl⟩
#rocq_ignore max_Z_cmra_total "Use scoped IsTotal instance"

scoped instance (a : α) : CMRA.CoreId a where
  core_id := by simp [pcore]
#rocq_ignore max_nat_core_id "Use scoped CoreId instance"
#rocq_ignore max_Z_core_id "Use scoped CoreId instance"
#rocq_ignore min_nat_core_id "Use scoped CoreId instance"

scoped instance [LawfulLeftIdentity (α := α) (· + ·) zero] : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := left_id _
  pcore_unit := rfl
#rocq_ignore max_natUR "Use Nat with scoped UCMRA instance"
#rocq_ignore max_nat_ucmra_mixin "Not needed"
#rocq_ignore max_nat_unit_instance "Use UCMRA instance"

scoped instance [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete

omit [Zero α] in
/-- The CMRA operation is `add` (which is `max`/`min` for max_nat/min_nat/max_Z). -/
@[simp, grind =, rocq_alias max_nat_op, rocq_alias max_Z_op, rocq_alias min_nat_op_min]
theorem op_eq {x y : α} : x • y = x + y := rfl

omit [Zero α] in
/-- Every element is its own core, so inclusion is absorption. Specialize this to get the
`≤`-phrased inclusion lemmas for `MaxNat`/`MaxZ`. -/
theorem inc_iff {x y : α} : x ≼ y ↔ x • y = y :=
  ⟨CMRA.op_core_right_of_inc, fun h => ⟨y, h.symm⟩⟩

omit [Zero α] in
/-- Sufficient condition for a local update on an idempotent structure, such as (ℕ, max). -/
theorem idem_local_update {x y x' : α} (h : x ≼ x') : (x, y) ~l~> (x', x') := by
  refine fun _ mz _ hn => ⟨trivial, OFE.Dist.of_eq ?_⟩
  cases mz with | none => rfl | some z =>
  replace hn : x = y • z := discrete hn
  exact (CMRA.op_core_left_of_inc <| .trans ⟨y, hn.trans CMRA.comm'⟩ h).symm

scoped instance {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

end OrdCommMonoidLike

/-! ### Carriers for the universal-core CMRA

The three `OrdCommMonoidLike` carriers of `numbers.v`, in Rocq's order. Only `MaxNat` has a
unit; `min` over `Nat` and `max` over `Int` have none, so `MinNat` and `MaxZ` are CMRAs but
not UCMRAs — matching Rocq, which has `min_natR`/`max_ZR` but no `min_natUR`/`max_ZUR`. -/

namespace Iris

section MaxNat

@[grind cases, rocq_alias max_nat]
structure MaxNat where
  ofNat ::
  toNat : Nat

instance : OfNat MaxNat n where ofNat := .ofNat n

@[grind]
def MaxNat.max (a b : MaxNat) : MaxNat where
  toNat := a.toNat.max b.toNat

scoped instance : Add MaxNat where add := .max
-- scoped instance : Max MaxNat where max := .max
scoped instance : LE MaxNat where le a b := a.toNat ≤ b.toNat

@[simp, grind =]
theorem MaxNat.le_toNat (a b : MaxNat) : a ≤ b ↔ a.toNat ≤ b.toNat := by rfl

@[simp, grind =]
theorem MaxNat.toNat_add (a b : MaxNat) : (a + b).toNat = a.toNat.max b.toNat := rfl

@[simp, grind =]
theorem MaxNat.add_ofNat (a b : Nat) : (MaxNat.ofNat a + MaxNat.ofNat b) = MaxNat.ofNat (a.max b) := rfl

@[grind =_]
theorem MaxNat.toNat_zero : (0 : MaxNat).toNat = 0 := rfl

@[grind =]
theorem MaxNat.zero_ofNat : (0 : MaxNat) = .ofNat 0 := rfl

theorem MaxNat.eq_toNat (a b : MaxNat) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MaxNat) (· + ·) where
  assoc := by grind
scoped instance : Commutative (α := MaxNat) (· + ·) where
  comm := by grind
scoped instance : LawfulLeftIdentity (α := MaxNat) (· + ·) (0 : MaxNat) where
  left_id a := by grind
scoped instance : Std.IdempotentOp (α := MaxNat) (· + ·) where
  idempotent x := by grind
scoped instance : COFE MaxNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxNat := ⟨fun h => h⟩
scoped instance : UCMRA MaxNat := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityHAddZero
scoped instance : CMRA.Discrete MaxNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.CoreId (a : MaxNat) := OrdCommMonoidLike.instCoreId _

@[rocq_alias max_nat_included]
theorem MaxNat.inc_iff {a b : MaxNat} : a ≼ b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toNat]
  grind

@[rocq_alias max_nat_local_update]
theorem MaxNat.local_update {a b a' : MaxNat} (h : a ≤ a') : (a, b) ~l~> (a', a') :=
  OrdCommMonoidLike.idem_local_update (inc_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_nat_is_op]
instance {a b : Nat} :
    IsOp d (MaxNat.ofNat (Nat.max a b)) (MaxNat.ofNat a) (MaxNat.ofNat b) where
  is_op := rfl

end MaxNat

section MinNat

@[grind cases, rocq_alias min_nat]
structure MinNat where
  ofNat ::
  toNat : Nat

instance : OfNat MinNat n where ofNat := .ofNat n

@[grind]
def MinNat.min (a b : MinNat) : MinNat where
  toNat := Nat.min a.toNat b.toNat

scoped instance : Add MinNat where add := .min
scoped instance : LE MinNat where le a b := a.toNat ≤ b.toNat

@[simp, grind =]
theorem MinNat.le_toNat (a b : MinNat) : a ≤ b ↔ a.toNat ≤ b.toNat := by rfl

@[simp, grind =]
theorem MinNat.toNat_add (a b : MinNat) : (a + b).toNat = Nat.min a.toNat b.toNat := rfl

@[simp, grind =]
theorem MinNat.add_ofNat (a b : Nat) :
    (MinNat.ofNat a + MinNat.ofNat b) = MinNat.ofNat (Nat.min a b) := rfl

theorem MinNat.eq_toNat (a b : MinNat) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MinNat) (· + ·) where
  assoc := by grind
scoped instance : Commutative (α := MinNat) (· + ·) where
  comm := by grind
scoped instance : IdempotentOp (α := MinNat) (· + ·) where
  idempotent _ := by grind
scoped instance : COFE MinNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete MinNat := ⟨fun h => h⟩
scoped instance : CMRA MinNat := OrdCommMonoidLike.instCMRA
scoped instance : CMRA.Discrete MinNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.IsTotal MinNat := OrdCommMonoidLike.instIsTotal
scoped instance : CMRA.CoreId (a : MinNat) := OrdCommMonoidLike.instCoreId _

/-- Inclusion is the *reverse* of `≤`, since the operation is `min`. -/
@[rocq_alias min_nat_included]
theorem MinNat.inc_iff {a b : MinNat} : a ≼ b ↔ b ≤ a := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toNat]
  grind

@[rocq_alias min_nat_local_update]
theorem MinNat.local_update {a b a' : MinNat} (h : a' ≤ a) : (a, b) ~l~> (a', a') :=
  OrdCommMonoidLike.idem_local_update (inc_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias min_nat_is_op]
instance {a b : Nat} :
    IsOp d (MinNat.ofNat (Nat.min a b)) (MinNat.ofNat a) (MinNat.ofNat b) where
  is_op := rfl

end MinNat

section MaxZ

@[grind cases, rocq_alias max_Z]
structure MaxZ where
  ofInt ::
  toInt : Int

@[grind]
def MaxZ.max (a b : MaxZ) : MaxZ where
  toInt := Max.max a.toInt b.toInt

scoped instance : Add MaxZ where add := .max
scoped instance : LE MaxZ where le a b := a.toInt ≤ b.toInt

@[simp, grind =]
theorem MaxZ.le_toInt (a b : MaxZ) : a ≤ b ↔ a.toInt ≤ b.toInt := by rfl

@[simp, grind =]
theorem MaxZ.toInt_add (a b : MaxZ) : (a + b).toInt = Max.max a.toInt b.toInt := rfl

@[simp, grind =]
theorem MaxZ.add_ofInt (a b : Int) : (MaxZ.ofInt a + MaxZ.ofInt b) = MaxZ.ofInt (Max.max a b) := rfl

theorem MaxZ.eq_toInt (a b : MaxZ) : a = b ↔ a.toInt = b.toInt := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MaxZ) (· + ·) where
  assoc := by grind
scoped instance : Commutative (α := MaxZ) (· + ·) where
  comm := by grind
scoped instance : IdempotentOp (α := MaxZ) (· + ·) where
  idempotent x := by grind
scoped instance : COFE MaxZ := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxZ := ⟨fun h => h⟩
scoped instance : CMRA MaxZ := OrdCommMonoidLike.instCMRA
scoped instance : CMRA.Discrete MaxZ := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.IsTotal MaxZ := OrdCommMonoidLike.instIsTotal
scoped instance : CMRA.CoreId (a : MaxZ) := OrdCommMonoidLike.instCoreId _

@[rocq_alias max_Z_included]
theorem MaxZ.inc_iff {a b : MaxZ} : a ≼ b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toInt]
  grind

@[rocq_alias max_Z_local_update]
theorem MaxZ.local_update {a b a' : MaxZ} (h : a ≤ a') : (a, b) ~l~> (a', a') :=
  OrdCommMonoidLike.idem_local_update (inc_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_Z_is_op]
instance {a b : Int} :
    IsOp d (MaxZ.ofInt (Max.max a b)) (MaxZ.ofInt a) (MaxZ.ofInt b) where
  is_op := rfl

end MaxZ

end Iris


/- NoCore core -/
namespace PosCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [IdempotentOp (α := α) (· + ·)]

variable {x y x' y' : α}

scoped instance : CMRA α where
  pcore _ := none
  op := add
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [discrete h]
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
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
#rocq_ignore pos_cancelable "Use scoped Cancelable instance"

scoped instance [IdentityFree α] {a : α} : CMRA.IdFree a where
  id_free0_r _ _ h := IdentityFree.id_free <| discrete h
#rocq_ignore pos_id_free "Use scoped IdentityFree instance"

#rocq_ignore pos_op_add "Not needed"

end PosCommMonoidLike
