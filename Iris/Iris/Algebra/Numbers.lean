/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros, Fernando Leal
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
public import Iris.Algebra.LocalUpdates

/-! ## Numbers CMRAs
For simple numerical types which form commutative monoids, there are three classes of CMRA:
- "Constant core": the core is a fixed value such as 0 (eg. (ℕ, +))
- "Universal core": every element is a core (eg. (ℕ, max))
- "No core": there is no core (eg. (PNat, +))
Depending on your application, you may either want to open these scopeds or declare an alias
to the scoped instances.

This file also includes some CMRA's for types with nonstandard operations, for example (ℕ, max).
These are newtyped to avoid clashing with the normal mathematical operations.
-/

@[expose] public section
local stepindex Nat

open Std

class IdentityFree (α : Type _) [Add α] where
  id_free {a b : α} : ¬ Add.add a b = a

class LeftCancelAdd (α : Type _) [Add α] where
  cancel_left {x₁ x₂ y : α} : y + x₁ = y + x₂ → x₁ = x₂

class LawfulAddLE (α : Type _) [Add α] [LE α] where
  le_iff_exists_add {x y : α} : x ≤ y ↔ ∃ z, y = x + z

class LawfulAddLT (α : Type _) [Add α] [LT α] where
  lt_iff_exists_add {x y : α} : x < y ↔ ∃ z, y = x + z

open Add Commutative in
theorem LeftCancelAdd.cancel_right {x₁ x₂ y : α} [Add α] [LeftCancelAdd α]
    [Commutative (add (α := α))] (h : add x₁ y = add x₂ y) : x₁ = x₂ := by
  refine cancel_left (y := y) ?_
  rw [← add_eq_hAdd, comm (op := Add.add) y x₁, h, comm (op := Add.add)]

/- Constant core -/
namespace CommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA

variable [OFE α] [OFE.Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero]
variable {x y x' y' : α}

scoped instance instCMRA : CMRA α where
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

#rocq_ignore natR "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore nat_ra_mixin "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore nat_op_instance "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore nat_pcore_instance "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore nat_valid_instance "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore nat_validN_instance "Use the (ℕ, +) Constant Core CMRA."
#rocq_ignore ZR "Use the (ℤ, +) Constant Core CMRA"
#rocq_ignore Z_ra_mixin "Use the (ℤ, +) Constant Core CMRA"
#rocq_ignore Z_op_instance "Use the (ℤ, +) Constant Core CMRA"
#rocq_ignore Z_pcore_instance "Use the (ℤ, +) Constant Core CMRA"
#rocq_ignore Z_valid_instance "Use the (ℤ, +) Constant Core CMRA"
#rocq_ignore Z_validN_instance "Use the (ℤ, +) Constant Core CMRA"

scoped instance instDiscrete : CMRA.Discrete α where discrete_valid := id
#rocq_ignore nat_cmra_discrete "Use the (ℕ, +) Constant Core instance."
#rocq_ignore Z_cmra_discrete "Use the (ℤ, +) Constant Core instance."

scoped instance instUCMRA : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := pcore_op_left rfl
  pcore_unit := rfl

#rocq_ignore natUR "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore nat_ucmra_mixin "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore nat_unit_instance "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore ZUR "Use the (ℤ, +) Constant Core UCMRA."
#rocq_ignore Z_ucmra_mixin "Use the (ℤ, +) Constant Core UCMRA."
#rocq_ignore Z_unit_instance "Use the (ℤ, +) Constant Core UCMRA."

scoped instance instCancelable [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
#rocq_ignore nat_cancelable "Use the (ℕ, +) Constant Core instance."
#rocq_ignore Z_cancelable "Use the (ℤ, +) Constant Core instance."

@[rocq_alias nat_op, rocq_alias Z_op]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := Iff.rfl

@[rocq_alias nat_included]
theorem inc_iff_le [LE α] [LawfulAddLE α] {x y : α} : x ≼ y ↔ x ≤ y :=
  included_iff.trans LawfulAddLE.le_iff_exists_add.symm

/-- Sufficient condition for a local update on a LeftCancelAdd structure, such as (ℕ, +) -/
@[rocq_alias nat_local_update, rocq_alias Z_local_update]
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

scoped instance instDiscreteE {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

scoped instance instCoreIdZero : CoreId (α := α) 0 where
  core_id := rfl

set_option synthInstance.checkSynthOrder false in
@[rocq_alias nat_is_op, rocq_alias Z_is_op]
scoped instance instIsOp {x y : α} : IsOp d (x + y) x y where
  is_op := rfl

end CommMonoidLike

/- Universal core -/
namespace OrdCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA IdempotentOp

variable [OFE α] [OFE.Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [IdempotentOp (α := α) (· + ·)]
variable [Zero α]
variable {x y x' y' : α}

scoped instance instCMRA : CMRA α where
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


#rocq_ignore max_natO "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_natR "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_nat_ra_mixin "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_nat_op_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_nat_pcore_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_nat_valid_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore max_nat_validN_instance "Use the (ℕ, max) Universal Core CMRA."

#rocq_ignore max_ZO "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_ZR "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_Z_ra_mixin "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_Z_op_instance "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_Z_pcore_instance "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_Z_valid_instance "Use the (ℤ, max) Universal Core CMRA."
#rocq_ignore max_Z_validN_instance "Use the (ℤ, max) Universal Core CMRA."

#rocq_ignore min_natO "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_natR "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_nat_ra_mixin "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_nat_op_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_nat_pcore_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_nat_valid_instance "Use the (ℕ, max) Universal Core CMRA."
#rocq_ignore min_nat_validN_instance "Use the (ℕ, max) Universal Core CMRA."

scoped instance : CMRA.Discrete α where
  discrete_valid := id
#rocq_ignore max_nat_cmra_discrete "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_Z_cmra_discrete "Use the (ℤ, max) Universal Core instance."
#rocq_ignore min_nat_cmra_discrete "Use the (ℕ, min) Universal Core instance."

scoped instance instIsTotal : CMRA.IsTotal α where
  total x := ⟨x, rfl⟩
#rocq_ignore max_Z_cmra_total "Use the (ℤ, max) Universal Core instance."

scoped instance instCoreId (a : α) : CMRA.CoreId a where
  core_id := rfl
#rocq_ignore max_nat_core_id "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_Z_core_id "Use the (ℤ, max) Universal Core instance."
#rocq_ignore min_nat_core_id "Use the (ℕ, min) Universal Core instance."

scoped instance instUCMRA [LawfulLeftIdentity (α := α) (· + ·) zero] : UCMRA α where
  unit := zero
  unit_valid := trivial
  unit_left_id := left_id _
  pcore_unit := rfl
#rocq_ignore max_Z_unit_instance "Rocq has no `max_Z_UCMRA`."
#rocq_ignore max_natUR "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_nat_ucmra_mixin "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_nat_unit_instance "Use the (ℕ, max) Universal Core instance."

scoped instance instCancelable [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete

omit [Zero α] in
@[simp, grind =, rocq_alias max_nat_op, rocq_alias max_Z_op, rocq_alias min_nat_op_min]
theorem op_eq {x y : α} : x • y = x + y := rfl

omit [Zero α] in
theorem inc_iff {x y : α} : x ≼ y ↔ x • y = y :=
  ⟨CMRA.op_core_right_of_inc, fun h => ⟨y, h.symm⟩⟩

omit [Zero α] in
/-- Sufficient condition for a local update on an idempotent structure. -/
theorem idem_local_update {x y x' : α} (h : x ≼ x') : (x, y) ~l~> (x', x') := by
  refine fun _ mz _ hn => ⟨trivial, OFE.Dist.of_eq ?_⟩
  cases mz with | none => rfl | some z =>
  replace hn : x = y • z := discrete hn
  exact (CMRA.op_core_left_of_inc <| .trans ⟨y, hn.trans CMRA.comm'⟩ h).symm

scoped instance instDiscreteE {a : α} : DiscreteE a := ⟨fun H => discrete H⟩

end OrdCommMonoidLike

/- NoCore core -/
namespace PosCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity CMRA

variable [OFE α] [OFE.Discrete α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]

variable {x y x' y' : α}

scoped instance instCMRA : CMRA α where
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
#rocq_ignore positiveR "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_ra_mixin "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_op_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_pcore_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_valid_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_validN_instance "Use (PNat, +) No Core CMRA."

scoped instance instDiscrete : CMRA.Discrete α where
  discrete_valid := id
#rocq_ignore pos_cmra_discrete "Use (PNat, +) No Core instance."

scoped instance instCancelable [LeftCancelAdd α] {a : α} : Cancelable a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
#rocq_ignore pos_cancelable "Use (PNat, +) No Core instance."

scoped instance instIdFree [IdentityFree α] {a : α} : CMRA.IdFree a where
  id_free0_r _ _ h := IdentityFree.id_free <| discrete h
#rocq_ignore pos_id_free "Use (PNat, +) No Core instance."

@[rocq_alias pos_op_add]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := Iff.rfl

@[rocq_alias pos_included]
theorem inc_iff_lt [LT α] [LawfulAddLT α] {x y : α} : x ≼ y ↔ x < y :=
  included_iff.trans LawfulAddLT.lt_iff_exists_add.symm

set_option synthInstance.checkSynthOrder false in
@[rocq_alias pos_is_op]
scoped instance instIsOp {x y : α} : IsOp d (x + y) x y where
  is_op := rfl

end PosCommMonoidLike

/-! ### New types for commutative monoids with nonstandard addition
This section covers the commutative monoids whose addition is not `Add`. As such, they are
wrapped in custom structures:
- (ℕ, max): `MaxNat`
- (ℤ, max): `MaxInt`
- (ℕ, min): `MinNat`
-/

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
scoped instance : LE MaxNat where le a b := a.toNat ≤ b.toNat

@[simp, grind =]
theorem MaxNat.le_toNat (a b : MaxNat) : a ≤ b ↔ a.toNat ≤ b.toNat := by rfl

@[simp, grind =]
theorem MaxNat.toNat_add (a b : MaxNat) : (a + b).toNat = a.toNat.max b.toNat := rfl

@[simp, grind =]
theorem MaxNat.add_ofNat (a b : Nat) :
    (MaxNat.ofNat a + MaxNat.ofNat b) = MaxNat.ofNat (a.max b) := rfl

@[grind =_]
theorem MaxNat.toNat_zero : (0 : MaxNat).toNat = 0 := rfl

@[grind =]
theorem MaxNat.zero_ofNat : (0 : MaxNat) = .ofNat 0 := rfl

theorem MaxNat.eq_toNat (a b : MaxNat) : a = b ↔ a.toNat = b.toNat := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MaxNat) (· + ·) where assoc := by grind
scoped instance : Commutative (α := MaxNat) (· + ·) where comm := by grind
scoped instance : LawfulLeftIdentity (α := MaxNat) (· + ·) (0 : MaxNat) where left_id a := by grind
scoped instance : Std.IdempotentOp (α := MaxNat) (· + ·) where idempotent x := by grind
scoped instance : COFE MaxNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxNat := ⟨fun h => h⟩
scoped instance : UCMRA MaxNat := OrdCommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete MaxNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.CoreId (a : MaxNat) := OrdCommMonoidLike.instCoreId _

@[rocq_alias max_nat_included]
theorem MaxNat.inc_iff {a b : MaxNat} : a ≼ b ↔ a ≤ b := by
  grind [OrdCommMonoidLike.inc_iff, eq_toNat]

@[rocq_alias max_nat_local_update]
theorem MaxNat.local_update {a b a' : MaxNat} (h : a ≤ a') : (a, b) ~l~> (a', a') :=
  OrdCommMonoidLike.idem_local_update (inc_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_nat_is_op]
instance {a b : Nat} :
    IsOp d (MaxNat.ofNat (Nat.max a b)) (MaxNat.ofNat a) (MaxNat.ofNat b) where
  is_op := rfl

end MaxNat

section MaxInt

@[grind cases, rocq_alias max_Z]
structure MaxInt where
  ofInt ::
  toInt : Int

@[grind]
def MaxInt.max (a b : MaxInt) : MaxInt where
  toInt := Max.max a.toInt b.toInt

scoped instance : Add MaxInt where add := .max
scoped instance : LE MaxInt where le a b := a.toInt ≤ b.toInt

@[simp, grind =]
theorem MaxInt.le_toInt (a b : MaxInt) : a ≤ b ↔ a.toInt ≤ b.toInt := by rfl

@[simp, grind =]
theorem MaxInt.toInt_add (a b : MaxInt) : (a + b).toInt = Max.max a.toInt b.toInt := rfl

@[simp, grind =]
theorem MaxInt.add_ofInt (a b : Int) :
    (MaxInt.ofInt a + MaxInt.ofInt b) = MaxInt.ofInt (Max.max a b) := rfl

theorem MaxInt.eq_toInt (a b : MaxInt) : a = b ↔ a.toInt = b.toInt := by
  constructor
  · rintro rfl; rfl
  · cases a; cases b; rintro rfl; rfl

scoped instance : Associative (α := MaxInt) (· + ·) where assoc := by grind
scoped instance : Commutative (α := MaxInt) (· + ·) where comm := by grind
scoped instance : IdempotentOp (α := MaxInt) (· + ·) where idempotent x := by grind
scoped instance : COFE MaxInt := COFE.ofDiscrete _
scoped instance : OFE.Discrete MaxInt := ⟨fun h => h⟩
scoped instance : CMRA MaxInt := OrdCommMonoidLike.instCMRA
scoped instance : CMRA.Discrete MaxInt := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.IsTotal MaxInt := OrdCommMonoidLike.instIsTotal
scoped instance : CMRA.CoreId (a : MaxInt) := OrdCommMonoidLike.instCoreId _

@[rocq_alias max_Z_included]
theorem MaxInt.inc_iff {a b : MaxInt} : a ≼ b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toInt]
  grind

@[rocq_alias max_Z_local_update]
theorem MaxInt.local_update {a b a' : MaxInt} (h : a ≤ a') : (a, b) ~l~> (a', a') :=
  OrdCommMonoidLike.idem_local_update (inc_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_Z_is_op]
instance {a b : Int} :
    IsOp d (MaxInt.ofInt (Max.max a b)) (MaxInt.ofInt a) (MaxInt.ofInt b) where
  is_op := rfl

end MaxInt

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

scoped instance : Associative (α := MinNat) (· + ·) where assoc := by grind
scoped instance : Commutative (α := MinNat) (· + ·) where comm := by grind
scoped instance : IdempotentOp (α := MinNat) (· + ·) where idempotent _ := by grind
scoped instance : COFE MinNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete MinNat := ⟨fun h => h⟩
scoped instance : CMRA MinNat := OrdCommMonoidLike.instCMRA
scoped instance : CMRA.Discrete MinNat := OrdCommMonoidLike.instDiscrete
scoped instance : CMRA.IsTotal MinNat := OrdCommMonoidLike.instIsTotal
scoped instance : CMRA.CoreId (a : MinNat) := OrdCommMonoidLike.instCoreId _

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

end Iris
