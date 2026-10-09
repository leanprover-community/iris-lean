/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Markus de Medeiros, Fernando Leal
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
public import Iris.Algebra.LocalUpdates

/-! ## Numbers CMRAs
For simple numerical types which form commutative monoids, there are three classes of ORA:
- "Constant core": the core is a fixed value such as 0 (eg. (ℕ, +))
- "Universal core": every element is a core (eg. (ℕ, max))
- "No core": there is no core (eg. (PNat, +))
Depending on your application, you may either want to open these scopeds or declare an alias
to the scoped instances.

This file also includes some ORA's for types with nonstandard operations, for example (ℕ, max).
These are newtyped to avoid clashing with the normal mathematical operations.
-/

@[expose] public section

variable {SI : Iris.stepindex (Type _)} [instSI : Iris.SIdx SI]

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
/- The constructions below are `def`s rather than instances (a type opts in explicitly). Prop-valued ones
stay `def`s so that section variables are included exactly as for the former instances. -/
set_option linter.defProp false

namespace CommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity ORA

variable [OFE SI α] [OFE.Discrete SI α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero]
variable {x y x' y' : α}

/-- The operation as a step-index-free data instance (Mathlib-style), so that lemmas about `•`
do not depend on the step index. Not an instance: a type opts in by declaring
`instance : Op T := CommMonoidLike.instOp` (a type can carry more than one sensible algebra). -/
@[reducible] def instOp : Op α where
  op := add
  assoc {x y z} := (Associative.assoc (op := add) x y z).symm
  comm {x y} := Commutative.comm (op := add) x y
attribute [local instance] instOp

/-- The constant core `zero`. -/
@[reducible] def instPCore : PCore α where
  pcore _ := some zero
  pcore_idem h := h
attribute [local instance] instPCore

@[reducible] def instRA : RA α where
  pcore_op_left h := Option.some.inj h ▸ left_id (op := add) _
attribute [local instance] instRA

@[reducible] def instURA : URA α where
  unit := zero
  unit_left_id := left_id (op := add) _
  pcore_unit := rfl
  total _ := ⟨zero, rfl⟩
attribute [local instance] instURA

@[reducible] def instCMRA : CMRA SI α :=
  CMRA.ofDiscreteTotal (fun _ => True)
    (fun _ _ _ => trivial)
    (fun _ _ => ⟨zero, (left_id (op := add) zero).symm⟩)
attribute [local instance] instCMRA

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

@[reducible] def instDiscrete : ORA.Discrete SI α where
  discrete_valid := id
  discrete_ord := CMRA.ord_of_ord0
attribute [local instance] instDiscrete
#rocq_ignore nat_cmra_discrete "Use the (ℕ, +) Constant Core instance."
#rocq_ignore Z_cmra_discrete "Use the (ℤ, +) Constant Core instance."

@[reducible] def instUCMRA : UCMRA SI α := UORA.ofUCMRAData { unit_valid := trivial }
attribute [local instance] instUCMRA

#rocq_ignore natUR "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore nat_ucmra_mixin "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore nat_unit_instance "Use the (ℕ, +) Constant Core UCMRA."
#rocq_ignore ZUR "Use the (ℤ, +) Constant Core UCMRA."
#rocq_ignore Z_ucmra_mixin "Use the (ℤ, +) Constant Core UCMRA."
#rocq_ignore Z_unit_instance "Use the (ℤ, +) Constant Core UCMRA."

@[reducible] def instCancelable [LeftCancelAdd α] {a : α} : Cancelable SI a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
attribute [local instance] instCancelable
#rocq_ignore nat_cancelable "Use the (ℕ, +) Constant Core instance."
#rocq_ignore Z_cancelable "Use the (ℤ, +) Constant Core instance."

omit [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero] in
@[rocq_alias nat_op, rocq_alias Z_op]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem ord_iff {x y : α} : x ≼ₒ[SI] y ↔ ∃ z, y = x + z := Iff.rfl

omit [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero] in
theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := Iff.rfl

theorem ord_iff_le [LE α] [LawfulAddLE α] {x y : α} : x ≼ₒ[SI] y ↔ x ≤ y :=
  ord_iff.trans LawfulAddLE.le_iff_exists_add.symm

omit [Zero α] [LawfulLeftIdentity (α := α) (· + ·) zero] in
@[rocq_alias nat_included]
theorem inc_iff_le [LE α] [LawfulAddLE α] {x y : α} : x ≼ y ↔ x ≤ y :=
  included_iff.trans LawfulAddLE.le_iff_exists_add.symm

/-- Sufficient condition for a local update on a LeftCancelAdd structure, such as (ℕ, +) -/
@[rocq_alias nat_local_update, rocq_alias Z_local_update]
theorem leftCancelAdd_local_update [LeftCancelAdd α] (h : add x y' = add x' y) :
    (x, y) ~l~>[SI] (x', y') := by
  refine discrete_unital_triv_local_update (fun _ => trivial) @fun z hz => ?_
  refine LeftCancelAdd.cancel_right (y := y) ?_
  calc
    add x' y = add x y' := h.symm
    _ = add (add y z) y' := by rw [hz]; rfl
    _ = add y' (add y z) := by rw [comm (op := add)]
    _ = add y' (add z y) := by rw [comm (op := add) z]
    _ = add (add y' z) y := by rw [assoc (op := add)]

@[reducible] def instDiscreteE {a : α} : DiscreteE SI a := ⟨fun H => discrete H⟩
attribute [local instance] instDiscreteE

@[reducible] def instCoreIdZero : CoreId (α := α) 0 where
  core_id := rfl
attribute [local instance] instCoreIdZero

set_option synthInstance.checkSynthOrder false in
@[rocq_alias nat_is_op, rocq_alias Z_is_op, reducible] def instIsOp {x y : α} : IsOp d (x + y) x y where
  is_op := rfl

end CommMonoidLike

/- Universal core -/
namespace OrdCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity ORA IdempotentOp

variable [OFE SI α] [OFE.Discrete SI α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]
variable [IdempotentOp (α := α) (· + ·)]
variable [Zero α]
variable {x y x' y' : α}

/-- The operation as a step-index-free data instance (Mathlib-style), so that lemmas about `•`
do not depend on the step index. Not an instance: a type opts in by declaring
`instance : Op T := CommMonoidLike.instOp` (a type can carry more than one sensible algebra). -/
@[reducible] def instOp : Op α where
  op := add
  assoc {x y z} := (Associative.assoc (op := add) x y z).symm
  comm {x y} := Commutative.comm (op := add) x y
attribute [local instance] instOp

/-- The universal core: every element is its own core. -/
@[reducible] def instPCore : PCore α where
  pcore := some
  pcore_idem _ := rfl
attribute [local instance] instPCore

@[reducible] def instRA : RA α where
  pcore_op_left h := Option.some.inj h ▸ idempotent _
attribute [local instance] instRA

@[reducible] def instIsTotal : IsTotal α where
  total x := ⟨x, rfl⟩
attribute [local instance] instIsTotal

@[reducible] def instCMRA : CMRA SI α :=
  CMRA.ofDiscreteTotal (fun _ => True)
    (fun _ _ _ => trivial)
    (fun _ y => ⟨y, rfl⟩)
attribute [local instance] instCMRA

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

@[reducible] def instDiscrete : ORA.Discrete SI α where
  discrete_valid := id
  discrete_ord := CMRA.ord_of_ord0
attribute [local instance] instDiscrete
#rocq_ignore max_nat_cmra_discrete "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_Z_cmra_discrete "Use the (ℤ, max) Universal Core instance."
#rocq_ignore min_nat_cmra_discrete "Use the (ℕ, min) Universal Core instance."

#rocq_ignore max_Z_cmra_total "Use the (ℤ, max) Universal Core instance."

@[reducible] def instCoreId (a : α) : CoreId a where
  core_id := rfl
attribute [local instance] instCoreId
#rocq_ignore max_nat_core_id "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_Z_core_id "Use the (ℤ, max) Universal Core instance."
#rocq_ignore min_nat_core_id "Use the (ℕ, min) Universal Core instance."

@[reducible] def instURA [LawfulLeftIdentity (α := α) (· + ·) zero] : URA α where
  unit := zero
  unit_left_id := left_id _
  pcore_unit := rfl
attribute [local instance] instURA

@[reducible] def instUCMRA [LawfulLeftIdentity (α := α) (· + ·) zero] : UCMRA SI α :=
  UORA.ofUCMRAData { unit_valid := trivial }
attribute [local instance] instUCMRA

#rocq_ignore max_natUR "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_nat_ucmra_mixin "Use the (ℕ, max) Universal Core instance."
#rocq_ignore max_nat_unit_instance "Use the (ℕ, max) Universal Core instance."

@[reducible] def instCancelable [LeftCancelAdd α] {a : α} : Cancelable SI a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
attribute [local instance] instCancelable

omit [Zero α] in
omit [IdempotentOp (α := α) (· + ·)] in
@[simp, grind =, rocq_alias max_nat_op, rocq_alias max_Z_op, rocq_alias min_nat_op_min]
theorem op_eq {x y : α} : x • y = x + y := rfl

omit [Zero α] in
theorem ord_iff {x y : α} : x ≼ₒ[SI] y ↔ x • y = y :=
  ⟨fun h => op_core_right_of_inc (OrdInc.ord_inc h), fun h => IncOrd.inc_ord ⟨y, h.symm⟩⟩

omit [Zero α] in
theorem inc_iff {x y : α} : x ≼ y ↔ x • y = y :=
  ⟨fun ⟨z, hz⟩ => hz ▸ Op.assoc.trans (congrArg (· • z) (idempotent x)), fun h => ⟨y, h.symm⟩⟩

omit [Zero α] in
theorem idem_local_update_ord {x y x' : α} (h : x ≼ₒ[SI] x') : (x, y) ~l~>[SI] (x', x') := by
  refine fun _ mz _ hn => ⟨trivial, OFE.Dist.of_eq ?_⟩
  cases mz with | none => rfl | some z =>
  replace hn : x = y • z := discrete hn
  exact (op_core_left_of_inc <| .trans ⟨y, hn.trans comm'⟩ (OrdInc.ord_inc h)).symm

omit [Zero α] in
/-- Sufficient condition for a local update on an idempotent structure. -/
theorem idem_local_update {x y x' : α} (h : x ≼ x') : (x, y) ~l~>[SI] (x', x') :=
  idem_local_update_ord (inc_iff_ord.mp h)

@[reducible] def instDiscreteE {a : α} : DiscreteE SI a := ⟨fun H => discrete H⟩
attribute [local instance] instDiscreteE

end OrdCommMonoidLike

/- NoCore core -/
namespace PosCommMonoidLike

open Iris Iris.OFE Add Zero One Associative Commutative LawfulLeftIdentity ORA

variable [OFE SI α] [OFE.Discrete SI α]
variable [Add α] [Associative (α := α) (· + ·)] [Commutative (α := α) (· + ·)]

variable {x y x' y' : α}

/-- The operation as a step-index-free data instance (Mathlib-style), so that lemmas about `•`
do not depend on the step index. Not an instance: a type opts in by declaring
`instance : Op T := CommMonoidLike.instOp` (a type can carry more than one sensible algebra). -/
@[reducible] def instOp : Op α where
  op := add
  assoc {x y z} := (Associative.assoc (op := add) x y z).symm
  comm {x y} := Commutative.comm (op := add) x y
attribute [local instance] instOp

/-- No element has a core. -/
@[reducible] def instPCore : PCore α where
  pcore _ := none
  pcore_idem h := by rcases h
attribute [local instance] instPCore

@[reducible] def instRA : RA α where
  pcore_op_left h := by rcases h
attribute [local instance] instRA

@[reducible] def instCMRA : CMRA SI α :=
  CMRA.ofDiscrete (fun _ => True)
    (fun _ _ _ => trivial)
    (by rintro _ _ ⟨⟩)
attribute [local instance] instCMRA

#rocq_ignore positiveR "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_ra_mixin "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_op_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_pcore_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_valid_instance "Use (PNat, +) No Core CMRA."
#rocq_ignore pos_validN_instance "Use (PNat, +) No Core CMRA."

@[reducible] def instDiscrete : ORA.Discrete SI α where
  discrete_valid := id
  discrete_ord := CMRA.ord_of_ord0
attribute [local instance] instDiscrete
#rocq_ignore pos_cmra_discrete "Use (PNat, +) No Core instance."

@[reducible] def instCancelable [LeftCancelAdd α] {a : α} : Cancelable SI a where
  cancelableN {_ _ _} _ := .of_eq ∘ LeftCancelAdd.cancel_left ∘ discrete
attribute [local instance] instCancelable
#rocq_ignore pos_cancelable "Use (PNat, +) No Core instance."

@[reducible] def instIdFree [IdentityFree α] {a : α} : IdFree SI a where
  id_free0_r _ _ h := IdentityFree.id_free <| discrete h
attribute [local instance] instIdFree
#rocq_ignore pos_id_free "Use (PNat, +) No Core instance."

@[rocq_alias pos_op_add]
theorem op_eq {x y : α} : x • y = x + y := rfl

theorem ord_iff {x y : α} : x ≼ₒ[SI] y ↔ ∃ z, y = x + z := Iff.rfl

theorem included_iff {x y : α} : x ≼ y ↔ ∃ z, y = x + z := Iff.rfl

theorem ord_iff_lt [LT α] [LawfulAddLT α] {x y : α} : x ≼ₒ[SI] y ↔ x < y :=
  ord_iff.trans LawfulAddLT.lt_iff_exists_add.symm

@[rocq_alias pos_included]
theorem inc_iff_lt [LT α] [LawfulAddLT α] {x y : α} : x ≼ y ↔ x < y :=
  included_iff.trans LawfulAddLT.lt_iff_exists_add.symm

set_option synthInstance.checkSynthOrder false in
@[rocq_alias pos_is_op, reducible] def instIsOp {x y : α} : IsOp d (x + y) x y where
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

/-! ## `(ℕ, +)`: the canonical resource algebra on `Nat` (Iris-Rocq `natR`/`natUR`)

`Nat` gets the additive algebra globally, as in Iris-Rocq and Mathlib (`Nat` is an additive monoid);
the `max` algebra lives on the wrapper `MaxNat`. -/
section NatAdd
open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open OFE ORA
variable {SI : stepindex (Type _)} [SIdx SI]

instance : Associative (α := Nat) (· + ·) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩
instance : LawfulLeftIdentity (α := Nat) (· + ·) Zero.zero := ⟨Nat.zero_add⟩
instance natCOFE : COFE SI Nat := COFE.ofDiscrete _
instance : OFE.Discrete SI Nat := ⟨fun h => h⟩
instance natOp : Op Nat := CommMonoidLike.instOp
instance natPCore : PCore Nat := CommMonoidLike.instPCore
instance natRA : RA Nat := CommMonoidLike.instRA
instance natURA : URA Nat := CommMonoidLike.instURA
instance natUCMRA : UCMRA SI Nat := CommMonoidLike.instUCMRA
instance : ORA.Discrete SI Nat := CommMonoidLike.instDiscrete
instance : LeftCancelAdd Nat := ⟨Nat.add_left_cancel⟩
instance {a : Nat} : Cancelable SI a := CommMonoidLike.instCancelable
instance : CoreId (0 : Nat) := CommMonoidLike.instCoreIdZero
set_option synthInstance.checkSynthOrder false in
instance natIsOp {x y : Nat} : IsOp d (x + y) x y := CommMonoidLike.instIsOp

end NatAdd


section MaxNat
open ORA

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
scoped instance : Op MaxNat := OrdCommMonoidLike.instOp
scoped instance : PCore MaxNat := OrdCommMonoidLike.instPCore
scoped instance : RA MaxNat := OrdCommMonoidLike.instRA
scoped instance : URA MaxNat := OrdCommMonoidLike.instURA
scoped instance : COFE SI MaxNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete SI MaxNat := ⟨fun h => h⟩
scoped instance : UCMRA SI MaxNat := OrdCommMonoidLike.instUCMRA
scoped instance : ORA.Discrete SI MaxNat := OrdCommMonoidLike.instDiscrete
scoped instance : CoreId (a : MaxNat) := OrdCommMonoidLike.instCoreId _

theorem MaxNat.ord_iff {a b : MaxNat} : a ≼ₒ[SI] b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.ord_iff, MaxNat.le_toNat, eq_toNat]
  change (a + b).toNat = b.toNat ↔ _
  rw [MaxNat.toNat_add]; constructor <;> intro h <;> simp only [Nat.max_def] at * <;> split at * <;> omega

theorem MaxNat.toNat_op (a b : MaxNat) : (a • b).toNat = Max.max a.toNat b.toNat := rfl

@[rocq_alias max_nat_included]
theorem MaxNat.inc_iff {a b : MaxNat} : a ≼ b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.inc_iff, MaxNat.le_toNat, eq_toNat]
  change (a + b).toNat = b.toNat ↔ _
  rw [MaxNat.toNat_add]; constructor <;> intro h <;> simp only [Nat.max_def] at * <;> split at * <;> omega

@[rocq_alias max_nat_local_update]
theorem MaxNat.local_update {a b a' : MaxNat} (h : a ≤ a') : (a, b) ~l~>[SI] (a', a') :=
  OrdCommMonoidLike.idem_local_update_ord (ord_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_nat_is_op]
instance {a b : Nat} :
    IsOp d (MaxNat.ofNat (Nat.max a b)) (MaxNat.ofNat a) (MaxNat.ofNat b) where
  is_op := rfl

end MaxNat

section MaxInt
open ORA

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
scoped instance : Op MaxInt := OrdCommMonoidLike.instOp
scoped instance : PCore MaxInt := OrdCommMonoidLike.instPCore
scoped instance : RA MaxInt := OrdCommMonoidLike.instRA
scoped instance : IsTotal MaxInt := OrdCommMonoidLike.instIsTotal
scoped instance : COFE SI MaxInt := COFE.ofDiscrete _
scoped instance : OFE.Discrete SI MaxInt := ⟨fun h => h⟩
scoped instance : CMRA SI MaxInt := OrdCommMonoidLike.instCMRA
scoped instance : ORA.Discrete SI MaxInt := OrdCommMonoidLike.instDiscrete
scoped instance : CoreId (a : MaxInt) := OrdCommMonoidLike.instCoreId _

theorem MaxInt.ord_iff {a b : MaxInt} : a ≼ₒ[SI] b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.ord_iff, OrdCommMonoidLike.op_eq, eq_toInt]
  grind

@[rocq_alias max_Z_included]
theorem MaxInt.inc_iff {a b : MaxInt} : a ≼ b ↔ a ≤ b := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toInt]
  grind

@[rocq_alias max_Z_local_update]
theorem MaxInt.local_update {a b a' : MaxInt} (h : a ≤ a') : (a, b) ~l~>[SI] (a', a') :=
  OrdCommMonoidLike.idem_local_update_ord (ord_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias max_Z_is_op]
instance {a b : Int} :
    IsOp d (MaxInt.ofInt (Max.max a b)) (MaxInt.ofInt a) (MaxInt.ofInt b) where
  is_op := rfl

end MaxInt

section MinNat
open ORA

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
scoped instance : Op MinNat := OrdCommMonoidLike.instOp
scoped instance : PCore MinNat := OrdCommMonoidLike.instPCore
scoped instance : RA MinNat := OrdCommMonoidLike.instRA
scoped instance : IsTotal MinNat := OrdCommMonoidLike.instIsTotal
scoped instance : COFE SI MinNat := COFE.ofDiscrete _
scoped instance : OFE.Discrete SI MinNat := ⟨fun h => h⟩
scoped instance : CMRA SI MinNat := OrdCommMonoidLike.instCMRA
scoped instance : ORA.Discrete SI MinNat := OrdCommMonoidLike.instDiscrete
scoped instance : CoreId (a : MinNat) := OrdCommMonoidLike.instCoreId _

theorem MinNat.ord_iff {a b : MinNat} : a ≼ₒ[SI] b ↔ b ≤ a := by
  rw [OrdCommMonoidLike.ord_iff, OrdCommMonoidLike.op_eq, eq_toNat]
  grind

@[rocq_alias min_nat_included]
theorem MinNat.inc_iff {a b : MinNat} : a ≼ b ↔ b ≤ a := by
  rw [OrdCommMonoidLike.inc_iff, OrdCommMonoidLike.op_eq, eq_toNat]
  grind

@[rocq_alias min_nat_local_update]
theorem MinNat.local_update {a b a' : MinNat} (h : a' ≤ a) : (a, b) ~l~>[SI] (a', a') :=
  OrdCommMonoidLike.idem_local_update_ord (ord_iff.mpr h)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias min_nat_is_op]
instance {a b : Nat} :
    IsOp d (MinNat.ofNat (Nat.min a b)) (MinNat.ofNat a) (MinNat.ofNat b) where
  is_op := rfl

end MinNat

end Iris
