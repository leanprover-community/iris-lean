/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Iris

@[expose] public section

/-!
# Subring CMRAs

Idempotent UCMRAs harvested from the `CompleteLattice` structure on Mathlib's
ring-theoretic subobject lattices. This is the ring-theoretic sibling of
`SubgroupCMRA` in `IrisMath.Subgroup` and `SubmoduleCMRA` in
`IrisMath.LatticeCMRAs`.

## Main definitions

* `SubringCMRA R`: subrings of a ring `R` under supremum (unit `⊥`).
* `SubsemiringCMRA R`: subsemirings of a semiring `R` under supremum (unit
  `⊥`).
* `SubfieldCMRA K`: subfields of a field `K` under supremum (unit `⊥`).
* `SubalgebraCMRA R A`: `R`-subalgebras of an `R`-algebra `A` under supremum
  (unit `⊥`).

## Recipe

In each case the carrier is wrapped in `LeibnizO` (discrete + Leibniz OFE) and
we instantiate the `OrdCommMonoidLike` recipe from `Iris/Algebra/Numbers.lean`.
That recipe surfaces a UCMRA whose `pcore` is `some` (every element is its own
core) and whose `Valid`/`ValidN` are trivially `True`. Concretely, each block:

1. transports `COFE` / `OFE.Discrete` / `OFE.Leibniz` from `LeibnizO`;
2. defines `Add` as the lattice join `⊔` and `Zero` as the bottom subobject `⊥`;
3. proves the algebraic laws (`Associative`, `Commutative`, `IdempotentOp`,
   `LawfulLeftIdentity`) by transporting the underlying `CompleteLattice` laws;
4. uses `OrdCommMonoidLike.instCMRA` etc. to obtain `CMRA`, `CMRA.Discrete`,
   and `UCMRA`.

Because the relevant `OrdCommMonoidLike` instances are declared `scoped`, the
ambient `inferInstance` machinery does not see them through `open`; we therefore
reference the underlying instance names (`instCMRA`, `instDiscrete`,
`instUCMRAOfLawfulLeftIdentityAddZero`, `instCoreId`) directly, mirroring the
style used in `IrisMath.LatticeCMRAs` and `IrisMath.Subgroup`.

## TODO

The four constructions below are structurally identical -- and identical to the
group-theoretic ones in `IrisMath.Subgroup`. A future refactor should subsume
them all (together with `SubmoduleCMRA`, `FilterCMRA`, `Opens`, `SigmaAlgebra`,
...) under a single generic `LatticeUCMRA L` parameterised by
`[CompleteLattice L]`, with the existing names becoming `abbrev`s. That change
necessarily touches every consumer of these CMRAs and is intentionally deferred.
-/

open Iris OFE CMRA Std

namespace IrisMath.Subring

/-! ## (A) Subrings under sup -/

/-- Subrings of a ring `R` as a UCMRA under join (`⊔`), with unit `⊥` (the
prime subring `Int.cast`). The operation is "the smallest subring containing
both", and every subring is its own core. -/
def SubringCMRA (R : Type _) [Ring R] : Type _ := LeibnizO (_root_.Subring R)

namespace SubringCMRA

variable {R : Type _} [Ring R]

instance : COFE (SubringCMRA R) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubringCMRA R) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubringCMRA R) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: subring join. -/
instance : Add (SubringCMRA R) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the bottom subring. -/
instance : Zero (SubringCMRA R) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubringCMRA R) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubringCMRA R) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubringCMRA R)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubringCMRA R)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubringCMRA R)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubringCMRA R) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubringCMRA R)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubringCMRA R) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubringCMRA R)) (0 : SubringCMRA R) where
  left_id a :=
    show (⟨(⊥ : _root_.Subring R) ⊔ a.car⟩ : SubringCMRA R) = a by
      cases a
      simp

instance : CMRA (SubringCMRA R) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubringCMRA R) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubringCMRA R) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every subring is its own core. -/
theorem coreId (a : SubringCMRA R) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the subring lattice:
`a ≤ a + b`. -/
theorem le_op_left (a b : SubringCMRA R) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubringCMRA R) : b.car ≤ (a + b).car := le_sup_right

/-- Every subring is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : SubringCMRA R) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubringCMRA R)) a

/-- Combining `⊥` and `⊤` in the `SubringCMRA` yields `⊤`. -/
example : (⟨⊥⟩ + ⟨⊤⟩ : SubringCMRA ℤ) = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.Subring ℤ) ⊔ ⊤⟩ : SubringCMRA ℤ) = ⟨⊤⟩
  rw [bot_sup_eq]

/-- The `UCMRA` instance on `SubringCMRA` is inferrable. -/
example : UCMRA (SubringCMRA ℤ) := inferInstance

/-- The unit is a left identity under the CMRA operation. -/
example (a : SubringCMRA ℤ) : 0 + a = a :=
  Std.LawfulLeftIdentity.left_id (op := Add.add (α := SubringCMRA ℤ)) a

end SubringCMRA

end IrisMath.Subring

namespace IrisMath.Subsemiring

/-! ## (B) Subsemirings under sup -/

/-- Subsemirings of a semiring `R` as a UCMRA under join (`⊔`), with unit `⊥`
(the bottom subsemiring). -/
def SubsemiringCMRA (R : Type _) [Semiring R] : Type _ := LeibnizO (_root_.Subsemiring R)

namespace SubsemiringCMRA

variable {R : Type _} [Semiring R]

instance : COFE (SubsemiringCMRA R) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubsemiringCMRA R) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubsemiringCMRA R) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: subsemiring join. -/
instance : Add (SubsemiringCMRA R) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the bottom subsemiring. -/
instance : Zero (SubsemiringCMRA R) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubsemiringCMRA R) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubsemiringCMRA R) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubsemiringCMRA R)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubsemiringCMRA R)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubsemiringCMRA R)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubsemiringCMRA R) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubsemiringCMRA R)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubsemiringCMRA R) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubsemiringCMRA R))
    (0 : SubsemiringCMRA R) where
  left_id a :=
    show (⟨(⊥ : _root_.Subsemiring R) ⊔ a.car⟩ : SubsemiringCMRA R) = a by
      cases a
      simp

instance : CMRA (SubsemiringCMRA R) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubsemiringCMRA R) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubsemiringCMRA R) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every subsemiring is its own core. -/
theorem coreId (a : SubsemiringCMRA R) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : SubsemiringCMRA R) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubsemiringCMRA R) : b.car ≤ (a + b).car := le_sup_right

/-- Every subsemiring is its own core. -/
theorem op_self (a : SubsemiringCMRA R) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubsemiringCMRA R)) a

/-- Combining `⊥` and `⊤` in the `SubsemiringCMRA` yields `⊤`. -/
example : (⟨⊥⟩ + ⟨⊤⟩ : SubsemiringCMRA ℕ) = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.Subsemiring ℕ) ⊔ ⊤⟩ : SubsemiringCMRA ℕ) = ⟨⊤⟩
  rw [bot_sup_eq]

/-- The `UCMRA` instance on `SubsemiringCMRA` is inferrable. -/
example : UCMRA (SubsemiringCMRA ℕ) := inferInstance

/-- The unit is a left identity under the CMRA operation. -/
example (a : SubsemiringCMRA ℕ) : 0 + a = a :=
  Std.LawfulLeftIdentity.left_id (op := Add.add (α := SubsemiringCMRA ℕ)) a

end SubsemiringCMRA

end IrisMath.Subsemiring

namespace IrisMath.Subfield

/-! ## (C) Subfields under sup -/

/-- Subfields of a field `K` as a UCMRA under join (`⊔`), with unit `⊥` (the
prime subfield). -/
def SubfieldCMRA (K : Type _) [Field K] : Type _ := LeibnizO (_root_.Subfield K)

namespace SubfieldCMRA

variable {K : Type _} [Field K]

instance : COFE (SubfieldCMRA K) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubfieldCMRA K) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubfieldCMRA K) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: subfield join. -/
instance : Add (SubfieldCMRA K) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the bottom subfield (the prime subfield). -/
instance : Zero (SubfieldCMRA K) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubfieldCMRA K) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubfieldCMRA K) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubfieldCMRA K)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubfieldCMRA K)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubfieldCMRA K)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubfieldCMRA K) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubfieldCMRA K)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubfieldCMRA K) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubfieldCMRA K)) (0 : SubfieldCMRA K) where
  left_id a :=
    show (⟨(⊥ : _root_.Subfield K) ⊔ a.car⟩ : SubfieldCMRA K) = a by
      cases a
      simp

instance : CMRA (SubfieldCMRA K) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubfieldCMRA K) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubfieldCMRA K) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every subfield is its own core. -/
theorem coreId (a : SubfieldCMRA K) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : SubfieldCMRA K) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubfieldCMRA K) : b.car ≤ (a + b).car := le_sup_right

/-- Every subfield is its own core. -/
theorem op_self (a : SubfieldCMRA K) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubfieldCMRA K)) a

/-- Combining `⊥` and `⊤` in the `SubfieldCMRA` yields `⊤`. -/
example : (⟨⊥⟩ + ⟨⊤⟩ : SubfieldCMRA ℚ) = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.Subfield ℚ) ⊔ ⊤⟩ : SubfieldCMRA ℚ) = ⟨⊤⟩
  rw [bot_sup_eq]

/-- The `UCMRA` instance on `SubfieldCMRA` is inferrable. -/
example : UCMRA (SubfieldCMRA ℚ) := inferInstance

/-- The unit is a left identity under the CMRA operation. -/
example (a : SubfieldCMRA ℚ) : 0 + a = a :=
  Std.LawfulLeftIdentity.left_id (op := Add.add (α := SubfieldCMRA ℚ)) a

end SubfieldCMRA

end IrisMath.Subfield

namespace IrisMath.Subalgebra

/-! ## (D) Subalgebras under sup -/

/-- `R`-subalgebras of an `R`-algebra `A` as a UCMRA under join (`⊔`), with
unit `⊥` (the image of `R` in `A`). -/
def SubalgebraCMRA (R : Type _) (A : Type _) [CommSemiring R] [Semiring A] [Algebra R A] :
    Type _ :=
  LeibnizO (_root_.Subalgebra R A)

namespace SubalgebraCMRA

variable {R : Type _} {A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

instance : COFE (SubalgebraCMRA R A) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubalgebraCMRA R A) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubalgebraCMRA R A) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: subalgebra join. -/
instance : Add (SubalgebraCMRA R A) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the bottom subalgebra (the image of `R`). -/
instance : Zero (SubalgebraCMRA R A) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubalgebraCMRA R A) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubalgebraCMRA R A) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubalgebraCMRA R A)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubalgebraCMRA R A)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubalgebraCMRA R A)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubalgebraCMRA R A) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubalgebraCMRA R A)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubalgebraCMRA R A) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubalgebraCMRA R A))
    (0 : SubalgebraCMRA R A) where
  left_id a :=
    show (⟨(⊥ : _root_.Subalgebra R A) ⊔ a.car⟩ : SubalgebraCMRA R A) = a by
      cases a
      simp

instance : CMRA (SubalgebraCMRA R A) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubalgebraCMRA R A) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubalgebraCMRA R A) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every subalgebra is its own core. -/
theorem coreId (a : SubalgebraCMRA R A) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : SubalgebraCMRA R A) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubalgebraCMRA R A) : b.car ≤ (a + b).car := le_sup_right

/-- Every subalgebra is its own core. -/
theorem op_self (a : SubalgebraCMRA R A) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubalgebraCMRA R A)) a

/-- Combining `⊥` and `⊤` in the `SubalgebraCMRA` yields `⊤`. -/
example : (⟨⊥⟩ + ⟨⊤⟩ : SubalgebraCMRA ℚ ℚ) = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.Subalgebra ℚ ℚ) ⊔ ⊤⟩ : SubalgebraCMRA ℚ ℚ) = ⟨⊤⟩
  rw [bot_sup_eq]

/-- The `UCMRA` instance on `SubalgebraCMRA` is inferrable. -/
example : UCMRA (SubalgebraCMRA ℚ ℚ) := inferInstance

/-- The unit is a left identity under the CMRA operation. -/
example (a : SubalgebraCMRA ℚ ℚ) : 0 + a = a :=
  Std.LawfulLeftIdentity.left_id (op := Add.add (α := SubalgebraCMRA ℚ ℚ)) a

end SubalgebraCMRA

end IrisMath.Subalgebra
