/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.Order.Filter.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Iris

@[expose] public section

/-!
# Lattice CMRAs

Idempotent UCMRAs harvested from Mathlib (semi)lattice / GCD structure.

## Main definitions

* `GCDCMRA α`: a `CommMonoidWithZero` with a `NormalizedGCDMonoid` structure and a
  trivial unit group, under `gcd` (unit `0`). Specializes to `Nat` and to
  `PNat`-flavored normalized GCD monoids.
* `GCDNat`: the legacy `Nat`-specific instance, kept as an alias for `GCDCMRA Nat`.
* `FilterCMRA α`: filters on `α` under infimum (unit `⊤`).
* `SubmoduleCMRA R M`: submodules of an `R`-module under supremum (unit `⊥`).
* `IdealCMRA R`: ideals of a semiring `R`, i.e. `SubmoduleCMRA R R`.

## Recipe

In each case the carrier is wrapped in `LeibnizO` (discrete + Leibniz OFE) and we
instantiate the `OrdCommMonoidLike` recipe from `Iris/Algebra/Numbers.lean`. That
recipe surfaces a UCMRA whose `pcore` is `some` (every element is its own core)
and whose `Valid`/`ValidN` are trivially `True`.

Because the relevant `OrdCommMonoidLike` instances are declared `scoped`, the
ambient `inferInstance` machinery does not see them through `open`; we therefore
reference the underlying instance names (`instCMRA`, `instDiscrete`,
`instUCMRAOfLawfulLeftIdentityAddZero`, `instCoreId`) directly, mirroring the
style used in `Iris/Instances/Lib/LaterCredits.lean`.

## Related files

The same recipe produces UCMRAs from other Mathlib sublattice / topological /
measure-theoretic structures:

* `IrisMath.Subgroup` — `SubgroupCMRA`, `AddSubgroupCMRA`, `SubmonoidCMRA`,
  `AddSubmonoidCMRA` (sub-(monoid|group) lattices under `⊔`).
* `IrisMath.Subring` — subring lattice under `⊔`.
* `IrisMath.Sublattice` — sublattice lattice under `⊔`.
* `IrisMath.Setoid` — equivalence relations under `⊔`.
* `IrisMath.SigmaAlgebra` — σ-algebras on a measurable space under `⊔`.
* `IrisMath.TopologicalSpace` — topologies on a type under `⊔`.
* `IrisMath.Opens` — open sets of a topological space under `⊔`.
-/

open Iris OFE CMRA Std

namespace IrisMath.Lattice

/-! ## (A) GCD under `NormalizedGCDMonoid` -/

/-- The carrier of the GCD CMRA: a `CommMonoidWithZero` `α` equipped with a
`NormalizedGCDMonoid` structure and a subsingleton unit group, wrapped in
`LeibnizO`. The Subsingleton-on-units hypothesis pins `normalize` to the
identity, which is what makes `gcd a a = a` and `gcd 0 a = a` (rather than
merely up to normalization). Both hold for `Nat`. -/
def GCDCMRA (α : Type*) [CommMonoidWithZero α] [NormalizedGCDMonoid α]
    [Subsingleton αˣ] : Type _ := LeibnizO α

namespace GCDCMRA

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α] [Subsingleton αˣ]

instance : COFE (GCDCMRA α) := inferInstanceAs (COFE (LeibnizO α))
instance : OFE.Discrete (GCDCMRA α) := inferInstanceAs (OFE.Discrete (LeibnizO α))
instance : OFE.Leibniz (GCDCMRA α) := inferInstanceAs (OFE.Leibniz (LeibnizO α))

/-- The CMRA operation: greatest common divisor. -/
instance : Add (GCDCMRA α) := ⟨fun a b ↦ ⟨gcd a.car b.car⟩⟩

/-- The CMRA unit: `0`. (For `NormalizedGCDMonoid`s, `gcd 0 a = a`.) -/
instance : Zero (GCDCMRA α) := ⟨⟨0⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : GCDCMRA α) : a + b = ⟨gcd a.car b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : GCDCMRA α) = ⟨0⟩ := rfl

/-- Helper: with `Subsingleton αˣ`, `normalize` is the identity. -/
private theorem normalize_eq' (a : α) : a * (normUnit a : α) = a := by
  rw [Subsingleton.elim (normUnit a) 1, Units.val_one, mul_one]

instance : Std.Associative (Add.add (α := GCDCMRA α)) where
  assoc a b c :=
    show (⟨gcd (gcd a.car b.car) c.car⟩ : GCDCMRA α)
        = ⟨gcd a.car (gcd b.car c.car)⟩ by
      rw [gcd_assoc]

instance : Std.Commutative (Add.add (α := GCDCMRA α)) where
  comm a b :=
    show (⟨gcd a.car b.car⟩ : GCDCMRA α) = ⟨gcd b.car a.car⟩ by
      rw [gcd_comm]

instance : Std.IdempotentOp (Add.add (α := GCDCMRA α)) where
  idempotent a :=
    show (⟨gcd a.car a.car⟩ : GCDCMRA α) = a by
      cases a with
      | mk x => exact congrArg _ (by rw [gcd_same]; exact normalize_eq' x)

instance : Std.LawfulLeftIdentity (Add.add (α := GCDCMRA α)) (0 : GCDCMRA α) where
  left_id a :=
    show (⟨gcd 0 a.car⟩ : GCDCMRA α) = a by
      cases a with
      | mk x => exact congrArg _ (by rw [gcd_zero_left]; exact normalize_eq' x)

instance : CMRA (GCDCMRA α) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (GCDCMRA α) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (GCDCMRA α) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every element is its own core. -/
theorem coreId (a : GCDCMRA α) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation refines knowledge in the divisibility lattice: the
operation `a + b = gcd a b` divides `a`. This shows the `+` is the "knowledge
meet" in the divisibility preorder. -/
theorem op_dvd_left (a b : GCDCMRA α) : (a + b).car ∣ a.car := gcd_dvd_left _ _

/-- Symmetrically, `a + b` divides `b`. -/
theorem op_dvd_right (a b : GCDCMRA α) : (a + b).car ∣ b.car := gcd_dvd_right _ _

/-- The operation is idempotent: `a + a = a` because `gcd a a = a`. -/
theorem op_self (a : GCDCMRA α) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := GCDCMRA α)) a

end GCDCMRA

/-- Legacy alias: the natural numbers as a UCMRA under `Nat.gcd`. -/
abbrev GCDNat : Type := GCDCMRA Nat

namespace GCDNat

/-- Unfolding lemma matching the original `Nat.gcd`-flavored statement. -/
theorem add_def (a b : GCDNat) : a + b = ⟨Nat.gcd a.car b.car⟩ := rfl

/-- The unit is `0`. -/
theorem zero_def : (0 : GCDNat) = ⟨0⟩ := rfl

end GCDNat

/-! ## (B) Filter under infimum -/

/-- Filters on `α` as a UCMRA under infimum (`⊓`), with unit `⊤` (the universal
filter). The operation is "the coarsest filter refining both", and every filter
is its own core. -/
def FilterCMRA (α : Type _) : Type _ := LeibnizO (_root_.Filter α)

namespace FilterCMRA

variable {α : Type _}

instance : COFE (FilterCMRA α) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (FilterCMRA α) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (FilterCMRA α) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: filter infimum. -/
instance : Add (FilterCMRA α) := ⟨fun a b ↦ ⟨a.car ⊓ b.car⟩⟩

/-- The CMRA unit: `⊤`, the universal filter. -/
instance : Zero (FilterCMRA α) := ⟨⟨⊤⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : FilterCMRA α) : a + b = ⟨a.car ⊓ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : FilterCMRA α) = ⟨⊤⟩ := rfl

instance : Std.Associative (Add.add (α := FilterCMRA α)) where
  assoc a b c :=
    show (⟨(a.car ⊓ b.car) ⊓ c.car⟩ : FilterCMRA α) = ⟨a.car ⊓ (b.car ⊓ c.car)⟩ by
      rw [inf_assoc]

instance : Std.Commutative (Add.add (α := FilterCMRA α)) where
  comm a b :=
    show (⟨a.car ⊓ b.car⟩ : FilterCMRA α) = ⟨b.car ⊓ a.car⟩ by
      rw [inf_comm]

instance : Std.IdempotentOp (Add.add (α := FilterCMRA α)) where
  idempotent a :=
    show (⟨a.car ⊓ a.car⟩ : FilterCMRA α) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := FilterCMRA α)) (0 : FilterCMRA α) where
  left_id a :=
    show (⟨(⊤ : _root_.Filter α) ⊓ a.car⟩ : FilterCMRA α) = a by
      cases a
      simp

instance : CMRA (FilterCMRA α) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (FilterCMRA α) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (FilterCMRA α) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every filter is its own core. -/
theorem coreId (a : FilterCMRA α) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation refines both arguments: `a + b ≤ a` in the filter order
(filter refinement). -/
theorem op_le_left (a b : FilterCMRA α) : (a + b).car ≤ a.car := inf_le_left

/-- Symmetric companion to `op_le_left`. -/
theorem op_le_right (a b : FilterCMRA α) : (a + b).car ≤ b.car := inf_le_right

/-- The operation is idempotent: `a + a = a` because filter infimum is. -/
theorem op_self (a : FilterCMRA α) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := FilterCMRA α)) a

end FilterCMRA

/-! ## (C) Submodule lattice under sup -/

/-- Submodules of an `R`-module `M` as a UCMRA under sum (`⊔`), with unit `⊥`.
The operation corresponds to "what subspace has been verified", and every
submodule is its own core. -/
def SubmoduleCMRA (R M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] : Type _ :=
  LeibnizO (Submodule R M)

namespace SubmoduleCMRA

variable {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]

instance : COFE (SubmoduleCMRA R M) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubmoduleCMRA R M) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubmoduleCMRA R M) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: submodule sum (lattice join). -/
instance : Add (SubmoduleCMRA R M) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the zero submodule. -/
instance : Zero (SubmoduleCMRA R M) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubmoduleCMRA R M) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubmoduleCMRA R M) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubmoduleCMRA R M)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubmoduleCMRA R M)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubmoduleCMRA R M)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubmoduleCMRA R M) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubmoduleCMRA R M)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubmoduleCMRA R M) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubmoduleCMRA R M)) (0 : SubmoduleCMRA R M) where
  left_id a :=
    show (⟨(⊥ : Submodule R M) ⊔ a.car⟩ : SubmoduleCMRA R M) = a by
      cases a
      simp

instance : CMRA (SubmoduleCMRA R M) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubmoduleCMRA R M) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubmoduleCMRA R M) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every submodule is its own core. -/
theorem coreId (a : SubmoduleCMRA R M) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the submodule lattice:
`a ≤ a + b`. -/
theorem le_op_left (a b : SubmoduleCMRA R M) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubmoduleCMRA R M) : b.car ≤ (a + b).car := le_sup_right

/-- The operation is idempotent: `a + a = a` because submodule join is. -/
theorem op_self (a : SubmoduleCMRA R M) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubmoduleCMRA R M)) a

end SubmoduleCMRA

/-! ## (D) Ideals of a semiring -/

/-- Ideals of a (semi)ring `R` as a UCMRA under sum, with unit the zero ideal.
This is `SubmoduleCMRA R R` since `Ideal R = Submodule R R` in Mathlib. -/
abbrev IdealCMRA (R : Type _) [Semiring R] : Type _ := SubmoduleCMRA R R

namespace IdealCMRA

variable {R : Type _} [Semiring R]

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : IdealCMRA R) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : IdealCMRA R) = ⟨⊥⟩ := rfl

/-- An ideal is below the operation result, in the ideal lattice. -/
theorem le_op_left (a b : IdealCMRA R) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : IdealCMRA R) : b.car ≤ (a + b).car := le_sup_right

/-- Every ideal is its own core. -/
theorem coreId (a : IdealCMRA R) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The operation is idempotent: `a + a = a` because ideal join is. -/
theorem op_self (a : IdealCMRA R) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := IdealCMRA R)) a

end IdealCMRA

end IrisMath.Lattice
