/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Iris

@[expose] public section

/-!
# Subgroup CMRAs

Idempotent UCMRAs harvested from the `CompleteLattice` structure on Mathlib's
subobject lattices. This is the group-theoretic sibling of `SubmoduleCMRA` in
`IrisMath.LatticeCMRAs`.

## Main definitions

* `SubgroupCMRA G`: subgroups of a group `G` under supremum (unit `⊥`).
* `AddSubgroupCMRA G`: additive subgroups of an additive group `G` under
  supremum (unit `⊥`).
* `SubmonoidCMRA M`: submonoids of a monoid `M` under supremum (unit `⊥`).
* `AddSubmonoidCMRA M`: additive submonoids of an additive monoid `M` under
  supremum (unit `⊥`).

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
style used in `IrisMath.LatticeCMRAs`.

## TODO

The four constructions below are structurally identical. A future refactor
should subsume them (along with `SubmoduleCMRA`, `FilterCMRA`, `Opens`,
`SigmaAlgebra`, ...) under a single generic `LatticeUCMRA L` parameterised by
`[CompleteLattice L]`, with the existing names becoming `abbrev`s. That change
necessarily touches every consumer of these CMRAs and is intentionally deferred.
-/

open Iris OFE CMRA Std

namespace IrisMath.Subgroup

/-! ## (A) Subgroups under sup -/

/-- Subgroups of a group `G` as a UCMRA under join (`⊔`), with unit `⊥` (the
trivial subgroup). The operation is "the smallest subgroup containing both",
and every subgroup is its own core. -/
def SubgroupCMRA (G : Type _) [Group G] : Type _ := LeibnizO (_root_.Subgroup G)

namespace SubgroupCMRA

variable {G : Type _} [Group G]

instance : COFE (SubgroupCMRA G) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubgroupCMRA G) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubgroupCMRA G) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: subgroup join. -/
instance : Add (SubgroupCMRA G) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the trivial subgroup `{1}`. -/
instance : Zero (SubgroupCMRA G) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubgroupCMRA G) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubgroupCMRA G) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubgroupCMRA G)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubgroupCMRA G)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubgroupCMRA G)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubgroupCMRA G) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubgroupCMRA G)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubgroupCMRA G) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubgroupCMRA G)) (0 : SubgroupCMRA G) where
  left_id a :=
    show (⟨(⊥ : _root_.Subgroup G) ⊔ a.car⟩ : SubgroupCMRA G) = a by
      cases a
      simp

instance : CMRA (SubgroupCMRA G) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubgroupCMRA G) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubgroupCMRA G) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every subgroup is its own core. -/
theorem coreId (a : SubgroupCMRA G) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the subgroup lattice:
`a ≤ a + b`. -/
theorem le_op_left (a b : SubgroupCMRA G) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubgroupCMRA G) : b.car ≤ (a + b).car := le_sup_right

/-- Every subgroup is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : SubgroupCMRA G) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubgroupCMRA G)) a

end SubgroupCMRA

/-! ## (B) Additive subgroups under sup -/

/-- Additive subgroups of an additive group `G` as a UCMRA under join (`⊔`),
with unit `⊥` (the trivial subgroup). -/
def AddSubgroupCMRA (G : Type _) [AddGroup G] : Type _ := LeibnizO (_root_.AddSubgroup G)

namespace AddSubgroupCMRA

variable {G : Type _} [AddGroup G]

instance : COFE (AddSubgroupCMRA G) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (AddSubgroupCMRA G) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (AddSubgroupCMRA G) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: additive-subgroup join. -/
instance : Add (AddSubgroupCMRA G) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the trivial additive subgroup `{0}`. -/
instance : Zero (AddSubgroupCMRA G) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : AddSubgroupCMRA G) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : AddSubgroupCMRA G) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := AddSubgroupCMRA G)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : AddSubgroupCMRA G)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := AddSubgroupCMRA G)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : AddSubgroupCMRA G) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := AddSubgroupCMRA G)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : AddSubgroupCMRA G) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := AddSubgroupCMRA G))
    (0 : AddSubgroupCMRA G) where
  left_id a :=
    show (⟨(⊥ : _root_.AddSubgroup G) ⊔ a.car⟩ : AddSubgroupCMRA G) = a by
      cases a
      simp

instance : CMRA (AddSubgroupCMRA G) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (AddSubgroupCMRA G) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (AddSubgroupCMRA G) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every additive subgroup is its own core. -/
theorem coreId (a : AddSubgroupCMRA G) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : AddSubgroupCMRA G) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : AddSubgroupCMRA G) : b.car ≤ (a + b).car := le_sup_right

/-- Every additive subgroup is its own core. -/
theorem op_self (a : AddSubgroupCMRA G) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := AddSubgroupCMRA G)) a

end AddSubgroupCMRA

/-! ## (C) Submonoids under sup -/

/-- Submonoids of a monoid `M` as a UCMRA under join (`⊔`), with unit `⊥` (the
trivial submonoid `{1}`). -/
def SubmonoidCMRA (M : Type _) [Monoid M] : Type _ := LeibnizO (_root_.Submonoid M)

namespace SubmonoidCMRA

variable {M : Type _} [Monoid M]

instance : COFE (SubmonoidCMRA M) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SubmonoidCMRA M) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SubmonoidCMRA M) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: submonoid join. -/
instance : Add (SubmonoidCMRA M) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the trivial submonoid `{1}`. -/
instance : Zero (SubmonoidCMRA M) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SubmonoidCMRA M) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SubmonoidCMRA M) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SubmonoidCMRA M)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SubmonoidCMRA M)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SubmonoidCMRA M)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SubmonoidCMRA M) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SubmonoidCMRA M)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SubmonoidCMRA M) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SubmonoidCMRA M)) (0 : SubmonoidCMRA M) where
  left_id a :=
    show (⟨(⊥ : _root_.Submonoid M) ⊔ a.car⟩ : SubmonoidCMRA M) = a by
      cases a
      simp

instance : CMRA (SubmonoidCMRA M) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SubmonoidCMRA M) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SubmonoidCMRA M) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every submonoid is its own core. -/
theorem coreId (a : SubmonoidCMRA M) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : SubmonoidCMRA M) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SubmonoidCMRA M) : b.car ≤ (a + b).car := le_sup_right

/-- Every submonoid is its own core. -/
theorem op_self (a : SubmonoidCMRA M) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SubmonoidCMRA M)) a

end SubmonoidCMRA

/-! ## (D) Additive submonoids under sup -/

/-- Additive submonoids of an additive monoid `M` as a UCMRA under join (`⊔`),
with unit `⊥` (the trivial additive submonoid `{0}`). -/
def AddSubmonoidCMRA (M : Type _) [AddMonoid M] : Type _ := LeibnizO (_root_.AddSubmonoid M)

namespace AddSubmonoidCMRA

variable {M : Type _} [AddMonoid M]

instance : COFE (AddSubmonoidCMRA M) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (AddSubmonoidCMRA M) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (AddSubmonoidCMRA M) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: additive-submonoid join. -/
instance : Add (AddSubmonoidCMRA M) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the trivial additive submonoid `{0}`. -/
instance : Zero (AddSubmonoidCMRA M) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : AddSubmonoidCMRA M) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : AddSubmonoidCMRA M) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := AddSubmonoidCMRA M)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : AddSubmonoidCMRA M)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := AddSubmonoidCMRA M)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : AddSubmonoidCMRA M) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := AddSubmonoidCMRA M)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : AddSubmonoidCMRA M) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := AddSubmonoidCMRA M))
    (0 : AddSubmonoidCMRA M) where
  left_id a :=
    show (⟨(⊥ : _root_.AddSubmonoid M) ⊔ a.car⟩ : AddSubmonoidCMRA M) = a by
      cases a
      simp

instance : CMRA (AddSubmonoidCMRA M) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (AddSubmonoidCMRA M) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (AddSubmonoidCMRA M) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every additive submonoid is its own core. -/
theorem coreId (a : AddSubmonoidCMRA M) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument: `a ≤ a + b`. -/
theorem le_op_left (a b : AddSubmonoidCMRA M) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : AddSubmonoidCMRA M) : b.car ≤ (a + b).car := le_sup_right

/-- Every additive submonoid is its own core. -/
theorem op_self (a : AddSubmonoidCMRA M) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := AddSubmonoidCMRA M)) a

end AddSubmonoidCMRA

end IrisMath.Subgroup
