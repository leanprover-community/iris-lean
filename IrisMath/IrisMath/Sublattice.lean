/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Sublattice
public import Iris

@[expose] public section

/-!
# Sublattice CMRAs

Idempotent UCMRAs harvested from the `CompleteLattice` structure on Mathlib's
`Sublattice L`. This is the order-theoretic sibling of `SubgroupCMRA` in
`IrisMath.Subgroup` and `SubmoduleCMRA` in `IrisMath.LatticeCMRAs`.

## Main definitions

* `SublatticeCMRA L`: sublattices of a lattice `L` under supremum (unit `⊥`).

## Recipe

The carrier is wrapped in `LeibnizO` (discrete + Leibniz OFE) and we instantiate
the `OrdCommMonoidLike` recipe from `Iris/Algebra/Numbers.lean`. That recipe
surfaces a UCMRA whose `pcore` is `some` (every element is its own core) and
whose `Valid`/`ValidN` are trivially `True`. Concretely:

1. transport `COFE` / `OFE.Discrete` / `OFE.Leibniz` from `LeibnizO`;
2. define `Add` as the lattice join `⊔` and `Zero` as the bottom sublattice `⊥`
   (which for `Sublattice` is the empty sublattice);
3. prove the algebraic laws (`Associative`, `Commutative`, `IdempotentOp`,
   `LawfulLeftIdentity`) by transporting the underlying `CompleteLattice` laws;
4. use `OrdCommMonoidLike.instCMRA` etc. to obtain `CMRA`, `CMRA.Discrete`,
   and `UCMRA`.

Because the relevant `OrdCommMonoidLike` instances are declared `scoped`, the
ambient `inferInstance` machinery does not see them through `open`; we therefore
reference the underlying instance names (`instCMRA`, `instDiscrete`,
`instUCMRAOfLawfulLeftIdentityAddZero`, `instCoreId`) directly, mirroring the
style used in `IrisMath.Subgroup` and `IrisMath.LatticeCMRAs`.
-/

open Iris OFE CMRA Std

namespace IrisMath.Sublattice

/-! ## Sublattices under sup -/

/-- Sublattices of a lattice `L` as a UCMRA under join (`⊔`), with unit `⊥`
(the empty sublattice). The operation is "the smallest sublattice containing
both", and every sublattice is its own core. -/
def SublatticeCMRA (L : Type _) [Lattice L] : Type _ := LeibnizO (_root_.Sublattice L)

namespace SublatticeCMRA

variable {L : Type _} [Lattice L]

instance : COFE (SublatticeCMRA L) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SublatticeCMRA L) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SublatticeCMRA L) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: sublattice join. -/
instance : Add (SublatticeCMRA L) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the empty sublattice. -/
instance : Zero (SublatticeCMRA L) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SublatticeCMRA L) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SublatticeCMRA L) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SublatticeCMRA L)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SublatticeCMRA L)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SublatticeCMRA L)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SublatticeCMRA L) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SublatticeCMRA L)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SublatticeCMRA L) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SublatticeCMRA L)) (0 : SublatticeCMRA L) where
  left_id a :=
    show (⟨(⊥ : _root_.Sublattice L) ⊔ a.car⟩ : SublatticeCMRA L) = a by
      cases a
      simp

instance : CMRA (SublatticeCMRA L) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SublatticeCMRA L) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SublatticeCMRA L) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every sublattice is its own core. -/
theorem coreId (a : SublatticeCMRA L) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the sublattice lattice:
`a ≤ a + b`. -/
theorem le_op_left (a b : SublatticeCMRA L) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SublatticeCMRA L) : b.car ≤ (a + b).car := le_sup_right

/-- Every sublattice is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : SublatticeCMRA L) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SublatticeCMRA L)) a

end SublatticeCMRA

end IrisMath.Sublattice
