/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sets.Compacts
public import Iris

@[expose] public section

/-!
# Compact sets as an idempotent UCMRA

`TopologicalSpace.Compacts X` carries a `SemilatticeSup` and `OrderBot`
structure in Mathlib: the compact subsets of any topological space are ordered
by inclusion, the join `⊔` is union (a finite union of compact sets is
compact), and the bottom element `⊥` is the empty compact set. Unlike opens
and closeds the meet (intersection) is not generally available — an arbitrary
intersection of compact sets need not be compact without further hypotheses
on `X` (e.g. Hausdorff).

We expose the resulting bounded join-semilattice as an idempotent UCMRA:

* `CompactsCMRA X`: compacts under supremum (union), unit `⊥` (the empty
  compact set). Intuition: each element is a "compact region", and combining
  two regions yields their (compact) union.

This sits alongside `IrisMath.Opens.OpensCMRA` and
`IrisMath.Opens.ClosedsCMRA`. As for those, the carrier is wrapped in
`LeibnizO` (discrete + Leibniz OFE) and the UCMRA structure comes from the
`OrdCommMonoidLike` recipe, surfaced by directly referencing the underlying
scoped instance names (`OrdCommMonoidLike.instCMRA` etc.).
-/

open Iris OFE CMRA Std TopologicalSpace

namespace IrisMath.Compacts

/-- Compact sets of a topological space `X` as a UCMRA under supremum (`⊔`),
with unit `⊥` (the empty compact set). The operation `K + L` is the union of
the underlying compacts (which is again compact), and every compact is its
own core. -/
def CompactsCMRA (X : Type _) [TopologicalSpace X] : Type _ :=
  LeibnizO (TopologicalSpace.Compacts X)

namespace CompactsCMRA

variable {X : Type _} [TopologicalSpace X]

instance : COFE (CompactsCMRA X) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (CompactsCMRA X) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (CompactsCMRA X) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: union of compact sets (the lattice join in
`TopologicalSpace.Compacts X`). -/
instance : Add (CompactsCMRA X) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the empty compact set `⊥`. -/
instance : Zero (CompactsCMRA X) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : CompactsCMRA X) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : CompactsCMRA X) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := CompactsCMRA X)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : CompactsCMRA X)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := CompactsCMRA X)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : CompactsCMRA X) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := CompactsCMRA X)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : CompactsCMRA X) = a by
      cases a
      exact congrArg _ (sup_idem _)

instance : Std.LawfulLeftIdentity (Add.add (α := CompactsCMRA X)) (0 : CompactsCMRA X) where
  left_id a :=
    show (⟨(⊥ : TopologicalSpace.Compacts X) ⊔ a.car⟩ : CompactsCMRA X) = a by
      cases a
      exact congrArg _ (bot_sup_eq _)

instance : CMRA (CompactsCMRA X) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (CompactsCMRA X) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (CompactsCMRA X) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every compact set is its own core. -/
example (a : CompactsCMRA X) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the lattice of compacts:
`a ≤ a + b`. -/
theorem le_op_left (a b : CompactsCMRA X) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : CompactsCMRA X) : b.car ≤ (a + b).car := le_sup_right

/-- Every compact set is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : CompactsCMRA X) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := CompactsCMRA X)) a

/-- Sanity example: two compacts combine via `+` to their union. -/
example (K L : TopologicalSpace.Compacts X) :
    (show CompactsCMRA X from ⟨K⟩) + (show CompactsCMRA X from ⟨L⟩)
      = (show CompactsCMRA X from ⟨K ⊔ L⟩) := rfl

end CompactsCMRA

end IrisMath.Compacts
