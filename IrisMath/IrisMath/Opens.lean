/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sets.Closeds
public import Iris

@[expose] public section

/-!
# Open and closed sets as idempotent UCMRAs

`TopologicalSpace.Opens X` and `TopologicalSpace.Closeds X` each carry a
`CompleteLattice` structure in Mathlib: the open (resp. closed) sets of a
topological space `X` are ordered by inclusion. For `Opens X` the supremum is
union (open) and the infimum is the interior of the intersection. For
`Closeds X` the supremum is again union (a finite union of closed sets is
closed) and the infimum is intersection (arbitrary intersections of closed
sets are closed).

We expose these join-semilattices with `⊥` as idempotent UCMRAs:

* `OpensCMRA X`: opens under supremum (union), unit `⊥` (the empty open set).
  Intuition: each element is a region "already opened", and combining two
  regions yields their union.
* `ClosedsCMRA X`: closeds under supremum (union), unit `⊥` (the empty closed
  set). Intuition: each element is a region "already closed off", and
  combining two regions yields their union.

These are the topological analogues of `IrisMath.Lattice.SubmoduleCMRA` and
`IrisMath.Subgroup.SubgroupCMRA`. As for those, the carrier is wrapped in
`LeibnizO` (discrete + Leibniz OFE) and the UCMRA structure comes from the
`OrdCommMonoidLike` recipe, surfaced by directly referencing the underlying
scoped instance names (`OrdCommMonoidLike.instCMRA` etc.).
-/

open Iris OFE CMRA Std TopologicalSpace

namespace IrisMath.Opens

/-! ## (A) Open sets under union -/

/-- Open sets of a topological space `X` as a UCMRA under supremum (`⊔`), with
unit `⊥` (the empty open set). The operation `U + V` is the union of the
underlying opens (which is again open), and every open is its own core. -/
def OpensCMRA (X : Type _) [TopologicalSpace X] : Type _ :=
  LeibnizO (TopologicalSpace.Opens X)

namespace OpensCMRA

variable {X : Type _} [TopologicalSpace X]

instance : COFE (OpensCMRA X) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (OpensCMRA X) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (OpensCMRA X) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: union of open sets (the lattice join in
`TopologicalSpace.Opens X`). -/
instance : Add (OpensCMRA X) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the empty open set `⊥`. -/
instance : Zero (OpensCMRA X) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : OpensCMRA X) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : OpensCMRA X) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := OpensCMRA X)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : OpensCMRA X)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := OpensCMRA X)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : OpensCMRA X) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := OpensCMRA X)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : OpensCMRA X) = a by
      cases a
      exact congrArg _ (sup_idem _)

instance : Std.LawfulLeftIdentity (Add.add (α := OpensCMRA X)) (0 : OpensCMRA X) where
  left_id a :=
    show (⟨(⊥ : TopologicalSpace.Opens X) ⊔ a.car⟩ : OpensCMRA X) = a by
      cases a
      exact congrArg _ (bot_sup_eq _)

instance : CMRA (OpensCMRA X) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (OpensCMRA X) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (OpensCMRA X) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every open set is its own core. -/
example (a : OpensCMRA X) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the lattice of opens:
`a ≤ a + b`. -/
theorem le_op_left (a b : OpensCMRA X) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : OpensCMRA X) : b.car ≤ (a + b).car := le_sup_right

/-- Every open set is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : OpensCMRA X) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := OpensCMRA X)) a

/-- Sanity example: two opens combine via `+` to their union. -/
example (U V : TopologicalSpace.Opens X) :
    (show OpensCMRA X from ⟨U⟩) + (show OpensCMRA X from ⟨V⟩)
      = (show OpensCMRA X from ⟨U ⊔ V⟩) := rfl

end OpensCMRA

/-! ## (B) Closed sets under union -/

/-- Closed sets of a topological space `X` as a UCMRA under supremum (`⊔`),
with unit `⊥` (the empty closed set). The operation `C + D` is the union of
the underlying closeds (a finite union of closed sets is closed), and every
closed is its own core. -/
def ClosedsCMRA (X : Type _) [TopologicalSpace X] : Type _ :=
  LeibnizO (TopologicalSpace.Closeds X)

namespace ClosedsCMRA

variable {X : Type _} [TopologicalSpace X]

instance : COFE (ClosedsCMRA X) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (ClosedsCMRA X) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (ClosedsCMRA X) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: union of closed sets (the lattice join in
`TopologicalSpace.Closeds X`). -/
instance : Add (ClosedsCMRA X) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the empty closed set `⊥`. -/
instance : Zero (ClosedsCMRA X) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : ClosedsCMRA X) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : ClosedsCMRA X) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := ClosedsCMRA X)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : ClosedsCMRA X)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := ClosedsCMRA X)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : ClosedsCMRA X) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := ClosedsCMRA X)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : ClosedsCMRA X) = a by
      cases a
      exact congrArg _ (sup_idem _)

instance : Std.LawfulLeftIdentity (Add.add (α := ClosedsCMRA X)) (0 : ClosedsCMRA X) where
  left_id a :=
    show (⟨(⊥ : TopologicalSpace.Closeds X) ⊔ a.car⟩ : ClosedsCMRA X) = a by
      cases a
      exact congrArg _ (bot_sup_eq _)

instance : CMRA (ClosedsCMRA X) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (ClosedsCMRA X) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (ClosedsCMRA X) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every closed set is its own core. -/
example (a : ClosedsCMRA X) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the lattice of closeds:
`a ≤ a + b`. -/
theorem le_op_left (a b : ClosedsCMRA X) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : ClosedsCMRA X) : b.car ≤ (a + b).car := le_sup_right

/-- Every closed set is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : ClosedsCMRA X) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := ClosedsCMRA X)) a

/-- Sanity example: two closeds combine via `+` to their union. -/
example (C D : TopologicalSpace.Closeds X) :
    (show ClosedsCMRA X from ⟨C⟩) + (show ClosedsCMRA X from ⟨D⟩)
      = (show ClosedsCMRA X from ⟨C ⊔ D⟩) := rfl

end ClosedsCMRA

end IrisMath.Opens
