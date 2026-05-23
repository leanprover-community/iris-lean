/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Iris

@[expose] public section

/-!
# Simple graphs as an idempotent UCMRA

Mathlib's `SimpleGraph V` is a `CompleteLattice` ordered by edge-set inclusion:

* `⊥` is the empty graph (no edges),
* `⊤` is the complete graph (every pair of distinct vertices is adjacent),
* `⊔` is the union of edge sets,
* `⊓` is the intersection of edge sets.

We expose this lattice as an idempotent UCMRA via the standard
`OrdCommMonoidLike` recipe, mirroring the constructions in
`IrisMath.Opens`, `IrisMath.Subgroup`, `IrisMath.Subring`, and
`IrisMath.LatticeCMRAs`.

* `SimpleGraphCMRA V`: simple graphs on the vertex set `V` under supremum
  (union of edges), unit `⊥` (the empty graph). Intuition: each element is a
  set of edges "already known to be present", and combining two graphs unions
  their edge sets.

As for the sister patterns, the carrier is wrapped in `LeibnizO`
(discrete + Leibniz OFE) and the UCMRA structure comes from the
`OrdCommMonoidLike` recipe, surfaced by referencing the underlying scoped
instance names (`OrdCommMonoidLike.instCMRA` etc.) directly.
-/

open Iris OFE CMRA Std

namespace IrisMath.SimpleGraph

/-! ## Simple graphs under union -/

/-- Simple graphs on a vertex set `V` as a UCMRA under supremum (`⊔`), with
unit `⊥` (the empty graph). The operation `G + H` is the union of the edge
sets, and every graph is its own core. -/
def SimpleGraphCMRA (V : Type _) : Type _ := LeibnizO (_root_.SimpleGraph V)

namespace SimpleGraphCMRA

variable {V : Type _}

instance : COFE (SimpleGraphCMRA V) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (SimpleGraphCMRA V) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (SimpleGraphCMRA V) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: union of edge sets (the lattice join in
`SimpleGraph V`). -/
instance : Add (SimpleGraphCMRA V) := ⟨fun a b ↦ ⟨a.car ⊔ b.car⟩⟩

/-- The CMRA unit: the empty graph `⊥`. -/
instance : Zero (SimpleGraphCMRA V) := ⟨⟨⊥⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : SimpleGraphCMRA V) : a + b = ⟨a.car ⊔ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : SimpleGraphCMRA V) = ⟨⊥⟩ := rfl

instance : Std.Associative (Add.add (α := SimpleGraphCMRA V)) where
  assoc a b c :=
    show (⟨(a.car ⊔ b.car) ⊔ c.car⟩ : SimpleGraphCMRA V)
        = ⟨a.car ⊔ (b.car ⊔ c.car)⟩ by
      rw [sup_assoc]

instance : Std.Commutative (Add.add (α := SimpleGraphCMRA V)) where
  comm a b :=
    show (⟨a.car ⊔ b.car⟩ : SimpleGraphCMRA V) = ⟨b.car ⊔ a.car⟩ by
      rw [sup_comm]

instance : Std.IdempotentOp (Add.add (α := SimpleGraphCMRA V)) where
  idempotent a :=
    show (⟨a.car ⊔ a.car⟩ : SimpleGraphCMRA V) = a by
      cases a
      simp

instance : Std.LawfulLeftIdentity (Add.add (α := SimpleGraphCMRA V))
    (0 : SimpleGraphCMRA V) where
  left_id a :=
    show (⟨(⊥ : _root_.SimpleGraph V) ⊔ a.car⟩ : SimpleGraphCMRA V) = a by
      cases a
      simp

instance : CMRA (SimpleGraphCMRA V) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (SimpleGraphCMRA V) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (SimpleGraphCMRA V) :=
  OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every simple graph is its own core. -/
theorem coreId (a : SimpleGraphCMRA V) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the lattice of simple graphs:
`a ≤ a + b`. -/
theorem le_op_left (a b : SimpleGraphCMRA V) : a.car ≤ (a + b).car := le_sup_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : SimpleGraphCMRA V) : b.car ≤ (a + b).car := le_sup_right

/-- Every simple graph is its own core: `a + a = a` because sup is idempotent. -/
theorem op_self (a : SimpleGraphCMRA V) : a + a = a :=
  Std.IdempotentOp.idempotent (op := Add.add (α := SimpleGraphCMRA V)) a

/-- Sanity example: two graphs combine via `+` to the graph with the union of
their edge sets. -/
example (G H : _root_.SimpleGraph V) :
    (show SimpleGraphCMRA V from ⟨G⟩) + (show SimpleGraphCMRA V from ⟨H⟩)
      = (show SimpleGraphCMRA V from ⟨G ⊔ H⟩) := rfl

/-- Combining `⊥` and `⊤` in the `SimpleGraphCMRA` yields `⊤`. -/
example : (⟨⊥⟩ + ⟨⊤⟩ : SimpleGraphCMRA ℕ) = ⟨⊤⟩ := by
  change (⟨(⊥ : _root_.SimpleGraph ℕ) ⊔ ⊤⟩ : SimpleGraphCMRA ℕ) = ⟨⊤⟩
  rw [bot_sup_eq]

/-- The `UCMRA` instance on `SimpleGraphCMRA` is inferrable. -/
example : UCMRA (SimpleGraphCMRA ℕ) := inferInstance

/-- The unit is a left identity under the CMRA operation. -/
example (a : SimpleGraphCMRA ℕ) : 0 + a = a :=
  Std.LawfulLeftIdentity.left_id (op := Add.add (α := SimpleGraphCMRA ℕ)) a

/-- Example: union of two specific small graphs on `Fin 3`. The graph with
just the edge `{0, 1}` combined with the graph with just the edge `{1, 2}`
yields the graph with both edges (the path `0 — 1 — 2`). -/
example :
    let G : _root_.SimpleGraph (Fin 3) := _root_.SimpleGraph.fromEdgeSet {s(0, 1)}
    let H : _root_.SimpleGraph (Fin 3) := _root_.SimpleGraph.fromEdgeSet {s(1, 2)}
    (show SimpleGraphCMRA (Fin 3) from ⟨G⟩) + (show SimpleGraphCMRA (Fin 3) from ⟨H⟩)
      = (show SimpleGraphCMRA (Fin 3) from ⟨G ⊔ H⟩) := rfl

end SimpleGraphCMRA

end IrisMath.SimpleGraph
