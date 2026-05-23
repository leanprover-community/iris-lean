/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Iris

@[expose] public section

/-!
# Multiset and Finset CMRAs

Two further UCMRAs harvested from Mathlib's container types, illustrating the
two flavors of the `…CommMonoidLike` recipes from `Iris/Algebra/Numbers.lean`:

* `MultisetCMRA α`: multisets under disjoint union `· + ·` with unit `0`.
  Multiset addition is *not* idempotent (`{a} + {a} ≠ {a}`), so we instantiate
  the **constant-core** `CommMonoidLike` recipe: `pcore` is the constant
  function `some 0`, and only `0` is a `CoreId`. Multiset addition is also
  left-cancellative, so we surface `LeftCancelAdd`, which in turn yields a
  `Cancelable` instance for every element.
* `FinsetCMRA α`: finite sets under union `· ∪ ·` with unit `∅`. Union *is*
  idempotent, so we instantiate the **universal-core** `OrdCommMonoidLike`
  recipe: `pcore a = some a` (every element is its own core), and every
  element is a `CoreId`.

As in `LatticeCMRAs.lean` the carriers are wrapped in `LeibnizO` and we
reference the `scoped` instances from `Iris/Algebra/Numbers.lean` by their
generated names (`CommMonoidLike.instCMRA`, `OrdCommMonoidLike.instCMRA`, etc.);
the ambient `inferInstance` machinery does not see those `scoped` instances
through a top-level `open`.
-/

open Iris OFE CMRA Std

namespace IrisMath.MultisetCMRA

/-! ## (A) Multisets under disjoint union -/

/-- Multisets on `α` as a UCMRA under disjoint union `· + ·`, with unit `0`
(the empty multiset). Not idempotent; uses the constant-core `CommMonoidLike`
recipe. -/
def _root_.IrisMath.MultisetCMRA (α : Type _) : Type _ := LeibnizO (Multiset α)

variable {α : Type _}

instance : COFE (MultisetCMRA α) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (MultisetCMRA α) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (MultisetCMRA α) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: disjoint union of multisets. -/
instance : Add (MultisetCMRA α) := ⟨fun a b ↦ ⟨a.car + b.car⟩⟩

/-- The CMRA unit: the empty multiset. -/
instance : Zero (MultisetCMRA α) := ⟨⟨0⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : MultisetCMRA α) : a + b = ⟨a.car + b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : MultisetCMRA α) = ⟨0⟩ := rfl

instance : Std.Associative (Add.add (α := MultisetCMRA α)) where
  assoc a b c :=
    show (⟨(a.car + b.car) + c.car⟩ : MultisetCMRA α) = ⟨a.car + (b.car + c.car)⟩ by
      rw [Multiset.add_assoc]

instance : Std.Commutative (Add.add (α := MultisetCMRA α)) where
  comm a b :=
    show (⟨a.car + b.car⟩ : MultisetCMRA α) = ⟨b.car + a.car⟩ by
      rw [Multiset.add_comm]

instance : Std.LawfulLeftIdentity (Add.add (α := MultisetCMRA α)) (0 : MultisetCMRA α) where
  left_id a :=
    show (⟨(0 : Multiset α) + a.car⟩ : MultisetCMRA α) = a by
      cases a; simp

instance : CMRA (MultisetCMRA α) := CommMonoidLike.instCMRA
instance : CMRA.Discrete (MultisetCMRA α) := CommMonoidLike.instDiscrete
instance : UCMRA (MultisetCMRA α) := CommMonoidLike.instUCMRA

/-- Multiset addition is left-cancellative: `y + x₁ = y + x₂` implies `x₁ = x₂`. -/
instance : LeftCancelAdd (MultisetCMRA α) where
  cancel_left {x₁ x₂ y} h := by
    have hcar : y.car + x₁.car = y.car + x₂.car := by
      simpa [add_def] using congrArg LeibnizO.car h
    cases x₁; cases x₂
    exact congrArg _ (Multiset.add_right_inj.mp hcar)

/-- The CMRA operation `+` recovers ordinary multiset addition pointwise: the
multiplicity of `x` in `a + b` is the sum of its multiplicities in `a` and `b`. -/
theorem op_count [DecidableEq α] (a b : MultisetCMRA α) (x : α) :
    (a + b).car.count x = a.car.count x + b.car.count x :=
  Multiset.count_add x a.car b.car

/-- The unit `0` is a `CoreId` (its core equals itself). -/
example : CMRA.CoreId (0 : MultisetCMRA α) :=
  open CommMonoidLike in inferInstance

/-- Every element of `MultisetCMRA α` is `Cancelable`, lifted from
`LeftCancelAdd`. -/
example (a : MultisetCMRA α) : Cancelable a :=
  open CommMonoidLike in inferInstance

/-- Concrete example: combining two multisets via the CMRA op gives their
disjoint union (multiplicities add). -/
example :
    let a : MultisetCMRA Nat := LeibnizO.mk ({1, 2} : Multiset Nat)
    let b : MultisetCMRA Nat := LeibnizO.mk ({2, 3} : Multiset Nat)
    a + b = LeibnizO.mk ({1, 2, 2, 3} : Multiset Nat) := by
  simp only [add_def]
  exact congrArg _ (by decide)

end IrisMath.MultisetCMRA

/-! ## (B) Finite sets under union -/

namespace IrisMath.FinsetCMRA

/-- Finite sets on `α` as a UCMRA under union `· ∪ ·`, with unit `∅`.
Idempotent; uses the universal-core `OrdCommMonoidLike` recipe, so every
element is its own core. -/
def _root_.IrisMath.FinsetCMRA (α : Type _) [DecidableEq α] : Type _ :=
  LeibnizO (Finset α)

variable {α : Type _} [DecidableEq α]

instance : COFE (FinsetCMRA α) := inferInstanceAs (COFE (LeibnizO _))
instance : OFE.Discrete (FinsetCMRA α) := inferInstanceAs (OFE.Discrete (LeibnizO _))
instance : OFE.Leibniz (FinsetCMRA α) := inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: union of finite sets. -/
instance : Add (FinsetCMRA α) := ⟨fun a b ↦ ⟨a.car ∪ b.car⟩⟩

/-- The CMRA unit: the empty finite set. -/
instance : Zero (FinsetCMRA α) := ⟨⟨∅⟩⟩

/-- Unfolding lemma for the operation. -/
theorem add_def (a b : FinsetCMRA α) : a + b = ⟨a.car ∪ b.car⟩ := rfl

/-- Unfolding lemma for the unit. -/
theorem zero_def : (0 : FinsetCMRA α) = ⟨∅⟩ := rfl

instance : Std.Associative (Add.add (α := FinsetCMRA α)) where
  assoc a b c :=
    show (⟨(a.car ∪ b.car) ∪ c.car⟩ : FinsetCMRA α) = ⟨a.car ∪ (b.car ∪ c.car)⟩ by
      rw [Finset.union_assoc]

instance : Std.Commutative (Add.add (α := FinsetCMRA α)) where
  comm a b :=
    show (⟨a.car ∪ b.car⟩ : FinsetCMRA α) = ⟨b.car ∪ a.car⟩ by
      rw [Finset.union_comm]

instance : Std.IdempotentOp (Add.add (α := FinsetCMRA α)) where
  idempotent a :=
    show (⟨a.car ∪ a.car⟩ : FinsetCMRA α) = a by
      cases a; simp

instance : Std.LawfulLeftIdentity (Add.add (α := FinsetCMRA α)) (0 : FinsetCMRA α) where
  left_id a :=
    show (⟨(∅ : Finset α) ∪ a.car⟩ : FinsetCMRA α) = a by
      cases a; simp

instance : CMRA (FinsetCMRA α) := OrdCommMonoidLike.instCMRA
instance : CMRA.Discrete (FinsetCMRA α) := OrdCommMonoidLike.instDiscrete
instance : UCMRA (FinsetCMRA α) := OrdCommMonoidLike.instUCMRAOfLawfulLeftIdentityAddZero

/-- Every Finset element is its own core (the operation is idempotent). -/
example (a : FinsetCMRA α) : CMRA.CoreId a := OrdCommMonoidLike.instCoreId _

/-- The CMRA operation dominates each argument in the subset lattice:
`a ⊆ a + b`. -/
theorem le_op_left (a b : FinsetCMRA α) : a.car ≤ (a + b).car := Finset.subset_union_left

/-- Symmetric companion to `le_op_left`. -/
theorem le_op_right (a b : FinsetCMRA α) : b.car ≤ (a + b).car := Finset.subset_union_right

/-- Concrete example: combining two finite sets via the CMRA op gives their
union. -/
example :
    let a : FinsetCMRA Nat := LeibnizO.mk ({1, 2} : Finset Nat)
    let b : FinsetCMRA Nat := LeibnizO.mk ({2, 3} : Finset Nat)
    a + b = LeibnizO.mk ({1, 2, 3} : Finset Nat) := by
  simp only [add_def]
  exact congrArg _ (by decide)

end IrisMath.FinsetCMRA

/-! ## (C) Sanity examples at the top level -/

#check (inferInstance : UCMRA (IrisMath.MultisetCMRA Nat))
#check (inferInstance : UCMRA (IrisMath.FinsetCMRA Nat))
