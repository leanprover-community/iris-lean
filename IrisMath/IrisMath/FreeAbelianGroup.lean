/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Iris

@[expose] public section

/-!
# Free abelian group CMRA

`FreeAbelianGroup α` is Mathlib's free abelian group on a type `α`: the
universal abelian group on a generating set. Every element is a finite
formal `ℤ`-linear combination of generators, so unlike `MultisetCMRA` we can
also account for *negative* amounts of a resource. This makes it the natural
choice for resource-accounting CMRAs that track balances (e.g. owed vs.
owned, fork-join thread budgets) rather than just disjoint supplies.

`FreeAbelianGroup α` is an `AddCommGroup`, hence in particular an
`AddCommMonoid` with cancellation. We surface it as an Iris UCMRA via the
**constant-core** `CommMonoidLike` recipe from `Iris/Algebra/Numbers.lean`:
the operation is the group's `+`, the unit is `0`, and `pcore` is the
constant function `some 0`.

Because `FreeAbelianGroup α` is a (cancellative) group, every element is
`Cancelable`; this follows from the scoped `Cancelable` instance in
`CommMonoidLike` together with `LeftCancelAdd`.

The carrier is wrapped in `LeibnizO` so that OFE equality is propositional
equality, matching `IrisMath/Multiset.lean`. As there, the scoped CMRA /
UCMRA instances from `Iris/Algebra/Numbers.lean` are referenced explicitly by
their generated names (`CommMonoidLike.instCMRA`, etc.).
-/

open Iris OFE CMRA Std

namespace IrisMath.FreeAbelianGroupCMRA

/-- The free abelian group on `α` as a UCMRA under addition `· + ·`, with
unit `0`. Uses the constant-core `CommMonoidLike` recipe. -/
def _root_.IrisMath.FreeAbelianGroupCMRA (α : Type _) : Type _ :=
  LeibnizO (FreeAbelianGroup α)

variable {α : Type _}

/-- COFE instance lifted from the `LeibnizO` wrapper. -/
instance : COFE (FreeAbelianGroupCMRA α) := inferInstanceAs (COFE (LeibnizO _))

/-- The OFE is discrete (inherited from `LeibnizO`). -/
instance : OFE.Discrete (FreeAbelianGroupCMRA α) :=
  inferInstanceAs (OFE.Discrete (LeibnizO _))

/-- The OFE is Leibniz (inherited from `LeibnizO`). -/
instance : OFE.Leibniz (FreeAbelianGroupCMRA α) :=
  inferInstanceAs (OFE.Leibniz (LeibnizO _))

/-- The CMRA operation: addition in the free abelian group. -/
instance : Add (FreeAbelianGroupCMRA α) := ⟨fun a b ↦ ⟨a.car + b.car⟩⟩

/-- The CMRA unit: the zero element of the free abelian group. -/
instance : Zero (FreeAbelianGroupCMRA α) := ⟨⟨0⟩⟩

/-- Unfolding lemma for the operation: `a + b` is the wrapped sum of the
underlying free-abelian-group elements. -/
theorem add_def (a b : FreeAbelianGroupCMRA α) : a + b = ⟨a.car + b.car⟩ := rfl

/-- Unfolding lemma for the unit: `0` wraps the zero of the free abelian
group. -/
theorem zero_def : (0 : FreeAbelianGroupCMRA α) = ⟨0⟩ := rfl

/-- The CMRA `op` agrees with the underlying free-abelian-group addition on
carriers: `(a + b).car = a.car + b.car`. -/
theorem op_add_def (a b : FreeAbelianGroupCMRA α) :
    (a + b).car = a.car + b.car := rfl

instance : Std.Associative (Add.add (α := FreeAbelianGroupCMRA α)) where
  assoc a b c :=
    show (⟨(a.car + b.car) + c.car⟩ : FreeAbelianGroupCMRA α)
        = ⟨a.car + (b.car + c.car)⟩ by
      rw [add_assoc]

instance : Std.Commutative (Add.add (α := FreeAbelianGroupCMRA α)) where
  comm a b :=
    show (⟨a.car + b.car⟩ : FreeAbelianGroupCMRA α) = ⟨b.car + a.car⟩ by
      rw [add_comm]

instance : Std.LawfulLeftIdentity (Add.add (α := FreeAbelianGroupCMRA α))
    (0 : FreeAbelianGroupCMRA α) where
  left_id a :=
    show (⟨(0 : FreeAbelianGroup α) + a.car⟩ : FreeAbelianGroupCMRA α) = a by
      cases a; simp

/-- The CMRA instance, supplied by the constant-core `CommMonoidLike` recipe. -/
instance : CMRA (FreeAbelianGroupCMRA α) := CommMonoidLike.instCMRA

/-- The CMRA is discrete (every step-indexed equality is genuine equality). -/
instance : CMRA.Discrete (FreeAbelianGroupCMRA α) := CommMonoidLike.instDiscrete

/-- The UCMRA instance, supplied by the constant-core `CommMonoidLike` recipe. -/
instance : UCMRA (FreeAbelianGroupCMRA α) := CommMonoidLike.instUCMRA

/-- Addition in the free abelian group is left-cancellative: this follows from
the underlying `AddCommGroup` structure. -/
instance : LeftCancelAdd (FreeAbelianGroupCMRA α) where
  cancel_left {x₁ x₂ y} h := by
    have hcar : y.car + x₁.car = y.car + x₂.car := by
      simpa [add_def] using congrArg LeibnizO.car h
    cases x₁; cases x₂
    exact congrArg _ (add_left_cancel hcar)

/-- The unit `0` is a `CoreId` (its core equals itself). -/
example : CMRA.CoreId (0 : FreeAbelianGroupCMRA α) :=
  open CommMonoidLike in inferInstance

/-- Every element of `FreeAbelianGroupCMRA α` is `Cancelable`, lifted from
`LeftCancelAdd` via the scoped instance in `CommMonoidLike`. -/
example (a : FreeAbelianGroupCMRA α) : Cancelable a :=
  open CommMonoidLike in inferInstance

/-- The single-generator embedding `FreeAbelianGroup.of`, lifted on the
domain side to the `LeibnizO` wrapper so it lives between two OFEs. Since
both OFEs are Leibniz this map is trivially non-expansive. -/
def ofL (x : LeibnizO α) : FreeAbelianGroupCMRA α := ⟨FreeAbelianGroup.of x.car⟩

/-- `ofL` is non-expansive: this is immediate because both source and target
OFEs are Leibniz. -/
instance : NonExpansive (ofL (α := α)) where
  ne _ _ _ h := by rw [eq_of_eqv (OFE.Discrete.discrete h)]

/-- `ofL` is injective: distinct generators give distinct elements in the
CMRA carrier. This is `FreeAbelianGroup.of_injective` transported through the
`LeibnizO` wrapper. -/
theorem ofL_injective : Function.Injective (ofL (α := α)) := by
  intro x y h
  have : FreeAbelianGroup.of x.car = FreeAbelianGroup.of y.car :=
    congrArg LeibnizO.car h
  cases x; cases y
  exact congrArg _ (FreeAbelianGroup.of_injective this)

/-- Specialisation of `ofL_injective`: distinct generators in `α` map to
distinct elements of `FreeAbelianGroupCMRA α`. -/
theorem ofL_ne_ofL_of_ne {x y : α} (h : x ≠ y) :
    ofL (⟨x⟩ : LeibnizO α) ≠ ofL (⟨y⟩ : LeibnizO α) := by
  intro hxy
  exact h (congrArg LeibnizO.car (ofL_injective hxy))

/-- The CMRA `+` on `FreeAbelianGroupCMRA α` is non-expansive in both
arguments. Trivial since the OFE is discrete + Leibniz, but recorded for
uniformity with the non-discrete CMRA API. -/
theorem add_ne₂ :
    NonExpansive₂ (· + · : FreeAbelianGroupCMRA α → FreeAbelianGroupCMRA α →
      FreeAbelianGroupCMRA α) where
  ne _ _ _ h₁ _ _ h₂ := by
    rw [eq_of_eqv (OFE.Discrete.discrete h₁), eq_of_eqv (OFE.Discrete.discrete h₂)]

/-- Concrete example: combining two generators via the CMRA op gives their
sum in the underlying free abelian group. -/
example (x y : α) :
    ofL ⟨x⟩ + ofL ⟨y⟩ = (⟨FreeAbelianGroup.of x + FreeAbelianGroup.of y⟩ :
      FreeAbelianGroupCMRA α) := rfl

end IrisMath.FreeAbelianGroupCMRA

/-! ## Sanity examples at the top level -/

#check (inferInstance : UCMRA (IrisMath.FreeAbelianGroupCMRA Nat))
