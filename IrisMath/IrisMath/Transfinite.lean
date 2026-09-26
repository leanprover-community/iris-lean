/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family
public import IrisMath.StepIndex

/-! # Ordinals as transfinite step-indices

This file ports `theories/algebra/ordinals/ord_stepindex.v` of Transfinite Iris, using Mathlib's
ordinals instead of the Aczel-tree set model of the Rocq development:

- `Ordinal` is a *transfinite* type of step-indices (`TransfiniteIndex`): `m + ω` is above all
  finite successors of `m`.
- `Ordinal.{u}` is a *large* type of step-indices for families indexed by `Type u`
  (`LargeIndex`): a small family of ordinals is bounded.

Consequently the `UPred` model over ordinals has the *existential property*
(`UPred.satisfiable_exists`) and the big later `⧍` is sound (`UPred.big_later_soundness`).
-/

@[expose] public section

noncomputable section

open Iris

theorem Ordinal.repeat_succ_eq_add (n : ℕ) (m : Ordinal) : Nat.repeat Order.succ n m = m + n := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih =>
    simp only [Nat.repeat, ih, Nat.cast_add, Nat.cast_one, ← add_assoc, Order.succ_eq_add_one]

/-- Transfinite Iris, `ordI` is a `TransfiniteIndex` (with `upper_limit α := α + ω`). -/
instance ordinalSIdxTransfinite : SIdxTransfinite Ordinal where
  upperLimit m := m + Ordinal.omega0
  iter_succ_lt_upperLimit n m := by
    change Nat.repeat Order.succ n m < m + Ordinal.omega0
    rw [Ordinal.repeat_succ_eq_add]
    exact (add_lt_add_iff_left m).mpr (Ordinal.natCast_lt_omega0 n)

/-- Transfinite Iris, `ordI` is a `LargeIndex` (`commute_exists`): for a small type `X`, if for
every ordinal some `x : X` satisfies a downward-closed predicate, then some `x` satisfies it for
all ordinals. Otherwise choose for every `x` an ordinal `a x` where it fails; the supremum of the
successors of these ordinals is a (small) ordinal at which no `x` satisfies the predicate. -/
instance ordinalSIdxLarge : SIdxLarge.{u} Ordinal.{u} where
  commute_exists {X} P hdown hsome := by
    by_contra hne
    push_neg at hne
    choose a ha using hne
    obtain ⟨x, hx⟩ := hsome (⨆ x, a x + 1)
    exact ha x (hdown x (a x) _ (Ordinal.lt_iSup_add_one a x) hx)

/-! ## Consequences for the `UPred` model over ordinals -/

section UPred

local stepindex Ordinal

variable {M : Type _} [UCMRA (SI := Ordinal.{u}) M]

/-- The existential property of Transfinite Iris for the `UPred` model over ordinals. -/
example {X : Type u} {P : X → UPred M} (h : UPred.satisfiable iprop(∃ x, P x)) :
    ∃ x, UPred.satisfiable (P x) :=
  UPred.satisfiable_exists h

/-- Soundness of the big later for the `UPred` model over ordinals. -/
example (φ : Prop) (h : iprop((True : UPred M) ⊢ ⧍ ⌜φ⌝)) : φ :=
  UPred.transfinite_soundness φ h

end UPred
