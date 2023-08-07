/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.Instances.Data.SetNotation

namespace Iris.Instances.Data

/-- Result of an operation on `State`. -/
inductive StateResult (α : Type)
  | unknown
  | result (x : α)
  | conflict
export StateResult (unknown)
export StateResult (result)
export StateResult (conflict)

/-- Implementation of a state datatype as a map from `Nat` to a `StateResult` with a value
from `Val`. -/
abbrev State (Val : Type) := Nat → StateResult Val

instance : EmptyCollection (State Val) where
  emptyCollection := fun _ => unknown

instance : Subset (State Val) where
  subset a b := ∀ i x, a i = result x → b i = result x

instance : Union (State Val) where
  union a b := fun i =>
    match a i, b i with
    | unknown , unknown  => unknown
    | result x, unknown  => result x
    | unknown , result y => result y
    | _       , _        => conflict

instance : Disjoint (State Val) where
  disjoint a b := ∀ i, a i = unknown ∨ b i = unknown

theorem empty_union {s : State Val} : s = ∅ ∪ s := by
  simp only [Union.union, EmptyCollection.emptyCollection]
  have : s = fun i => s i := by simp
  rw [this]
  simp only
  apply funext
  intro i
  cases s i
  <;> simp

theorem union_comm {a b : State Val} : a ∪ b = b ∪ a := by
  simp only [Union.union]
  apply funext
  intro i
  cases a i
  <;> cases b i
  <;> simp

theorem union_assoc {a b c : State Val} : (a ∪ b) ∪ c = a ∪ (b ∪ c) := by
  simp only [Union.union]
  apply funext
  intro i
  cases a i
  <;> cases b i
  <;> cases c i
  <;> simp

theorem empty_disjoint {s : State Val} : ∅ || s := by
  simp [Disjoint.disjoint, EmptyCollection.emptyCollection]

theorem disjoint_comm {a b : State Val} : a || b ↔ b || a := by
  simp only [Disjoint.disjoint]
  constructor
  all_goals
    intro h i
    cases h i
    <;> try { apply Or.inl ; assumption }
    <;> try { apply Or.inr ; assumption }

theorem disjoint_assoc {a b c : State Val} : a ∪ b || c → a || b → (a || c) ∧ (b || c) := by
  simp only [Disjoint.disjoint, Union.union]
  intro h_abc h_ab
  constructor
  all_goals
    intro i
    cases h_ab i
    <;> try { apply Or.inl ; assumption }
    cases h_abc i
    <;> try { apply Or.inr ; assumption }
  case left.inr.inl h_b h_ab' =>
    rw [h_b] at h_ab'
    cases h_ai : a i
    <;> rw [h_ai] at h_ab'
    <;> simp only at h_ab'
    apply Or.inl
    simp
  case right.inl.inl h_a h_ab' =>
    rw [h_a] at h_ab'
    cases h_bi : b i
    <;> rw [h_bi] at h_ab'
    <;> simp only at h_ab'
    apply Or.inl
    simp

theorem disjoint_union {a b c : State Val} : a || b → a || c → a || b ∪ c := by
  simp only [Disjoint.disjoint, Union.union]
  intro h_ab h_ac i
  cases h_ab i
  <;> cases h_ac i
  <;> try { apply Or.inl ; assumption }
  case inr.inr h_b h_c =>
    rw [h_b, h_c]
    simp

end Iris.Instances.Data
