/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/

import Iris.Std.Positive

/-! # Finite Sets of Invariant Names

Reference: `stdpp/theories/gset.v`, `iris/algebra/gset.v`

Finite sets of invariant names, used to track which invariants are currently
disabled in world satisfaction (`ownD` tokens). The predicate-based representation
mirrors `CoPset` for uniformity, providing union, difference, disjointness, and
subset operations needed by the `GSetDisj` CMRA.

## Main Definitions

- `GSet` — set of invariant names (`Positive`), represented as a membership predicate
- `GSet.singleton` — singleton set `{[i]}`
- `GSet.union`, `GSet.empty` — set operations
- `GSet.Disjoint`, `GSet.Subset` — predicates
-/

namespace Iris

/-! ## Definition -/

/-- Set of invariant names, used for disabled invariant tokens. -/
structure GSet where
  /-- Membership predicate. -/
  mem : Positive → Prop

namespace GSet

@[ext]
theorem ext {s₁ s₂ : GSet} (h : ∀ n, s₁.mem n ↔ s₂.mem n) : s₁ = s₂ := by
  -- extensionality for predicate-based sets
  cases s₁; cases s₂; simp only [mk.injEq]
  exact funext fun n => propext (h n)

/-! ## Constructors and Operations -/

def empty : GSet := by
  -- empty set: always false
  exact ⟨fun _ => False⟩

def singleton (n : Positive) : GSet := by
  -- singleton membership
  exact ⟨fun m => m = n⟩

def union (s₁ s₂ : GSet) : GSet := by
  -- union membership via disjunction
  exact ⟨fun n => s₁.mem n ∨ s₂.mem n⟩

def diff (s₁ s₂ : GSet) : GSet := by
  -- set difference: left membership and not right membership
  exact ⟨fun n => s₁.mem n ∧ ¬s₂.mem n⟩

instance : EmptyCollection GSet := ⟨empty⟩
instance : Singleton Positive GSet := ⟨singleton⟩
instance : Union GSet := ⟨union⟩
instance : SDiff GSet := ⟨diff⟩

/-! ## Predicates -/

def Disjoint (s₁ s₂ : GSet) : Prop := by
  -- disjointness means no shared element
  exact ∀ n, ¬(s₁.mem n ∧ s₂.mem n)

def Subset (s₁ s₂ : GSet) : Prop := by
  -- subset means elementwise implication
  exact ∀ n, s₁.mem n → s₂.mem n

instance : HasSubset GSet := ⟨Subset⟩

noncomputable instance (s₁ s₂ : GSet) : Decidable (Disjoint s₁ s₂) := by
  -- classical decidability for predicates
  exact Classical.propDecidable _

/-! ## Simp Lemmas -/

@[simp] theorem mem_empty (n : Positive) : (∅ : GSet).mem n ↔ False := by
  -- unfold empty membership
  rfl

@[simp] theorem mem_singleton (n m : Positive) : ({m} : GSet).mem n ↔ n = m := by
  -- unfold singleton membership
  rfl

@[simp] theorem mem_union (s₁ s₂ : GSet) (n : Positive) :
    (s₁ ∪ s₂).mem n ↔ s₁.mem n ∨ s₂.mem n := by
  -- unfold union membership
  rfl

@[simp] theorem mem_diff (s₁ s₂ : GSet) (n : Positive) :
    (s₁ \ s₂).mem n ↔ s₁.mem n ∧ ¬s₂.mem n := by
  -- unfold difference membership
  rfl

/-! ## Set Algebra Laws -/

theorem union_assoc (s₁ s₂ s₃ : GSet) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  -- associativity of union via propositional associativity
  ext n; simp [or_assoc]

theorem union_comm (s₁ s₂ : GSet) : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  -- commutativity of union via propositional commutativity
  ext n; simp [or_comm]

theorem union_empty (s : GSet) : s ∪ ∅ = s := by
  -- right identity of union
  ext n; simp

theorem empty_union (s : GSet) : ∅ ∪ s = s := by
  -- left identity of union
  ext n; simp

theorem union_idem (s : GSet) : s ∪ s = s := by
  -- idempotence of union
  ext n; simp [or_self]

/-! ## Disjointness and Subset -/

theorem disjoint_comm {s₁ s₂ : GSet} : Disjoint s₁ s₂ ↔ Disjoint s₂ s₁ := by
  -- symmetry by swapping conjuncts
  refine ⟨?_, ?_⟩
  · intro h n hn
    exact h n ⟨hn.2, hn.1⟩
  · intro h n hn
    exact h n ⟨hn.2, hn.1⟩

theorem disjoint_empty_right (s : GSet) : Disjoint s ∅ := by
  -- no element can be in an empty set
  intro _ hn; exact hn.2

theorem disjoint_empty_left (s : GSet) : Disjoint ∅ s := by
  -- no element can be in an empty set
  intro _ hn; exact hn.1

/-- Any subset can be decomposed as a disjoint union with the set difference. -/
theorem subseteq_disjoint_union {s₁ s₂ : GSet} (h : s₁ ⊆ s₂) :
    ∃ s₃, s₂ = s₁ ∪ s₃ ∧ Disjoint s₁ s₃ := by
  -- choose the set difference as a disjoint complement
  refine ⟨s₂ \ s₁, ?_, ?_⟩
  · ext n; simp; constructor
    · intro hn
      by_cases h₁ : s₁.mem n
      · exact Or.inl h₁
      · exact Or.inr ⟨hn, h₁⟩
    · rintro (h₁ | ⟨h₂, _⟩)
      · exact h _ h₁
      · exact h₂
  · exact fun _ ⟨h₁, _, h₃⟩ => h₃ h₁

end GSet

end Iris
