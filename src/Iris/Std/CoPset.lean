/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/

import Iris.Std.Positive

/-! # Co-finite Powerset of Invariant Names

Reference: `stdpp/theories/coPset.v`

Invariant masks track which invariants are currently enabled or available for
opening. A mask is a (potentially co-finite) set of invariant names. The fancy
update modality `|={E1,E2}=> P` uses masks to prevent double-opening: opening
an invariant removes its name from the mask, and closing it adds the name back.

We use a predicate-based representation rather than a literal co-finite `Finset`.
This is sufficient for mask reasoning and disjointness but does not provide
decidable membership — classical decidability is used where needed.

## Main Definitions

- `CoPset` — set of invariant names, represented as a membership predicate
- Set operations: `empty`, `top`, `union`, `inter`, `diff`, `compl`, `singleton`
- Predicates: `Disjoint`, `Subset`

## Main Results

- `union_assoc`, `union_comm`, `empty_union` — union forms a commutative monoid
- `subseteq_disjoint_union` — any subset decomposes into a disjoint union
-/

namespace Iris

/-! ## Definition -/

/-- Co-finite powerset of invariant names. Used for invariant masks. -/
structure CoPset where
  /-- Membership predicate. -/
  mem : Positive → Prop

namespace CoPset

@[ext]
theorem ext {s₁ s₂ : CoPset} (h : ∀ n, s₁.mem n ↔ s₂.mem n) : s₁ = s₂ := by
  -- extensionality for predicate-based sets
  cases s₁; cases s₂; simp only [mk.injEq]
  exact funext fun n => propext (h n)

/-! ## Basic Constructors -/

def empty : CoPset := by
  -- empty set: always false
  exact ⟨fun _ => False⟩

def top : CoPset := by
  -- top set: always true
  exact ⟨fun _ => True⟩

def singleton (n : Positive) : CoPset := by
  -- singleton membership
  exact ⟨fun m => m = n⟩

instance : EmptyCollection CoPset := ⟨empty⟩
instance : Singleton Positive CoPset := ⟨singleton⟩

/-! ## Set Operations -/

def union (s₁ s₂ : CoPset) : CoPset := by
  -- union membership via disjunction
  exact ⟨fun n => s₁.mem n ∨ s₂.mem n⟩

def inter (s₁ s₂ : CoPset) : CoPset := by
  -- intersection membership via conjunction
  exact ⟨fun n => s₁.mem n ∧ s₂.mem n⟩

def diff (s₁ s₂ : CoPset) : CoPset := by
  -- set difference: left membership and not right membership
  exact ⟨fun n => s₁.mem n ∧ ¬s₂.mem n⟩

def compl (s : CoPset) : CoPset := by
  -- complement: negate membership
  exact ⟨fun n => ¬s.mem n⟩

instance : Union CoPset := ⟨union⟩
instance : Inter CoPset := ⟨inter⟩
instance : SDiff CoPset := ⟨diff⟩

/-! ## Predicates -/

/-- Two sets are disjoint if they share no elements. -/
def Disjoint (s₁ s₂ : CoPset) : Prop := by
  -- disjointness means no shared element
  exact ∀ n, ¬(s₁.mem n ∧ s₂.mem n)

/-- Subset relation. -/
def Subset (s₁ s₂ : CoPset) : Prop := by
  -- subset means elementwise implication
  exact ∀ n, s₁.mem n → s₂.mem n

instance : HasSubset CoPset := ⟨Subset⟩

noncomputable instance (s₁ s₂ : CoPset) : Decidable (Disjoint s₁ s₂) := by
  -- classical decidability for predicate-based disjointness
  exact Classical.propDecidable _

/-! ## Simp Lemmas -/

@[simp] theorem mem_empty (n : Positive) : (∅ : CoPset).mem n ↔ False := by
  -- unfold empty membership
  rfl

@[simp] theorem mem_top (n : Positive) : CoPset.top.mem n ↔ True := by
  -- unfold top membership
  rfl

@[simp] theorem mem_singleton (n m : Positive) : ({m} : CoPset).mem n ↔ n = m := by
  -- unfold singleton membership
  rfl

@[simp] theorem mem_union (s₁ s₂ : CoPset) (n : Positive) :
    (s₁ ∪ s₂).mem n ↔ s₁.mem n ∨ s₂.mem n := by
  -- unfold union membership
  rfl

@[simp] theorem mem_inter (s₁ s₂ : CoPset) (n : Positive) :
    (s₁ ∩ s₂).mem n ↔ s₁.mem n ∧ s₂.mem n := by
  -- unfold intersection membership
  rfl

@[simp] theorem mem_diff (s₁ s₂ : CoPset) (n : Positive) :
    (s₁ \ s₂).mem n ↔ s₁.mem n ∧ ¬s₂.mem n := by
  -- unfold difference membership
  rfl

@[simp] theorem mem_compl (s : CoPset) (n : Positive) :
    s.compl.mem n ↔ ¬s.mem n := by
  -- unfold complement membership
  rfl

/-! ## Set Algebra Laws -/

theorem union_assoc (s₁ s₂ s₃ : CoPset) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  -- associativity of union via propositional associativity
  ext n; simp [or_assoc]

theorem union_comm (s₁ s₂ : CoPset) : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  -- commutativity of union via propositional commutativity
  ext n; simp [or_comm]

theorem union_empty (s : CoPset) : s ∪ ∅ = s := by
  -- right identity of union
  ext n; simp

theorem empty_union (s : CoPset) : ∅ ∪ s = s := by
  -- left identity of union
  ext n; simp

theorem union_idem (s : CoPset) : s ∪ s = s := by
  -- idempotence of union
  ext n; simp [or_self]

/-! ## Subset Lemmas -/

theorem subset_refl (s : CoPset) : s ⊆ s := by
  -- subset reflexivity
  intro _ h; exact h

theorem subset_union_left (s₁ s₂ : CoPset) : s₁ ⊆ s₁ ∪ s₂ := by
  -- left subset into union
  intro _ h; exact Or.inl h

theorem subset_union_right (s₁ s₂ : CoPset) : s₂ ⊆ s₁ ∪ s₂ := by
  -- right subset into union
  intro _ h; exact Or.inr h

/-! ## Disjointness Lemmas -/

theorem disjoint_comm {s₁ s₂ : CoPset} : Disjoint s₁ s₂ ↔ Disjoint s₂ s₁ := by
  -- symmetry by swapping conjuncts
  refine ⟨?_, ?_⟩
  · intro h n hn
    exact h n ⟨hn.2, hn.1⟩
  · intro h n hn
    exact h n ⟨hn.2, hn.1⟩


theorem disjoint_empty_right (s : CoPset) : Disjoint s ∅ := by
  -- empty set is disjoint on the right
  intro _ hn; exact hn.2


theorem disjoint_empty_left (s : CoPset) : Disjoint ∅ s := by
  -- empty set is disjoint on the left
  intro _ hn; exact hn.1

/-- Any subset can be decomposed as a disjoint union with the set difference. -/
theorem subseteq_disjoint_union {s₁ s₂ : CoPset} (h : s₁ ⊆ s₂) :
    ∃ s₃, s₂ = s₁ ∪ s₃ ∧ Disjoint s₁ s₃ := by
  -- choose the set difference as the disjoint complement
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

end CoPset

end Iris
