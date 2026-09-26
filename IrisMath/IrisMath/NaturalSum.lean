/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Mathlib.SetTheory.Ordinal.Family

/-! # The natural (Hessenberg) sum of ordinals

This file ports the part of `theories/algebra/ordinals/arithmetic.v` of Transfinite Iris that is
used by time credits: the natural sum `a ♯ b` of ordinals, which, unlike ordinal addition, is
commutative and strictly monotone (hence cancellative) in both arguments. The definition and
proofs follow Mathlib's (former) `Mathlib.SetTheory.Ordinal.NaturalOps`, which is not part of the
Mathlib version used here.
-/

@[expose] public noncomputable section

set_option linter.deprecated false

universe u

namespace Ordinal

/-- The natural (Hessenberg) sum of ordinals (Rocq: `natural_addition`). -/
def nadd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | a, b => max (blsub.{u, u} a fun a' _ => nadd a' b) (blsub.{u, u} b fun b' _ => nadd a b')
termination_by a b => (a, b)
decreasing_by
  · exact Prod.Lex.left _ _ ‹_›
  · exact Prod.Lex.right _ ‹_›

@[inherit_doc] scoped infixl:65 " ♯ " => nadd

variable {a b c d : Ordinal.{u}}

theorem nadd_def (a b : Ordinal.{u}) :
    a ♯ b = max (blsub.{u, u} a fun a' _ => a' ♯ b) (blsub.{u, u} b fun b' _ => a ♯ b') := by
  rw [nadd]

theorem lt_nadd_iff :
    a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by
  rw [nadd_def]
  simp [lt_blsub_iff]

theorem nadd_le_iff :
    b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by
  rw [nadd_def]
  simp [blsub_le_iff]

/-- Rocq: `natural_addition_strict_compat` (right argument). -/
theorem nadd_lt_nadd_left (h : b < c) (a : Ordinal.{u}) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)

/-- Rocq: `natural_addition_strict_compat` (left argument). -/
theorem nadd_lt_nadd_right (h : b < c) (a : Ordinal.{u}) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)

theorem nadd_le_nadd_left (h : b ≤ c) (a : Ordinal.{u}) : a ♯ b ≤ a ♯ c := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (nadd_lt_nadd_left h a).le
  · exact le_rfl

theorem nadd_le_nadd_right (h : b ≤ c) (a : Ordinal.{u}) : b ♯ a ≤ c ♯ a := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl

/-- Rocq: `natural_addition_comm`. -/
theorem nadd_comm (a b : Ordinal.{u}) : a ♯ b = b ♯ a := by
  rw [nadd_def, nadd_def (a := b), max_comm]
  congr <;> ext c hc <;> apply nadd_comm
termination_by (a, b)
decreasing_by
  · exact Prod.Lex.right _ ‹_›
  · exact Prod.Lex.left _ _ ‹_›

/-- Rocq: `natural_addition_zero_left_id` (right version). -/
theorem nadd_zero (a : Ordinal.{u}) : a ♯ 0 = a := by
  induction a using Ordinal.lt_wf.induction with | _ a IH => ?_
  rw [nadd_def, blsub_zero, max_zero_right]
  calc _ = blsub.{u, u} a (fun b _ => b) := by congr; funext b hb; exact IH b hb
    _ = a := blsub_id a

/-- Rocq: `natural_addition_zero_left_id`. -/
theorem zero_nadd (a : Ordinal.{u}) : 0 ♯ a = a := by
  rw [nadd_comm, nadd_zero]

theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{u}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    blsub.{u, u} _ f = max (blsub.{u, u} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
      (blsub.{u, u} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) := by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  · intro i h
    rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ ha'))
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ hb'))
  all_goals
    apply blsub_le_of_brange_subset.{u, u, u}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self

/-- Rocq: `natural_addition_assoc`. -/
theorem nadd_assoc (a b c : Ordinal.{u}) : a ♯ b ♯ c = a ♯ (b ♯ c) := by
  rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc]
  · congr <;> ext d hd <;> apply nadd_assoc
  · exact fun _ _ h => nadd_le_nadd_left h a
  · exact fun _ _ h => nadd_le_nadd_right h c
termination_by (a, b, c)
decreasing_by
  · exact Prod.Lex.left _ _ ‹_›
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ ‹_›)
  · exact Prod.Lex.right _ (Prod.Lex.right _ ‹_›)

/-- Rocq: `natural_addition_cancel`. -/
theorem nadd_left_cancel (h : a ♯ b = a ♯ c) : b = c := by
  rcases lt_trichotomy b c with hbc | hbc | hbc
  · exact absurd h (nadd_lt_nadd_left hbc a).ne
  · exact hbc
  · exact absurd h (nadd_lt_nadd_left hbc a).ne'

/-- Rocq: `natural_addition_succ`. -/
theorem nadd_one (a : Ordinal.{u}) : a ♯ 1 = Order.succ a := by
  induction a using Ordinal.lt_wf.induction with | _ a IH => ?_
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff]
  intro i hi
  rw [IH i hi, Order.succ_lt_succ_iff]
  exact hi

end Ordinal
