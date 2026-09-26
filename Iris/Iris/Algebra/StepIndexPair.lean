/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.StepIndexTransfinite

/-! # Lexicographic pairs of step-indices

This file ports the `pair_index` section of Transfinite Iris's `algebra/stepindex.v`: the
lexicographic product of two types of step-indices is a type of step-indices (Rocq: `pairI`).
The successor increments the second component, so `SIdxPair Nat Nat` is (order-isomorphic to)
`ω²`, the smallest transfinite type of step-indices that does not need ordinals. It is transfinite
(`SIdxTransfinite`), but not large.
-/

@[expose] public section

namespace Iris

/-- Lexicographically ordered pairs of step-indices (Rocq: `pairI`). -/
@[ext]
structure SIdxPair (I : Type u) (J : Type v) where
  fst : I
  snd : J

namespace SIdxPair

variable {I : Type u} {J : Type v} [SIdx I] [SIdx J]

/-- The lexicographic order (Rocq: `pair_lt`). -/
instance : LT (SIdxPair I J) where
  lt p q := p.fst < q.fst ∨ (p.fst = q.fst ∧ p.snd < q.snd)

instance : LE (SIdxPair I J) where
  le p q := p < q ∨ p = q

theorem lt_def {p q : SIdxPair I J} : p < q ↔ p.fst < q.fst ∨ (p.fst = q.fst ∧ p.snd < q.snd) :=
  .rfl

theorem lt_wf : WellFounded ((· < ·) : SIdxPair I J → SIdxPair I J → Prop) := by
  refine ⟨fun ⟨a, b⟩ => ?_⟩
  induction a using (SIdx.lt_wf (I := I)).induction generalizing b with
  | _ a iha =>
    induction b using (SIdx.lt_wf (I := J)).induction with
    | _ b ihb =>
      refine ⟨_, fun ⟨a', b'⟩ h => ?_⟩
      rcases h with h | ⟨h, h'⟩
      · exact iha a' h b'
      · cases h
        exact ihb b' h'

/-- Rocq: `pair_index_mixin`, `pairI`.

This is not a global instance: it would make type class search for `SIdx ?SI` (with the step-index
type still unknown) enumerate `SIdxPair Nat (SIdxPair Nat …)` forever. Register it for a concrete
abbreviation with `local instance` and then `local stepindex`. -/
@[rocq_alias pair_index_mixin, reducible]
def instSIdx : SIdx (SIdxPair I J) where
  zero := ⟨0, 0⟩
  succ p := ⟨p.fst, SIdx.succ p.snd⟩
  lt_trans {p q r} hpq hqr := by
    rcases hpq with h1 | ⟨h1, h1'⟩ <;> rcases hqr with h2 | ⟨h2, h2'⟩
    · exact .inl (SIdx.lt_trans h1 h2)
    · exact .inl (h2 ▸ h1)
    · exact .inl (h1 ▸ h2)
    · exact .inr ⟨h1.trans h2, SIdx.lt_trans h1' h2'⟩
  lt_wf := lt_wf
  lt_trichotomyT p q :=
    match SIdx.lt_trichotomyT p.fst q.fst with
    | .inl h => .inl (.inl h)
    | .inr (.inr h) => .inr (.inr (.inl h))
    | .inr (.inl h) =>
      match SIdx.lt_trichotomyT p.snd q.snd with
      | .inl h' => .inl (.inr ⟨h, h'⟩)
      | .inr (.inl h') => .inr (.inl (SIdxPair.ext h h'))
      | .inr (.inr h') => .inr (.inr (.inr ⟨h.symm, h'⟩))
  le_lteq := .rfl
  not_lt_zero p h := by
    rcases h with h | ⟨_, h⟩
    · exact SIdx.not_lt_zero _ h
    · exact SIdx.not_lt_zero _ h
  lt_succ_self p := .inr ⟨rfl, SIdx.lt_succ_self _⟩
  succ_le_of_lt {p q} h := by
    rcases h with h | ⟨h, h'⟩
    · exact .inl (.inl h)
    · rcases SIdx.le_lteq.mp (SIdx.succ_le_of_lt h') with h'' | h''
      · exact .inl (.inr ⟨h, h''⟩)
      · exact .inr (SIdxPair.ext h h'')
  weak_case p :=
    match SIdx.weak_case p.snd with
    | .inl ⟨b, hb⟩ => .inl ⟨⟨p.fst, b⟩, SIdxPair.ext rfl hb⟩
    | .inr hlim => .inr fun q hq => by
      rcases hq with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨h, hlim _ h'⟩

attribute [local instance] instSIdx

theorem succ_def (p : SIdxPair I J) : SIdx.succ p = ⟨p.fst, SIdx.succ p.snd⟩ := rfl

theorem repeat_succ (k : Nat) (m : I) (n : J) :
    Nat.repeat SIdx.succ k (⟨m, n⟩ : SIdxPair I J) = ⟨m, Nat.repeat SIdx.succ k n⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.repeat, ih, succ_def]

/-- Rocq: `pair_rc_right`. -/
@[rocq_alias pair_rc_right]
theorem le_right_iff {n : I} {m m' : J} :
    (⟨n, m⟩ : SIdxPair I J) ≤ ⟨n, m'⟩ ↔ m ≤ m' := by
  constructor
  · rintro ((h | ⟨_, h⟩) | h)
    · exact absurd h (SIdx.lt_irrefl n)
    · exact SIdx.le_lteq.mpr (.inl h)
    · cases h; exact SIdx.le_refl
  · intro h
    rcases SIdx.le_lteq.mp h with h | rfl
    · exact .inl (.inr ⟨rfl, h⟩)
    · exact .inr rfl

/-- Pairs of step-indices are transfinite: `(succ m, n)` is above all `(m, succ^k n)`. -/
instance instSIdxTransfinite : SIdxTransfinite (SIdxPair I J) where
  upperLimit p := ⟨SIdx.succ p.fst, p.snd⟩
  iter_succ_lt_upperLimit k p := by
    rw [repeat_succ]
    exact .inl (SIdx.lt_succ_self _)

end SIdxPair

end Iris
