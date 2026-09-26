/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.StepIndex

/-! # Properties of step-index types used by Transfinite Iris

This file ports the step-index property classes of Transfinite Iris
(`theories/algebra/stepindex.v`, Spies et al., PLDI 2021):

- `SIdxTransfinite` (`TransfiniteIndex`): above every index there is an index that is larger than
  all its finite successors. Needed for the soundness of `⧍` ("big later") and hence for
  adequacy of the transfinite program logic.
- `SIdxLarge` (`LargeIndex`): existential quantification over a (small) type commutes with
  universal quantification over step-indices, for downward-closed predicates. This is the
  "existential property" of the paper and holds for sufficiently large ordinals.
- The classes `FiniteExistential` and `FiniteBoundedExistential` of the Rocq development hold for
  every type of step-indices since Lean's logic is classical; they are stated as theorems here
  (`SIdx.forall_or`, `SIdx.forall_lt_or`, `SIdx.commute_finite_exists`,
  `SIdx.commute_finite_bounded_exists`). The Rocq class `Classical` is not needed.
-/

@[expose] public section

namespace Iris

open SIdx

/-- A type of step-indices is *transfinite* if above every index there is an index that is larger
than all its finite successors (Transfinite Iris, `TransfiniteIndex`). -/
class SIdxTransfinite (I : Type u) [SIdx I] where
  /-- An index above all finite iterates of `succᵢ` starting at the argument. -/
  upperLimit : I → I
  /-- Every finite iterate of `succᵢ` is below `upperLimit`. -/
  iter_succ_lt_upperLimit (n : Nat) (m : I) : Nat.repeat SIdx.succ n m < upperLimit m

/-- A type of step-indices is *large* (relative to the universe `v`) if existential quantification
over types in `Type v` commutes with universal quantification over the indices, for predicates
that are downward closed in the index (Transfinite Iris, `LargeIndex`).

This is the *existential property* of the Transfinite Iris paper. It fails for `Nat` and holds
for the ordinals of a larger universe. -/
class SIdxLarge.{v} (I : Type u) [SIdx I] : Prop where
  commute_exists {X : Type v} (P : X → I → Prop) :
    (∀ x a b, a < b → P x b → P x a) → (∀ a, ∃ x, P x a) → ∃ x, ∀ a, P x a

namespace SIdx

variable {I : Type u} [SIdx I]

/-- Transfinite Iris's `FiniteExistential` (`can_split_or`) holds classically for every type of
step-indices (cf. `classical_finite_existential`). -/
theorem forall_or {P Q : I → Prop}
    (hP : ∀ {a b}, a ≤ b → P b → P a) (hQ : ∀ {a b}, a ≤ b → Q b → Q a)
    (h : ∀ a, P a ∨ Q a) : (∀ a, P a) ∨ (∀ a, Q a) := by
  refine Classical.or_iff_not_imp_left.mpr fun hnP m => ?_
  obtain ⟨a, hPa⟩ := Classical.not_forall.mp hnP
  rcases le_total (n := a) (m := m) with hle | hle
  · rcases h m with hPm | hQm
    · exact absurd (hP hle hPm) hPa
    · exact hQm
  · rcases h a with hPa' | hQa
    · exact absurd hPa' hPa
    · exact hQ hle hQa

/-- `Transfinite Iris`'s `can_commute_finite_exists`: an existential over a finite set of
witnesses (given by a list `l`) commutes with universal quantification over step-indices. -/
theorem commute_finite_exists {X : Type v} (P : X → I → Prop) (Q : X → Prop) (l : List X)
    (hfin : ∀ x, Q x → x ∈ l) (hdown : ∀ x {a b}, a ≤ b → P x b → P x a)
    (hsome : ∀ a, ∃ x, Q x ∧ P x a) : ∃ x, ∀ a, P x a := by
  have hsome' : ∀ a, ∃ x, x ∈ l ∧ P x a := fun a =>
    let ⟨x, hQ, hP⟩ := hsome a; ⟨x, hfin x hQ, hP⟩
  clear hsome hfin
  induction l with
  | nil => obtain ⟨_, h, _⟩ := hsome' 0; cases h
  | cons x l ih =>
    rcases forall_or (P := P x) (Q := fun a => ∃ y, y ∈ l ∧ P y a) (hdown x)
        (fun hab ⟨y, hy, hPy⟩ => ⟨y, hy, hdown y hab hPy⟩)
        (fun a => by
          obtain ⟨y, hy, hPy⟩ := hsome' a
          rcases List.mem_cons.mp hy with rfl | hy
          · exact .inl hPy
          · exact .inr ⟨y, hy, hPy⟩) with h | h
    · exact ⟨x, h⟩
    · exact ih h

/-- Transfinite Iris's `can_commute_finite_bounded_exists`: the bounded version of
`commute_finite_exists`. -/
theorem commute_finite_bounded_exists {X : Type v} (P : X → I → Prop) (Q : X → Prop) (l : List X)
    {c : I} (hc : 0 < c) (hfin : ∀ x, Q x → x ∈ l) (hdown : ∀ x {a b}, a ≤ b → P x b → P x a)
    (hsome : ∀ a, a < c → ∃ x, Q x ∧ P x a) : ∃ x, ∀ a, a < c → P x a := by
  have hsome' : ∀ a, a < c → ∃ x, x ∈ l ∧ P x a := fun a ha =>
    let ⟨x, hQ, hP⟩ := hsome a ha; ⟨x, hfin x hQ, hP⟩
  clear hsome hfin
  induction l with
  | nil => obtain ⟨_, h, _⟩ := hsome' 0 hc; cases h
  | cons x l ih =>
    rcases forall_lt_or (P := P x) (Q := fun a => ∃ y, y ∈ l ∧ P y a) (hdown x)
        (fun hab ⟨y, hy, hPy⟩ => ⟨y, hy, hdown y hab hPy⟩)
        (fun a ha => by
          obtain ⟨y, hy, hPy⟩ := hsome' a ha
          rcases List.mem_cons.mp hy with rfl | hy
          · exact .inl hPy
          · exact .inr ⟨y, hy, hPy⟩) with h | h
    · exact ⟨x, h⟩
    · exact ih h

end SIdx

end Iris
