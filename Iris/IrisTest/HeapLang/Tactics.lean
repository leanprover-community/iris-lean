/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.ProofMode
public import Iris.HeapLang

namespace Iris.HeapLang

section Fractional

variable {hlc : HasLC} {GF : BundledGFunctors} [ι : HeapLangGS hlc GF]

/--
  Tests `icases` with the use of `intoSepFractionalHalf` after backtracking
  from `intoSepFractional`.
-/
example (l : Loc) (v : Val) :
    l ↦ v ⊢ l ↦{.own (.half 1)} v ∗ l ↦{.own (.half 1)} v := by
  iintro Hl
  icases Hl with ⟨H1, H2⟩
  iframe

/--
  Tests `icases` with the use of `intoSepFractional`, which has higher
  priority than `intoSepFractionalHalf`.
-/
example (l : Loc) (v : Val) :
    l ↦{.own (q1 + q2)} v ⊢ l ↦{.own q1} v ∗ l ↦{.own q2} v := by
  iintro Hl
  icases Hl with ⟨H1, H2⟩
  iframe

/-- Tests `icombine` with the use of `combineSepAsFractionalHalf`. -/
example (l : Loc) (v : Val) :
    l ↦{.own (.half 1)} v ∗ l ↦{.own (.half 1)} v ⊢ l ↦ v := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 as Hl
  iassumption

/-- Tests `icombine` with the use of `combineSepAsFractional`. -/
example (l : Loc) (v : Val) :
    l ↦{.own q1} v ∗ l ↦{.own q2} v ⊢ l ↦{.own (q1 + q2)} v := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 as Hl
  iassumption

end Fractional
