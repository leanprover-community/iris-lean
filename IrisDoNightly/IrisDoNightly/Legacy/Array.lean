module

public import IrisDoNightly.Legacy.HeapAxioms

/-!
# Array reasoning for HeapLang `bytes`

`arrayPointsTo l vs` (`l ↦∗ vs`, defined in `SepLogic`) owns a contiguous block of cells holding
`vs`. This file develops the structural lemmas needed to reason about index-based loops over such a
block: the `cons`/`append` decompositions and the "focus on cell `i`" split. These are the
work-horses behind every codec that walks a `bytes` left to right.
-/

open Lean.Order
open Iris.HeapLang

@[expose] public section

namespace Iris.HeapLang

/-! ## Location offset arithmetic -/

@[simp] theorem Loc.add_zero (l : Loc) : l + (0 : Int) = l := by
  ext; simp

theorem Loc.add_assoc (l : Loc) (m n : Int) : l + m + n = l + (m + n) := by
  ext; simp; omega

namespace SL

/-! ## Structural lemmas for `↦∗` -/

@[simp] theorem arrayPointsTo_nil (l : Loc) : (l ↦∗ ([] : List Val)) = emp := rfl

theorem arrayPointsTo_cons (l : Loc) (v : Val) (vs : List Val) :
    (l ↦∗ (v :: vs)) = ((l ↦ v) ∗ ((l + (1 : Int)) ↦∗ vs)) := rfl

theorem arrayPointsTo_singleton (l : Loc) (v : Val) : (l ↦∗ [v]) = (l ↦ v) := by
  rw [arrayPointsTo_cons, arrayPointsTo_nil, sepConj_emp]

/-- Splitting an array assertion at a `++`: the suffix lives `vs.length` cells further along. -/
theorem arrayPointsTo_append (l : Loc) (vs ws : List Val) :
    (l ↦∗ (vs ++ ws)) = ((l ↦∗ vs) ∗ ((l + (vs.length : Int)) ↦∗ ws)) := by
  induction vs generalizing l with
  | nil => simp [emp_sepConj]
  | cons v vs ih =>
    have hoff : l + (1 : Int) + (vs.length : Int) = l + ((v :: vs).length : Int) := by
      ext; simp only [loc_add_n, List.length_cons]; push_cast; omega
    rw [List.cons_append, arrayPointsTo_cons, arrayPointsTo_cons, ih, hoff, sepConj_assoc]

/-- Split an array assertion at an index `i ≤ |vs|`: the tail lives `i` cells along.  The work-horse
for focusing cell `i` of an index-based loop (combine with `arrayPointsTo_cons` on the tail). -/
theorem arrayPointsTo_split (l : Loc) (vs : List Val) (i : Nat) (h : i ≤ vs.length) :
    (l ↦∗ vs) = ((l ↦∗ (vs.take i)) ∗ ((l + (i : Int)) ↦∗ (vs.drop i))) := by
  have hsplit := arrayPointsTo_append l (vs.take i) (vs.drop i)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left h] at hsplit
  exact hsplit

end SL
end Iris.HeapLang
