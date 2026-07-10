/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.BigOp
public import Iris.Algebra.CMRA
meta import Iris.Std.RocqPorting

namespace Iris.Algebra

open OFE Iris.Std MonoidOps BigOpL

public section

variable {M : Type _} [CMRA M]

/-! # Big operators over CMRAs -/

variable {A : Type _}

namespace BigOpL

@[rocq_alias big_opL_None]
theorem bigOpL_none {f : Nat → A → Option M} {l : List A} :
    ([^ CMRA.op list] k ↦ x ∈ l, f k x) = none ↔
      ∀ k x, l[k]? = some x → f k x = none := by
  induction l generalizing f with
  | nil => exact iff_of_true rfl (by simp)
  | cons a l ih =>
    rw [bigOpL_cons, Iris.Option.op_none_iff, ih]
    refine ⟨fun ⟨h0, hl⟩ k x hx => ?_,
      fun h => ⟨h 0 a rfl, fun k x hx => h (k + 1) x hx⟩⟩
    match k with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      exact hx ▸ h0
    | k + 1 => exact hl k x hx

end BigOpL

namespace BigOpM

open scoped PartialMap
open LawfulPartialMap LawfulFiniteMap

variable {M' : Type _ → Type _} {K : Type _} {V : Type _} [LawfulFiniteMap M' K]

@[rocq_alias big_opM_None]
theorem bigOpM_none {f : K → V → Option M} {m : M' V} :
    ([^ CMRA.op map] k ↦ x ∈ m, f k x) = none ↔
      ∀ k x, get? m k = some x → f k x = none := by
  simp only [bigOpM, bigOpL_none]
  refine ⟨fun h k x hk => ?_,
    fun h i kx hi => h kx.1 kx.2 (toList_get.mp (List.mem_of_getElem? hi))⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (toList_get.mpr hk)
  exact h i (k, x) hi

end BigOpM

namespace BigOpS

variable {S : Type _} [LawfulFiniteSet S A]

@[rocq_alias big_opS_None]
theorem bigOpS_none {f : A → Option M} {s : S} :
    ([^ CMRA.op set] x ∈ s, f x) = none ↔ ∀ x, x ∈ s → f x = none := by
  simp only [bigOpS, bigOpL_none]
  refine ⟨fun h x hx => ?_,
    fun h k x hi => h x (FiniteSet.mem_toList.mp (List.mem_of_getElem? hi))⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (FiniteSet.mem_toList.mpr hx)
  exact h i x hi

end BigOpS

namespace BigOpMS

variable {MS : Type _} [LawfulFiniteMultiSet MS A]

@[rocq_alias big_opMS_None]
theorem bigOpMS_none {f : A → Option M} {X : MS} :
    ([^ CMRA.op mset] x ∈ X, f x) = none ↔ ∀ x, x ∈ X → f x = none := by
  simp only [bigOpMS, bigOpL_none]
  refine ⟨fun h x hx => ?_,
    fun h k x hi => h x (LawfulFiniteMultiSet.mem_toList.mp (List.mem_of_getElem? hi))⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (LawfulFiniteMultiSet.mem_toList.mpr hx)
  exact h i x hi

end BigOpMS

end
end Iris.Algebra
