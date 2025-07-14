/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap

-- Heaps with finite domain, represented as an association list


inductive FiniteDomFunction (K V : Type _)
| empty : FiniteDomFunction K V
| set : K → V → FiniteDomFunction K V



-- noncomputable def instFiniteHeap {K V : Type _} : Heap (List (K × V)) K V where
--   ofFun := sorry

  -- get l k := l[k]
  -- set := fset
  -- ofFun := id
  -- get_set_eq H := by rw [H]; simp [fset]
  -- get_set_ne H := by simp_all [fset]
  -- ofFun_get := rfl


/-
noncomputable def instClassicalHeap : Heap (K → Option V) K V where
  toStore := instClassicalStore
  point k ov := fset (fun _ => none) k ov
  point_get_eq H := by simp [H, StoreLike.get, fset, instClassicalStore]
  point_get_ne H := by simp [H, StoreLike.get, fset, instClassicalStore]


theorem coinfinte_exists_next {f : K → Option V} :
    infinite (cosupport f) → ∃ k, f k = none := by
  rintro ⟨enum, Henum, Henum_inj⟩
  exists (enum 0)
  simp [cosupport] at Henum
  apply Henum

/-- This is closer to gmap, but still a generalization. Among other things, gmap can only express
finite maps. To support allocation, you actually only need the complement to be infinite. This construction can,
for example, express an infinite number of pices of ghost state while retaining the ability to dynamically
allocate new ghost state. -/
noncomputable def instClassicaAllocHeap : AllocHeap (K → Option V) K V where
  toHeap := instClassicalHeap
  hasRoom f := infinite <| cosupport f
  fresh HC := Classical.choose (coinfinte_exists_next HC)
  fresh_get {_ HC} := Classical.choose_spec (coinfinte_exists_next HC)
  hasRoom_set_fresh {_ H _} := coinfinite_fset_coinfinite _ H
-/
end instances
