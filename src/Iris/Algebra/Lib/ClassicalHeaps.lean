/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap

-- Library functions: move me


-- TODO: Move do a library file?
section instances

noncomputable def instClassicalStore {K V : Type _} : Store (K → V) K V where
  get := id
  set := fset
  of_fun := id
  get_set_eq H := by rw [H]; simp [fset]
  get_set_ne H := by simp_all [fset]
  of_fun_get := rfl

noncomputable def instClassicalHeap : Heap (K → Option V) K V where
  toStore := instClassicalStore
  point k ov := fset (fun _ => none) k ov
  point_get_eq H := by simp [H, StoreLike.get, fset, instClassicalStore]
  point_get_ne H := by simp [H, StoreLike.get, fset, instClassicalStore]


abbrev CoInfiniteHeap (K V : Type _) : Type _ :=
  { f : K → Option V // coinfinite (support f) }


/-- This is closer to gmap, but still a generalization. Among other things, gmap can only express
finite maps. To support allocation, you actually only need the complement to be infinite. This construction can,
for example, express an infinite number of pices of ghost state while retaining the ability to dynamically
allocate new ghost state. -/
noncomputable instance : AllocHeap (CoInfiniteHeap K V) K V where
  get := sorry -- id
  set f k ov := ⟨fset f.1 k ov, coinfinite_fset_coinfinite f.1 f.2⟩
  of_fun := sorry -- id
    -- Hm--this should actually be a coinfinite function in this case.
  get_set_eq H := by
    rw [H]; simp [fset]
    sorry
  get_set_ne H := by
    simp_all [fset]
    sorry
  of_fun_get := by
    sorry
  point k ov := sorry -- fset (fun _ => none) k ov
  point_get_eq H := by
    -- simp [H, StoreLike.get, fset, instClassicalStore]
    sorry
  point_get_ne H := by
    -- simp [H, StoreLike.get, fset, instClassicalStore]
    sorry
  fresh := sorry
  fresh_get := sorry




end instances
