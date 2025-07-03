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


theorem coinfinte_exists_next {f : K → Option V} :
  coinfinite (support f) → ∃ k, f k = none := by sorry


/-- This is closer to gmap, but still a generalization. Among other things, gmap can only express
finite maps. To support allocation, you actually only need the complement to be infinite. This construction can,
for example, express an infinite number of pices of ghost state while retaining the ability to dynamically
allocate new ghost state. -/
noncomputable def instClassicaAllocHeap : AllocHeap (K → Option V) K V where
  toHeap := instClassicalHeap
  fresh HC _ := Classical.choose (coinfinte_exists_next HC)
  fresh_get HC := Classical.choose_spec (coinfinte_exists_next HC)

-- TODO: Heaps indexed by natural numbers. Still a generalization over Iris because
-- an infinite number of values can be givien non-default values!

end instances
