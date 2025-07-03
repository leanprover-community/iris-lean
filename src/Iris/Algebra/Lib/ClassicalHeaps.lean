/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap

-- Library functions: move me

/-- A set whose complement is infinite -/
def coinfinite (S : P → Prop) : Prop :=
  ∃ f : Nat → P, (∀ n, S <| f n) ∧ (∀ n m : Nat, f n = f m → n = m)

/-- Arbitrarily changing one element of a co-infinite set yields a co-infinite set -/
theorem cofinite_alter_cofinite {S S' : P → Prop} (p' : P) (Ha : ∀ p, p ≠ p' → S p = S' p)
    (Hs : coinfinite S) : coinfinite S' := by
  rcases Hs with ⟨f, HfS, Hfinj⟩
  -- Basically, alter f so that f never hits p'.
  rcases (Classical.em (∃ n, f n = p')) with (⟨n, H⟩|H)
  · exists fun n' => if n' < n then f n' else f n'.succ
    constructor
    · intro n'
      simp only []
      split
      · rw [← Ha]
        · apply HfS
        · rename_i Hk'
          intro Hk
          exact Nat.lt_irrefl (n := n) <| (Hfinj _ _ (Hk ▸ H)) ▸ Hk'
      · rw [← Ha]
        · apply HfS
        · rename_i Hk'
          intro Hk
          have _ := (Hfinj _ _ (Hk ▸ H)) ▸ Hk'
          simp_all
    · intro n' m'
      simp only []
      split <;> split
      · apply Hfinj
      · intro H
        have Hfinj' := Hfinj _ _ H
        exfalso
        subst Hfinj'
        rename_i HK HK'
        apply HK
        exact Nat.lt_of_succ_lt HK'
      · intro H
        have Hfinj' := Hfinj _ _ H
        exfalso
        subst Hfinj'
        rename_i HK HK'
        apply HK
        exact Nat.lt_of_succ_lt HK'
      · intro H
        exact Nat.succ_inj.mp (Hfinj n'.succ m'.succ H)
  · exists f
    refine ⟨?_, Hfinj⟩
    exact fun n => (Ha _ (H ⟨n, ·⟩)) ▸ HfS n

-- TODO: Move do a library file?
section instances

open Classical in
/- Update a (classical) function at a point. Used to specify the correctness of stores. -/
noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
  fun k' => if (k = k') then v else f k'

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

@[simp] def support (f : K → Option V) : K → Prop := ((· == true) ∘ Option.isSome ∘ f)

abbrev CoInfiniteHeap (K V : Type _) : Type _ :=
  { f : K → Option V // coinfinite (support f) }

theorem coinfinite_fset_coinfinite (f : K → Option V) (H : coinfinite (support f)) :
    coinfinite (support (fset f k v)) := by
  apply cofinite_alter_cofinite  k _ H
  intro p Hpk
  simp [support, fset]
  split
  · simp_all
  · rfl

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
