/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap

-- Library functions: move me

/-- A set S is infinite if there exists an injection from Nat into the set of elements
  such that S holds. -/
def infinite (S : P → Prop) : Prop :=
  ∃ f : Nat → P, (∀ n, S <| f n) ∧ (∀ n m : Nat, f n = f m → n = m)

class InfiniteType (T : Type _) where
  enum : Nat → T
  enum_inj : ∀ n m : Nat, enum n = enum m → n = m


/-- Arbitrarily changing one element of a co-infinite set yields a co-infinite set -/
theorem cofinite_alter_cofinite {S S' : P → Prop} (p' : P) (Ha : ∀ p, p ≠ p' → S p = S' p)
    (Hs : infinite S) : infinite S' := by
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

open Classical in
/- Update a (classical) function at a point. Used to specify the correctness of stores. -/
noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
  fun k' => if (k = k') then v else f k'

@[simp] def cosupport (f : K → Option V) : K → Prop := ((· == false) ∘ Option.isSome ∘ f)

theorem coinfinite_fset_coinfinite (f : K → Option V) (H : infinite (cosupport f)) :
    infinite (cosupport (fset f k v)) := by
  apply cofinite_alter_cofinite  k _ H
  intro p Hpk
  simp [cosupport, fset]
  split
  · simp_all
  · rfl

section instances

noncomputable instance instClassicalStore {K V : Type _} : Store (K → V) K V where
  get := id
  set := fset
  get_set_eq H := by rw [H]; simp [fset]
  get_set_ne H := by simp_all [fset]

noncomputable instance instClassicalHeap : Heap (K → Option V) K V where
  hmap h f k := match f k with | none => none | some x => h k x
  get_hmap := by
    intro f t k
    simp [Store.get, Option.bind]
    cases h1 : t k <;> simp_all
  empty _ := none
  get_empty := by simp [Store.get]
  merge op f1 f2 k :=
    match f1 k, f2 k with
    | some v1, some v2 => some <| op v1 v2
    | some v1, none => some v1
    | none, some v2 => some v2
    | none, none => none
  get_merge := by
    simp [Store.get]
    intros
    split <;> simp_all [Option.merge]

theorem coinfinte_exists_next {f : K → Option V} :
    infinite (cosupport f) → ∃ k, f k = none := by
  rintro ⟨enum, Henum, Henum_inj⟩
  exists (enum 0)
  simp [cosupport] at Henum
  apply Henum

noncomputable instance instClassicaAllocHeap : AllocHeap (K → Option V) K V where
  toHeap := instClassicalHeap
  notFull f := infinite <| cosupport f
  fresh HC := Classical.choose (coinfinte_exists_next HC)
  get_fresh {_ HC} := Classical.choose_spec (coinfinte_exists_next HC)

noncomputable instance [InfiniteType K] : UnboundedHeap ( K → Option V) K V where
  notFull_empty := by
    simp [notFull, empty, Function.comp, infinite]
    exists InfiniteType.enum
    exact fun n m a => InfiniteType.enum_inj n m a
  notFull_set_fresh {t v H} := by
    simp only [notFull] at ⊢ H
    apply cofinite_alter_cofinite (Hs := H) (p' := @fresh (K → Option V) K _ _ _ H)
    intro p
    intro Hp
    simp [cosupport]
    simp [Store.set, fset]
    split <;> simp_all

end instances
