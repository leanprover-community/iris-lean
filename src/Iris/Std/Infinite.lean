/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

/-- A set S is infinite if there exists an injection from Nat into the set of elements
  such that S holds. -/
def infinite (S : P → Prop) : Prop :=
  ∃ f : Nat → P, (∀ n, S <| f n) ∧ (∀ n m : Nat, f n = f m → n = m)

class InfiniteType (T : Type _) where
  enum : Nat → T
  enum_inj : ∀ n m : Nat, enum n = enum m → n = m

open Classical in
/-- Arbitrarily changing one element of a co-infinite set yields a co-infinite set -/
theorem cofinite_alter_cofinite {S S' : P → Prop} (p' : P) (Ha : ∀ p, p ≠ p' → S p = S' p)
    (Hs : infinite S) : infinite S' := by
  rcases Hs with ⟨f, HfS, Hfinj⟩
  -- Basically, alter f so that f never hits p'.
  rcases em (∃ n, f n = p') with (⟨n, H⟩|H)
  · exists fun n' => if n' < n then f n' else f n'.succ; grind
  · exists f; grind

open Classical in
/- Update a (classical) function at a point. Used to specify the correctness of stores. -/
noncomputable def fset {K V : Type _} (f : K → V) (k : K) (v : V) : K → V :=
  fun k' => if k = k' then v else f k'

@[simp] def cosupport (f : K → Option V) : K → Prop := ((· == false) ∘ Option.isSome ∘ f)

theorem coinfinite_fset_coinfinite (f : K → Option V) (H : infinite (cosupport f)) :
    infinite (cosupport (fset f k v)) := by
  apply cofinite_alter_cofinite  k _ H
  simp [fset]
  grind

theorem coinfinte_exists_next {f : K → Option V} :
    infinite (cosupport f) → ∃ k, f k = none := by
  rintro ⟨enum, Henum, _⟩
  exists enum 0
  simp [] at Henum
  grind
