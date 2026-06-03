/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Linter.Header
public import Iris

/-! # The abstract recipe behind every non-extensional `LawfulPartialMap`

Across the `IrisMath/Instances/` collection, every intrinsically non-extensional instance turned
out to have the *same* shape, forced by the polymorphism of `get? : M V → K → Option V`:

> Store, at each key, a value of some richer "payload" type `S V`, and observe it through a
> *readout* `ρ : S V → Option V`.  The seven `LawfulPartialMap` laws hold as soon as `S` carries a
> distinguished "pure" payload `pure v : S V` with `ρ (pure v) = some v`, because every operation
> can be implemented by reading out, combining the resulting `Option`s, and re-storing a `pure`.
> The instance is **non-extensional** exactly when `ρ` is not injective: two payloads `p ≠ p'` with
> `ρ p = ρ p'` give two representatives the interface cannot distinguish.

This file makes that recipe a single, reusable theorem.  A `Readout S` bundles `pure` and `ρ` with
the one coherence law `ρ (pure v) = some v`.  From it we derive a `LawfulPartialMap` on
`ReadoutMap S K V := K → Option (S V)`, plus a general non-extensionality criterion.

Every concrete instance is then a one-liner:
- `GermMap`/`ConstOnFilterMap` : `S V = Idx → V`, `pure v = const v`, `ρ = l-eventual value`.
- `KnowledgeMap`              : `S V = Set V`,   `pure v = {v}`,    `ρ s = (if s = {v} then v)`.
- `HistoryMap`/`ResidueMap`    : `S V = List V`,  `pure v = [v]`,    `ρ = getLast?`/`head?`.

The point: non-extensionality is not ad hoc — it is precisely the failure of `ρ` to be injective,
and the entire `PartialMap` algebra is transported through `ρ` uniformly.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

/-- A `Readout` on a payload functor `S` is a way to store a value (`pure`) and observe it (`ρ`),
such that observing a freshly-stored value returns it.  `ρ` need not be injective — that is exactly
the room for non-extensionality. -/
structure Readout (S : Type _ → Type _) where
  /-- Store a value as a canonical "pure" payload. -/
  pure : {V : Type _} → V → S V
  /-- Observe a payload, possibly forgetting structure. -/
  ρ : {V : Type _} → S V → Option V
  /-- Reading out a freshly-stored value returns it. -/
  ρ_pure : {V : Type _} → (v : V) → ρ (pure v) = some v

namespace Readout

variable {S : Type _ → Type _} (R : Readout S) {K : Type _} [DecidableEq K] {V V' : Type _}

/-- The partial map carrier: a function from keys to optional payloads. -/
def Map (_R : Readout S) (K V : Type _) : Type _ := K → Option (S V)

variable (K V) in
/-- Reading out an `Option`-payload cell. -/
def get? (m : R.Map K V) (k : K) : Option V := (m k).bind R.ρ

@[simp] theorem get?_pure_cell (m : R.Map K V) (k : K) :
    R.get? K V m k = (m k).bind R.ρ := rfl

/-- Storing the readout of an option as a pure payload round-trips through `ρ`. -/
@[simp] theorem rho_store (o : Option V) : (o.map R.pure).bind R.ρ = o := by
  cases o with
  | none => rfl
  | some v => simp [R.ρ_pure]

noncomputable instance instPartialMap : PartialMap (R.Map K) K where
  get? := R.get? K _
  insert m k v := fun k' => if k = k' then some (R.pure v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k => ((R.get? K _ m k).bind (f k)).map R.pure
  merge op m₁ m₂ :=
    fun k => (Option.merge (op k) (R.get? K _ m₁ k) (R.get? K _ m₂ k)).map R.pure

@[simp] theorem get?_eq (m : R.Map K V) (k : K) :
    PartialMap.get? m k = (m k).bind R.ρ := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap (R.Map K) K where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, instPartialMap, if_pos h, Option.bind_some, R.ρ_pure]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, instPartialMap, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, instPartialMap, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, instPartialMap, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (((R.get? K V m k).bind (f k)).map R.pure).bind R.ρ = (R.get? K V m k).bind (f k)
    exact R.rho_store _
  get?_merge {V op m₁ m₂ k} := by
    show ((Option.merge (op k) (R.get? K V m₁ k) (R.get? K V m₂ k)).map R.pure).bind R.ρ
      = Option.merge (op k) (R.get? K V m₁ k) (R.get? K V m₂ k)
    exact R.rho_store _

/-! ## Non-extensionality criterion

The map is non-extensional exactly when the readout `ρ` collapses two distinct payloads. -/

/-- **General non-extensionality.**  If two payloads `p ≠ p'` have the same readout (`ρ p = ρ p'`),
then the two singleton maps storing them at a key are `PartialMap.equiv` but unequal.  Hence any
readout whose `ρ` is not injective yields a non-extensional `LawfulPartialMap`. -/
theorem nonextensional_of_readout_eq (k₀ : K) {p p' : S V}
    (hρ : R.ρ p = R.ρ p') (hne : p ≠ p') :
    PartialMap.equiv (M := R.Map K)
        (fun k => if k = k₀ then some p else none)
        (fun k => if k = k₀ then some p' else none)
      ∧ (fun k => if k = k₀ then some p else none)
          ≠ (fun k : K => if k = k₀ then some p' else none) := by
  refine ⟨fun k => ?_, ?_⟩
  · show ((if k = k₀ then some p else none).bind R.ρ) = ((if k = k₀ then some p' else none).bind R.ρ)
    by_cases hk : k = k₀
    · rw [if_pos hk, if_pos hk, Option.bind_some, Option.bind_some, hρ]
    · rw [if_neg hk, if_neg hk]
  · intro h
    have h0 := congrFun h k₀
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    exact hne h0

/-- **The converse: injective total readout ⇒ extensional.**  If `ρ` is injective and never returns
`none` (so every payload denotes *some* value), then `(·).bind ρ` is injective on `Option (S V)`,
hence `PartialMap.equiv` implies equality and the map is `ExtensionalPartialMap`.  Together with
`nonextensional_of_readout_eq` this pins the innovation precisely: **a `Readout` map is
non-extensional iff its readout `ρ` is non-injective** (in the total case).  The earlier hand-built
instances are non-extensional *because* their readouts genuinely collapse data. -/
noncomputable def extensionalOfInjective
    (hinj : ∀ {V : Type _}, Function.Injective (R.ρ (V := V)))
    (htot : ∀ {V : Type _} (p : S V), R.ρ p ≠ none) :
    ExtensionalPartialMap (R.Map K) K where
  toPartialMap := R.instPartialMap
  equiv_iff_eq {V m₁ m₂} := by
    refine ⟨fun h => funext fun k => ?_, fun h => h ▸ fun _ => rfl⟩
    have hk : (m₁ k).bind R.ρ = (m₂ k).bind R.ρ := h k
    cases h₁ : m₁ k with
    | none =>
      cases h₂ : m₂ k with
      | none => rfl
      | some p₂ => rw [h₁, h₂] at hk; exact absurd hk.symm (htot p₂)
    | some p₁ =>
      cases h₂ : m₂ k with
      | none => rw [h₁, h₂] at hk; exact absurd hk (htot p₁)
      | some p₂ =>
        rw [h₁, h₂] at hk
        simp only [Option.bind_some] at hk
        exact congrArg some (hinj hk)

end Readout

/-! ## Worked specializations of the abstract recipe

These show three previously hand-built instances arising as `Readout` corollaries with NO new
proof work — the laws come entirely from `instLawfulPartialMap`. -/

/-- `List V` with `pure v = [v]` and `ρ = getLast?` — the write-log / "last writer wins" readout
(the `HistoryMap` pattern).  `getLast?` is non-injective, so this is non-extensional. -/
def historyReadout : Readout List where
  pure v := [v]
  ρ := List.getLast?
  ρ_pure v := rfl

/-- `List V` with `pure v = [v]` and `ρ = head?` — the polynomial-residue / first-coefficient
readout (the `ResidueMap` pattern). -/
def residueReadout : Readout List where
  pure v := [v]
  ρ := List.head?
  ρ_pure v := rfl

/-- Non-extensionality of the write-log readout, as a corollary of the general criterion:
`[7]` and `[3, 7]` have the same `getLast?` but are distinct. -/
example :
    PartialMap.equiv (M := historyReadout.Map Nat)
        (fun k => if k = 0 then some [7] else none)
        (fun k => if k = 0 then some [3, 7] else none)
      ∧ (fun k => if k = 0 then some [7] else none)
          ≠ (fun k : Nat => if k = 0 then some [3, (7 : Nat)] else none) :=
  historyReadout.nonextensional_of_readout_eq 0 rfl (by decide)

/-- Non-extensionality of the residue readout: `[0]` and `[0, 1]` share `head?` but differ. -/
example :
    PartialMap.equiv (M := residueReadout.Map Nat)
        (fun k => if k = 0 then some [0] else none)
        (fun k => if k = 0 then some [0, 1] else none)
      ∧ (fun k => if k = 0 then some [0] else none)
          ≠ (fun k : Nat => if k = 0 then some [0, (1 : Nat)] else none) :=
  residueReadout.nonextensional_of_readout_eq 0 rfl (by decide)

end IrisMath.Instances
