/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris

/-! # `ConstOnFilterMap`: the general non-extensional `LawfulPartialMap` from a filter

This file isolates the *general construction* behind `GermMap`, `ProductGermMap`, the
almost-everywhere random-variable map, and `CoarseningMap`.  All four are the SAME
construction instantiated at different "negligibility structures":

  GermMap          = `(Idx, l) := (ℕ, atTop)`            — differences on finite prefixes ignored
  ProductGermMap   = `(Idx, l) := (ℕ × ℕ, atTop)`        — differences on filter-thin crosses ignored
  a.e. r.v. map    = `(Idx, l) := (Ω, μ.ae)`             — differences on null sets ignored
  CoarseningMap    = `(Idx, l) := (ℕ, 𝓟 cell)`           — differences off a coarse cell ignored

## The construction

Fix an index type `Idx` and a filter `l : Filter Idx` with `[l.NeBot]`.  Define

  `ConstOnFilterMap l V := K → Option (Idx → V)`

storing at each key a *representative family* `Idx → V`.  The observation

  `get? m k := eventualValue l (m k)`

returns the unique value `c` such that the stored family is `=ᶠ[l]` the constant family `const c`
(if one exists), and `none` otherwise.  Because `l.NeBot`, that value is unique, so `get?` is
well-defined; and because two families agreeing `l`-eventually have the same `eventualValue`,
`get?` factors through the quotient of `Idx → V` by `Filter.EventuallyEq l`.

**This is the precise sense in which iris-lean's `PartialMap` admits genuinely non-extensional
instances:** `get?` may factor through a quotient by a filter's *small sets*.  Whenever `l` is not
the principal filter of a single point, distinct representatives differing only on an `l`-small set
collapse to the same observation, so `PartialMap.equiv` does not imply `=`.

All seven `LawfulPartialMap` laws are proved once here, filter-agnostically; every concrete instance
is a one-line specialization (`K := ℕ`, choose `(Idx, l)`).
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap Filter

variable {K : Type _} [DecidableEq K] {Idx : Type _} {V V' : Type _}

open Classical in
/-- The `l`-eventual value of a family `Idx → V`: the unique `c` with `s =ᶠ[l] (fun _ => c)`,
if one exists.  Well-defined (unique `c`) when `[l.NeBot]`. -/
noncomputable def eventualValue (l : Filter Idx) (s : Idx → V) : Option V :=
  if h : ∃ c, s =ᶠ[l] (fun _ => c) then some h.choose else none

variable {l : Filter Idx}

/-- For a `NeBot` filter, two constant families that agree `l`-eventually have equal constants. -/
theorem const_eq_of_eventuallyEq [l.NeBot] {c c' : V}
    (h : (fun _ : Idx => c) =ᶠ[l] (fun _ => c')) : c = c' := by
  obtain ⟨i, hi⟩ := h.exists
  exact hi

/-- If `s` is `l`-eventually constant `= c`, its `eventualValue` is `some c`. -/
theorem eventualValue_of_eventuallyEq [l.NeBot] {s : Idx → V} {c : V}
    (h : s =ᶠ[l] (fun _ => c)) : eventualValue l s = some c := by
  have hex : ∃ c, s =ᶠ[l] (fun _ => c) := ⟨c, h⟩
  rw [eventualValue, dif_pos hex]
  exact congrArg some (const_eq_of_eventuallyEq (hex.choose_spec.symm.trans h))

/-- The eventual value of a constant family is that constant. -/
@[simp] theorem eventualValue_const [l.NeBot] (v : V) :
    eventualValue l (fun _ : Idx => v) = some v :=
  eventualValue_of_eventuallyEq EventuallyEq.rfl

/-- **Germ-invariance**: families agreeing `l`-eventually have the same `eventualValue`.
This is the heart of non-extensionality — the observation factors through `Filter.EventuallyEq`. -/
theorem eventualValue_congr [l.NeBot] {s s' : Idx → V} (h : s =ᶠ[l] s') :
    eventualValue l s = eventualValue l s' := by
  by_cases hex : ∃ c, s =ᶠ[l] (fun _ => c)
  · obtain ⟨c, hc⟩ := hex
    rw [eventualValue_of_eventuallyEq hc, eventualValue_of_eventuallyEq (h.symm.trans hc)]
  · have hex' : ¬ ∃ c, s' =ᶠ[l] (fun _ => c) := fun ⟨c, hc⟩ => hex ⟨c, h.trans hc⟩
    rw [eventualValue, dif_neg hex, eventualValue, dif_neg hex']

/-- **Converse of `eventualValue_of_eventuallyEq`.** If the `l`-eventual value of `s` is `some c`,
then `s` really is `l`-eventually constant `= c`.  Lets one read a genuine convergence fact back out
of a germ — the inverse direction of the germ quotient. -/
theorem eventuallyEq_of_eventualValue [l.NeBot] {s : Idx → V} {c : V}
    (h : eventualValue l s = some c) : s =ᶠ[l] (fun _ => c) := by
  by_cases hex : ∃ c, s =ᶠ[l] (fun _ => c)
  · rw [eventualValue, dif_pos hex] at h
    have hc : hex.choose = c := Option.some.inj h
    rw [← hc]; exact hex.choose_spec
  · rw [eventualValue, dif_neg hex] at h; simp at h

/-- **Germ tail-invariance.** Over `atTop`, dropping the first term of a sequence does not change
its eventual value: the germ depends only on arbitrarily-late behavior.  (The shift `(· + 1)` is
`atTop`-to-`atTop` cofinal, so eventual-constancy transfers in both directions.) -/
theorem eventualValue_tail {s : ℕ → V} :
    eventualValue atTop (fun n => s (n + 1)) = eventualValue atTop s := by
  rcases hs : eventualValue atTop s with _ | c
  · rcases ht : eventualValue atTop (fun n => s (n + 1)) with _ | c'
    · rfl
    · exfalso
      have htc : (fun n => s (n + 1)) =ᶠ[atTop] (fun _ => c') := eventuallyEq_of_eventualValue ht
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htc
      have hsc : s =ᶠ[atTop] (fun _ => c') :=
        Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => by
          have := hN (m - 1) (by omega)
          simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using this⟩
      rw [eventualValue_of_eventuallyEq hsc] at hs
      simp at hs
  · have hsc : s =ᶠ[atTop] (fun _ => c) := eventuallyEq_of_eventualValue hs
    have htc : (fun n => s (n + 1)) =ᶠ[atTop] (fun _ => c) :=
      (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id).eventually hsc
    rw [eventualValue_of_eventuallyEq htc]

/-- The general construction: a partial map storing a representative family at each key,
observed only up to `l`-eventual equality. -/
def ConstOnFilterMap (_l : Filter Idx) (K V : Type _) : Type _ := K → Option (Idx → V)

namespace ConstOnFilterMap

variable (l)

/-- The forgetful denotation: read back the `l`-eventual value stored at `k`. -/
noncomputable def get? (m : ConstOnFilterMap l K V) (k : K) : Option V :=
  (m k).bind (eventualValue l)

/-- Insert stores the *constant* family `fun _ => v`. -/
def insert (m : ConstOnFilterMap l K V) (k : K) (v : V) : ConstOnFilterMap l K V :=
  fun k' => if k = k' then some (fun _ => v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : ConstOnFilterMap l K V) (k : K) : ConstOnFilterMap l K V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : ConstOnFilterMap l K V := fun _ => none

/-- `bindAlter` applies `f` to the eventual value of each stored family, restoring a constant. -/
noncomputable def bindAlter (f : K → V → Option V') (m : ConstOnFilterMap l K V) :
    ConstOnFilterMap l K V' :=
  fun k => (get? l m k).bind (fun v => (f k v).map (fun w => fun _ => w))

/-- `merge` combines the eventual values of two stored families, restoring a constant. -/
noncomputable def merge (op : K → V → V → V) (m₁ m₂ : ConstOnFilterMap l K V) :
    ConstOnFilterMap l K V :=
  fun k => (Option.merge (op k) (get? l m₁ k) (get? l m₂ k)).map (fun w => fun _ => w)

variable [l.NeBot]

noncomputable instance instPartialMap : PartialMap (ConstOnFilterMap l K) K where
  get? := get? l
  insert := insert l
  delete := delete l
  empty := empty l
  bindAlter := bindAlter l
  merge := merge l

@[simp] theorem get?_eq (m : ConstOnFilterMap l K V) (k : K) :
    PartialMap.get? m k = (m k).bind (eventualValue l) := rfl

noncomputable instance instLawfulPartialMap : LawfulPartialMap (ConstOnFilterMap l K) K where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ConstOnFilterMap.insert, if_pos h, Option.bind_some,
      eventualValue_const]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, ConstOnFilterMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ConstOnFilterMap.delete, if_pos h, Option.bind_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, ConstOnFilterMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (ConstOnFilterMap.bindAlter l f m k).bind (eventualValue l)
      = (get? l m k).bind (f k)
    unfold ConstOnFilterMap.bindAlter
    cases hv : get? l m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [eventualValue_const]
  get?_merge {V op m₁ m₂ k} := by
    show (ConstOnFilterMap.merge l op m₁ m₂ k).bind (eventualValue l)
      = Option.merge (op k) (get? l m₁ k) (get? l m₂ k)
    unfold ConstOnFilterMap.merge
    cases h : Option.merge (op k) (get? l m₁ k) (get? l m₂ k) with
    | none => simp
    | some w => simp [eventualValue_const]

/-! ## Non-extensionality, once and for all

If the filter `l` is *not* the pure filter of a single point — concretely, if there exist two
distinct families `s ≠ s'` that are `l`-eventually equal — then `ConstOnFilterMap l K` is
non-extensional.  We package the witness abstractly: any `l`-small modification of a constant
family is observationally invisible. -/

/-- **General non-extensionality.**  Given a key `k₀` and two families `s, s'` that agree
`l`-eventually (`s =ᶠ[l] s'`) but are unequal as functions (`s ≠ s'`), the two singleton maps
storing them are `PartialMap.equiv` yet distinct.  Hence any filter with a nontrivial small set
yields a non-extensional `PartialMap`. -/
theorem nonextensional_of_eventuallyEq (k₀ : K) {s s' : Idx → V}
    (heq : s =ᶠ[l] s') (hne : s ≠ s') :
    PartialMap.equiv (M := ConstOnFilterMap l K)
        (fun k => if k = k₀ then some s else none)
        (fun k => if k = k₀ then some s' else none)
      ∧ (fun k => if k = k₀ then some s else none)
          ≠ (fun k : K => if k = k₀ then some s' else none) := by
  refine ⟨fun k => ?_, ?_⟩
  · show ((if k = k₀ then some s else none).bind (eventualValue l))
        = ((if k = k₀ then some s' else none).bind (eventualValue l))
    by_cases hk : k = k₀
    · rw [if_pos hk, if_pos hk, Option.bind_some, Option.bind_some, eventualValue_congr heq]
    · rw [if_neg hk, if_neg hk]
  · intro h
    have h0 := congrFun h k₀
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    exact hne h0

end ConstOnFilterMap

/-! ## Specializations (each is a one-liner)

`GermMap`        — `ConstOnFilterMap (atTop : Filter ℕ) ℕ` (finite-prefix differences ignored).
`ProductGermMap` — `ConstOnFilterMap (atTop : Filter (ℕ × ℕ)) ℕ` (thin-cross differences ignored).
The almost-everywhere random-variable map — `ConstOnFilterMap (μ.ae) ℕ`.
`CoarseningMap`  — `ConstOnFilterMap (𝓟 {i | c i = c i₀}) ℕ` (off-cell differences ignored).

The example below shows the non-extensionality witness specialized to `(ℕ, atTop)`: the constant-`0`
sequence versus a sequence bumped at index `0` agree `atTop`-eventually but differ as functions,
so they collapse. -/

open ConstOnFilterMap in
example :
    PartialMap.equiv (M := ConstOnFilterMap (atTop : Filter ℕ) ℕ)
        (fun k => if k = 0 then some (fun _ => 0) else none)
        (fun k => if k = 0 then some (fun n => if n = 0 then 1 else 0) else none)
      ∧ (fun k => if k = 0 then some (fun _ => (0 : ℕ)) else none)
          ≠ (fun k : ℕ => if k = 0 then some (fun n => if n = 0 then 1 else 0) else none) := by
  refine nonextensional_of_eventuallyEq (l := (atTop : Filter ℕ)) 0 ?_ ?_
  · rw [EventuallyEq, eventually_atTop]
    exact ⟨1, fun b hb => by simp [Nat.one_le_iff_ne_zero.mp hb]⟩
  · intro h
    have := congrFun h 0
    simp at this

end IrisMath.Instances
