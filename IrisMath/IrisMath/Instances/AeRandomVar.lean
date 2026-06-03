module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Order.Filter.Germ.Basic
public import Iris

/-! # A non-extensional `LawfulPartialMap` of random variables modulo a.e. equality

This file builds a `LawfulPartialMap` whose stored cells each carry a **random variable**
`Ω → δ` — a measurable "ghost" observed only up to almost-everywhere equality with respect to a
fixed measure `μ` on `Ω` — alongside the actual value.  The denotation (`get?`) forgets the
random variable entirely (it is `μ`-a.e. data, invisible to any observer), so two stores whose
ghost random variables differ only on a `μ`-null set have *identical* denotations yet are
*distinct* Lean values.  This is the non-extensionality prize.

## Representation

Fix a measurable space `Ω` and a measure `μ : Measure Ω`, a key type `K` with `DecidableEq K`.
The carrier, polymorphic in the value type `V`, is a function-keyed store of raw cells:

```
RawCell μ V := (Ω → V) × V                  -- a raw random variable + the value
AeStore μ K V := K → Option (RawCell μ V)
```

`get? m k` projects out only the value component `V`, throwing away the random variable.  The
partial-map value type is therefore the bare `V`, and `PartialMap.equiv` (pointwise `get?`
equality) compares only the values — never the ghost random variables.

The reason this is the *a.e.* construction rather than arbitrary junk: the discarded component is
exactly a random variable `Ω → V`, which the measure observes only through its a.e.-class
`Filter.Germ (ae μ) V`.  Two cells whose random variables agree `μ`-a.e. (`f =ᵐ[μ] g`, i.e.
`(↑f : Germ (ae μ) V) = ↑g`) are semantically identical from the measure's perspective; the store
identifies even more (it forgets the r.v. completely), and in particular identifies them — see
`aeStore_nonExtensional_of_ae` and `aeStore_nonExtensional_of_null` below.

All seven `LawfulPartialMap` laws hold, proved by reducing every operation to the pointwise
functional model `IrisMath.PMapHarness.Den` on `K → Option V`.

## The value CMRA / HeapView applicability

The natural value CMRA upgrades the value slot from a bare `V` to an a.e.-class of a random
variable, `Filter.Germ (ae μ) δ`, the quotient of `Ω → δ` by `=ᵐ[μ]`.  For any `AddCommMonoid δ`
(`δ = ℝ`, integrable r.v.s, …) `Filter.Germ` transports the monoid pointwise, giving the
commutative monoid of **random variables under pointwise addition, modulo a.e.**.  Its OFE is
precisely the `aeOFE` of `MeasureTheory.lean`: `x ≡ y ↔ x =ᵐ[μ] y`.  With the unital/trivial
validity this is a value (U)CMRA, and heap cells store an a.e.-class of a random variable.

The frame-preserving updates `~~>` this enables are exactly the **a.e.-invisible** ones:

* **Replace by an a.e.-equal random variable.**  `f =ᵐ[μ] g ⇒ (↑f : Germ (ae μ) V) = ↑g`, so the
  germ-valued cell is unchanged: a `~~>` update by reflexivity that nevertheless rewires the raw
  random variable on a null set (`germ_update_ae`).
* **Modify on a null set.**  Overwriting `f` on any `S` with `μ S = 0` keeps the same germ, hence
  the same cell (`germ_eq_of_modify_null`).

No observer whose view factors through `get?`/the germ can detect these updates: the measure
cannot see the change.  This is the measure-theoretic analogue of the classical "ghost" / null
frame updates of a `HeapView` CMRA.
-/

@[expose] public section

noncomputable section

open Iris Iris.Std Filter MeasureTheory

namespace IrisMath.Instances.AeRandomVar

variable {Ω : Type _} [MeasurableSpace Ω] {K : Type _} [DecidableEq K]

/-! ## Carrier -/

/-- A raw cell: a raw random variable `Ω → V` (the "ghost", observed only up to `μ`-a.e.
equality) paired with the stored value `V`. -/
abbrev RawCell (_μ : Measure Ω) (V : Type _) : Type _ := (Ω → V) × V

/-- The carrier: a function-keyed store of raw cells.  Two stores that differ only in the ghost
random variables (e.g. they differ only on a `μ`-null set) denote the same partial map but are
distinct Lean values. -/
def AeStore (μ : Measure Ω) (K V : Type _) : Type _ := K → Option (RawCell μ V)

variable {μ : Measure Ω} {V V' : Type _}

/-- The constant random variable at `v`; the canonical ghost attached by `insert`. -/
@[simp] def constRV (v : V) : RawCell μ V := (fun _ => v, v)

/-! ## `PartialMap` instance

`get?` reads off only the value component, so the denotation is `K → Option V`, exactly the
functional model.  Every operation mirrors `IrisMath.PMapHarness.Den`. -/

instance instPartialMapAeStore : PartialMap (AeStore μ K) K where
  get? m k := (m k).map Prod.snd
  insert m k v := fun k' => if k = k' then some (constRV v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k =>
    (m k).bind fun c => (f k c.2).map constRV
  merge op m₁ m₂ := fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some c, none => some c
    | none, some c => some c
    | some c₁, some c₂ => some (constRV (op k c₁.2 c₂.2))

@[simp] theorem get?_def (m : AeStore μ K V) (k : K) :
    get? m k = (m k).map Prod.snd := rfl

instance instLawfulPartialMapAeStore : LawfulPartialMap (AeStore μ K) K where
  get?_empty k := rfl
  get?_insert_eq := by
    intro V m k k' v h
    simp only [get?, Iris.Std.insert, h, if_pos, Option.map_some, constRV]
  get?_insert_ne := by
    intro V m k k' v h
    simp only [get?, Iris.Std.insert]
    rw [if_neg h]
  get?_delete_eq := by
    intro V m k k' h
    simp only [get?, Iris.Std.delete, h, if_pos, Option.map_none]
  get?_delete_ne := by
    intro V m k k' h
    simp only [get?, Iris.Std.delete]
    rw [if_neg h]
  get?_bindAlter := by
    intro V V' k m f
    simp only [get?, bindAlter]
    cases h : m k with
    | none => rfl
    | some c =>
      simp only [Option.bind_some, Option.map_some, Option.map_map]
      cases hf : f k c.2 with
      | none => rfl
      | some x => simp [constRV]
  get?_merge := by
    intro V op m₁ m₂ k
    simp only [get?, merge]
    cases h₁ : m₁ k <;> cases h₂ : m₂ k <;>
      simp [Option.merge, constRV]

/-! ## Non-extensionality

The ghost random variable is invisible to `get?`.  In particular, two singleton stores whose
ghosts agree `μ`-a.e. (hence have equal germs) but are not equal as raw functions are
`PartialMap.equiv` yet unequal as Lean values. -/

/-- **Core non-extensionality witness.**  If the two ghost random variables `f, g : Ω → V` are
unequal as raw functions, the singleton stores carrying them (with the same value `v` at the same
key `k`) are `PartialMap.equiv` (their denotations both send `k ↦ some v`, everything else to
`none`) but unequal Lean values. -/
theorem aeStore_nonExtensional
    {f g : Ω → V} {v : V} {k : K} (hne : f ≠ g) :
    let m₁ : AeStore μ K V := fun k' => if k = k' then some (f, v) else none
    let m₂ : AeStore μ K V := fun k' => if k = k' then some (g, v) else none
    PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ := by
  refine ⟨?_, ?_⟩
  · intro k'
    simp only [get?_def]
    by_cases hk : k = k' <;> simp [hk]
  · intro heq
    apply hne
    have hk := congrFun heq k
    rw [if_pos rfl, if_pos rfl] at hk
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    exact hk.1

/-- **A.e.-flavored non-extensionality.**  The witnessing ghosts can be taken `μ`-a.e. equal — so
they are *identical from the measure's point of view* (equal germs `(↑f : Germ (ae μ) V) = ↑g`) —
yet still distinct raw functions, producing the same denotation but distinct stores.  This is the
sense in which the a.e.-quotient is the source of non-extensionality. -/
theorem aeStore_nonExtensional_of_ae
    {f g : Ω → V} {v : V} {k : K}
    (_hae : (↑f : Germ (ae μ) V) = (↑g : Germ (ae μ) V)) (hne : f ≠ g) :
    let m₁ : AeStore μ K V := fun k' => if k = k' then some (f, v) else none
    let m₂ : AeStore μ K V := fun k' => if k = k' then some (g, v) else none
    PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ :=
  aeStore_nonExtensional hne

/-- **Concrete instantiation.**  Given any `μ`-null set `S` and ghosts `f, g` agreeing off `S`,
they are `μ`-a.e. equal (`germ` equal) and, if they differ somewhere, distinct raw functions —
yielding non-extensionality from a genuine "difference on a null set". -/
theorem aeStore_nonExtensional_of_null
    {S : Set Ω} (hS : μ S = 0)
    {f g : Ω → V} {v : V} {k : K}
    (hoff : ∀ ω, ω ∉ S → f ω = g ω) (hne : f ≠ g) :
    let m₁ : AeStore μ K V := fun k' => if k = k' then some (f, v) else none
    let m₂ : AeStore μ K V := fun k' => if k = k' then some (g, v) else none
    PartialMap.equiv m₁ m₂ ∧ m₁ ≠ m₂ := by
  have hae : (↑f : Germ (ae μ) V) = (↑g : Germ (ae μ) V) := by
    rw [Germ.coe_eq]
    refine Filter.eventuallyEq_of_mem (s := Sᶜ) ?_ (fun ω hω => hoff ω hω)
    rw [mem_ae_iff]; simpa using hS
  exact aeStore_nonExtensional_of_ae hae hne

/-! ## Value CMRA / update sketch

Concrete statements backing the applicability discussion in the module header. -/

/-- **Replace by an a.e.-equal random variable.**  If `f =ᵐ[μ] g` then the germ-valued heap
cells are equal: a frame-preserving update by reflexivity that nonetheless changes the raw random
variable on a null set. -/
theorem germ_update_ae {f g : Ω → V} (h : f =ᵐ[μ] g) :
    (↑f : Germ (ae μ) V) = (↑g : Germ (ae μ) V) := Germ.coe_eq.mpr h

/-- **Modify on a null set.**  Overwriting `f` on a `μ`-null set `S` by arbitrary values `h`
leaves the germ-valued heap cell unchanged. -/
theorem germ_eq_of_modify_null {S : Set Ω} [∀ ω, Decidable (ω ∈ S)] (hS : μ S = 0) (f h : Ω → V) :
    (↑(S.piecewise h f) : Germ (ae μ) V) = (↑f : Germ (ae μ) V) := by
  rw [Germ.coe_eq]
  refine Filter.eventuallyEq_of_mem (s := Sᶜ) ?_ (fun ω hω => Set.piecewise_eq_of_notMem _ _ _ hω)
  rw [mem_ae_iff]; simpa using hS

end IrisMath.Instances.AeRandomVar
