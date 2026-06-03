/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Iris

/-! # Abelianization maps: a non-extensional `LawfulPartialMap`

This file builds a `PartialMap` / `LawfulPartialMap` instance whose stored data carries strictly
more information than its observable denotation: each key is assigned both a value and a *concrete
group element* `g` of a fixed **non-abelian** group `G`, while `get?` (hence `PartialMap.equiv`)
only observes the value.  Distinct group elements lying in the same **abelianization class** (i.e.
differing by a commutator / conjugation) therefore give equal denotations but unequal carriers —
the construction is lawful yet **non-extensional**.

It is the group-theoretic generalization of `IrisMath.OrbitMap`.  Where `OrbitMap` quotients an
integer representative by the *cyclic* additive action of `n·ℤ` (orbits in `ℤ ⧸ n·ℤ ≃ ZMod n`),
`AbelianizationMap` quotients a representative `g ∈ G` by the *commutator subgroup* `[G, G]`, i.e.
observes it only through the abelianization map `Abelianization.of : G →* Abelianization G`.
Both are instances of the same slogan: **observe a stored representative only up to a group
quotient**; here the quotient is the abelianization `G ⧸ [G, G]`.

## The abelianization / quotient structure

Fix a group `G`.  The abelianization is the universal abelian quotient `Gᵃᵇ = G ⧸ [G, G]`, with
projection `Abelianization.of : G →* Abelianization G`.  Two elements have the same image iff they
differ by an element of the commutator subgroup; in particular **conjugate elements always have the
same abelianization image**, since in the commutative group `Gᵃᵇ`

  `of (h * g * h⁻¹) = of h * of g * (of h)⁻¹ = of g`.

Each stored cell records:

* a *representative* `g : G`, only ever observed through its abelianization class `Abelianization.of
  g`, and
* the *value* `v : V` that `get?` returns.

The `G` component is invisible to `get?`, which is the source of non-extensionality and of the
frame-preserving updates discussed at the end of the file.

For the non-extensionality witness we take `G = Equiv.Perm (Fin 3)` (the symmetric group `S₃`),
which is genuinely non-abelian: its commutator subgroup is the alternating group `A₃`, and its
abelianization is `ℤ/2` detected by the sign.  Two distinct transpositions are conjugate in `S₃`
(`swap 0 2 = (swap 1 2) * (swap 0 1) * (swap 1 2)⁻¹`), hence collapse to the same abelianization
class while remaining distinct elements of `S₃` — a real distinct-representative / same-image pair.

## Design

`AbelianizationMap G K V := K → Option (G × V)`.  The first projection is the (unobserved)
representative `g ∈ G`; the second is the value returned by `get?`.  The `PartialMap` operations
keep a canonical representative in sync with the value, but only the value is observable.  This
mirrors `IrisMath.OrbitMap`'s `K → Option (ℤ × V)` shape exactly, replacing the integer
orbit-representative by a group representative and the `ZMod n` orbit observation by the
abelianization observation `Abelianization.of`.
-/

@[expose] public section

namespace IrisMath

open Iris.Std Iris.Std.PartialMap

variable {K : Type _} [DecidableEq K]

/-- An abelianization map for a group `G`: each key carries a representative `g ∈ G` together with
its value. -/
def AbelianizationMap (G : Type _) (K : Type _) (V : Type _) : Type _ := K → Option (G × V)

namespace AbelianizationMap

variable {G : Type _} [Group G] {V V' : Type _}

/-- The observation: send a stored group representative to its **abelianization class** in
`Abelianization G = G ⧸ [G, G]`, via the universal projection `Abelianization.of`.  This is the
group-quotient analogue of `OrbitMap.obs`: it forgets everything about `g` except its image modulo
the commutator subgroup. -/
abbrev obs (g : G) : Abelianization G := Abelianization.of g

/-- **Conjugate representatives observe equally.**  In the abelian quotient `Gᵃᵇ` conjugation is
inert: `of (h * g * h⁻¹) = of g`.  Replacing a stored representative by a conjugate is therefore
invisible to `obs`. -/
@[simp] theorem obs_conj (h g : G) : obs (h * g * h⁻¹) = obs g := by
  simp only [obs, map_mul, map_inv]
  rw [mul_comm (Abelianization.of h) (Abelianization.of g), mul_assoc,
    mul_inv_cancel, mul_one]

/-! ## The operations.

`get?` reads only the value (second) component; the representative (first) component is carried
along but never observed. -/

/-- Pick a stored representative for a freshly-produced value.  We expose it as a field-free helper
so the operations stay polymorphic in `V`; `get?` never inspects it, so the canonical choice `1`
(the group identity) suffices. -/
def rep (G : Type _) [Group G] : {V : Type _} → V → G := fun _ => 1

instance instPartialMap : PartialMap (AbelianizationMap G K) K where
  get? m k := (m k).map Prod.snd
  insert m k v := fun k' => if k = k' then some (rep G v, v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k =>
    (m k).bind fun gv => (f k gv.2).map fun v' => (rep G v', v')
  merge op m₁ m₂ := fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some x, some y => let v := op k x.2 y.2; some (rep G v, v)

/-- The seven `LawfulPartialMap` laws.  Each holds because `get?` is the second projection and
every operation maintains the value component exactly as in the functional model. -/
instance instLawfulPartialMap : LawfulPartialMap (AbelianizationMap G K) K where
  get?_empty k := rfl
  get?_insert_eq := by simp only [get?, Iris.Std.insert]; grind
  get?_insert_ne := by simp only [get?, Iris.Std.insert]; grind
  get?_delete_eq := by simp only [get?, Iris.Std.delete]; grind
  get?_delete_ne := by simp only [get?, Iris.Std.delete]; grind
  get?_bindAlter := by
    intro V V' k m f
    simp only [get?, bindAlter]
    cases h : m k with
    | none => simp
    | some gv =>
      simp only [Option.map_some, Option.bind_some]
      cases hf : f k gv.2 with
      | none => simp
      | some w => simp
  get?_merge := by
    intro V op m₁ m₂ k
    simp only [get?, merge, Option.merge]
    cases h₁ : m₁ k <;> cases h₂ : m₂ k <;> simp

/-! ## Non-extensionality

We exhibit two carriers that observe identically (`PartialMap.equiv`) but differ as functions:
they store the same value but **conjugate** representatives `g` and `h * g * h⁻¹`. -/

/-- A one-key map storing value `v` with representative `g`. -/
def cell (k : K) (g : G) (v : V) : AbelianizationMap G K V :=
  fun k' => if k = k' then some (g, v) else none

variable (k : K) (v : V)

/-- **Observational equality.**  Two cells at the same key with the same value are
`PartialMap.equiv` *regardless of the stored representative*: `get?` never sees the `G`.  In
particular this holds for conjugate representatives `g` and `h * g * h⁻¹`. -/
theorem cell_equiv (g g' : G) :
    PartialMap.equiv (M := AbelianizationMap G K) (cell k g v) (cell k g' v) := by
  intro k'
  simp only [get?, cell]
  by_cases h : k = k' <;> simp [h]

omit [Group G] in
/-- **Distinct representatives give distinct carriers.**  If `g ≠ g'` then the two single-key cells
storing `g` resp. `g'` (with the same value) are unequal as functions. -/
theorem cell_ne {g g' : G} (hg : g ≠ g') (k : K) (v : V) :
    (cell k g v : AbelianizationMap G K V) ≠ cell k g' v := by
  intro hcontra
  have hk := congrFun hcontra k
  simp only [cell, if_true] at hk
  -- `hk : some (g, v) = some (g', v)`, so the first components agree: `g = g'`.
  exact hg (congrArg Prod.fst ((Option.some.injEq _ _).mp hk))

/-! ### The concrete non-abelian witness: `S₃ = Equiv.Perm (Fin 3)`

Two distinct transpositions are conjugate in `S₃`, hence share an abelianization class while being
distinct group elements.  This is a genuine distinct-representative / same-image pair: `S₃` is
non-abelian (its commutator subgroup `A₃` is nontrivial), so `Abelianization.of` is genuinely
forgetful here. -/

/-- The transposition `(0 1)` in `S₃`. -/
abbrev g₀ : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The transposition `(0 2)` in `S₃`, equal to the conjugate `(1 2)·(0 1)·(1 2)⁻¹`. -/
abbrev g₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The conjugating element `(1 2)`: it carries `(0 1)` to `(0 2)`. -/
abbrev h₀ : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- `(0 2)` is the conjugate of `(0 1)` by `(1 2)`: `g₁ = h₀ * g₀ * h₀⁻¹`. -/
theorem g₁_eq_conj : g₁ = h₀ * g₀ * h₀⁻¹ := by decide

/-- The two transpositions are **distinct** elements of `S₃`. -/
theorem g₀_ne_g₁ : g₀ ≠ g₁ := by decide

/-- The two transpositions have the **same abelianization image**: conjugate elements collapse in
`Abelianization (Equiv.Perm (Fin 3))`.  This is the crux of non-extensionality — distinct group
elements, equal quotient image. -/
theorem obs_g₀_eq_g₁ : obs g₀ = obs g₁ := by
  rw [g₁_eq_conj, obs_conj]

/-- **Non-extensionality witness.**  Two conjugate transpositions `(0 1)` and `(0 2)` in `S₃`:
their cells are `PartialMap.equiv` (same value, and the representative is unobserved) yet `≠` (the
stored group elements are distinct).  The representatives even have equal abelianization image
(`obs_g₀_eq_g₁`), so this is a genuine quotient collapse, not an artifact of `get?` ignoring `G`. -/
theorem nonextensional (k : K) (v : V) :
    PartialMap.equiv (M := AbelianizationMap (Equiv.Perm (Fin 3)) K)
        (cell k g₀ v) (cell k g₁ v) ∧
      (cell k g₀ v : AbelianizationMap (Equiv.Perm (Fin 3)) K V) ≠ cell k g₁ v :=
  ⟨cell_equiv k v g₀ g₁, cell_ne g₀_ne_g₁ k v⟩

/-- There is no `ExtensionalPartialMap` instance for `AbelianizationMap`: over the non-abelian `S₃`,
`equiv` is strictly coarser than `=`, so `equiv_iff_eq` would fail on the conjugate witnesses
above. -/
theorem not_extensional (k : K) (v : V) :
    ¬ (PartialMap.equiv (M := AbelianizationMap (Equiv.Perm (Fin 3)) K)
          (cell k g₀ v) (cell k g₁ v) →
        (cell k g₀ v : AbelianizationMap (Equiv.Perm (Fin 3)) K V) = cell k g₁ v) :=
  fun hh => cell_ne g₀_ne_g₁ k v (hh (cell_equiv k v g₀ g₁))

end AbelianizationMap

end IrisMath

/-! ## Applicability: abelianization maps and the `HeapView` CMRA

Recall `Iris.Algebra.HeapView`: from a `LawfulPartialMap M K` with a CMRA-valued value type one
forms the authoritative/fragment camera `HeapView F K V`, with

* `Auth dq m`   — authoritative ownership of the whole heap `m : M V`, fraction `dq`;
* `Frag k dq v` — fragmentary ownership of key `k` holding value `v`.

The frame-preserving updates `~~>` there (`update_one_alloc`, `update_one_delete`,
`update_replace`, `update_of_local_update`, `update_auth_op_frag`, …) all reduce to *local updates
on the value at a single key*, and every relational premise is phrased through `get?`.  This is
exactly where the abelianization structure pays off.

### Abelianization classes are the logical content of a cell

The logical content of a stored cell is its *abelianization class* `obs g = Abelianization.of g ∈
G ⧸ [G, G]`.  A heap that "remembers only data invariant under conjugation / commutators" stores a
representative `g ∈ G` but exposes, through `get?`, only data invariant under the abelianization
projection.

### Conjugation is a no-op ⇒ an abelianization frame-preserving update

Because `get?` returns only the *value* and never the stored representative `g`, **any change to a
stored representative is invisible to every `HeapR`/`HeapView` premise**.  The canonical such
change is *replacing a representative by a conjugate*: `g ↦ h * g * h⁻¹`.  Since
`obs (h * g * h⁻¹) = obs g`
(`AbelianizationMap.obs_conj`), conjugation keeps the abelianization class — and the value — fixed.
Concretely, with `m := cell k g v` and `m' := cell k (h * g * h⁻¹) v` (using
`IrisMath.AbelianizationMap.cell`):

  `PartialMap.equiv m m'`   (proved here as `AbelianizationMap.cell_equiv`),

so the induced authoritative element satisfies the frame-preserving update

  `Auth (.own one) m ~~> Auth (.own one) m'`

— it is the identity update up to `equiv`, preserving every premise verbatim because those premises
see only `get?`.  This is a genuinely **group-theoretic** frame-preserving update: "replace a stored
group element by a conjugate" is observationally inert, realized as a CMRA update.  It generalizes
the `OrbitMap` slogan "adding a multiple of `n` to a representative is inert" from the cyclic group
`ZMod n` to the abelianization quotient `G ⧸ [G, G]` of an arbitrary (possibly non-abelian) group.

### From cyclic orbits to abelianization orbits

This file generalizes `IrisMath.OrbitMap` along one axis only — the group quotient through which
the stored representative is observed:

| construction          | representative | quotient               | observation         |
| --------------------- | -------------- | ---------------------- | ------------------- |
| `OrbitMap n`          | `z : ℤ`        | `ℤ ⧸ n·ℤ ≃ ZMod n`     | `z ↦ (z : ZMod n)`  |
| `AbelianizationMap G` | `g : G`        | `G ⧸ [G, G]`           | `g ↦ of g`          |

Both are "observe a stored representative up to a group quotient", with the quotient semantics
living entirely in the witnesses and applicability while `get?` stays a bare second projection.  For
non-abelian `G` (e.g. `S₃`) the commutator subgroup `[G, G]` is nontrivial, so the quotient is a
proper collapse: non-extensionality is genuine.
-/
