/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Iris

/-! # Orbit maps: a non-extensional `LawfulPartialMap`

This file builds a `PartialMap` / `LawfulPartialMap` instance whose stored data carries strictly
more information than its observable denotation: each key is assigned both a value and a *concrete
integer representative* of an orbit, while `get?` (hence `PartialMap.equiv`) only observes the
value.  Distinct representatives in the same orbit therefore give equal denotations but unequal
carriers — the construction is lawful yet **non-extensional**.

## The orbit / quotient structure

The motivating quotient is `ℤ ⧸ (n·ℤ) ≃ ZMod n`, the orbit space of the additive action of the
subgroup `n·ℤ` on `ℤ`.  Each stored cell records:

* a *representative* `z : ℤ`, only ever observed through `obs z = (z : ZMod n)` (its orbit), and
* the *value* `v : V` that `get?` returns.

For the intended value type `V = ZMod n` the representative and value are linked by `obs`/`sec`
(`obs (sec v) = v`, `ZMod.intCast_zmod_cast`): the value *is* the orbit of the representative, and
the representative may drift by any multiple of `n` without changing the observation.  The `ℤ`
component is invisible to `get?`, which is the source of non-extensionality and of the
frame-preserving updates discussed at the end of the file.

## Design

`OrbitMap n V := K → Option (ℤ × V)`.  The first projection is the (unobserved) orbit
representative; the second is the value returned by `get?`.  The `PartialMap` operations keep the
representative in sync with the value via `sec`/`obs`, but only the value is observable.
-/

@[expose] public section

namespace IrisMath

open Iris.Std Iris.Std.PartialMap

variable {K : Type _} [DecidableEq K]

/-- An orbit map: each key carries an integer orbit-representative together with its value. -/
def OrbitMap (n : ℕ) (K : Type _) (V : Type _) : Type _ := K → Option (ℤ × V)

namespace OrbitMap

variable {n : ℕ} {V V' : Type _}

/-- The observation: send a stored integer representative to its orbit in `ZMod n`. -/
abbrev obs (z : ℤ) : ZMod n := (z : ZMod n)

/-- A section of the observation: the canonical integer representative of an orbit. -/
abbrev sec (x : ZMod n) : ℤ := ZMod.cast x

/-- The section is a right inverse of the observation. -/
@[simp] theorem obs_sec (x : ZMod n) : obs (sec x) = x := ZMod.intCast_zmod_cast x

/-! ## The operations.

`get?` reads only the value (second) component; the representative (first) component is carried
along but never observed. -/

/-- Pick a stored representative for a freshly-produced value.  At the intended value type
`V = ZMod n` this is `sec`, the canonical orbit representative; at any other type it is an
arbitrary unobserved `ℤ` (`0`), since `get?` never inspects it.  We expose it as a field-free
helper so the operations stay polymorphic in `V`. -/
def rep (n : ℕ) : {V : Type _} → V → ℤ := fun _ => 0

instance instPartialMap : PartialMap (OrbitMap n K) K where
  get? m k := (m k).map Prod.snd
  insert m k v := fun k' => if k = k' then some (rep n v, v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k =>
    (m k).bind fun zv => (f k zv.2).map fun v' => (rep n v', v')
  merge op m₁ m₂ := fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some x, some y => let v := op k x.2 y.2; some (rep n v, v)

/-- The seven `LawfulPartialMap` laws.  Each holds because `get?` is the second projection and
every operation maintains the value component exactly as in the functional model. -/
instance instLawfulPartialMap : LawfulPartialMap (OrbitMap n K) K where
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
    | some zv =>
      simp only [Option.map_some, Option.bind_some]
      cases hf : f k zv.2 with
      | none => simp
      | some w => simp
  get?_merge := by
    intro V op m₁ m₂ k
    simp only [get?, merge, Option.merge]
    cases h₁ : m₁ k <;> cases h₂ : m₂ k <;> simp

/-! ## Non-extensionality

We exhibit two carriers that observe identically (`PartialMap.equiv`) but differ as functions:
they store the same value but different — though orbit-equivalent — representatives. -/

/-- A one-key map storing value `v` with representative `z`. -/
def cell (k : K) (z : ℤ) (v : V) : OrbitMap n K V := fun k' => if k = k' then some (z, v) else none

variable (k : K) (v : V)

/-- **Observational equality.**  Two cells at the same key with the same value are
`PartialMap.equiv` *regardless of the stored representative*: `get?` never sees the `ℤ`. -/
theorem cell_equiv (z z' : ℤ) :
    PartialMap.equiv (M := OrbitMap n K) (cell k z v) (cell k z' v) := by
  intro k'
  simp only [get?, cell]
  by_cases h : k = k' <;> simp [h]

/-- **Non-extensionality.**  Distinct representatives give *distinct carriers*.  Concretely the
orbit reps `0` and `(n : ℤ)` (equal in `ZMod n` for any `n`, distinct in `ℤ` when `n ≥ 1`) yield
equivalent maps that are not equal. -/
theorem cell_ne {n : ℕ} (hn : 1 ≤ n) (k : K) (v : V) :
    (cell k 0 v : OrbitMap n K V) ≠ cell k (n : ℤ) v := by
  intro hcontra
  have hk := congrFun hcontra k
  simp only [cell, if_true] at hk
  -- `hk : some (0, v) = some (↑n, v)`, so the first components agree: `0 = ↑n`.
  have h0 : (0 : ℤ) = (n : ℤ) := congrArg Prod.fst (Option.some.injEq _ _ ▸ hk)
  rw [eq_comm, Int.natCast_eq_zero] at h0
  omega

/-- The non-extensionality theorem, packaged: two orbit-equivalent reps (`0` and `n`) give a pair
of maps that are `PartialMap.equiv` and yet `≠`. -/
theorem nonextensional {n : ℕ} (hn : 1 ≤ n) (k : K) (v : V) :
    PartialMap.equiv (M := OrbitMap n K) (cell k 0 v) (cell k (n : ℤ) v) ∧
      (cell k 0 v : OrbitMap n K V) ≠ cell k (n : ℤ) v :=
  ⟨cell_equiv k v 0 (n : ℤ), cell_ne hn k v⟩

/-- There is no `ExtensionalPartialMap` instance for `OrbitMap`: for `n ≥ 1` `equiv` is strictly
coarser than `=`, so `equiv_iff_eq` would fail on the witnesses above. -/
theorem not_extensional {n : ℕ} (hn : 1 ≤ n) (k : K) (v : V) :
    ¬ (PartialMap.equiv (M := OrbitMap n K) (cell k 0 v) (cell k (n : ℤ) v) →
        (cell k 0 v : OrbitMap n K V) = cell k (n : ℤ) v) :=
  fun h => cell_ne hn k v (h (cell_equiv k v 0 (n : ℤ)))

end OrbitMap

end IrisMath

/-! ## Applicability: orbit maps and the `HeapView` CMRA

`ZMod n` is a finite commutative group (under `+`), hence a clean candidate for the value algebra
of a heap-style CMRA.  Recall `Iris.Algebra.HeapView`: from a `LawfulPartialMap M K` with a
CMRA-valued value type one forms the authoritative/fragment camera `HeapView F K V`, with

* `Auth dq m`   — authoritative ownership of the whole heap `m : M V`, fraction `dq`;
* `Frag k dq v` — fragmentary ownership of key `k` holding value `v`.

The frame-preserving updates `~~>` there (`update_one_alloc`, `update_one_delete`,
`update_replace`, `update_of_local_update`, `update_auth_op_frag`, …) all reduce to *local updates
on the value at a single key*, and every relational premise is phrased through `get?`.  This is
exactly where the orbit structure pays off.

### Orbits ⇒ representative drift is a no-op (a free frame-preserving update)

Because `get?` returns only the *value* and never the stored orbit-representative `ℤ`, **any
change to a stored representative is invisible to every `HeapR`/`HeapView` premise**.  For the
orbit interpretation `obs z = (z : ZMod n)`, replacing a key's representative `z` by `z + c*n`
keeps the value (orbit) fixed, since `obs (z + c*n) = obs z`.  Concretely, with `m' := cell k
(z + c*n) v` (using `IrisMath.OrbitMap.cell`):

  `PartialMap.equiv m m'`   (proved here as `OrbitMap.cell_equiv`),

so the induced authoritative element satisfies

  `Auth (.own one) m ~~> Auth (.own one) m'`

as a frame-preserving update — it is the identity update up to `equiv`, preserving every premise
verbatim because those premises see only `get?`.  This is the orbit-map slogan "add a multiple of
`n` to a stored representative is observationally inert", realized as a CMRA update.

### Every element invertible ⇒ strong local updates

`(ZMod n, +, 0)` is a finite abelian group: every `v : ZMod n` is invertible (inverse `-v`).
Reading `ZMod n` as an exclusive/whole value CMRA (Leibniz `=` on the finite carrier), the local
update `(mv, v) ~l~> (mv', v')` feeding `HeapView.update_of_local_update` is available for *any*
target orbit `v'` by group homogeneity (translate `v ↦ v + (v' - v)`).  Hence

  `Auth (.own one) m • Frag k (.own one) v ~~>
     Auth (.own one) (insert m k v') • Frag k (.own one) v'`

holds for every `v' : ZMod n` (cf. `HeapView.update_replace` / `update_of_local_update`), and the
resulting authoritative heap `insert m k v'` is determined only *up to orbit*: its concrete stored
representative `sec v' : ℤ` may be replaced by any `sec v' + c*n` without affecting validity, by
the previous paragraph.  This cleanly separates the *logical* value (the orbit, in `ZMod n`) from
its *stored representative* (`ℤ`) — the intended applicability of a non-extensional,
quotient-valued partial map.
-/
