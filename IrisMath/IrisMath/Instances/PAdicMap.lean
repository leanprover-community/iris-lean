/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Iris

/-! # p-adic maps: an inverse-limit non-extensional `LawfulPartialMap`

This file builds a `PartialMap` / `LawfulPartialMap` instance whose stored data carries strictly
more information than its observable denotation: each key is assigned both a value and a *concrete
integer approximation* of a p-adic number, while `get?` (hence `PartialMap.equiv`) only observes
the value.  Integers that agree modulo a fixed precision `p ^ N` therefore give equal denotations
but unequal carriers — the construction is lawful yet **non-extensional**.

It is a direct generalization of `IrisMath.OrbitMap`: where `OrbitMap` observes a stored `ℤ`
through a *single* quotient `ZMod n`, `PAdicMap` observes it through a *fixed-precision truncation*
in the **inverse-limit tower** of the p-adic integers

  `ℤ_p  =  lim_N  ZMod (p ^ N)`     (`Mathlib.NumberTheory.Padics.PadicIntegers`, `ℤ_[p]`).

The truncations `ZMod (p ^ N)` form a projective system: for `M ≤ N` the ring map
`ZMod (p ^ N) → ZMod (p ^ M)` *refines precision* the other way, and `OrbitMap n` is recovered as
the single rung `n = p ^ N`.  The novelty over `OrbitMap` is exactly this tower: the observation is
a p-adic truncation, the applicable value algebra is the inverse-limit ring `ℤ_[p]` (or any finite
rung `ZMod (p ^ N)`), and the natural frame-preserving updates are tower moves — "add a multiple of
`p ^ N`" and "refine the precision `N`".

## The truncation / inverse-limit structure

Fix a prime `p` and a precision `N : ℕ`.  The observation is the ring truncation

  `obs z = (z : ZMod (p ^ N))`,

the image of the integer `z` in the `N`-th rung of the tower.  Each stored cell records:

* an *approximation* `z : ℤ`, only ever observed through `obs z : ZMod (p ^ N)` (its truncation),
  and
* the *value* `v : V` that `get?` returns.

For the intended value type `V = ZMod (p ^ N)` the approximation and value are linked by
`obs`/`sec` (`obs (sec v) = v`, `ZMod.intCast_zmod_cast`): the value *is* the p-adic truncation of
the approximation, and the approximation may drift by any multiple of `p ^ N` (a p-adically small
perturbation, `‖p ^ N‖_p = p ^ (-N)`) without changing the observation.  The `ℤ` component is
invisible to `get?`, which is the source of non-extensionality and of the frame-preserving updates
discussed at the end of the file.

## Design

`PAdicMap p N V := K → Option (ℤ × V)`.  The first projection is the (unobserved) p-adic
approximation; the second is the value returned by `get?`.  The `PartialMap` operations keep the
approximation in sync with the value via `sec`/`obs`, but only the value is observable.  This
mirrors `OrbitMap` structurally; the content lives in the quotient (`ZMod (p ^ N)` instead of an
arbitrary `ZMod n`) and its tower of refinements.
-/

@[expose] public section

namespace IrisMath

open Iris.Std Iris.Std.PartialMap

variable {K : Type _} [DecidableEq K]

set_option linter.unusedVariables false in
/-- A p-adic map at prime `p` and precision `N`: each key carries an integer p-adic approximation
together with its value.  The approximation is observed only through `ZMod (p ^ N)`, the `N`-th
rung of the inverse-limit tower `ℤ_[p] = lim_N ZMod (p ^ N)`.

`p` and `N` are phantom type parameters: the carrier is `K → Option (ℤ × V)` regardless, but they
select which rung of the tower `obs`/`sec` (and hence instance resolution) observes through. -/
def PAdicMap (p : ℕ) (N : ℕ) (K : Type _) (V : Type _) : Type _ := K → Option (ℤ × V)

namespace PAdicMap

variable {p N : ℕ} {V V' : Type _}

/-- The observation: send a stored integer approximation to its truncation in the `N`-th rung
`ZMod (p ^ N)` of the p-adic tower. -/
abbrev obs (z : ℤ) : ZMod (p ^ N) := (z : ZMod (p ^ N))

/-- A section of the observation: the canonical integer representative of a truncation. -/
abbrev sec (x : ZMod (p ^ N)) : ℤ := ZMod.cast x

/-- The section is a right inverse of the observation (`obs (sec x) = x`). -/
@[simp] theorem obs_sec (x : ZMod (p ^ N)) : obs (sec x) = x := ZMod.intCast_zmod_cast x

/-! ## The operations.

`get?` reads only the value (second) component; the approximation (first) component is carried
along but never observed. -/

/-- Pick a stored approximation for a freshly-produced value.  At the intended value type
`V = ZMod (p ^ N)` the canonical choice would be `sec`, the lift of the truncation; at any other
type it is an arbitrary unobserved `ℤ` (`0`), since `get?` never inspects it.  We keep it
`0`-valued and polymorphic in `V`, exactly as `OrbitMap.rep`. -/
def rep (_p _N : ℕ) : {V : Type _} → V → ℤ := fun _ => 0

instance instPartialMap : PartialMap (PAdicMap p N K) K where
  get? m k := (m k).map Prod.snd
  insert m k v := fun k' => if k = k' then some (rep p N v, v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k =>
    (m k).bind fun zv => (f k zv.2).map fun v' => (rep p N v', v')
  merge op m₁ m₂ := fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some x, some y => let v := op k x.2 y.2; some (rep p N v, v)

/-- The seven `LawfulPartialMap` laws.  Each holds because `get?` is the second projection and
every operation maintains the value component exactly as in the functional model. -/
instance instLawfulPartialMap : LawfulPartialMap (PAdicMap p N K) K where
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
they store the same value but different — though truncation-equivalent — p-adic approximations. -/

/-- A one-key map storing value `v` with approximation `z`. -/
def cell (k : K) (z : ℤ) (v : V) : PAdicMap p N K V :=
  fun k' => if k = k' then some (z, v) else none

variable (k : K) (v : V)

/-- **Observational equality.**  Two cells at the same key with the same value are
`PartialMap.equiv` *regardless of the stored approximation*: `get?` never sees the `ℤ`. -/
theorem cell_equiv (z z' : ℤ) :
    PartialMap.equiv (M := PAdicMap p N K) (cell k z v) (cell k z' v) := by
  intro k'
  simp only [get?, cell]
  by_cases h : k = k' <;> simp [h]

/-- **Non-extensionality.**  Distinct approximations give *distinct carriers*.  Concretely the
truncation-equal reps `0` and `(p ^ N : ℤ)` (equal in `ZMod (p ^ N)`, distinct in `ℤ` whenever
`p ^ N ≥ 2`, e.g. any prime `p ≥ 2` and `N ≥ 1`) yield equivalent maps that are not equal.

The witness `p ^ N` is the p-adically *small* perturbation `‖p ^ N‖_p = p ^ (-N)`: pushing the
approximation by it is the canonical "increase precision is observationally inert" move of the
inverse-limit tower. -/
theorem cell_ne (hpN : 2 ≤ p ^ N) (k : K) (v : V) :
    (cell k 0 v : PAdicMap p N K V) ≠ cell k (p ^ N : ℤ) v := by
  intro hcontra
  have hk := congrFun hcontra k
  simp only [cell, if_true] at hk
  -- `hk : some (0, v) = some (↑(p ^ N), v)`, so the first components agree: `0 = ↑(p ^ N)`.
  have h0 : (0 : ℤ) = (p ^ N : ℤ) := congrArg Prod.fst (Option.some.injEq _ _ ▸ hk)
  have : ((p ^ N : ℕ) : ℤ) = 0 := by push_cast at h0 ⊢; omega
  rw [Int.natCast_eq_zero] at this
  omega

/-- The non-extensionality theorem, packaged: two truncation-equivalent reps (`0` and `p ^ N`)
give a pair of maps that are `PartialMap.equiv` and yet `≠`. -/
theorem nonextensional (hpN : 2 ≤ p ^ N) (k : K) (v : V) :
    PartialMap.equiv (M := PAdicMap p N K) (cell k 0 v) (cell k (p ^ N : ℤ) v) ∧
      (cell k 0 v : PAdicMap p N K V) ≠ cell k (p ^ N : ℤ) v :=
  ⟨cell_equiv k v 0 (p ^ N : ℤ), cell_ne hpN k v⟩

/-- There is no `ExtensionalPartialMap` instance for `PAdicMap`: when `p ^ N ≥ 2`, `equiv` is
strictly coarser than `=`, so `equiv_iff_eq` would fail on the witnesses above. -/
theorem not_extensional (hpN : 2 ≤ p ^ N) (k : K) (v : V) :
    ¬ (PartialMap.equiv (M := PAdicMap p N K) (cell k 0 v) (cell k (p ^ N : ℤ) v) →
        (cell k 0 v : PAdicMap p N K V) = cell k (p ^ N : ℤ) v) :=
  fun h => cell_ne hpN k v (h (cell_equiv k v 0 (p ^ N : ℤ)))

end PAdicMap

end IrisMath

/-! ## Applicability: p-adic maps, the tower of updates, and the `HeapView` CMRA

### The value algebra: `ZMod (p ^ N)` and the inverse-limit ring `ℤ_[p]`

For a prime `p` and precision `N`, the `N`-th rung `ZMod (p ^ N)` is a **finite commutative local
ring**: its unique maximal ideal is `(p)`, its residue field is `ZMod p`, and an element is a unit
iff it is a unit mod `p` (iff `p ∤` it).  The rungs assemble into the projective tower

  `⋯ → ZMod (p ^ (N+1)) → ZMod (p ^ N) → ⋯ → ZMod p`,

whose inverse limit is the ring of p-adic integers `ℤ_[p]` (Mathlib's
`Mathlib.NumberTheory.Padics.PadicIntegers`, notation `ℤ_[p]`).  `ℤ_[p]` is a commutative DVR with
maximal ideal `(p)` and `ℤ_[p] / (p ^ N) ≃ ZMod (p ^ N)` — the very truncation `obs` used above.
Reading either `ZMod (p ^ N)` or `ℤ_[p]` as the value type of a heap-style CMRA gives the intended
applicability of this non-extensional, p-adically-valued partial map.

Recall `Iris.Algebra.HeapView`: from a `LawfulPartialMap M K` with a CMRA-valued value type one
forms the authoritative/fragment camera `HeapView F K V`, with

* `Auth dq m`   — authoritative ownership of the whole heap `m : M V`, fraction `dq`;
* `Frag k dq v` — fragmentary ownership of key `k` holding value `v`.

The frame-preserving updates `~~>` there (`update_one_alloc`, `update_one_delete`,
`update_replace`, `update_of_local_update`, `update_auth_op_frag`, …, in `HeapView.lean` lines
314–495) all reduce to *local updates on the value at a single key*, and every relational premise is
phrased through `get?`.  This is exactly where the p-adic tower pays off.

### Tower move 1 — "add a multiple of `p ^ N`": a free frame-preserving update

Because `get?` returns only the *value* and never the stored p-adic approximation `ℤ`, **any change
to a stored approximation is invisible to every `HeapR`/`HeapView` premise**.  For the truncation
interpretation `obs z = (z : ZMod (p ^ N))`, replacing a key's approximation `z` by `z + c * p ^ N`
keeps the value (truncation) fixed, since `obs (z + c * p ^ N) = obs z` (the perturbation
`c * p ^ N` is p-adically small, `‖c * p ^ N‖_p ≤ p ^ (-N)`).  Concretely, with
`m' := cell k (z + c * p ^ N) v` (using `IrisMath.PAdicMap.cell`):

  `PartialMap.equiv m m'`   (the `N = N` instance of `PAdicMap.cell_equiv`),

so the induced authoritative element satisfies

  `Auth (.own one) m ~~> Auth (.own one) m'`

as a frame-preserving update — it is the identity update up to `equiv`, preserving every premise
verbatim because those premises see only `get?`.  This is the p-adic slogan "increasing the
precision of a stored approximation is observationally inert", realized as a CMRA update; the
non-extensionality witness above is the special case `z = 0`, `c = 1`.

### Tower move 2 — "refine the precision `N`": the inverse-limit hierarchy

The rungs are linked by ring maps `π_{N} : ZMod (p ^ (N+1)) → ZMod (p ^ N)` (reduction).  A
`PAdicMap p N` observes through `obs_N`, and `PAdicMap p (N+1)` through the finer `obs_{N+1}` with
`π_N ∘ obs_{N+1} = obs_N`.  Thus the family `(PAdicMap p N)_N` is itself a tower: a single stored
`ℤ` approximation, viewed at every precision at once, *is* an element of the inverse limit `ℤ_[p]`
when the truncations are coherent.  Raising `N` strictly *shrinks* each `equiv`-class
(more reps become distinguishable), giving a *hierarchy of frame-preserving updates*: every update
valid at precision `N` lifts to one at precision `N+1`, but not conversely — the finer the rung, the
fewer the inert approximation-drifts.  In the limit `N → ∞` (i.e. in `ℤ_[p]`) only genuinely equal
p-adic integers collapse, recovering an extensional observation.

### Units and strong local updates on `ZMod (p ^ N)`

`(ZMod (p ^ N), +, 0)` is a finite abelian group: every `v : ZMod (p ^ N)` is invertible under `+`
(inverse `-v`).  Reading `ZMod (p ^ N)` as an exclusive/whole value CMRA (Leibniz `=` on the finite
carrier), the local update `(mv, v) ~l~> (mv', v')` feeding `HeapView.update_of_local_update`
(line 426) is available for *any* target truncation `v'` by group homogeneity
(translate `v ↦ v + (v' - v)`).  Hence one concrete update:

  `Auth (.own one) m • Frag k (.own one) v ~~>
     Auth (.own one) (insert m k v') • Frag k (.own one) v'`

holds for every `v' : ZMod (p ^ N)` (cf. `HeapView.update_replace` (line 438) /
`update_of_local_update`), and the resulting authoritative heap `insert m k v'` is determined only
*up to the `N`-th truncation*: its concrete stored approximation `sec v' : ℤ` may be replaced by any
`sec v' + c * p ^ N` without affecting validity, by Tower move 1.  Multiplicatively, the unit group
`(ZMod (p ^ N))ˣ` (the `p ∤ ·` elements, of order `p ^ (N-1) (p-1)`) furnishes further
*scaling* local updates `v ↦ u * v` for `u` a unit.  This cleanly separates the *logical* value
(the truncation, in `ZMod (p ^ N)` / `ℤ_[p]`) from its *stored approximation* (`ℤ`) — the intended
applicability of a non-extensional, p-adically-valued partial map, generalizing `OrbitMap` from a
single quotient to the full inverse-limit tower.
-/
