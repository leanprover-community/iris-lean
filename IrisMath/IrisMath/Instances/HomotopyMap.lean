/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Iris

/-! # Homotopy (π₀) maps: a non-extensional, *topological* `LawfulPartialMap`

This file builds a `PartialMap` / `LawfulPartialMap` instance whose stored data carries strictly
more information than its observable denotation: each key is assigned both a value and a *concrete
point of the punctured line `ℝ ∖ {0}`* (modelled combinatorially by a nonzero integer
representative), while `get?` (hence `PartialMap.equiv`) only observes the value.  Two
representatives lying in the **same path-component** of `ℝ ∖ {0}` therefore give equal denotations
but unequal carriers — the construction is lawful yet **non-extensional**.

It is the *topological* member of the same family as `IrisMath.OrbitMap` (algebraic orbit under a
cyclic group) and `IrisMath.GaloisMap` (Galois orbit under `Gal(ℚ(√d)/ℚ) ≃ ℤ/2`).  Where those
quotient a representative by a **group action**, `HomotopyMap` quotients a representative by the
**path-component relation** of a topological space — i.e. by `π₀`.  All three realize the single
slogan: **observe a stored representative only up to an equivalence**; here the equivalence is
"lies in the same connected piece", a genuinely topological quotient rather than an algebraic one.

## The π₀ / quotient structure

The motivating space is the **punctured line** `X = ℝ ∖ {0}`.  Its path-components are exactly the
two open rays

  `(-∞, 0)`   and   `(0, +∞)`,

so `π₀(ℝ ∖ {0})` is a *two-point* set, detected by the **sign**:

  `π₀(ℝ ∖ {0}) ≃ {-1, +1}`,    `obs x = sign x`.

Two points on the same side of `0` are joined by a straight-line path that never crosses `0`, hence
are path-connected and lie in the same component; two points on opposite sides cannot be so joined.
The observation `obs = sign` is precisely the `π₀` quotient map.  We model a point of `ℝ ∖ {0}`
combinatorially by a *nonzero integer representative* `z : ℤ` (any nonzero `z` names a point of one
of the two rays); the homotopy/path-component content lives entirely in `obs = Int.sign` and in the
witnesses below, while `get?` stays as elementary as `OrbitMap`'s — just a projection.

Each stored cell records:

* a *representative* `z : ℤ`, only ever observed through its path-component `obs z = Int.sign z`
  (which component of `ℝ ∖ {0}` the point sits in), and
* the *value* `v : V` that `get?` returns.

The `ℤ` component is invisible to `get?`, which is the source of non-extensionality and of the
*homotopy-theoretic* frame-preserving updates discussed at the end of the file.

## Design

`HomotopyMap K V := K → Option (ℤ × V)`.  The first projection is the (unobserved) point of
`ℝ ∖ {0}`; the second is the value returned by `get?`.  The `PartialMap` operations carry a
representative along but never observe it.  This mirrors `IrisMath.OrbitMap`'s `K → Option (ℤ × V)`
shape *exactly*, replacing the `ZMod n` orbit observation by the path-component observation
`obs = Int.sign`.
-/

@[expose] public section

namespace IrisMath

open Iris.Std Iris.Std.PartialMap

variable {K : Type _} [DecidableEq K]

/-- A homotopy (π₀) map: each key carries a point of the punctured line `ℝ ∖ {0}` (modelled by a
nonzero integer representative) together with its value.  Only the value is observable. -/
def HomotopyMap (K : Type _) (V : Type _) : Type _ := K → Option (ℤ × V)

namespace HomotopyMap

variable {V V' : Type _}

/-- The observation: send a stored point of `ℝ ∖ {0}` to its **path-component**, i.e. to the
element of `π₀(ℝ ∖ {0}) ≃ {-1, +1}` it lies in.  Combinatorially this is `Int.sign`. -/
abbrev obs (z : ℤ) : ℤ := Int.sign z

/-- A section of the observation: the canonical representative point of a component.  The two
components `(-∞, 0)` and `(0, +∞)` of `ℝ ∖ {0}` are named by their basepoints `-1` and `+1`. -/
abbrev sec (s : ℤ) : ℤ := Int.sign s

/-- Positive representatives all lie in the same path-component `(0, +∞)`: `obs` is constant `1`
on them.  This is the topological content "`1` and `5` are path-connected in `ℝ ∖ {0}`". -/
@[simp] theorem obs_pos {z : ℤ} (h : 0 < z) : obs z = 1 := Int.sign_eq_one_of_pos h

/-- Negative representatives all lie in the same path-component `(-∞, 0)`: `obs` is constant `-1`
on them. -/
@[simp] theorem obs_neg {z : ℤ} (h : z < 0) : obs z = -1 := Int.sign_eq_neg_one_of_neg h

/-! ## The operations.

`get?` reads only the value (second) component; the representative (first) component — the point of
`ℝ ∖ {0}` — is carried along but never observed. -/

/-- Pick a stored representative point for a freshly-produced value.  Since `get?` never inspects
it, any fixed nonzero integer naming a point of `ℝ ∖ {0}` will do; we use the basepoint `1` of the
positive component `(0, +∞)`.  Field-free so the operations stay polymorphic in `V`. -/
def rep : {V : Type _} → V → ℤ := fun _ => 1

instance instPartialMap : PartialMap (HomotopyMap K) K where
  get? m k := (m k).map Prod.snd
  insert m k v := fun k' => if k = k' then some (rep v, v) else m k'
  delete m k := fun k' => if k = k' then none else m k'
  empty := fun _ => none
  bindAlter f m := fun k =>
    (m k).bind fun zv => (f k zv.2).map fun v' => (rep v', v')
  merge op m₁ m₂ := fun k =>
    match m₁ k, m₂ k with
    | none, none => none
    | some x, none => some x
    | none, some y => some y
    | some x, some y => let v := op k x.2 y.2; some (rep v, v)

/-- The seven `LawfulPartialMap` laws.  Each holds because `get?` is the second projection and
every operation maintains the value component exactly as in the functional model. -/
instance instLawfulPartialMap : LawfulPartialMap (HomotopyMap K) K where
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

We exhibit two carriers that observe identically (`PartialMap.equiv`) but differ as functions: they
store the same value at points of `ℝ ∖ {0}` that are **path-connected** (same `π₀`-class), so the
observation `get?` cannot distinguish them. -/

/-- A one-key map storing value `v` at the point `z ∈ ℝ ∖ {0}`. -/
def cell (k : K) (z : ℤ) (v : V) : HomotopyMap K V := fun k' => if k = k' then some (z, v) else none

variable (k : K) (v : V)

/-- **Observational equality.**  Two cells at the same key with the same value are
`PartialMap.equiv` *regardless of the stored point*: `get?` never sees the `ℤ`, hence never sees
which point of a component (or even which component) was stored. -/
theorem cell_equiv (z z' : ℤ) :
    PartialMap.equiv (M := HomotopyMap K) (cell k z v) (cell k z' v) := by
  intro k'
  simp only [get?, cell]
  by_cases h : k = k' <;> simp [h]

/-- **Non-extensionality, the homotopy witness.**  The representatives `1` and `5` are *distinct
points* of `ℝ ∖ {0}` yet lie in the *same path-component* `(0, +∞)`:

  `obs 1 = Int.sign 1 = 1 = Int.sign 5 = obs 5`,

so the straight path `t ↦ (1 - t)·1 + t·5 = 1 + 4t` from `1` to `5` stays in `(0, +∞)`, never
crossing `0`.  They are therefore `π₀`-equal, hence give `PartialMap.equiv` cells — but as stored
functions the cells differ, because `5 ≠ 1`. -/
theorem cell_ne (k : K) (v : V) :
    (cell k 1 v : HomotopyMap K V) ≠ cell k 5 v := by
  intro hcontra
  have hk := congrFun hcontra k
  simp only [cell, if_true] at hk
  -- `hk : some (1, v) = some (5, v)`, so the first components agree: `1 = 5`.
  have h1 : (1 : ℤ) = 5 := congrArg Prod.fst (Option.some.injEq _ _ ▸ hk)
  omega

/-- The path-components really do agree on the witness: `1` and `5` have the same `π₀`-class. -/
theorem obs_witness : obs (1 : ℤ) = obs (5 : ℤ) := by decide

/-- The non-extensionality theorem, packaged: two points `1` and `5` in the *same* path-component
of `ℝ ∖ {0}` (both positive, `π₀`-class `+1`) give a pair of maps that are `PartialMap.equiv` and
yet `≠`. -/
theorem nonextensional (k : K) (v : V) :
    PartialMap.equiv (M := HomotopyMap K) (cell k 1 v) (cell k 5 v) ∧
      (cell k 1 v : HomotopyMap K V) ≠ cell k 5 v :=
  ⟨cell_equiv k v 1 5, cell_ne k v⟩

/-- There is no `ExtensionalPartialMap` instance for `HomotopyMap`: `equiv` is strictly coarser
than `=`, so `equiv_iff_eq` would fail on the path-connected witnesses `1`, `5`. -/
theorem not_extensional (k : K) (v : V) :
    ¬ (PartialMap.equiv (M := HomotopyMap K) (cell k 1 v) (cell k 5 v) →
        (cell k 1 v : HomotopyMap K V) = cell k 5 v) :=
  fun h => cell_ne k v (h (cell_equiv k v 1 5))

end HomotopyMap

end IrisMath

/-! ## Applicability: π₀ maps and the `HeapView` CMRA

Recall `Iris.Algebra.HeapView` (`HeapView.lean`, lines 314–495): from a `LawfulPartialMap M K` with
a CMRA-valued value type one forms the authoritative/fragment camera `HeapView F K V`, with

* `Auth dq m`   — authoritative ownership of the whole heap `m : M V`, fraction `dq`;
* `Frag k dq v` — fragmentary ownership of key `k` holding value `v`.

The frame-preserving updates `~~>` there (`update_one_alloc`, `update_one_delete`,
`update_replace`, `update_of_local_update`, `update_auth_op_frag`, …) all reduce to *local updates
on the value at a single key*, and every relational premise is phrased through `get?`.  The π₀
structure interacts with this in a purely topological way.

### Path-components ⇒ deforming the representative within its component is a no-op

The heap built from `HomotopyMap` remembers, per key, only the **homotopy / path-component class**
of its stored point of `ℝ ∖ {0}`: `get?` returns just the value, never the point, so the heap is
blind to *where in its component* the representative sits.  A **homotopy** of the stored point —
continuously sliding it along a path inside its component, e.g. deforming `1 ⤳ 5` along
`t ↦ 1 + 4t ∈ (0, +∞)` — changes the concrete representative but never crosses `0`, hence preserves
its `π₀`-class and is **invisible to every `HeapR`/`HeapView` premise**.

Concretely, with `m' := cell k 5 v` obtained from `m := cell k 1 v` by such a path-homotopy (using
`IrisMath.HomotopyMap.cell`):

  `PartialMap.equiv m m'`   (proved here as `HomotopyMap.cell_equiv`),

so the induced authoritative element satisfies the frame-preserving update

  `Auth (.own one) m ~~> Auth (.own one) m'`,

the identity update up to `equiv`.  This is a genuinely **topological** frame-preserving update: it
*moves* the stored point of `ℝ ∖ {0}` (a homotopy of representatives) while preserving every premise
verbatim, because those premises see only `get?` and `get?` sees only the path-component.  The
slogan is "deform the representative within its connected piece — a homotopy — and the π₀
observation cannot tell".  Crossing `0` is exactly what is *not* allowed (it would change the
component, hence the
observation): the permissible updates are precisely the homotopies, i.e. the `π₀`-preserving moves.

### The family: one slogan, algebra → topology

`HomotopyMap` completes the "observe a stored representative up to an equivalence" family across the
algebra/topology divide:

* `OrbitMap`    — representative `z : ℤ`, equivalence = **cyclic group orbit** `ℤ ⧸ nℤ ≃ ZMod n`;
* `GaloisMap`   — representative `a + b√d`, equivalence = **Galois orbit** `Gal(ℚ(√d)/ℚ) ≃ ℤ/2`;
* `HomotopyMap` — representative point of `ℝ ∖ {0}`, equivalence = **path-component / π₀-orbit**.

All three share the carrier `K → Option (Rep × V)`, store a representative `Rep` plus value, take
`get? = Prod.snd`, and put the quotient semantics in the witnesses and in this applicability note.
The first two quotient by a *group action* (algebra); `HomotopyMap` quotients by the *connectivity
relation* of a space (topology).  The frame-preserving updates degenerate accordingly: orbit drift
`z ↦ z + cn`, Galois conjugation `b ↦ -b`, and here a **homotopy of the representative within its
path-component** — all observationally inert, all valid `~~>` up to `equiv`.
-/
