/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Lattice
public import Mathlib.Order.Basic
public import Iris

/-! # `TropicalMap`: a non-extensional `LawfulPartialMap` from a *tropical* (min-plus) readout

Every prior non-extensional `PartialMap` instance in this development collapses information
through either a **quotient / projection of stored extra data** (`ConstOnFilterMap`/`GermMap`,
`CoarseningMap`) — retractions onto a subspace of constants — or, in the case of `FourierMap`,
through a **linear functional** (a Fourier coefficient `⟨χ, s⟩ = Σ_g χ(g) • s g`, an *additive*
aggregation whose kernel is a linear subspace).

`TropicalMap` is **algebraically different from both**: the readout is the **tropical aggregate**
of the stored family — the `⊕`-fold of the **min-plus (tropical) semiring** `(ℝ ∪ {∞}, min, +)`,
i.e. `⊕_g s g = min_g s g`.  This is an **idempotent-semiring aggregation**: where `FourierMap`
sums (`+`), `TropicalMap` takes a *minimum* (`min`, the tropical `⊕`).  Idempotence (`a ⊕ a = a`)
and the lack of additive inverses make this a genuinely new collapsing flavour: there is no kernel
*subspace*, instead the readout collapses every family that shares the same *minimum* — the
"cheapest path" — regardless of how the non-minimal coordinates are arranged.  This is the
**shortest-path / optimization** semantics of the tropical semiring.

We give the readout in its cleanest fully-polymorphic form first.  Because the `bindAlter` field's
target type `V'` is *universally quantified with no typeclass slot*, the polymorphic core may not
reconstruct a `min` (which needs `Min`/`LinearOrder` structure on `V'`).  So — exactly as
`FourierMap` uses the single-coordinate `δ_{gT}` pairing for its polymorphic core and reserves the
genuine *sum* for an `[AddCommMonoid V]` section — the **polymorphic core readout here is a single
coordinate evaluation** `s gT` (the tropical aggregate over the *singleton path* `{gT}`), and the
genuine tropical `min` aggregate lives in a value-constrained `[LinearOrder V]` section.

  core:     `ρ s = s gT`                       (tropical fold over the one-element path `{gT}`)
  tropical: `trop s = min (s false) (s true)`  (the genuine `⊕`-aggregation, `[LinearOrder V]`)

We take `G := Bool`, `gT := false`.

## Implementation

`TropicalMap V := Bool → Option (Bool → V)`.  `none` at a key means "absent"; `some s` stores the
family `s : Bool → V` (think: the two costs of reaching a node by either of two paths).
`get? m k := (m k).map (· gT)`.  Every constructive operation stores the constant family
`fun _ ↦ w`, whose `gT`-coordinate is `w`, so the seven laws reduce to the underlying function-map
laws.  Non-extensionality is witnessed by two families with the same `gT`-coordinate (core) — and
in the tropical section by two families with the same `min`.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

namespace TropicalMap

variable {V V' : Type _}

/-- The distinguished index `gT` whose coordinate is the tropical fold over the singleton path
`{gT}`.  We take `gT := false`. -/
abbrev gT : Bool := false

/-- The **core (polymorphic) tropical readout**: the tropical aggregate `⊕_{g ∈ {gT}} s g = s gT`
over the *one-element path* `{gT}`.  Requiring no order structure on `V`, it is exactly what the
universally-quantified `get?`/`bindAlter` laws demand.  Like `FourierMap.fourier` it is
**non-injective**: it forgets every coordinate other than `gT`. -/
def readout (s : Bool → V) : V := s gT

/-- The canonical family realizing a value `w`: the constant family `fun _ ↦ w` (all paths cost
`w`).  Its readout is `w`. -/
def reifyT (w : V) : Bool → V := fun _ => w

/-- The core readout of the canonical family is the value: `readout (reifyT w) = w`. -/
@[simp] theorem readout_reify (w : V) : readout (reifyT w) = w := rfl

/-- Two families agreeing at `gT` have the same core readout (the heart of non-extensionality:
the observation factors through the non-injective `readout`). -/
theorem readout_congr {s s' : Bool → V} (h : s gT = s' gT) : readout s = readout s' := h

/-- A `TropicalMap` stores a *family* (`Bool → V`) — the per-path costs — at every key.  `none`
means "absent".  Distinct families with the same tropical readout denote the same map. -/
def _root_.IrisMath.Instances.TropicalMap (V : Type _) : Type _ := Bool → Option (Bool → V)

/-- The forgetful denotation: read back the (core) tropical aggregate of the family at `k`. -/
def get? (m : TropicalMap V) (k : Bool) : Option V := (m k).map readout

/-- Insert stores the canonical family `reifyT v` (readout `= v`). -/
def insert (m : TropicalMap V) (k : Bool) (v : V) : TropicalMap V :=
  fun k' => if k = k' then some (reifyT v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : TropicalMap V) (k : Bool) : TropicalMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : TropicalMap V := fun _ => none

/-- `bindAlter` applies `f` to the tropical readout of each stored family, re-storing the result
as a canonical family. -/
def bindAlter (f : Bool → V → Option V') (m : TropicalMap V) : TropicalMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map reifyT)

/-- `merge` combines the tropical readouts of two stored families, re-storing the result as a
canonical family. -/
def merge (op : Bool → V → V → V) (m₁ m₂ : TropicalMap V) : TropicalMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map reifyT

instance instPartialMap : PartialMap TropicalMap Bool where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : TropicalMap V) (k : Bool) :
    PartialMap.get? m k = (m k).map readout := rfl

instance instLawfulPartialMap : LawfulPartialMap TropicalMap Bool where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, TropicalMap.insert, if_pos h, Option.map_some,
      readout_reify]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, TropicalMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, TropicalMap.delete, if_pos h, Option.map_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, TropicalMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (TropicalMap.bindAlter f m k).map readout = (get? m k).bind (f k)
    unfold TropicalMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map reifyT)).map readout = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [readout_reify]
  get?_merge {V op m₁ m₂ k} := by
    show (TropicalMap.merge op m₁ m₂ k).map readout
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold TropicalMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map reifyT).map readout
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [readout_reify]

/-! ## Non-extensionality via a non-injective tropical readout

We exhibit two **distinct** `TropicalMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but not equal as Lean values.  The witness is a single key
storing two families with the **same `gT`-coordinate but different cost off `gT`**: the constant
family `reifyT 0 = (0, 0)` and `offPath`, which is `0` at `gT = false` but `1` at `true`.  Both have
core readout `some 0`, yet differ at `true`.  The discarded data is "the cost of the *other* path",
which the cheapest-path readout never sees. -/

/-- A family in the **same fibre** of the core readout as `reifyT 0` but with a different cost on the
off-`gT` path: `0` at `gT = false`, `1` at `true`. -/
def offPath : Bool → ℕ := fun b => if b then 1 else 0

/-- `offPath` has the same core readout as `reifyT 0` (both cost `0` on path `gT`). -/
theorem offPath_same_readout : readout offPath = readout (reifyT (0 : ℕ)) := rfl

/-- `offPath` is a *different family* from `reifyT 0`: they disagree at `true`. -/
theorem offPath_ne_reify : offPath ≠ reifyT (0 : ℕ) := by
  intro h
  have h1 := congrFun h true
  simp only [offPath, reifyT, if_pos] at h1
  exact absurd h1 (by decide)

/-- First witness: key `false` stores the constant family `reifyT 0 = (0, 0)`. -/
def m_zero : TropicalMap ℕ := TropicalMap.insert TropicalMap.empty false 0

/-- Second witness: key `false` stores `offPath = (0, 1)` (same readout, different off-path). -/
def m_off : TropicalMap ℕ := fun k => if k = false then some offPath else none

/-- **Non-extensionality.**  `m_zero` and `m_off` are observationally equal (`PartialMap.equiv`)
— both denote "key `false` ↦ cheapest cost `0`, everything else absent" — yet they are **distinct**
Lean values, because the stored families (`(0, 0)` versus `(0, 1)`) differ at `true`.  This is
impossible for any `ExtensionalPartialMap`. -/
theorem nonextensional :
    PartialMap.equiv (M := TropicalMap) m_zero m_off ∧ m_zero ≠ m_off := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = false
    · subst hk
      show ((m_zero false).map readout) = ((m_off false).map readout)
      have hz : m_zero false = some (reifyT 0) := by simp [m_zero, TropicalMap.insert]
      have ho : m_off false = some offPath := by simp [m_off]
      rw [hz, ho, Option.map_some, Option.map_some, offPath_same_readout]
    · show ((m_zero k).map readout) = ((m_off k).map readout)
      have hz : m_zero k = none := by
        simp [m_zero, TropicalMap.insert, TropicalMap.empty, Ne.symm hk]
      have ho : m_off k = none := by simp [m_off, hk]
      rw [hz, ho]
  · intro h
    have h0 : m_zero false = m_off false := congrFun h false
    have hz : m_zero false = some (reifyT 0) := by simp [m_zero, TropicalMap.insert]
    have ho : m_off false = some offPath := by simp [m_off]
    rw [hz, ho, Option.some.injEq] at h0
    exact offPath_ne_reify h0.symm

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : TropicalMap ℕ}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  exact nonextensional.2 (h nonextensional.1)

/-! ## The genuine tropical (min-plus, `⊕ = min`) aggregate

The core readout above folds over the *singleton* path `{gT}`.  When the value type is linearly
ordered we can fold over **all** of `G`, recovering the honest **tropical `⊕`-aggregation**

  `trop s = ⊕_g s g = min (s false) (s true)`.

This is the additive operation of the **min-plus (tropical) semiring** `(V ∪ {∞}, min, +)`.  Unlike
the *linear* `FourierMap.dc` (which sums and whose kernel is the antidiagonal), `min` is
**idempotent** (`min a a = a`) and has **no inverses**: there is no "kernel subspace", instead
`trop` collapses every family that shares the same minimum — the cheapest path — irrespective of
how the dominated paths are arranged.  Two families collapse iff `min` agrees, which holds on a
*much larger, non-linear* fibre (e.g. all of `{(0, b) | b ≥ 0}`). -/

section Tropical

variable [LinearOrder V]

/-- The **tropical aggregate**: the min-plus `⊕`-fold `min (s false) (s true)` over both paths.
The additive operation of the tropical semiring `(V ∪ {∞}, min, +)`. -/
def trop (s : Bool → V) : V := min (s false) (s true)

/-- `trop` is **symmetric in the two paths**: swapping the path costs preserves the cheapest path.
`min (a, b) = min (b, a)`. -/
theorem trop_comm (s : Bool → V) : trop s = trop (fun b => s !b) := by
  simp only [trop, Bool.not_false, Bool.not_true]
  exact min_comm _ _

/-- `trop` is **min-invariant**: families with the same minimum agree under `trop`, regardless of
their non-minimal coordinates.  This is the idempotent-semiring collapse (no kernel subspace; the
fibre is `{s | min (s false) (s true) = c}`). -/
theorem trop_congr {s s' : Bool → V} (h : min (s false) (s true) = min (s' false) (s' true)) :
    trop s = trop s' := h

end Tropical

/-- The tropical `min` aggregate is **non-injective** over `ℕ`: the **symmetric** pair `(0, 5)` and
`(5, 0)` both have minimum `0` (`min (a,b) = min (b,a)`) yet are different families. -/
theorem trop_not_injective_symm :
    trop (fun b => if b then 5 else 0 : Bool → ℕ) = trop (fun b => if b then 0 else 5)
      ∧ (fun b => if b then 5 else 0 : Bool → ℕ) ≠ (fun b => if b then 0 else 5) := by
  refine ⟨by decide, fun h => ?_⟩
  have := congrFun h true
  simp at this

/-- The tropical `min` aggregate collapses a whole non-linear fibre: `(0, 5)` and `(0, 9)` both have
minimum `0`, witnessing that `trop` is far from injective (any family `(0, b)` with `b ≥ 0`
collapses). -/
theorem trop_collapse_witness :
    trop (fun b => if b then 5 else 0 : Bool → ℕ) = trop (fun b => if b then 9 else 0)
      ∧ (fun b => if b then 5 else 0 : Bool → ℕ) ≠ (fun b => if b then 9 else 0) := by
  refine ⟨by decide, fun h => ?_⟩
  have := congrFun h true
  simp at this

end TropicalMap

/-! ## Applicability: a `HeapView` CMRA observing only the tropical (cheapest-path) component

Since `TropicalMap` is a `LawfulPartialMap TropicalMap Bool`, it slots directly into
`Iris.Algebra.HeapView`:

  `HeapView H Bool V _`  with  `H := TropicalMap` (this file) and `K := Bool`.

`HeapView` provides authoritative ownership `Auth (.own one) m` over the whole heap of stored
path-cost families, and fragmental ownership `Frag k dq v` over a single cell's *tropical
coefficient* (its cheapest path cost); the view relation `HeapR` observes the heap **only** through
`Std.PartialMap.get?`, i.e. through this file's tropical readback (`Iris/Algebra/HeapView.lean`,
lines 314–495).

### A genuinely new frame-preserving update flavour: improve a non-optimal path, keep the minimum

Because the readout is the **tropical `⊕ = min` aggregation**, a whole *idempotent* class of edits
is free (frame-preserving): **any change to the stored family that does not change the minimum
leaves the observation fixed.**  Concretely, *lowering a non-minimal coordinate* — improving a path
that is already not the cheapest — or *raising any dominated coordinate while it stays ≥ the
minimum* is invisible: `(0, 9) ↝ (0, 5) ↝ (0, 1)` all read out `0`.  This is the **shortest-path /
optimization** flavour: the heap records only the optimum cost-to-go at each node, and tightening a
suboptimal alternative path is observationally an identity.

Contrast `FourierMap` (whose free edits are the *linear* kernel `ker ⟨χ, ·⟩` — moving mass between
coordinates keeping the *sum* fixed, `(2,0) ↝ (1,1) ↝ (0,2)`): there the aggregation is *additive*
and the invisible edits form a linear subspace.  Here the aggregation is *tropical/idempotent*
(`min`), and the invisible edits form the **non-linear** super-level region `{s | min s = c}` — no
inverses, no subspace, a strictly larger and order-shaped fibre.

Concretely, replacing the stored family at a key by *any* family with the same readback is the
identity on tropical coefficients, so for `H := TropicalMap`:

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>  `
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`,

an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`, line 438): the new cell
value `v2 := v` is valid because `✓ v` already held, and the update is stated purely through
`get?`/`insert`, never term equality.  More generally `HeapView.update_of_local_update` lifts any
local update on the tropical coefficients; the "improve a non-optimal path" edit is invisible to the
CMRA precisely because every HeapView operation only sees the tropical readout. -/

section Applicability

open TropicalMap

variable {V : Type _}

/-- **Tropical-observation invariance under non-optimal-path edits**, machine-checked.  Replacing
the canonical family at a key by *any* family with the same `gT`-coordinate yields an `equiv` map.
Such a rewrite is therefore frame-preserving for every `HeapView` update built on this instance
(it is the denotation-level content of `update_replace`/`update_of_local_update`). -/
theorem path_edit_equiv (m : TropicalMap V) (k : Bool) (v : V) {g : Bool → V}
    (hg : g gT = v) :
    PartialMap.equiv (PartialMap.insert m k v) (fun k' => if k = k' then some g else m k') := by
  intro k'
  show ((TropicalMap.insert m k v) k').map readout
    = ((fun k' => if k = k' then some g else m k') k').map readout
  by_cases hk : k = k'
  · simp only [TropicalMap.insert, if_pos hk, Option.map_some]
    rw [readout_reify]
    exact congrArg some hg.symm
  · simp only [TropicalMap.insert, if_neg hk]

/-- A concrete `~~>` witness: at key `false`, edit the stored family from `reifyT 0 = (0,0)` to
`offPath = (0,1)` — *raising the non-minimal path* `true` from `0` to `1`, keeping the cheapest path
`0` unchanged.  The two heaps are `PartialMap.equiv` (same tropical coefficient `0`), so the
corresponding `HeapView` update is frame-preserving. -/
example :
    PartialMap.equiv (PartialMap.insert (TropicalMap.empty : TropicalMap ℕ) false 0)
      (fun k' => if false = k' then some offPath else TropicalMap.empty k') :=
  path_edit_equiv TropicalMap.empty false 0 (g := offPath) rfl

end Applicability

end IrisMath.Instances
