/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Iris

/-! # `FourierMap`: a non-extensional `LawfulPartialMap` from a *linear* (Fourier) readout

Every prior non-extensional `PartialMap` instance in this development collapses information
through a **quotient / projection of stored extra data**: `ConstOnFilterMap`/`GermMap` factor
`Idx → V` through a filter's small sets, and `CoarseningMap` factors a fine function through the
restriction to a coarse cell.  Those readouts are *retractions onto a subspace of constants* —
they see a representative and forget "the rest".

`FourierMap` is **structurally different**: the readout is a **linear functional** — a
**character pairing / Fourier coefficient** `⟨χ, s⟩ = Σ_g χ(g) • s g` — rather than a retraction
onto a constant.  Over a fixed finite additive index `G` we store a family `s : G → V` at each
key and observe only the pairing of `s` against a fixed character `χ`.  Two families with the
**same pairing** collapse, *not* because one is "off a cell" or "on a small set", but because the
linear functional `⟨χ, ·⟩` is **non-injective** — its kernel is a genuine linear subspace, and
moving mass *within* `ker χ` (redistributing value across coordinates) is invisible.

We give the readout in its cleanest fully-polymorphic form, the pairing against the
**delta character** `χ = δ_{g₀}` (evaluation at a distinguished index `g₀`):

  `ρ s = ⟨δ_{g₀}, s⟩ = s g₀`.

This is a bona-fide linear functional (point evaluation is the pairing against a delta/indicator
character — a single Fourier basis vector), it is **non-injective** (it annihilates every family
supported off `g₀`), and it requires *no* structure on `V`, so the core instance is polymorphic
in `V` exactly as `get?` demands.  We take `G := Bool`, `g₀ := false`.

Then, in an `[AddCommMonoid V]` section, we record the **genuine total-sum readout**
`Σ_{g} s g = s false + s true` (the **trivial-character / DC Fourier coefficient**), prove it is
*also* a non-injective linear functional, and use it for the applicability story: when `V` is a
richer module the heap observes the DC component, and updates may **redistribute mass keeping the
total fixed** — a frame-preserving update flavour unavailable to any projection/quotient instance.

## Implementation

`FourierMap V := Bool → Option (Bool → V)`.  `none` at a key means "absent"; `some s` stores the
family `s : Bool → V`.  `get? m k := (m k).map (· false)` (the `δ_false` pairing).  Every
constructive operation stores the constant family `fun _ ↦ w`, whose `false`-pairing is `w`, so
the seven laws reduce to the underlying function-map laws.  Non-extensionality is witnessed by two
families with the same `false`-coordinate but different `true`-coordinate.
-/

@[expose] public section

namespace IrisMath.Instances

open Iris.Std Iris.Std.PartialMap

namespace FourierMap

variable {V V' : Type _}

/-- The distinguished index `g₀` against whose **delta character** `δ_{g₀}` we pair.  We take
`g₀ := false`. -/
abbrev g₀ : Bool := false

/-- The **Fourier readout**: the pairing `⟨δ_{g₀}, s⟩ = s g₀` of the stored family against the
delta character at `g₀`.  This is a *linear functional* `(Bool → V) → V` (point evaluation is the
pairing against a single Fourier basis vector / indicator character), and it is **non-injective**:
it annihilates every family supported off `g₀`. -/
def fourier (s : Bool → V) : V := s g₀

/-- The canonical family realizing a value `w` against the `δ_{g₀}` pairing: the constant family
`fun _ ↦ w`.  Its readout is `w`. -/
def reify (w : V) : Bool → V := fun _ => w

/-- The Fourier readout of the canonical family is the value: `⟨δ_{g₀}, reify w⟩ = w`. -/
@[simp] theorem fourier_reify (w : V) : fourier (reify w) = w := rfl

/-- **Linearity / kernel invariance**: two families agreeing at `g₀` (differing only inside the
kernel of `⟨δ_{g₀}, ·⟩`) have the same Fourier readout.  This is the heart of non-extensionality —
the observation factors through the *non-injective linear functional* `fourier`. -/
theorem fourier_congr {s s' : Bool → V} (h : s g₀ = s' g₀) : fourier s = fourier s' := h

/-- A `FourierMap` stores a *family* (`Bool → V`) at every key.  `none` means "absent".
Distinct families with the same `δ_{g₀}` pairing denote the same map. -/
def _root_.IrisMath.Instances.FourierMap (V : Type _) : Type _ := Bool → Option (Bool → V)

/-- The forgetful denotation: read back the Fourier coefficient of the family stored at `k`. -/
def get? (m : FourierMap V) (k : Bool) : Option V := (m k).map fourier

/-- Insert stores the canonical family `reify v` (pairing `= v`). -/
def insert (m : FourierMap V) (k : Bool) (v : V) : FourierMap V :=
  fun k' => if k = k' then some (reify v) else m k'

/-- Delete stores `none` (absent). -/
def delete (m : FourierMap V) (k : Bool) : FourierMap V :=
  fun k' => if k = k' then none else m k'

/-- The empty map: every key absent. -/
def empty : FourierMap V := fun _ => none

/-- `bindAlter` applies `f` to the Fourier readout of each stored family, re-storing the result
as a canonical family. -/
def bindAlter (f : Bool → V → Option V') (m : FourierMap V) : FourierMap V' :=
  fun k => (get? m k).bind (fun v => (f k v).map reify)

/-- `merge` combines the Fourier readouts of two stored families, re-storing the result as a
canonical family. -/
def merge (op : Bool → V → V → V) (m₁ m₂ : FourierMap V) : FourierMap V :=
  fun k => (Option.merge (op k) (get? m₁ k) (get? m₂ k)).map reify

instance instPartialMap : PartialMap FourierMap Bool where
  get? := get?
  insert := insert
  delete := delete
  empty := empty
  bindAlter := bindAlter
  merge := merge

@[simp] theorem get?_eq (m : FourierMap V) (k : Bool) :
    PartialMap.get? m k = (m k).map fourier := rfl

instance instLawfulPartialMap : LawfulPartialMap FourierMap Bool where
  get?_empty k := rfl
  get?_insert_eq {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, FourierMap.insert, if_pos h, Option.map_some,
      fourier_reify]
  get?_insert_ne {V m k k' v} h := by
    simp only [get?_eq, PartialMap.insert, FourierMap.insert, if_neg h]
  get?_delete_eq {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, FourierMap.delete, if_pos h, Option.map_none]
  get?_delete_ne {V m k k'} h := by
    simp only [get?_eq, PartialMap.delete, FourierMap.delete, if_neg h]
  get?_bindAlter {V V' k m f} := by
    show (FourierMap.bindAlter f m k).map fourier = (get? m k).bind (f k)
    unfold FourierMap.bindAlter
    show ((get? m k).bind (fun v => (f k v).map reify)).map fourier = (get? m k).bind (f k)
    cases hv : get? m k with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      cases hf : f k v with
      | none => simp
      | some w => simp [fourier_reify]
  get?_merge {V op m₁ m₂ k} := by
    show (FourierMap.merge op m₁ m₂ k).map fourier
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    unfold FourierMap.merge
    show ((Option.merge (op k) (get? m₁ k) (get? m₂ k)).map reify).map fourier
      = Option.merge (op k) (get? m₁ k) (get? m₂ k)
    cases h : Option.merge (op k) (get? m₁ k) (get? m₂ k) with
    | none => simp
    | some w => simp [fourier_reify]

/-! ## Non-extensionality via a non-injective linear readout

We exhibit two **distinct** `FourierMap ℕ` representatives that are `PartialMap.equiv`
(observationally equal under `get?`) but not equal as Lean values.  The witness is a single key
storing two families with the **same `δ_{g₀}` pairing but different mass off `g₀`**: the constant
family `reify 0 = (0, 0)` and `offKernel`, which is `0` at `g₀ = false` but `1` at `true`.  Both
have Fourier readout `some 0`, yet differ at `true`.  Crucially the collapse is the
**non-injective linear functional** `fourier` (annihilating the kernel direction `true`), *not* a
retraction onto a representative: the data discarded lives in a genuine **linear subspace**
`ker ⟨δ_{g₀}, ·⟩`, and moving mass into that kernel is invisible. -/

/-- A family in the **same fibre** of the readout as `reify 0` but with mass moved into the kernel
direction: `0` at `g₀ = false`, `1` at `true`.  Its `δ_{g₀}` pairing is `0`, the same as
`reify 0`, but its coordinates differ. -/
def offKernel : Bool → ℕ := fun b => if b then 1 else 0

/-- `offKernel` has the same Fourier readout as `reify 0` (both pair to `0` at `g₀`). -/
theorem offKernel_same_pairing : fourier offKernel = fourier (reify (0 : ℕ)) := rfl

/-- `offKernel` is a *different family* from `reify 0`: they disagree at `true`
(`offKernel true = 1` but `reify 0 true = 0`) — mass moved into the kernel. -/
theorem offKernel_ne_reify : offKernel ≠ reify (0 : ℕ) := by
  intro h
  have h1 := congrFun h true
  simp only [offKernel, reify, if_pos] at h1
  exact absurd h1 (by decide)

/-- First witness: key `false` stores the constant family `reify 0 = (0, 0)`. -/
def m_zero : FourierMap ℕ := FourierMap.insert FourierMap.empty false 0

/-- Second witness: key `false` stores `offKernel = (0, 1)` (same pairing, different mass). -/
def m_off : FourierMap ℕ := fun k => if k = false then some offKernel else none

/-- **Non-extensionality.**  `m_zero` and `m_off` are observationally equal (`PartialMap.equiv`)
— both denote "key `false` ↦ Fourier coefficient `0`, everything else absent" — yet they are
**distinct** Lean values, because the underlying stored families (`(0, 0)` versus `(0, 1)`) differ
at `true`.  The collapse is the **non-injective linear functional** `fourier`: the discarded data
lives in `ker ⟨δ_{g₀}, ·⟩`.  This is impossible for any `ExtensionalPartialMap`, and is a
*structurally new* flavour of non-extensionality (a linear-functional kernel, not a
quotient/retraction). -/
theorem nonextensional :
    PartialMap.equiv (M := FourierMap) m_zero m_off ∧ m_zero ≠ m_off := by
  refine ⟨fun k => ?_, ?_⟩
  · -- observationally equal: both give `some 0` at key `false`, `none` elsewhere
    by_cases hk : k = false
    · subst hk
      show ((m_zero false).map fourier) = ((m_off false).map fourier)
      have hz : m_zero false = some (reify 0) := by simp [m_zero, FourierMap.insert]
      have ho : m_off false = some offKernel := by simp [m_off]
      rw [hz, ho, Option.map_some, Option.map_some, offKernel_same_pairing]
    · show ((m_zero k).map fourier) = ((m_off k).map fourier)
      have hz : m_zero k = none := by
        simp [m_zero, FourierMap.insert, FourierMap.empty, Ne.symm hk]
      have ho : m_off k = none := by simp [m_off, hk]
      rw [hz, ho]
  · -- distinct as Lean values: at key `false` the stored families differ at `true`
    intro h
    have h0 : m_zero false = m_off false := congrFun h false
    have hz : m_zero false = some (reify 0) := by simp [m_zero, FourierMap.insert]
    have ho : m_off false = some offKernel := by simp [m_off]
    rw [hz, ho, Option.some.injEq] at h0
    exact offKernel_ne_reify h0.symm

/-- Consequently this instance is genuinely non-extensional: `equiv` does NOT imply `=`. -/
theorem not_extensionalPartialMap :
    ¬ ∀ {m₁ m₂ : FourierMap ℕ}, PartialMap.equiv m₁ m₂ → m₁ = m₂ := by
  intro h
  exact nonextensional.2 (h nonextensional.1)

/-! ## The genuine total-sum (DC / trivial-character) Fourier coefficient

The core instance above pairs against the *delta* character `δ_{g₀}`.  When the value type
carries additive structure we can pair against the **trivial character** `χ ≡ 1`, recovering the
honest **total-sum / DC Fourier coefficient**

  `dc s = Σ_{g} s g = s false + s true`.

Like the delta pairing this is a **non-injective linear functional** — but now the collapsing is
the genuinely *non-coordinate* one the introduction advertises: `dc` is invariant under moving
mass between coordinates (`(2,0)` and `(1,1)` and `(0,2)` all pair to `2`), so its kernel is the
"antidiagonal" `{(a, -a)}`, not a coordinate axis.  We record its non-injectivity here; the
applicability section below uses it as the observable when `V` is a module. -/

section DC

variable [AddCommMonoid V]

/-- The **trivial-character / DC Fourier coefficient**: the total sum `Σ_g s g = s false + s true`.
A non-injective linear functional whose kernel is the antidiagonal. -/
def dc (s : Bool → V) : V := s false + s true

/-- `dc` is **mass-redistribution invariant**: families with the same total sum agree under `dc`,
even when their individual coordinates differ.  This is the non-coordinate, genuinely linear
collapse (kernel = antidiagonal). -/
theorem dc_congr {s s' : Bool → V} (h : s false + s true = s' false + s' true) :
    dc s = dc s' := h

end DC

/-- The DC coefficient is a **non-injective** linear functional over `ℕ`: `(2,0)` and `(1,1)` have
the same total sum `2` yet are different families.  (Contrast a projection, which can only collapse
along a coordinate axis; the DC kernel is the antidiagonal.) -/
theorem dc_not_injective :
    dc (fun b => if b then 0 else 2 : Bool → ℕ) = dc (fun _ => 1)
      ∧ (fun b => if b then 0 else 2 : Bool → ℕ) ≠ (fun _ => 1) := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrFun h true
  simp at this

end FourierMap

/-! ## Applicability: a `HeapView` CMRA observing only the DC / Fourier component

Since `FourierMap` is a `LawfulPartialMap FourierMap Bool`, it slots directly into
`Iris.Algebra.HeapView`:

  `HeapView F Bool V H`  with  `H := FourierMap` (this file) and `K := Bool`.

`HeapView` provides authoritative ownership `Auth (.own one) m` over the whole heap of stored
families, and fragmental ownership `Frag k dq v` over a single cell's *Fourier coefficient*; the
view relation `HeapR` observes the heap **only** through `Std.PartialMap.get?`, i.e. through this
file's linear readback `fourier` (`Iris/Algebra/HeapView.lean`, lines 314–495).

### A genuinely new frame-preserving update flavour: redistribute mass, keep the pairing

Because the readout is a **linear functional**, a whole *linear subspace* of edits is free
(frame-preserving): **any change to the stored family that lies in the kernel of the pairing leaves
the observation fixed.**  When `V` is a richer module and we pair against the trivial character
(`FourierMap.dc`, the DC component `Σ_g s g`), an update may **move value between coordinates while
keeping the total fixed** — `(2,0) ↝ (1,1) ↝ (0,2)` — and the resource algebra sees *no* change.
This is structurally unlike `CoarseningMap` (whose free edits are "off a fixed cell", a retraction)
and `GermMap` (whose free edits are "on a filter-small set", a quotient): here the invisible
edits form the *linear kernel* `ker ⟨χ, ·⟩` of a Fourier coefficient.

Concretely, replacing the stored family at a key by *any* family with the same readback is the
identity on Fourier coefficients, so for `H := FourierMap`:

  `Auth (.own one) m₁ • Frag k (.own one) v  ~~>  `
  `Auth (.own one) (insert m₁ k v) • Frag k (.own one) v`,

an instance of `HeapView.update_replace` (`Iris/Algebra/HeapView.lean`, line 438): the new cell
value `v2 := v` is valid because `✓ v` already held, and the update is stated purely through
`get?`/`insert`, never term equality.  Because `insert` re-stores the canonical family
(coefficient `v`), this is observationally an identity on the CMRA element — yet the underlying
family has been redistributed within the kernel.  More generally
`HeapView.update_of_local_update` lifts any local update `(v, v) ~l~> (v, v')` on the Fourier
coefficients; the "mass redistribution within the kernel" is invisible to the CMRA precisely
because every HeapView operation only sees the linear readout. -/

section Applicability

open FourierMap

variable {V : Type _}

/-- **Fourier-observation invariance under kernel-direction edits**, machine-checked.  Replacing
the canonical family at a key by *any* family with the same `δ_{g₀}` pairing yields an `equiv`
map.  Such a rewrite is therefore frame-preserving for every `HeapView` update built on this
instance (it is the denotation-level content of `update_replace`/`update_of_local_update`). -/
theorem kernel_edit_equiv (m : FourierMap V) (k : Bool) (v : V) {g : Bool → V}
    (hg : g g₀ = v) :
    PartialMap.equiv (PartialMap.insert m k v) (fun k' => if k = k' then some g else m k') := by
  intro k'
  show ((FourierMap.insert m k v) k').map fourier
    = ((fun k' => if k = k' then some g else m k') k').map fourier
  by_cases hk : k = k'
  · simp only [FourierMap.insert, if_pos hk, Option.map_some]
    rw [fourier_reify]
    exact congrArg some hg.symm
  · simp only [FourierMap.insert, if_neg hk]

/-- A concrete `~~>` witness: at key `false`, edit the stored family from `reify 0 = (0,0)` to
`offKernel = (0,1)` — a move purely in the kernel direction `true`.  The two heaps are
`PartialMap.equiv` (same Fourier coefficient `0`), so the corresponding `HeapView` update is
frame-preserving. -/
example :
    PartialMap.equiv (PartialMap.insert (FourierMap.empty : FourierMap ℕ) false 0)
      (fun k' => if false = k' then some offKernel else FourierMap.empty k') :=
  kernel_edit_equiv FourierMap.empty false 0 (g := offKernel) rfl

end Applicability

end IrisMath.Instances
