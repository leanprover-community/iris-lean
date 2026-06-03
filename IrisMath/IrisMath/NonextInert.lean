/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.ConstOnFilterMap

/-! # Non-extensionality is logically inert in `HeapView`

This file formalizes, as a sorry-free Lean theorem, the claim that **non-extensionality is
logically inert in `HeapView`**: any two `LawfulPartialMap` representatives with the same `get?`
readout produce *equal* (`≡`) `HeapView` authority resources, hence are indistinguishable by every
Iris proposition.

The recurring critic argument — "the camera factors through `get?`, so any non-extensional store is
simulable by the extensional heap over its `get?` readout" — is here turned into a theorem.  The
chain is short and entirely structural:

* The store OFE (`Iris.Heap.instOFE`, `PartialMap.instOFE`) is *defined through* `get?`:
  `m₁ ≡ m₂ ⟺ get? m₁ ≡ get? m₂`.  Hence `PartialMap.eqv_of_Equiv : PartialMap.equiv t₁ t₂ → t₁ ≡ t₂`
  (two reps with equal `get?` are already OFE-equal).
* `HeapView.Auth dq` is non-expansive in its map argument (`View.auth_ne`), so OFE-equal maps give
  OFE-equal authorities (`auth_equiv_of_get_eq`).
* `iOwn γ` is non-expansive in its resource argument, and `≡` resources are `⊣⊢` Iris propositions
  (`equiv_iff`), so owning the authority over `m₁` is *the same Iris proposition* as over `m₂`
  (`auth_iprop_indistinguishable`).

## Verdict

The inertness is formally established for **general** `LawfulPartialMap`: equiv representatives
(`PartialMap.equiv`, i.e. equal `get?`) yield an *identical* Iris resource `iOwn γ (Auth dp ·)`, so
the non-extensional difference is invisible to every Iris connective.  The non-extensionality is a
purely *modeling/representational* device.  The corollary `auth_indistinguishable_germ`
instantiates this at a genuinely non-extensional store (`ConstOnFilterMap atTop`) using its
`nonextensional_of_eventuallyEq` witness — two distinct families `m₁ ≠ m₂` with `PartialMap.equiv`,
yet `iOwn γ (Auth dp m₁) ⊣⊢ iOwn γ (Auth dp m₂)`: *distinct heaps, same Iris resource.*

The genuine logical content lives in the *value CMRA* `V` (the fragments `Frag k dq v` distinguish
values via `get? m k`), which the extensional simulation over `get?` shares verbatim; the store's
choice of representative carries none.

## Loophole

The inertness covers exactly the observations that factor through `get?` (which is *all* of the
`HeapView` CMRA structure: `HeapR` reads the model only through `Std.PartialMap.get?`).  An
observation that does *not* factor through `get?` — e.g. reading the raw stored representative
family of a `ConstOnFilterMap` cell as a Lean term (`m k : Idx → V`), outside the OFE/CMRA — is not
covered, but no such observation is expressible as an Iris proposition over the `HeapView` resource:
every Iris connective sees the resource only up to `≡`, which is `get?`-equality.
-/

@[expose] public section

namespace IrisMath.NonextInert

open Iris Iris.BI COFE Iris.Std
open HeapView One DFrac
open scoped Filter

/-! ## Theorem 1 (camera level): equiv representatives give OFE-equal authorities -/

section CameraLevel

variable {F K V : Type _} {H : Type _ → Type _}
  [UFraction F] [Iris.Std.LawfulPartialMap H K] [CMRA V]

/-- **Theorem 1 — `auth_equiv_of_get_eq` (camera level).**

If two heaps `m₁ m₂ : H V` have the same `get?` readout (`PartialMap.equiv m₁ m₂`), then the
`HeapView` authorities over them are OFE-equal: `Auth dp m₁ ≡ Auth dp m₂`.

Proof: the store OFE identifies equal-`get?` reps (`PartialMap.eqv_of_Equiv`), and `Auth dp` is
non-expansive in its map argument (the `NonExpansive (Auth dp)` instance, i.e. `View.auth_ne`), so
it preserves that equivalence.  This is the precise camera-level statement that the non-extensional
difference between `m₁` and `m₂` is already invisible at the level of the resource. -/
theorem auth_equiv_of_get_eq (dp : DFrac F) {m₁ m₂ : H V}
    (h : Iris.Std.PartialMap.equiv m₁ m₂) :
    (Auth dp m₁ : HeapView F K V H) ≡ Auth dp m₂ :=
  OFE.NonExpansive.eqv (f := (Auth dp : H V → HeapView F K V H))
    (PartialMap.eqv_of_Equiv h)

end CameraLevel

/-! ## Theorem 2 (logic level): equiv representatives give the same Iris proposition

We mirror the `auth`/`HeapF`/`ElemG` boilerplate of `IrisMath.Demos.EventualValue`. -/

section LogicLevel

variable {F K V : Type _} {H : Type _ → Type _}
  [UFraction F] [Iris.Std.LawfulPartialMap H K] [CMRA V]

/-- The heap functor: `constOF` of the generic `HeapView` CMRA over the store `H`. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F K V H

variable {GF} [ElemG GF (HeapF (F := F) (K := K) (V := V) (H := H))]

/-- Authoritative (fractional) ownership of the whole heap, as an Iris proposition. -/
noncomputable def auth (γ : GName) (dp : DFrac F) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F) (K := K) (V := V) (H := H)) γ (Auth dp m)

/-- **Theorem 2 — `auth_iprop_indistinguishable` (logic level).**

If `m₁` and `m₂` have the same `get?` readout (`PartialMap.equiv m₁ m₂`), then owning the authority
over `m₁` is *the same Iris proposition* as owning it over `m₂`:

> `iOwn γ (Auth dp m₁) ⊣⊢ iOwn γ (Auth dp m₂)`.

This is the formal statement that the non-extensional difference between `m₁` and `m₂` is invisible
to every Iris connective: any context built from `auth γ dp m₁` is `⊣⊢` to the same context built
from `auth γ dp m₂`.

Proof: lift `auth_equiv_of_get_eq` (Theorem 1) through the non-expansiveness of `iOwn γ` to an OFE
equivalence of resources, then convert `≡` of resources to `⊣⊢` of `iOwn`s via `equiv_iff`. -/
theorem auth_iprop_indistinguishable (γ : GName) (dp : DFrac F) {m₁ m₂ : H V}
    (h : Iris.Std.PartialMap.equiv m₁ m₂) :
    auth (F := F) (GF := GF) γ dp m₁ ⊣⊢ auth (F := F) (GF := GF) γ dp m₂ :=
  equiv_iff.mp
    (OFE.NonExpansive.eqv
      (f := iOwn (GF := GF) (F := HeapF (F := F) (K := K) (V := V) (H := H)) γ)
      (auth_equiv_of_get_eq dp h))

end LogicLevel

/-! ## Theorem 3 (concrete corollary): a genuinely non-extensional store

We instantiate Theorems 1–2 at the `ConstOnFilterMap atTop` store over `ℕ` keys — the canonical
non-extensional `LawfulPartialMap` (`IrisMath.Instances.ConstOnFilterMap`) — using its own
non-extensionality witness `nonextensional_of_eventuallyEq`.  The value CMRA is `Agree (LeibnizO ℕ)`
(a genuine CMRA).  We pick two cell-`0` families that agree `atTop`-eventually but differ as
functions:

* `m₁` stores `fun _ => a` (the constant family),
* `m₂` stores `fun n => if n = 0 then b else a` (bumped at index `0`),

which are `=ᶠ[atTop]` (they agree for all `n ≥ 1`) yet unequal as Lean functions (they differ at
`n = 0` when `a ≠ b`).  The conclusion: the two *distinct* heaps own the *same* Iris resource. -/

section Corollary

open IrisMath.Instances Iris.Std

/-- The non-extensional store: `ConstOnFilterMap atTop` over `ℕ` keys. -/
abbrev GH : Type _ → Type _ := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

/-- Cell values: agreement on `ℕ`, a genuine CMRA. -/
abbrev GV : Type _ := Agree (LeibnizO ℕ)

variable {F} [UFraction F]
variable {GF} [ElemG GF (HeapF (F := F) (K := Nat) (V := GV) (H := GH))]

/-- The constant-family witness: cell `0` stores `fun _ => a`. -/
noncomputable def m_const (a : GV) : GH GV := fun k => if k = 0 then some (fun _ => a) else none

/-- The bumped-family witness: cell `0` stores `fun n => if n = 0 then b else a` (same germ when
`a` is the tail value, different rep). -/
noncomputable def m_bump (a b : GV) : GH GV :=
  fun k => if k = 0 then some (fun n => if n = 0 then b else a) else none

/-- The two witness families agree `atTop`-eventually (they coincide for all `n ≥ 1`). -/
theorem m_witness_eventuallyEq (a b : GV) :
    (fun _ => a) =ᶠ[Filter.atTop (α := ℕ)] (fun n => if n = 0 then b else a) := by
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨1, fun n hn => by rw [if_neg (by omega)]⟩

/-- The two witness heaps are `PartialMap.equiv` (observationally equal under `get?`) — for *any*
`a b`, since the `equiv` half of non-extensionality needs only the `atTop`-eventual agreement of the
stored families, not `a ≠ b`.  Proved directly via `eventualValue_congr`. -/
theorem m_witness_equiv (a b : GV) :
    PartialMap.equiv (M := GH) (m_const a) (m_bump a b) := by
  refine fun k => ?_
  change ((m_const a k).bind (eventualValue (Filter.atTop (α := ℕ))))
      = ((m_bump a b k).bind (eventualValue (Filter.atTop (α := ℕ))))
  by_cases hk : k = 0
  · rw [m_const, m_bump, if_pos hk, if_pos hk, Option.bind_some, Option.bind_some,
      eventualValue_congr (m_witness_eventuallyEq a b)]
  · rw [m_const, m_bump, if_neg hk, if_neg hk]

/-- The two witness heaps are genuinely **distinct** Lean values when `a ≠ b`: their stored
representative families differ at index `0`.  This is the non-extensionality witness proper. -/
theorem m_witness_ne (a b : GV) (hab : a ≠ b) : m_const a ≠ m_bump a b := by
  intro h
  have h0 := congrFun h 0
  rw [m_const, m_bump, if_pos rfl, if_pos rfl, Option.some.injEq] at h0
  exact hab (by have := congrFun h0 0; simpa using this)

/-- **Theorem 3 — the punchline corollary.**

At the genuinely non-extensional store `ConstOnFilterMap atTop`, the two *distinct* witness heaps
`m_const a ≠ m_bump a b` (which differ in their stored representative family at index `0`) own the
**same** Iris authority resource:

> `iOwn γ (Auth dp (m_const a)) ⊣⊢ iOwn γ (Auth dp (m_bump a b))`.

The witnessed non-extensionality (`m_const a ≠ m_bump a b`) is logically a no-op: the difference
between the constant family and its bumped representative — visible at the level of raw Lean terms —
is *erased* by `get?` and hence by every Iris proposition.  Distinct heaps, same Iris resource. -/
theorem auth_indistinguishable_germ (γ : GName) (dp : DFrac F) (a b : GV) :
    auth (F := F) (GF := GF) γ dp (m_const a) ⊣⊢ auth (F := F) (GF := GF) γ dp (m_bump a b) :=
  auth_iprop_indistinguishable (F := F) (GF := GF) γ dp (m_witness_equiv a b)

end Corollary

end IrisMath.NonextInert
