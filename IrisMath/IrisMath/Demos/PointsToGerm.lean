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

/-! # Demo 2 — A working points-to heap over a non-extensional container

This demo builds the *program-logic workhorse* — an authoritative heap with a `↦` points-to and the
lookup/agreement rule — entirely over the non-extensional `ConstOnFilterMap atTop` (the `GermMap`).
It shows the framework is a genuine drop-in: every lemma a separation-logic researcher relies on
(`auth ∗ k ↦ v ⊢ ⌜the heap maps k to v⌝`, frame-preserving updates) works verbatim, and the *only*
thing that changes is the mathematics of what "the heap maps `k` to `v`" means.

For the standard `gmap`/`AssocList` heap, the lookup rule reads `get? m k = some v` on the nose.
For our `GermMap`, `get? m k` is the **eventual value** of the stored sequence at `k`, so the rule
reads `get? m k ≡ some v` — *the heap maps `k` to a cell whose germ is `v`*.  The agreement is up to
the filter's small sets (finite modifications of the stored sequence are invisible).  This is a
strictly more flexible heap discipline, obtained for free from the generic Iris machinery.
-/

@[expose] public section

namespace IrisMath.Demos.PointsToGerm

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The non-extensional heap container: `ConstOnFilterMap atTop` (the GermMap), keyed by `ℕ`. -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

/-- Values: agreement on strings (so a cell carries a single agreed-upon string germ). -/
abbrev V := Agree (LeibnizO String)

variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over our non-extensional heap. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap. -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- The points-to assertion: full ownership of cell `k` holding the germ-value `v`. -/
noncomputable def pointsTo (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

@[inherit_doc] notation:50 k " ↦[" γ "] " v => pointsTo γ k v

/-- **Heap lookup / agreement rule** — the workhorse of every heap program logic.

Owning the authority `m` together with the points-to `k ↦ v` proves that the heap maps `k` to a
cell whose observation is `v`.  Over the GermMap this `≡{0}≡` is *germ agreement*: `get? m k` is the
eventual value of the stored sequence, so the rule says "the sequence at `k` eventually equals `v`".

The proof is the generic Iris lemma `auth_op_frag_one_validN_iff`; the heap-specific content is just
what `get? m k` computes to. -/
theorem lookup (γ : GName) (m : H V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ pointsTo (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-- **Frame-preserving cell update**, lifted to an `IProp` fancy update.  Owning the authority and
the points-to, one can replace the cell value by any valid `v'`, updating both the authoritative
heap (its stored sequence at `k`) and the points-to.  This is `HeapView.update_replace` (the rule
behind a heap *store*) transported through `iOwn_update_op` — it works over the non-extensional heap
with no change.  Over the GermMap the new authoritative cell may be realized by any sequence whose
germ is `v'`. -/
theorem store (γ : GName) (m : H V) (k : Nat) (v v' : V) (Hv' : ✓ v') :
    auth (F := F) (GF := GF) γ m ∗ pointsTo (F := F) (GF := GF) γ k v ⊢
      |==> (auth (F := F) (GF := GF) γ (Std.PartialMap.insert m k v')
            ∗ pointsTo (F := F) (GF := GF) γ k v') := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (HeapView.update_replace (F := F) (m1 := m) (k := k) (v1 := v) (v2 := v') Hv')).trans ?_
  exact BIUpdate.mono iOwn_op.mp

end IrisMath.Demos.PointsToGerm
