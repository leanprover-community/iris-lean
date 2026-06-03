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

/-! # Demo 11 — The view relation *is* a refinement relation (no heap)

`HeapView`'s view relation `HeapR` relates an authoritative ("model") map to a fragment
("observation") map: validity of `Auth m • Frag k v` says the model at `k` *agrees with* (dominates,
in the CMRA order) the observation `v`.  Read this way, `HeapView` is a **refinement / simulation**
resource: the authority is an **abstract specification's state**, fragments are an **implementation's
observations**, and `auth ∗ obs` is the proposition "*the implementation refines the spec at this
location*."

Using the non-extensional `ConstOnFilterMap atTop` (GermMap) as the container makes the refinement
hold **up to a quotient** — here, up to the germ along `atTop`.  Concretely: an implementation that
observes a converging *approximation sequence* refines an abstract spec that fixes only the *limit*.
The two need not agree on the nose; they must agree *eventually* (the filter's small sets are the
slack the simulation is allowed).  This is exactly the setting of *coupled / up-to* simulations.

We prove the refinement square: holding the abstract authority `m` and a concrete observation
`obs k v`, the spec's value at `k` agrees (`≡{0}≡`) with the observation — refinement as camera
validity — and that this agreement is genuinely *coarser than equality* (distinct concrete
approximation sequences refine the same abstract limit).
-/

@[expose] public section

namespace IrisMath.Demos.RefinementWitness

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The container: `ConstOnFilterMap atTop` — abstract values are *limits*; concrete observations are
*approximation sequences*, observed up to their eventual value. -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

/-- Values: an abstract observable (a string label here; in practice a result value). -/
abbrev V := Agree (LeibnizO String)

variable {F} [UFraction F]

abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- **The abstract specification state.**  The authority records, for every location `k`, the
abstract (limit) value the spec prescribes there. -/
noncomputable def spec (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- **A concrete observation.**  The implementation owns a fragment recording what it observes at
location `k` — its converging approximation, observed up to the germ. -/
noncomputable def observes (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

/-- **The refinement square.**  If the abstract spec is `m` and the implementation observes `v` at
`k`, then the spec's value at `k` agrees with the observation: `get? m k ≡{0}≡ some v`.  For the
GermMap this is agreement of the *eventual values* — the implementation refines the spec **up to the
filter** (up to finite stutter / up to precision), not on the nose.  This is the generic
`auth_op_frag_one_validN_iff`; the refinement-up-to-quotient is the mathematics of the container. -/
theorem refines (γ : GName) (m : H V) (k : Nat) (v : V) :
    spec (F := F) (GF := GF) γ m ∗ observes (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (HeapView.auth_op_frag_one_validN_iff.mp H).2.2

/-- **Refinement is coarser than equality.**  Two *different* concrete spec-maps (storing distinct
approximation sequences with the same limit) are refinement-equivalent (`≡`) yet unequal as data —
so a single abstract spec is refined by genuinely different concrete implementations.  An extensional
heap could not express this: there refinement would collapse to literal equality of the concrete
representations.  (Reuses the GermMap non-extensionality witness: `fun _ ↦ a` vs the sequence that
differs only at index `0`.) -/
theorem refinement_is_up_to_quotient :
    ∃ (m₁ m₂ : H V), (m₁ ≡ m₂) ∧ m₁ ≠ m₂ := by
  let a : V := toAgree ⟨"a"⟩
  let b : V := toAgree ⟨"b"⟩
  have hab : a ≠ b := by
    intro h
    have hcar : a.car = b.car := congrArg Agree.car h
    simp only [a, b, toAgree, List.cons.injEq, and_true] at hcar
    exact absurd (congrArg LeibnizO.car hcar) (by decide)
  refine ⟨fun k => if k = 0 then some (fun _ => a) else none,
          fun k => if k = 0 then some (fun n => if n = 0 then b else a) else none, ?_, ?_⟩
  · have hev : (fun m => if m = 0 then b else a) =ᶠ[Filter.atTop (α := ℕ)] (fun _ => a) := by
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      exact ⟨1, fun m hm => by simp [Nat.one_le_iff_ne_zero.mp hm]⟩
    refine OFE.equiv_dist.mpr (fun n k => ?_)
    show (ConstOnFilterMap.get? _ _ k) ≡{n}≡ (ConstOnFilterMap.get? _ _ k)
    by_cases hk : k = 0
    · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, if_pos hk, if_pos hk,
        Option.bind_some, Option.bind_some, eventualValue_const, eventualValue_congr hev,
        eventualValue_const]
    · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, if_neg hk, if_neg hk]
  · intro h
    have h0 := congrFun h 0
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    have h00 := congrFun h0 0
    rw [if_pos rfl] at h00
    exact hab h00

/-! ## The point

`refines` is the standard "the implementation's observation is consistent with the spec" rule, and
it is the *generic* `auth_op_frag` agreement — no new metatheory.  By choosing the non-extensional
GermMap container, that same rule expresses refinement **up to a quotient**: the implementation may
observe any approximation sequence with the right limit, and `refinement_is_up_to_quotient` exhibits
genuinely distinct concrete maps refining one abstract spec.  The view relation `HeapR` is, quite
literally, the simulation relation — and the container's mathematics chooses *how much slack* the
simulation gets (here: agreement modulo the filter's small sets). -/

end IrisMath.Demos.RefinementWitness
