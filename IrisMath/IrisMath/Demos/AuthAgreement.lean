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

/-! # Demo 1 — Why a non-extensional heap matters: coarsened authoritative agreement

This demo plugs one of the auto-researcher's non-extensional `LawfulPartialMap` instances —
`ConstOnFilterMap atTop` (the `GermMap`: cells store a *sequence* `ℕ → V`, observed at its eventual
value) — into the **generic** Iris `HeapView` resource algebra, exactly the way `AssocList` is used
in `Iris/Examples/IProp.lean`.  Nothing about `HeapView`, `iOwn`, `Auth`, or the proof mode changes:
the mathematics is entirely in the choice of heap container.

## The point an Iris researcher cares about

For the *standard* extensional heap (`gmap`/`AssocList`/`ExtTreeMap`), two authoritative assertions
`Auth m₁ • Auth m₂` being valid forces `m₁ = m₂` *on the nose* (Leibniz equality), because those
containers satisfy `equiv ↔ eq`.

For our **non-extensional** container, the very same generic lemma
`HeapView.equiv_of_valid_auth_op` yields only `m₁ ≡ m₂` — and here `≡` is the heap OFE's
equivalence, which is *pointwise equality of the observation* `get?`.  For `ConstOnFilterMap atTop`
that means **"the two heaps agree at every key up to a finite modification of the stored
sequence"** — agreement modulo the filter's small sets, NOT literal equality of representatives.

So the researcher gets, for free from the existing Iris agreement principle, a *coarser,
mathematically meaningful* notion of "two authorities agree": agreement up to a null set / a finite
prefix / a germ — whatever the chosen filter forgets.  This is impossible to state with the
extensional heap, where agreement is always brute Leibniz equality.
-/

@[expose] public section

namespace IrisMath.Demos.AuthAgreement

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The non-extensional heap container: `ConstOnFilterMap atTop` over `ℕ` keys (the `GermMap`). -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

-- A type of fractions (kept polymorphic, as in the upstream example).
variable {F} [UFraction F]

/-- The heap functor: a constant OFunctor wrapping the `HeapView` CMRA over our non-extensional
heap, with `Agree (LeibnizO String)` values.  Compare `Iris/Examples/IProp.lean`'s `F1`, which uses
`AssocList` in the same slot — we simply substitute the non-extensional container. -/
abbrev HeapF : COFE.OFunctorPre :=
  constOF <| HeapView F Nat (Agree (LeibnizO String)) H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap `m`, as an `IProp`. -/
noncomputable def auth (γ : GName) (m : H (Agree (LeibnizO String))) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- **The headline.**  Two *full* authoritative assertions over the non-extensional heap, when
jointly owned, force the two heaps to be *equivalent* — i.e. equal at every key under the heap OFE.
The proof is the generic Iris agreement lemma `equiv_of_valid_auth_op`; the *meaning* of the
conclusion `m₁ ≡ m₂` is supplied by the mathematics of the container.

For `ConstOnFilterMap atTop`, `m₁ ≡ m₂` unfolds (via the heap OFE) to "`get? m₁ k ≡ get? m₂ k` for
all `k`": the two heaps observe the same *eventual value* at every key — they may store genuinely
different sequences differing on finite prefixes.  With an extensional heap this same conclusion
would be the much stronger `m₁ = m₂`. -/
theorem auth_op_agree (γ : GName) (m₁ m₂ : H (Agree (LeibnizO String))) :
    auth (F := F) (GF := GF) γ m₁ ∗ auth (F := F) (GF := GF) γ m₂ ⊢
      ⌜m₁ ≡{0}≡ m₂⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  -- `H : ✓{0} (Auth (own one) m₁ • Auth (own one) m₂)`; the generic Iris agreement lemma turns
  -- joint authoritative validity into heap-OFE (step-indexed) equivalence of the two heaps.
  ipure_intro
  exact dist_of_validN_auth_op H

/-! ## The punchline: the agreement is genuinely coarser than equality

`auth_op_agree` concludes `m₁ ≡ m₂`.  For our non-extensional container this is *pointwise
agreement of the observation* `get?` — not Leibniz equality.  We exhibit two heaps `m₁ ≢ ` ... no:
two heaps that ARE `≡` (so the agreement principle is satisfied) yet are `≠` as Lean values.  An
extensional heap could never witness this: there `≡` and `=` coincide. -/

/-- Two `GermMap` representatives at key `0`: the constant sequence `fun _ ↦ a` versus a sequence
that stores a *different* value `b` at index `0` but `a` everywhere after.  Since they agree for all
`n ≥ 1` they are equal along `atTop`, so they have the same eventual value — **equivalent** in the
heap OFE — yet they are **distinct** Lean values (they differ at index `0`, where `a ≠ b`).  An
extensional heap could never witness this gap between `≡` and `=`; for it the agreement principle
`auth_op_agree` would force the representatives to be literally equal. -/
theorem agreement_is_coarser_than_equality :
    ∃ (m₁ m₂ : H (Agree (LeibnizO String))),
      (m₁ ≡ m₂) ∧ m₁ ≠ m₂ := by
  let a : Agree (LeibnizO String) := toAgree ⟨"a"⟩
  let b : Agree (LeibnizO String) := toAgree ⟨"b"⟩
  have hab : a ≠ b := by
    intro h
    have hcar : a.car = b.car := congrArg Agree.car h
    simp only [a, b, toAgree, List.cons.injEq, and_true] at hcar
    -- `hcar : (⟨"a"⟩ : LeibnizO String) = ⟨"b"⟩`; project to the underlying strings
    exact absurd (congrArg LeibnizO.car hcar) (by decide)
  refine ⟨fun k => if k = 0 then some (fun _ => a) else none,
          fun k => if k = 0 then some (fun n => if n = 0 then b else a) else none, ?_, ?_⟩
  · -- equivalent: at key 0 both observe eventual value `a` (the `bumped`-at-0 sequence agrees with
    -- the constant for all n ≥ 1); elsewhere both absent.
    have hev : (fun m => if m = 0 then b else a) =ᶠ[Filter.atTop (α := ℕ)] (fun _ => a) := by
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      exact ⟨1, fun m hm => by simp [Nat.one_le_iff_ne_zero.mp hm]⟩
    refine OFE.equiv_dist.mpr (fun n k => ?_)
    show (ConstOnFilterMap.get? _ _ k) ≡{n}≡ (ConstOnFilterMap.get? _ _ k)
    by_cases hk : k = 0
    · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, if_pos hk, if_pos hk,
        Option.bind_some, Option.bind_some, eventualValue_const, eventualValue_congr hev,
        eventualValue_const]
    · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, if_neg hk, if_neg hk]
  · -- distinct Lean values: evaluate at key 0, index 0, where the stored sequences differ (`a ≠ b`)
    intro h
    have h0 := congrFun h 0
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    have h00 := congrFun h0 0
    rw [if_pos rfl] at h00
    exact hab h00

end IrisMath.Demos.AuthAgreement
