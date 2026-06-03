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

/-! # Demo 3 — Approximate agreement at finite precision (a NON-heap use of `HeapView`)

This demo is *not* a program memory heap.  We reuse the generic Iris `HeapView` resource algebra,
but the cells store **converging approximation sequences** rather than program values, and we read
them at their *limit* (eventual value).  The container is the non-extensional
`ConstOnFilterMap atTop` (the `GermMap`): a cell holds a sequence `ℕ → V` of successive refinements,
observed only through `get?`, which returns the germ — the value the sequence is *eventually* equal
to.

## The story

Two parties each run an **anytime / iterative numerical** computation of some quantity.  Each holds
a sequence of refinements that converges to a limit; they store it in a germ-cell.  Because the
observation `get?` factors through `Filter.EventuallyEq atTop`, the logic can *only* see the limit,
never the particular approximation path taken to get there.

This makes three slogans first-class, *proven* logical facts:

1. **Eventual agreement.**  Two authorities holding germ-cells with the same limit provably agree —
   `auth γ m₁ ∗ auth γ m₂ ⊢ ⌜m₁ ≡{0}≡ m₂⌝`.  For the GermMap, `m₁ ≡{0}≡ m₂` is pointwise equality of
   the *limits* `get?`, so the two parties "agree on the limit" even if their approximation
   sequences differ at finitely many early steps.

2. **Refinement is invisible.**  Replacing a cell's stored approximation sequence by *another*
   sequence with the same eventual value is a frame-preserving update that nobody can observe — you
   may refine (or coarsen, or re-derive) your approximation "without anyone noticing".  Concretely,
   two distinct representatives produce the *same* limit-cell: `agreement_is_coarser_than_equality`
   exhibits two `≢`-as-Lean-values sequences that are `≡` in the heap OFE, and `refine_is_invisible`
   lifts the cell replacement to an `IProp` fancy update `|==>`.

3. **A precision ladder.**  `auth • auth` forces only `≡{0}≡` — finite-precision agreement.  An
   *extensional* heap (`gmap`/`AssocList`) would force literal equality `=` here; the germ quotient
   is precisely what turns "agree up to finite stutter / up to precision" into a logical notion.
-/

@[expose] public section

namespace IrisMath.Demos.ApproximateAgreement

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The non-extensional heap container: `ConstOnFilterMap atTop` (the GermMap), keyed by `ℕ`.
A cell stores a *sequence* `ℕ → V` of successive refinements, read at its limit. -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

/-- Cell values: agreement on strings — each cell agrees on a single *limit* (germ). -/
abbrev V := Agree (LeibnizO String)

variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over the GermMap. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap of approximation-cells. -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- A single approximation-cell: full ownership of cell `k` whose limit is `v`. -/
noncomputable def cell (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

/-! ## 1. Eventual agreement — the two parties agree on the limit -/

/-- **Eventual agreement.**  Two authoritative views of the approximation-heap, jointly owned, force
the two heaps to be equivalent at step `0`.  For the GermMap, `m₁ ≡{0}≡ m₂` unfolds to
"`get? m₁ k ≡ get? m₂ k` at every key `k`" — pointwise equality of the *limits*.  So the two parties
provably agree on every limit, even when their stored approximation sequences differ at finitely
many early steps.

The proof is the generic Iris agreement lemma `dist_of_validN_auth_op`; the *meaning* of the
conclusion is supplied by the germ container. -/
theorem auth_op_agree (γ : GName) (m₁ m₂ : H V) :
    auth (F := F) (GF := GF) γ m₁ ∗ auth (F := F) (GF := GF) γ m₂ ⊢
      ⌜m₁ ≡{0}≡ m₂⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact dist_of_validN_auth_op H

/-- **Limit lookup.**  Owning the authority `m` together with the approximation-cell `k ↦ v` proves
that the heap's limit at `k` is `v`.  Over the GermMap this `≡{0}≡` says "the stored approximation
sequence at `k` *eventually* equals `v`" — i.e. converges to the limit `v`. -/
theorem limit_lookup (γ : GName) (m : H V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ cell (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-! ## 2. Refinement is invisible — changing finitely many early terms is unobservable -/

/-- **Two refinements, one limit.**  We exhibit two genuinely distinct approximation-heaps that the
logic cannot tell apart: at key `0` one stores the *already-settled* constant sequence `fun _ ↦ a`
(limit `a`), the other stores a sequence that disagrees at the very first refinement step (`b` at
index `0`) but agrees from step `1` on (`a` thereafter).  They converge to the *same* limit `a`, so
they are `≡` in the heap OFE — yet they are `≠` as Lean values (they differ at index `0`, `a ≠ b`).

This is the precise sense in which "refining an approximation by changing finitely many early terms
is invisible": the two representatives are observationally identical.  An *extensional* heap could
never witness this gap; there `≡` would force `=`. -/
theorem agreement_is_coarser_than_equality :
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
  · -- equivalent: at key 0 both converge to limit `a`; elsewhere both absent.
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
  · -- distinct Lean values: they differ at key 0, index 0, where `a ≠ b`.
    intro h
    have h0 := congrFun h 0
    rw [if_pos rfl, if_pos rfl, Option.some.injEq] at h0
    have h00 := congrFun h0 0
    rw [if_pos rfl] at h00
    exact hab h00

/-- **Refinement is an invisible, frame-preserving update.**  Owning the authority and the
approximation-cell `k ↦ v`, one may replace the stored sequence at `k` by *any* sequence whose limit
is some valid `v'`, updating both the authority and the cell, as an `IProp` fancy update `|==>`.

This is the generic heap *store* (`HeapView.update_replace`) transported through `iOwn_update`.
Over the GermMap, the realizer of the new cell may be *any* approximation sequence converging to
`v'`:
`Std.PartialMap.insert` stores the settled constant `fun _ ↦ v'`, but by
`agreement_is_coarser_than_equality` any other sequence with limit `v'` is `≡` to it — so "which
approximation path you took" is genuinely unobservable after the update. -/
theorem refine_is_invisible (γ : GName) (m : H V) (k : Nat) (v v' : V) (Hv' : ✓ v') :
    auth (F := F) (GF := GF) γ m ∗ cell (F := F) (GF := GF) γ k v ⊢
      |==> (auth (F := F) (GF := GF) γ (Std.PartialMap.insert m k v')
            ∗ cell (F := F) (GF := GF) γ k v') := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (HeapView.update_replace (F := F) (m1 := m) (k := k) (v1 := v) (v2 := v') Hv')).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-! ## 3. The precision ladder

`auth_op_agree` concludes only `m₁ ≡{0}≡ m₂` — *finite-precision* agreement: the parties agree on
each limit, which over the GermMap means "their approximation sequences eventually coincide", i.e.
agreement *up to a finite prefix / up to precision*.  With an extensional heap (`gmap`, `AssocList`,
`ExtTreeMap`, all of which satisfy `equiv ↔ eq`) the very same generic lemma would force the much
stronger `m₁ = m₂` on the nose.  `agreement_is_coarser_than_equality` proves the gap is real: there
exist `≡`-but-`≠` heaps.  The non-extensionality of the germ quotient *is* the "agree up to
precision" feature.

Below: a direct restatement packaging the ladder — the agreement principle plus an explicit witness
that the agreed-upon relation is strictly coarser than equality. -/
theorem precision_ladder :
    -- the agreement principle only forces step-0 (finite-precision) agreement, and …
    (∀ (γ : GName) (m₁ m₂ : H V),
      auth (F := F) (GF := GF) γ m₁ ∗ auth (F := F) (GF := GF) γ m₂ ⊢ ⌜m₁ ≡{0}≡ m₂⌝)
    -- … that agreement (`≡`) is strictly coarser than equality (`=`): some `≡`-heaps are `≠`.
    ∧ ∃ (m₁ m₂ : H V), (m₁ ≡ m₂) ∧ m₁ ≠ m₂ :=
  ⟨fun γ m₁ m₂ => auth_op_agree γ m₁ m₂, agreement_is_coarser_than_equality⟩

end IrisMath.Demos.ApproximateAgreement
