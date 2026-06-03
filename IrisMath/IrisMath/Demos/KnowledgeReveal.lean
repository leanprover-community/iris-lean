/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.KnowledgeMap

/-! # Demo 3 — A weird problem: a heap cell that owns an *unknown* value

**The problem.**  A protocol has a *committed-but-undisclosed* value at a location `k` — think of a
sealed bid, a commitment in a crypto protocol, or an oracle that has fixed an answer but not yet
revealed it.  We want the location to be a *real, owned heap cell* (so it participates in separation
logic, framing, transfer of ownership) while its value is genuinely *not yet observable*.  On a
standard `gmap` heap you cannot do this: a cell either maps to a concrete value or is absent; there
is no "present but unknown" state.

**The solution.**  Use the auto-researcher's `KnowledgeMap` as the `HeapView` container.  A cell
stores a *knowledge state* — a set of candidate values — and the observation `get?` returns `some v`
only when that set has collapsed to the singleton `{v}` (the value is *pinned*), and `none` while it
is still uncertain.  This is a genuinely non-extensional heap: many distinct knowledge states (e.g.
"any value", "one of two") all observe as `none`, yet are different owned resources.

Below we plug `KnowledgeMap` into the generic Iris `HeapView`/`iOwn` machinery and prove the rule a
verifier actually needs: **owning the points-to `k ↦ v` proves the committed value at `k` is exactly
`v`** — i.e. a fragment witnesses that the secret is determined.  Dually, an authoritative cell may
be left *unpinned* (committed but unknown) and the heap is still perfectly valid.
-/

@[expose] public section

namespace IrisMath.Demos.KnowledgeReveal

open Iris Iris.BI COFE
open HeapView One DFrac Excl
open IrisMath.Instances

/-- The heap container: `KnowledgeMap` over `ℕ` keys.  A cell holds a *set of candidate values*. -/
abbrev H := KnowledgeMap (K := Nat)

/-- Values are exclusive natural numbers (the "secret" payload). -/
abbrev V := Excl Nat

variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over the knowledge heap. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole knowledge heap.  The authoritative map `m : H V` assigns to
each key a *knowledge state* (`Set V`); a key whose state is not a singleton is "committed but
unknown". -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- The points-to: a fragment asserting the committed value at `k` is (revealed to be) `v`. -/
noncomputable def revealed (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

/-- **Reveal rule (the verifier's workhorse).**  If we hold the authority over the heap `m` and a
points-to fragment `revealed γ k v`, then the committed value at `k` is determined to be `v`:
the observation `get? m k` (which is `some w` iff the knowledge state at `k` is the singleton
`{w}`) equals `some v`.  In protocol terms: *possessing the opened commitment proves what was
committed.*

The proof is the generic Iris lemma `auth_op_frag_one_validN_iff` — unchanged from any heap.  The
KnowledgeMap-specific content is the *meaning* of `get? m k = some v`: the cell's candidate set has
collapsed to exactly `{v}`. -/
theorem reveal (γ : GName) (m : H V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ revealed (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-- **Two revealed fragments at the same key disagree.**  If two parties each claim to hold the
opened commitment at `k`, with *different* values, that is contradictory — exclusive fragment
ownership rules it out.  This is the standard points-to exclusivity, here giving "a commitment
opens to at most one value." -/
theorem reveal_agree (γ : GName) (k : Nat) (v w : V) :
    revealed (F := F) (GF := GF) γ k v ∗ revealed (F := F) (GF := GF) γ k w ⊢
      ⌜(v • w : V) ≡{0}≡ v • w ∧ ✓{0} (v • w)⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact ⟨.rfl, (frag_op_validN_iff.mp H).2⟩

/-! ## The point

`reveal` and `reveal_agree` are *exactly* the rules a separation-logic researcher would write for a
points-to heap — and they are proved by the **generic** Iris lemmas, with no new metatheory.  What
the `KnowledgeMap` instance buys is a new, mathematically-principled cell *state* the standard heap
cannot express: **"present and owned, but not yet observable."**  An authoritative heap can hold a
non-singleton knowledge state at `k` (a live commitment), participate in all the usual ownership
discipline, and only later be refined to a singleton when the value is disclosed — the
non-extensionality (`equiv` not `eq`) is precisely what makes "unknown but owned" a first-class
heap state. -/

end IrisMath.Demos.KnowledgeReveal
