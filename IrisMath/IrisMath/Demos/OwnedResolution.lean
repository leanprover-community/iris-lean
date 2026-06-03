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
public import IrisMath.Instances.VariableFilterMap

/-! # Demo B — Owned, tunable observation *resolution*

Every standard Iris heap commits, once and for all, to a *single* notion of equality on cell
contents: `gmap`/`AssocList`/`ExtTreeMap` all satisfy `equiv ↔ eq`, so "the value at `k`" is a
Leibniz-fixed datum and "two heaps agree" always means *brute equality of representatives*.  The
equivalence relation under which a cell is read is part of the ambient metatheory, not part of the
state.  There is **no resource you can own, frame, or update that adjusts what "equal" means**.

This demo plugs `VariableFilterMap` — the auto-researcher's non-extensional `LawfulPartialMap`
whose **per-cell filter is itself stored heap state** — into the generic Iris `HeapView` resource
algebra (`Iris/Examples/IProp.lean` uses `AssocList` in the identical slot).  A present cell stores
a pair `⟨l, s⟩`: a filter `l : Filter ℕ` *and* a representative sequence `s : ℕ → V`, and `get?`
reads back the `l`-eventual constant value of `s` **using that cell's own filter**.  The filter `l`
is the cell's *resolution* — the size of the "small / negligible" sets it forgets — and because it
lives in the cell, it is owned, transferable ghost state, comparable from cell to cell, and
adjustable by frame-preserving update.

## The deep idea

Picture two observers watching the same evolving data at *different resolutions* — filters
`l₁ ⊑ l₂` (mathlib `l₁ ≤ l₂` means `l₁` **finer**, `l₂` **coarser**).  A coarse observer forgets
more; a fine observer distinguishes more.  Each holds an observation fragment that *carries its own
filter*.  Three facts then become first-class, ownable, and provable inside the *unchanged* logic:

* `observe_at` — an observation fragment records a value *at a stated resolution*, and joint
  validity with the authority forces the authority to agree (the lookup at the cell's stored
  filter).
* `coarsen` (the **prize**) — you may always **lower your own resolution** (`l → l'`, `l ≤ l'`),
  forgetting more, by a *frame-preserving update*.  This is the move with no analogue in standard
  Iris: it does not change any value, it changes *the equivalence relation the value is read modulo*
  — and it is monotone (you can only forget more, never disagree), so it is invisible to every
  frame.  We lift `VariableFilterMap.equiv_coarsen_cell` to an `IProp` `|==>`.
* `agree_at_coarser` — two observers at comparable resolutions provably **agree on the coarser
  observation**: if both reps are eventually constant along the coarser `l₂`, their `l₂`-germs
  coincide.

## The framing an Iris researcher cares about

The `coarsen` update is the headline.  In a fixed-equality CMRA the only updates are *value*
updates — `update_replace`, allocation, fraction shuffling — all of which respect one immutable
notion of "the same value".  Here the **resolution is itself a resource**, and the legal move is
*monotone weakening of the cell's own equality relation*.  "You may always forget more" is a
frame-preserving update precisely because forgetting more can never manufacture disagreement with a
frame that already observed the value: the observation `some v` is preserved along the entire
`≤`-chain on which the rep stays eventually constant (`get?_coarsen`).  The asymmetry — finer
preserves, coarser only forgets — is what makes this update genuinely one-directional.

This is the concrete skeleton of *up-to / coupled simulation* reasoning and of
**multi-resolution monitoring**: a coupling relates two systems up to a chosen observation
equivalence, and "weakening the coupling" (observing more coarsely) is sound exactly when it
forgets, never invents.  Theorem 4's doc comment develops this — "a logic where the notion of
equality is owned ghost state."
-/

@[expose] public section

namespace IrisMath.Demos.OwnedResolution

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances IrisMath.Instances.VariableFilterMap
open scoped Filter

/-- Values are `Agree (LeibnizO String)` (an agreement camera over a discrete label), exactly as in
the other heap-flavoured demos. -/
abbrev V := Agree (LeibnizO String)

-- A fraction type for the authoritative/fragmental split (kept polymorphic, as upstream).
variable {F} [UFraction F]

/-- The resolution functor: a constant OFunctor wrapping the generic `HeapView` CMRA over
`VariableFilterMap ℕ` — the heap whose cells store *their own filter*.  Compare
`Iris/Examples/IProp.lean`'s `F1`, which puts `AssocList` in this slot; we substitute the
filter-carrying container, and nothing about `HeapView`, `iOwn`, `Auth`, or the proof mode changes.

That this typechecks is the first deliverable: `VariableFilterMap ℕ` is a `LawfulPartialMap … ℕ`,
so it composes with `HeapView` with no bespoke glue. -/
abbrev ResF : COFE.OFunctorPre :=
  constOF <| HeapView F Nat V (VariableFilterMap Nat)

variable {GF} [ElemG GF (ResF (F := F))]

/-- Authoritative ownership of the whole resolution heap `m`: per cell, not just a value but the
**resolution** `l` at which that value is observed. -/
noncomputable def auth (γ : GName) (m : VariableFilterMap Nat V) : IProp GF :=
  iOwn (GF := GF) (F := ResF (F := F)) γ (Auth (own one) m)

/-- An **observation fragment**: full (`own one`) fractional ownership of cell `k`, recording that
its observed value is `v`.  (The *resolution* at which `k` is read lives in the authority's stored
cell; this fragment is the observer's claim on the observed value.) -/
noncomputable def obs (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := ResF (F := F)) γ (Frag k (own one) v)

/-! ## Theorem 1 — `observe_at`: a fragment pins the observation at the cell's resolution

An observation fragment together with the authority forces the authority's *observed value* at `k`
— `get? m k`, the read-back of the cell's rep through **the cell's own filter** — to equal `v`.
This is the generic `HeapView.auth_op_frag_one_validN_iff`; the new content is that `get?` here
silently resolves through whatever resolution the authority stored at `k`.  The observer learns the
value *modulo that cell's equality*, never the raw representative. -/
theorem observe_at (γ : GName) (m : VariableFilterMap Nat V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ obs (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (HeapView.auth_op_frag_one_validN_iff.mp H).2.2

/-! ## Theorem 2 — `coarsen`: lowering your own resolution is a frame-preserving update (THE PRIZE)

The defining new move.  Consider an authority whose only live cell `k₀` stores the *finer* filter
`l` over a constant rep `fun _ ↦ v`.  We **coarsen** it to `l'` with `l ≤ l'` (so `l'` is coarser,
forgetting more), keeping the same observed value `v`.

The pure engine is `VariableFilterMap.equiv_coarsen_cell`: re-storing a constant cell under a
different (`≤`-comparable) filter is `PartialMap.equiv`-preserving — the observation `some v` is
unchanged because a constant rep is eventually `v` along *every* `NeBot` filter.  The asymmetry that
makes "coarsen" sound lives in `get?_coarsen`: a finer filter preserves whatever a coarser one
already justified, so weakening can only forget, never disagree.

We lift this to an `IProp` `|==>`.  Because the cell-rewrite is an `equiv`, the two authoritative
maps are `≡` in the heap OFE (`PartialMap.eqv_of_Equiv`), hence the two `Auth` elements are `≡`
(`Auth` is non-expansive), hence the two `auth` `IProp`s are `⊣⊢` (`iOwn` is non-expansive).  An
update between propositionally-equal resources is then immediate (`BIUpdate.intro`).  *The value
never moves; only the cell's notion of equality does* — and that is exactly what no fixed-equality
CMRA can express. -/

/-- The single-cell authoritative heap storing value `v` at `k₀` under filter `l`. -/
noncomputable def cellAuth (l : Filter ℕ) (k₀ : Nat) (v : V) : VariableFilterMap Nat V :=
  fun k => if k = k₀ then some ⟨l, fun _ => v⟩ else none

/-- **The resolution-lowering update.**  An authority observing cell `k₀` at the *finer* resolution
`l` may freely **coarsen** to `l'` (`l ≤ l'`, `l'` coarser), forgetting more while preserving the
observed value `v`.  This is a frame-preserving `|==>` with no analogue in any fixed-equality CMRA:
it updates *the cell's equality relation*, not its value.  The direction is the whole content —
`l ≤ l'` is exactly mathlib's "`l` finer, `l'` coarser", and `get?_coarsen` certifies that the
observation survives the move (forgetting more can never contradict a frame). -/
theorem coarsen (γ : GName) (k₀ : Nat) (v : V) {l l' : Filter ℕ} [l.NeBot] [l'.NeBot]
    (hmono : l ≤ l') :
    auth (F := F) (GF := GF) γ (cellAuth l k₀ v) ⊢
      |==> auth (F := F) (GF := GF) γ (cellAuth l' k₀ v) := by
  -- The cell-rewrite is `equiv`-preserving (the engine `equiv_coarsen_cell`, here read finer →
  -- coarser via `.symm`), so the two authoritative heaps are heap-OFE equivalent, the two `auth`
  -- propositions are `⊣⊢`, and the update is `BIUpdate.intro`.
  have hequiv : Std.PartialMap.equiv (M := VariableFilterMap Nat)
      (cellAuth l k₀ v) (cellAuth l' k₀ v) :=
    (equiv_coarsen_cell k₀ (l := l) (l' := l') hmono).symm
  have heqv : Auth (F := F) (V := V) (H := VariableFilterMap Nat) (own one) (cellAuth l k₀ v)
      ≡ Auth (own one) (cellAuth l' k₀ v) :=
    OFE.NonExpansive.eqv (PartialMap.eqv_of_Equiv hequiv)
  have hbi : auth (F := F) (GF := GF) γ (cellAuth l k₀ v) ⊣⊢
      auth (F := F) (GF := GF) γ (cellAuth l' k₀ v) :=
    equiv_iff.mp (OFE.NonExpansive.eqv (f := iOwn (GF := GF) (F := ResF (F := F)) γ) heqv)
  exact hbi.mp.trans BIUpdate.intro

/-! ## Theorem 3 — `agree_at_coarser`: comparable observers agree on the coarse view

Two observers store cell `k₀` under comparable filters `l₁ ≤ l₂` (so `l₂` is the coarser one) with
representative sequences `s₁`, `s₂` that are each eventually the *same* constant `v` along the
coarser `l₂`.  Then their *coarse* observations coincide: both `l₂`-germs are `some v`.  This is the
provable core of "observers at comparable resolutions agree on what the coarser one sees" — coarse
agreement is forced even though the fine observers may distinguish `s₁` from `s₂`.

Stated purely (an agreement of `eventualValue l₂`), the proof is `eventualValue_of_eventuallyEq`
applied to each rep.  The finer filter `l₁` would *also* read `some v` here (`get?_coarsen`), but
it may resolve *other* cells to more values — coarse agreement is the robust transferable
invariant. -/
theorem agree_at_coarser {s₁ s₂ : ℕ → V} {v : V} {l₁ l₂ : Filter ℕ} [l₁.NeBot] [l₂.NeBot]
    (_hmono : l₁ ≤ l₂) (h₁ : s₁ =ᶠ[l₂] (fun _ => v)) (h₂ : s₂ =ᶠ[l₂] (fun _ => v)) :
    eventualValue l₂ s₁ = eventualValue l₂ s₂ := by
  rw [eventualValue_of_eventuallyEq h₁, eventualValue_of_eventuallyEq h₂]

/-! ## Theorem 4 (doc) — a logic where the notion of equality is owned ghost state

Step back from the mechanics.  In *every* standard Iris instantiation the heap's value equivalence
is a fixed feature of the CMRA: `gmap`/`AssocList`/`ExtTreeMap` all satisfy `equiv ↔ eq`, so "the
value at `k`" is a Leibniz-fixed datum and there is exactly **one** way two heaps can agree.  You
own values; you never own *the relation those values are read modulo*.

`VariableFilterMap` makes that relation a **per-cell, monotone, transferable resource**:

* **Per-cell.**  Cell `k₁` may forget finite prefixes (`atTop`) while cell `k₂` forgets nothing
  (`pure i`) — different equalities coexisting in one heap, each owned by its cell
  (`VariableFilterMap.nonextensional_distinct_filters`).
* **Monotone.**  The only legal adjustment is *coarsening* — `coarsen` above — and it is
  frame-preserving precisely because forgetting more is one-directional: it weakens the cell's
  equality without ever inventing a disagreement a frame could detect (`get?_coarsen`).  You can
  lower your resolution; you cannot silently sharpen it past what your rep supports.
* **Transferable.**  The resolution rides inside the cell, so it is owned, framed, and split exactly
  like any other heap resource — `∗`-separated fragments carry their own resolutions.

The slogan: **a logic where the notion of equality is itself owned, adjustable ghost state.**

### Why this is the right skeleton for coupled / up-to simulations and multi-resolution monitoring

* *Up-to / coupled simulations.*  A simulation up to an equivalence `R` relates two systems modulo
  `R`; soundness of "weakening the coupling" (relating up to a *coarser* `R`) is exactly the
  requirement that coarsening forgets, never invents — our `coarsen` is that move made a
  frame-preserving resource update.  Owning the relation as state means a proof can *carry* and
  *adjust* its coupling locally, per location, rather than fixing one global bisimulation up-to.
* *Multi-resolution monitoring.*  A monitor watching a stream at resolution `l` sees the
  `l`-eventual value; a supervisory monitor at coarser `l'` sees less.  `observe_at` is a monitor's
  read at its own resolution; `agree_at_coarser` is the consistency guarantee that comparable
  monitors never contradict on the coarse view; `coarsen` is a monitor *voluntarily downgrading* its
  resolution (e.g. to save bandwidth) with a soundness certificate — its past observations remain
  valid.

None of this is expressible against a fixed-equality heap, where the equivalence is metatheory.
Here it is `iOwn`-able state, and "lower your resolution" is a theorem of the *unchanged* base
logic — `coarsen` above, proved with nothing but `equiv_coarsen_cell`, non-expansiveness, and
`BIUpdate.intro`. -/

end IrisMath.Demos.OwnedResolution
