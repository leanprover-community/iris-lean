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

/-! # Demo A — Own a limit before it converges (the germ as a semantic `▷`)

This demo builds an authoritative heap over `ConstOnFilterMap atTop` — the *GermMap* — and reads it
not as "a heap of finite values" but as **a heap of ongoing computations**.  A cell at key `k`
stores an entire *stream of approximations* `s : ℕ → V` (think: the successive outputs of an
anytime/iterative process), and the heap's observation `get? m k` returns the **`atTop`-eventual
value of `s`** — its *limit*, the value the stream settles down to.

The point a separation-logic researcher should find striking is not the heap mechanics (those are
the standard `HeapView` rules, unchanged) but the *resource* you end up holding:

> a points-to `k ↦ v` over this heap is ownership of **"the answer at infinity"** — the limit of an
> ongoing computation — **before any finite stage of the computation has produced it**.

Nothing about `k ↦ v` mentions a particular index.  The resource is the germ: the equivalence class
of the stream modulo finite (more precisely, `atTop`-small) modifications.  Because it is an honest
Iris resource, you can frame it, split it, and trade it across an arbitrary precondition `P` — you
transfer the not-yet-computed limit just like any other piece of separated state.

## The three moves

1. `own_limit` — *the points-to is a limit assertion.*  `auth ∗ k ↦ v ⊢ ⌜get? m k ≡ some v⌝`.
   Over the GermMap the right-hand side is not "the cell stores `v`" but "the cell's stream **tends
   to** `v`."  The mechanics are the generic lookup lemma; the *meaning* is convergence.

2. `stabilize` — *the limit was valid all along; stabilization just reveals it.*  If a concrete
   stream `s` is eventually constant `= v` (`s =ᶠ[atTop] const v` — a purely classical convergence
   fact), then a cell holding the raw stream `s` and a cell holding the abstract limit `const v` are
   the **same heap resource** (`equiv`).  So the abstract-limit points-to is justified directly from
   the concrete, not-yet-collapsed stream.  This is the conceptual core: the limit resource is
   present the moment the stream converges, with no operational "step to the fixed point."

3. `frame_unknown` — *trade the answer at infinity.*  `(k ↦ v) ∗ P ⊢ P ∗ (k ↦ v)`.  Trivial by
   commutativity of `∗`, and that triviality *is* the message: ownership of a limit produced by an
   ongoing process is framed exactly like any other resource, with no knowledge of any finite stage.

## The `▷`/germ relationship (theorem 4): complementary, not identical

A tempting slogan is "the filter `atTop` is the semantic shadow of `▷`."  We pin down the *precise*
relationship, which is more interesting than the slogan: the germ and the step-index are
**complementary, transverse** observations of a stream, and the germ is provably **not** subsumed by
Iris's step-indexing machinery.  First the easy half — limit facts are `▷`-stable
(`own_limit_later`, `stabilize_later`).  Then we build the step-indexed OFE the discrete cell was
hiding (`ApproxStream`, the prefix metric), show prepending a stage (`cons`) is `Contractive` — a
genuine `▷`-guard — and compute the germ of its guarded fixpoint (`germ_of_guarded_fixpoint`, the
*continuous* special case).  Step 4e pins down the *obstruction* — the standard reason limits are
not step-indexed, made precise in this OFE: the germ is **not determined by any finite prefix**
(`germ_not_determined_by_prefix`, so it is not non-expansive) and is **discontinuous on Cauchy
chains** (`germ_discontinuous`, so `compl`/`fixpoint` cannot compute it).  The genuinely
heap-specific payoff is the later-elimination dichotomy (final section): because this heap's store
OFE is *defined through the germ readout*, `▷` is eliminable from a limit cell exactly when its germ
is a discrete value.  Finally we close the loop back to the heap (`limit_from_fixpoint`).
-/

@[expose] public section

namespace IrisMath.Demos.EventualValue

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances
open scoped Filter

/-- The non-extensional heap container: `ConstOnFilterMap atTop` over `ℕ` keys — the GermMap, read
here as "a heap of streams observed at their limits." -/
abbrev H := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat

/-- Cell values: agreement on strings, so each cell carries a single agreed-upon limit value. -/
abbrev V := Agree (LeibnizO String)

variable {F} [UFraction F]

/-- The heap functor — `constOF` of the generic `HeapView` CMRA over the GermMap. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole heap of streams. -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- The limit points-to: full ownership of cell `k`, whose germ — the limit of the stored stream —
is `v`.  Read `k ↦ v` as "**cell `k`'s ongoing computation converges to `v`**." -/
noncomputable def pointsTo (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

@[inherit_doc] notation:50 k " ↦[" γ "] " v => pointsTo γ k v

/-- **Theorem 1 — `own_limit`: the points-to is a limit assertion.**

Owning the authority `m` and the limit points-to `k ↦ v` proves `get? m k ≡{0}≡ some v`.  Over the
GermMap `get? m k` is the `atTop`-eventual value of the stream stored at `k`, so this reads:

> the cell's stream of approximations **converges to `v`**.

What you own when you own `k ↦ v` is therefore the *limit*, not a stored constant: the resource
pins down where an ongoing computation lands, agreeing only up to the filter's small sets (any
finite prefix of the stream is irrelevant).  The proof is the generic `auth_op_frag_one_validN_iff`;
the heap-specific content is entirely in what `get?` means. -/
theorem own_limit (γ : GName) (m : H V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ pointsTo (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-! ## Theorem 2 — `stabilize`: the limit was valid all along

The conceptual core.  We take a cell holding a *raw stream* `s : ℕ → V` — an honest, not-yet-
collapsed sequence of approximations — and a pure convergence hypothesis `s =ᶠ[atTop] const v`
("the stream is eventually constant `= v`").  We show two things:

* a heap whose cell `k` stores the raw stream `s` and a heap whose cell `k` stores the abstract
  limit `const v` are **the same heap resource** (`equiv`), and hence
* the limit points-to is justified directly from the raw-stream heap: `auth (storing s) ∗ k ↦ v`
  already proves `get? (storing s) k ≡ some v`.

The message: convergence is not an operational *step* to a fixed point; the moment the stream
converges, the limit resource is *already present* and equal to the constant-cell resource.
Stabilization reveals what was valid all along. -/

/-- A heap that is empty except at key `k`, where it stores the given family `s : ℕ → V`. -/
noncomputable def cell (k : Nat) (s : ℕ → V) : H V :=
  fun k' => if k = k' then some s else none

/-- **The germ collapse.**  If a raw stream `s` is `atTop`-eventually the constant `v`, then storing
`s` at cell `k` is the *same heap resource* as storing the abstract limit `const v`: the two heaps
are `equiv` under the heap OFE.  This is the precise sense in which "the limit is valid before the
stream has visibly converged" — the raw-stream heap and the limit heap are interchangeable. -/
theorem cell_eqv_const (k : Nat) (s : ℕ → V) (v : V)
    (hs : s =ᶠ[Filter.atTop (α := ℕ)] (fun _ => v)) :
    (cell k s) ≡ (cell k (fun _ => v)) := by
  refine OFE.equiv_dist.mpr (fun n k' => ?_)
  change (ConstOnFilterMap.get? _ (cell k s) k') ≡{n}≡ (ConstOnFilterMap.get? _ (cell k _) k')
  by_cases hk : k = k'
  · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, cell, cell, if_pos hk, if_pos hk,
      Option.bind_some, Option.bind_some, eventualValue_congr hs, eventualValue_const]
  · rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, cell, cell, if_neg hk, if_neg hk]

/-- **Theorem 2 — `stabilize`.**  Given a concrete stream `s` that converges to `v`
(`s =ᶠ[atTop] const v`), the authority storing the *raw stream* at `k`, together with the limit
points-to `k ↦ v`, already proves the cell's observation is `v`:

> `auth (storing the raw stream s) ∗ k ↦ v ⊢ ⌜get? k ≡ some v⌝`.

We never had to "run" the stream to its fixed point or insert the constant: the proof routes through
`own_limit` after collapsing the raw-stream heap to the limit heap via `cell_eqv_const` (the heap
OFE makes them the same resource).  The limit resource was valid the moment the stream converged. -/
theorem stabilize (γ : GName) (k : Nat) (s : ℕ → V) (v : V)
    (hs : s =ᶠ[Filter.atTop (α := ℕ)] (fun _ => v)) :
    auth (F := F) (GF := GF) γ (cell k s) ∗ pointsTo (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? (cell k s) k ≡{0}≡ some v⌝ := by
  -- The germ of the raw-stream cell equals the germ of the limit cell: passing to the germ erases
  -- the difference between the stream and its limit (`eventualValue_congr`).
  have hget : Std.PartialMap.get? (cell k s) k = Std.PartialMap.get? (cell k (fun _ => v)) k := by
    change (ConstOnFilterMap.get? _ (cell k s) k) = (ConstOnFilterMap.get? _ (cell k _) k)
    rw [ConstOnFilterMap.get?, ConstOnFilterMap.get?, cell, cell, if_pos rfl, if_pos rfl,
      Option.bind_some, Option.bind_some, eventualValue_congr hs]
  rw [hget]
  -- Rewrite the authority over the raw-stream heap to the authority over the limit heap, using that
  -- the two heaps are the same resource (`cell_eqv_const`), then apply the lookup rule unchanged.
  have heqv :
      iprop(auth (F := F) (GF := GF) γ (cell k s)) ⊣⊢
        iprop(auth (F := F) (GF := GF) γ (cell k (fun _ => v))) :=
    equiv_iff.mp (OFE.NonExpansive.eqv
      (f := iOwn (GF := GF) (F := HeapF (F := F)) γ)
      (OFE.NonExpansive.eqv (f := Auth (H := H) (own one)) (cell_eqv_const k s v hs)))
  refine (sep_mono_l heqv.1).trans ?_
  exact own_limit (F := F) (GF := GF) γ (cell k (fun _ => v)) k v

/-! ## Theorem 3 — `frame_unknown`: trade the answer at infinity -/

/-- **Theorem 3 — `frame_unknown`.**  Own a limit points-to `k ↦ v` — ownership of where an ongoing
computation lands at infinity — together with an *arbitrary* other resource `P`, and you may frame
it freely:

> `(k ↦ v) ∗ P ⊢ P ∗ (k ↦ v)`.

This is trivially `∗`-commutativity, and the triviality is exactly the point.  The limit of a stream
produced by a process that **has not finished, and whose finite stages you cannot inspect**, is a
first-class separation-logic resource: you transfer it across `P` with no knowledge of any
approximation `s n`.  Anytime/iterative computation becomes ordinary framed ghost state. -/
theorem frame_unknown (γ : GName) (k : Nat) (v : V) (P : IProp GF) :
    iprop((pointsTo (F := F) (GF := GF) γ k v) ∗ P) ⊢
      iprop(P ∗ (pointsTo (F := F) (GF := GF) γ k v)) :=
  sep_comm.1

/-! ## Theorem 4 — the `▷` / Löb correspondence, mechanized

The slogan of this demo is that the value-level filter `atTop` is the *semantic shadow* of Iris's
logical `▷`.  We make that precise in three escalating steps.

### Step 4a — the easy half: limits are `▷`-stable

If, one approximation-step `▷` later, we hold the lookup evidence that cell `k`'s stream converges
to `v`, then that limit fact holds `▷` later as well.  This is just `own_limit`/`stabilize` under
`later_mono`: the logical reflection of *`atTop` is closed under "advance by one stage."* -/
theorem own_limit_later (γ : GName) (m : H V) (k : Nat) (v : V) :
    iprop(▷ (auth (F := F) (GF := GF) γ m ∗ pointsTo (F := F) (GF := GF) γ k v)) ⊢
      iprop(▷ ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝) :=
  later_mono (own_limit (F := F) (GF := GF) γ m k v)

/-- **`▷`-`stabilize`.**  The stabilization rule survives under the later modality: waiting one more
approximation does not change the limit — `▷` commutes with passing to the germ. -/
theorem stabilize_later (γ : GName) (k : Nat) (s : ℕ → V) (v : V)
    (hs : s =ᶠ[Filter.atTop (α := ℕ)] (fun _ => v)) :
    iprop(▷ (auth (F := F) (GF := GF) γ (cell k s) ∗ pointsTo (F := F) (GF := GF) γ k v)) ⊢
      iprop(▷ ⌜Std.PartialMap.get? (cell k s) k ≡{0}≡ some v⌝) :=
  later_mono (stabilize (F := F) (GF := GF) γ k s v hs)

/-! ### Step 4b — the step-indexed model: streams whose stage *is* the step index

The fragments above live in the demo's discrete `Agree` cell OFE, where the *cell-level* `▷` is
trivial.  To exhibit the deep half of the correspondence we build the OFE that discreteness was
hiding: the **prefix metric** on streams of approximations, where `dist n` compares exactly the
first `n` stages.  Here the approximation stage and Iris's step index are *literally the same
number*, so `▷` (drop one index) is "advance the stream by one stage," and `cons` (prepend a stage)
is a genuine `▷`-guard (it is `Contractive`).  In this model the germ of a guarded fixpoint is
computable (`germ_of_guarded_fixpoint`, via `fixpoint`/`fixpoint_unique`).  But the more informative
content is in Step 4e: the germ is *transverse* to the `▷`-filtration (not determined by any finite
prefix, and discontinuous on Cauchy chains), so it is **not** subsumed by `compl`/`fixpoint`.  The
relationship between `atTop` and `▷` is one of complementarity, not
identity. -/

/-- A stream of approximations, carrying the **prefix (step-indexed) OFE**: two streams are
`n`-equivalent when they agree on their first `n` stages, and equivalent (`≡`) exactly when equal.
As `n → ∞` the relation refines to equality — the canonical *non-discrete* COFE in which the
approximation stage is the step index, the structure Iris's `▷` lives on. -/
@[ext] structure ApproxStream (α : Type*) where
  /-- The `n`-th approximation the stream produces. -/
  run : ℕ → α

namespace ApproxStream
variable {α : Type*}

/-- The prefix-metric OFE: `dist n` compares the first `n` stages; `≡` is genuine equality. -/
instance instOFE : OFE (ApproxStream α) where
  Equiv s s' := s = s'
  Dist n s s' := ∀ m, m < n → s.run m = s'.run m
  dist_eqv :=
    ⟨fun _ _ _ => rfl, fun h m hm => (h m hm).symm,
      fun h₁ h₂ m hm => (h₁ m hm).trans (h₂ m hm)⟩
  equiv_dist := by
    refine ⟨fun h _ _ _ => by rw [h], fun h => ?_⟩
    ext m
    exact h (m + 1) m (Nat.lt_succ_self m)
  dist_lt h hlt k hk := h k (Nat.lt_trans hk hlt)

/-- Completeness: the limit of a Cauchy chain reads the diagonal `m ↦ (c (m+1)).run m`.  This is
exactly the colimit-over-stages that the germ computes. -/
instance instCOFE : IsCOFE (ApproxStream α) where
  compl c := ⟨fun m => (c (m + 1)).run m⟩
  conv_compl {n c} := by
    intro m hm
    have hle : m + 1 ≤ n := hm
    exact (c.cauchy hle m (Nat.lt_succ_self m)).symm

instance [Inhabited α] : Inhabited (ApproxStream α) := ⟨⟨fun _ => default⟩⟩

/-- On streams, `≡` is definitionally genuine equality (the OFE is non-discrete, but its `Equiv`
relation is `Eq`).  This bridges the OFE-level `fixpoint` lemmas back to propositional equality. -/
theorem equiv_eq {s s' : ApproxStream α} (h : s ≡ s') : s = s' := h

/-- **Prepend a stage.**  `cons a s` outputs `a` at stage `0` and defers to `s` afterwards.  This is
the stream-level **guard**: prepending an approximation is `Contractive`, the algebraic hallmark of
a `▷`-guarded map (`cons a s ≡{n+1}≡ cons a s' ↔ s ≡{n}≡ s'`, and always `≡{0}≡`). -/
def cons (a : α) (s : ApproxStream α) : ApproxStream α where
  run n := match n with | 0 => a | m + 1 => s.run m

/-- The constant stream — the canonical representative of the germ value `a`. -/
def constStream (a : α) : ApproxStream α where
  run _ := a

/-- Prepending a stage is `Contractive`: agreement on the first `n` stages of the inputs (one stage
*later*) gives agreement on the first `n` stages of the outputs.  This is the `▷`-guard. -/
instance instContractiveCons (a : α) : OFE.Contractive (cons a) where
  distLater_dist {_ _s _s'} h m hm :=
    match m, hm with
    | 0, _ => rfl
    | m + 1, hm => h (m + 1) hm m (Nat.lt_succ_self m)

/-- The constant stream is a fixed point of `cons a` (prepending `a` to `a, a, …` changes nothing).
This is the guarded recursion equation `s = cons a s`, solved on the nose by the constant stream. -/
theorem cons_constStream (a : α) : cons a (constStream a) = constStream a := by
  ext m; match m with | 0 => rfl | _ + 1 => rfl

/-- `cons a` packaged as a contractive hom, the input the `fixpoint` API expects. -/
def consHom (a : α) : ApproxStream α -c> ApproxStream α := Function.toContractiveHom (cons a)

/-- The **guarded fixpoint** of `cons a`: the unique stream `s` with `s ≡ cons a s`, produced by
Banach's contraction theorem (`fixpoint`).  Each `▷`-guard makes `cons a` a contraction, and the
fixed point is the germ of its iterates — Iris's `μ x. cons a (▷ x)`. -/
noncomputable def gfix (a : α) [Inhabited α] : ApproxStream α := fixpoint (cons a)

/-- The guarded fixpoint of `cons a` *is* the constant stream — uniqueness of contraction fixed
points (`fixpoint_unique`) pins it down, since `constStream a` already solves `s ≡ cons a s`. -/
theorem gfix_eq_constStream (a : α) [Inhabited α] : gfix a = constStream a := by
  have h : constStream a ≡ fixpoint (consHom a) :=
    fixpoint_unique (f := consHom a) (OFE.Equiv.of_eq (cons_constStream a).symm)
  exact (equiv_eq h).symm

/-- **Germ of a guarded fixpoint (the continuous special case).**

The germ (`eventualValue atTop`) of the guarded fixpoint of `cons a` is `a`.  Honest caveat: this
holds because `gfix a` *collapses* to `constStream a` (`gfix_eq_constStream`), the case where the
germ happens to be continuous — so the germ here reads off a value that is constant at every stage,
rather than extracting a genuinely infinitary limit.  The general germ is *not* a limit of
approximants; see `germ_discontinuous`.  This lemma is the well-behaved instance compatible with the
`atTop`/`▷` analogy, not the analogy itself. -/
theorem germ_of_guarded_fixpoint (a : α) [Inhabited α] :
    eventualValue (Filter.atTop (α := ℕ)) (gfix a).run = some a := by
  rw [gfix_eq_constStream]
  exact eventualValue_const a

/-- **Theorem 4 (Löb form).**  *Any* stream satisfying the guarded recursion equation `s ≡ cons a s`
has germ `a`.  Read the hypothesis as "`s`, one approximation-step later, is `a`-then-`s`"; the
conclusion extracts its limit.  This is the value-level Löb step: a fact guaranteed `▷` later at
every stage holds of the limit.  Proof: contraction fixed points are unique, so `s` is `gfix a`. -/
theorem germ_of_guarded_recursion (a : α) [Inhabited α] {s : ApproxStream α}
    (h : s ≡ cons a s) : eventualValue (Filter.atTop (α := ℕ)) s.run = some a := by
  have hs : s = gfix a := equiv_eq (fixpoint_unique (f := consHom a) h)
  rw [hs]; exact germ_of_guarded_fixpoint a

/-! ### Step 4d — general reasoning principles, and why the correspondence is *not* trivial

A skeptic will object that everything above is the textbook stream COFE plus "`germ` of a constant
is the constant," and so says nothing.  The objection is answered by isolating the two principles
the correspondence actually rests on, and by exhibiting a guarded recursion whose germ is
**`none`** — which the constant-stream reading cannot produce. -/

/-- The **germ** of a stream: its `atTop`-eventual value (`none` if the stream never settles). -/
noncomputable def germ (s : ApproxStream α) : Option α :=
  eventualValue (Filter.atTop (α := ℕ)) s.run

/-- **Principle 1 — the guard is germ-invisible (`germ` strips one `▷`).**  Prepending a stage — the
`▷`-guard `cons` — leaves the germ unchanged: `germ (cons a s) = germ s`.  So `germ` *coequalizes
the guard*: it factors through the `▷`-quotient.  This is the precise bridge between step-indexing
and the filter — a single `▷`-step is an `atTop`-small modification, and the germ is blind to those.
It is the value-level form of the move pure Iris forbids, "discard a `▷`," and it holds for the same
reason `eventualValue` is tail-invariant (`eventualValue_tail`), not by any constancy assumption. -/
theorem germ_cons (a : α) (s : ApproxStream α) : germ (cons a s) = germ s := by
  show eventualValue (Filter.atTop (α := ℕ)) (cons a s).run
      = eventualValue (Filter.atTop (α := ℕ)) s.run
  exact (eventualValue_tail (s := (cons a s).run)).symm

/-- Restatement of the headline in germ language: the germ of the guarded fixpoint of `cons a` is
`some a`.  (Definitionally `germ_of_guarded_fixpoint`.) -/
theorem germ_gfix (a : α) [Inhabited α] : germ (gfix a) = some a := germ_of_guarded_fixpoint a

/-- The **2-periodic guard** `altOp a b s = cons a (cons b s)` — two nested `▷`-guards. -/
def altOp (a b : α) (s : ApproxStream α) : ApproxStream α := cons a (cons b s)

instance instContractiveAltOp (a b : α) : OFE.Contractive (altOp a b) where
  distLater_dist h := (OFE.ne_of_contractive (cons a)).ne ((instContractiveCons b).distLater_dist h)

/-- `altOp a b` packaged as a contractive hom. -/
def altOpHom (a b : α) : ApproxStream α -c> ApproxStream α := Function.toContractiveHom (altOp a b)

/-- The guarded-recursive **oscillator**: the unique solution of `t ≡ cons a (cons b t)` — the
2-periodic stream `a, b, a, b, …`.  This is a perfectly legitimate Löb/guarded-recursive definition;
Banach's theorem produces it with *no* convergence assumption whatsoever. -/
noncomputable def altFix (a b : α) [Inhabited α] : ApproxStream α := fixpoint (altOp a b)

theorem altFix_unfold (a b : α) [Inhabited α] : altFix a b = cons a (cons b (altFix a b)) :=
  equiv_eq (fixpoint_unfold (altOpHom a b))

theorem altFix_run_zero (a b : α) [Inhabited α] : (altFix a b).run 0 = a := by
  rw [altFix_unfold]; rfl

theorem altFix_run_one (a b : α) [Inhabited α] : (altFix a b).run 1 = b := by
  rw [altFix_unfold]; rfl

theorem altFix_run_succ_succ (a b : α) [Inhabited α] (k : ℕ) :
    (altFix a b).run (k + 2) = (altFix a b).run k := by
  conv_lhs => rw [altFix_unfold]
  rfl

theorem altFix_run_double (a b : α) [Inhabited α] (j : ℕ) : (altFix a b).run (2 * j) = a := by
  induction j with
  | zero => exact altFix_run_zero a b
  | succ j ih => rw [Nat.mul_succ, altFix_run_succ_succ]; exact ih

theorem altFix_run_double_succ (a b : α) [Inhabited α] (j : ℕ) :
    (altFix a b).run (2 * j + 1) = b := by
  induction j with
  | zero => exact altFix_run_one a b
  | succ j ih =>
    rw [Nat.mul_succ, show 2 * j + 2 + 1 = (2 * j + 1) + 2 from rfl, altFix_run_succ_succ]
    exact ih

/-- **Principle 2 — the germ is a *partial* denotation of guarded recursion.**

The guarded-recursive oscillator `altFix a b = a, b, a, b, …` has **no germ** when `a ≠ b`:
`germ (altFix a b) = none`.  So the germ of a guarded fixpoint is not always "read off the guard as
a constant" — it is a limit that may fail to exist (here, the elementary fact that an alternating
sequence does not converge).  Together with `germ_gfix` (`germ (gfix a) = some a`) this exhibits
`germ` as a **partial denotation**: `some v` when the recursion converges, `none` when it
oscillates.  Modest, but it confirms the germ ↔ fixpoint map is not the trivial constant map. -/
theorem germ_altFix_none (a b : α) [Inhabited α] (hab : a ≠ b) : germ (altFix a b) = none := by
  show eventualValue (Filter.atTop (α := ℕ)) (altFix a b).run = none
  rcases h : eventualValue (Filter.atTop (α := ℕ)) (altFix a b).run with _ | v
  · rfl
  · exfalso
    have hconv : (altFix a b).run =ᶠ[Filter.atTop] (fun _ => v) := eventuallyEq_of_eventualValue h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hconv
    have ha : a = v := (altFix_run_double a b N).symm.trans (hN (2 * N) (by omega))
    have hb : b = v := (altFix_run_double_succ a b N).symm.trans (hN (2 * N + 1) (by omega))
    exact hab (ha.trans hb.symm)

/-- When `a = b` the oscillator degenerates: it is the constant stream (uniqueness of the guarded
fixpoint, since `constStream a` solves `t ≡ cons a (cons a t)`). -/
theorem altFix_diag_eq_const (a : α) [Inhabited α] : altFix a a = constStream a := by
  have hfix : altOp a a (constStream a) = constStream a := by
    show cons a (cons a (constStream a)) = constStream a
    rw [cons_constStream, cons_constStream]
  exact (equiv_eq (fixpoint_unique (f := altOpHom a a) (OFE.Equiv.of_eq hfix.symm))).symm

/-- The other half of the dichotomy: when `a = b` the oscillator's germ exists and is `some a`.
Convergent ↦ `some`, oscillating ↦ `none`. -/
theorem germ_altFix_diag (a : α) [Inhabited α] : germ (altFix a a) = some a := by
  show eventualValue (Filter.atTop (α := ℕ)) (altFix a a).run = some a
  rw [altFix_diag_eq_const]; exact eventualValue_const a

/-! ### Step 4e — the germ is *transverse* to `▷`, and not subsumed by step-indexing

The honest correspondence is sharper than "`atTop` is the shadow of `▷`."  The step-index `dist n`
and the `▷`-tower are determined by a stream's *finite prefix* and are blind to its tail; the germ
is determined by the *eventual tail* and is blind to the prefix (`germ_cons`).  They are
**complementary**, not "one phenomenon."  Two theorems make this precise and — crucially — show the
germ is genuine infinitary data that Iris's own `compl`/`fixpoint`/`▷` machinery cannot produce:

* `germ_not_determined_by_prefix` — for *every* `n`, two streams agreeing on their first `n` stages
  can have different germs.  So the germ is **not non-expansive**: no finite approximation, and no
  amount of `▷`-unfolding, pins down the eventual value.
* `germ_discontinuous` — there is a Cauchy chain whose COFE limit has germ `some a` while every term
  has germ `some b`.  The germ of the limit is **not** the limit of the germs; the germ is
  discontinuous, so `compl`/`fixpoint` (which see a chain only through its finite approximations)
  cannot compute it.

This is also the honest reading of `germ_of_guarded_fixpoint`: it succeeds only because `gfix a`
collapses to `constStream a` (the *continuous* special case); for general chains the germ is not a
limit of approximants, as `germ_discontinuous` shows. -/

/-- The germ of a constant stream is that constant. -/
theorem germ_constStream (a : α) : germ (constStream a) = some a :=
  eventualValue_const a

/-- The stream that is `a` for the first `n` stages and `b` thereafter. -/
def prefixThen (n : ℕ) (a b : α) : ApproxStream α := ⟨fun m => if m < n then a else b⟩

/-- The germ of `prefixThen n a b` is `some b`: the eventual tail is constant `b`, regardless of how
long the `a`-prefix is. -/
theorem germ_prefixThen (n : ℕ) (a b : α) : germ (prefixThen n a b) = some b := by
  show eventualValue (Filter.atTop (α := ℕ)) (prefixThen n a b).run = some b
  apply eventualValue_of_eventuallyEq
  exact Filter.eventually_atTop.mpr ⟨n, fun m hm => by
    show (if m < n then a else b) = b
    rw [if_neg (by omega)]⟩

/-- **Principle 3 — the germ is not determined by any finite prefix (`germ` is not non-expansive).**
For every `n`, the constant stream `a` and `prefixThen n a b` agree on their first `n` stages, yet
(for `a ≠ b`) have different germs.  Hence no finite approximation — equivalently, no finite amount
of `▷`-unfolding — determines the eventual value.  The germ is *transverse* to the entire
step-index filtration: it reads exactly the data `dist n` discards. -/
theorem germ_not_determined_by_prefix (n : ℕ) (a b : α) (hab : a ≠ b) :
    constStream a ≡{n}≡ prefixThen n a b ∧ germ (constStream a) ≠ germ (prefixThen n a b) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · show a = (if m < n then a else b)
    rw [if_pos hm]
  · rw [germ_constStream, germ_prefixThen]
    exact fun h => hab (Option.some.inj h)

/-- The Cauchy chain `k ↦ prefixThen k a b` (longer and longer `a`-prefixes, then `b`).  Successive
terms agree on ever-longer prefixes, so it converges in the COFE — to `constStream a`. -/
def discChain (a b : α) : Chain (ApproxStream α) where
  chain k := prefixThen k a b
  cauchy {n i} h := fun m hm => by
    show (if m < i then a else b) = (if m < n then a else b)
    rw [if_pos (by omega), if_pos hm]

/-- The COFE limit of `discChain a b` is the constant stream `a`: the diagonal `m ↦ (c (m+1)) m`
sits inside every prefix, so it is `a` everywhere. -/
theorem discChain_compl (a b : α) : COFE.compl (discChain a b) = constStream a := by
  ext m
  show (if m < m + 1 then a else b) = a
  rw [if_pos (Nat.lt_succ_self m)]

/-- **Principle 4 — the germ is discontinuous; `compl`/`fixpoint` cannot compute it.**

The chain `discChain a b` is Cauchy with COFE limit `constStream a` (germ `some a`), yet *every*
term has germ `some b`.  So for `a ≠ b`, `germ (compl c) = some a ≠ some b = germ (c k)` for every
`k`: **the germ of the limit is not the limit of the germs.**  The germ is thus not a continuous
functional of the stream OFE, hence cannot be obtained from `COFE.compl` or Iris's `fixpoint` —
which access a chain only through its finite (`dist n`) approximations.  This pins down precisely
what the filter germ adds over step-indexing: a genuinely infinitary observation `▷` cannot make. -/
theorem germ_discontinuous (a b : α) (hab : a ≠ b) (k : ℕ) :
    germ (COFE.compl (discChain a b)) ≠ germ (discChain a b k) := by
  rw [discChain_compl, germ_constStream]
  show some a ≠ germ (prefixThen k a b)
  rw [germ_prefixThen]
  exact fun h => hab (Option.some.inj h)

end ApproxStream

/-! ### Step 4c — back to the heap: a points-to justified by a guarded fixpoint

We close the loop: store the guarded-fixpoint stream `gfix v` in cell `k`.  Its germ is `v`
(`germ_of_guarded_fixpoint`), so the heap observes the cell as exactly `v`, and the limit points-to
`k ↦ v` is justified — by a value the heap obtained through *guarded recursion alone*, with no
finite stage having stored `v`. -/

/-- `V` is inhabited (some agreed string), so guarded fixpoints over `V` exist. -/
instance : Inhabited V := ⟨toAgree ⟨""⟩⟩

/-- **The germ of the guarded-fixpoint cell is `v`.**  Storing `gfix v` at `k`, the heap's
observation `get?` returns exactly `some v` — the cell's value is the limit of a guarded recursion,
not a stored constant. -/
theorem fixpoint_cell_get (k : Nat) (v : V) :
    Std.PartialMap.get? (cell k (ApproxStream.gfix v).run) k = some v := by
  change ConstOnFilterMap.get? _ (cell k (ApproxStream.gfix v).run) k = some v
  rw [ConstOnFilterMap.get?, cell, if_pos rfl, Option.bind_some]
  exact ApproxStream.germ_of_guarded_fixpoint v

/-- **Theorem 4 (capstone) — own a limit defined by guarded recursion.**  The authority storing the
guarded-fixpoint stream `gfix v` at `k`, together with the limit points-to `k ↦ v`, proves the
cell's observation is `v`.  The stored stream is Iris's `μ x. cons v (▷ x)`: the points-to thus owns
"the answer at infinity" of a genuinely guarded computation.  The ownership half is `own_limit`
verbatim; that the observed limit *equals* `v` is `fixpoint_cell_get`, i.e. the germ ⟷ guarded
fixpoint theorem. -/
theorem limit_from_fixpoint (γ : GName) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ (cell k (ApproxStream.gfix v).run) ∗
        pointsTo (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? (cell k (ApproxStream.gfix v).run) k ≡{0}≡ some v⌝ :=
  own_limit (F := F) (GF := GF) γ (cell k (ApproxStream.gfix v).run) k v

/-! ## Later-elimination from a limit cell — *exactly* when the germ has stabilized

A natural question: can `▷` be **freely eliminated** from ownership of a limit cell, i.e. is limit
ownership `Timeless`?  The honest answer pinpoints what the germ does and does not buy.

The store OFE on the germ heap is defined *through the germ readout* (`Iris.Heap.instOFE`):
`m ≡{n}≡ m'  ⟺  ∀ k, get? m k ≡{n}≡ get? m' k` in `Option V`.  So the heap's step-indexing **is**
the germ observation's step-indexing, and the later is eliminable from a limit cell `k ↦ v` *exactly
when* the germ value `v` is a discrete OFE element (`DiscreteE v`) — i.e. when the limit has
**stabilized** to a step-independent value.

* If the value space `V` is a *discrete* OFE (as in this demo's `Agree (LeibnizO String)`), every
  germ is discrete, so limit ownership is unconditionally timeless and `▷` strips freely — but only
  because `V` is discrete; the filter/germ adds nothing here.  This is the degenerate case.
* For a *genuinely step-indexed* value space, the heap is non-discrete and `▷` is **not** freely
  eliminable in general: it strips only at cells whose germ is discrete.  The germ structure
  *localizes* timelessness to the stabilized cells. -/

namespace LaterElim
open Iris.OFE

/-- **The limit observation `k ↦ v` is later-eliminable iff the germ value is discrete.**
`some v` (the cell's germ readout) is discrete in `Option V` iff `v` is discrete in `V`. -/
theorem obs_discreteE_iff {α : Type _} [OFE α] (v : α) :
    DiscreteE (some v : Option α) ↔ DiscreteE v := by
  refine ⟨fun h => ⟨fun {y} hy => ?_⟩, fun h => Option.some_is_discrete h⟩
  exact equiv_dist.mpr fun n =>
    some_dist_some.mp ((h.discrete (some_dist_some.mpr hy)).dist)

/-- **The actual later-elimination.**  When the germ value `v` is discrete, the step-`0` observation
— what survives after a `▷` is stripped — already determines the full observation: any `o ≡{0}≡
some v` satisfies `o ≡ some v`.  This is precisely "`▷` freely eliminated from the limit cell." -/
theorem obs_later_strip {α : Type _} [OFE α] (v : α) [DiscreteE (some v : Option α)]
    {o : Option α} (h : o ≡{0}≡ some v) : o ≡ some v :=
  (DiscreteE.discrete h.symm).symm

/-! ### A genuinely step-indexed germ heap where `▷` is *not* freely eliminable

We instantiate the germ container at the non-discrete value OFE `Later (LeibnizO ℕ)` (Iris's `▷`
type former).  The resulting heap is genuinely step-indexed; we exhibit a limit cell from which the
later cannot be stripped. -/

/-- A non-discrete value OFE: `Later (LeibnizO ℕ)` — `next x ≡{0}≡ next y` always, but `next 0 ≢
next 1`.  No element is discrete. -/
abbrev WL := Later (LeibnizO ℕ)

/-- The germ heap over the non-discrete value space `WL`; genuinely step-indexed. -/
abbrev LHeap := ConstOnFilterMap (Filter.atTop (α := ℕ)) Nat WL

/-- A one-cell limit heap storing the constant sequence `fun _ => v` at key `0`. -/
def latHeap (v : WL) : LHeap := fun k' => if k' = 0 then some (fun _ => v) else none

/-- The cell's germ observation is exactly `v`. -/
theorem latHeap_obs (v : WL) : Std.PartialMap.get? (latHeap v) 0 = some v := by
  change ConstOnFilterMap.get? _ (latHeap v) 0 = some v
  rw [ConstOnFilterMap.get?, latHeap, if_pos rfl, Option.bind_some]
  exact eventualValue_const v

/-- **The germ heap is non-discrete: `▷` is not freely eliminable from a limit cell.**  The two
limit heaps storing `next 0` and `next 1` agree at step `0` (after a `▷` is stripped) — their germ
observations are `0`-equal — yet they are not equivalent.  So owning "the limit at cell `0`" up to
one `▷` does *not* pin the limit: the later genuinely cannot be discarded for a non-stabilized
(non-discrete) germ.  Contrast `obs_later_strip`, which strips the later exactly when the germ is
discrete. -/
theorem latHeap_later_not_eliminable :
    (latHeap (Later.next ⟨0⟩) ≡{0}≡ latHeap (Later.next ⟨1⟩)) ∧
      ¬ (latHeap (Later.next ⟨0⟩) ≡ latHeap (Later.next ⟨1⟩)) := by
  refine ⟨fun k' => ?_, fun h => ?_⟩
  · rcases eq_or_ne k' 0 with hk | hk
    · subst hk
      rw [latHeap_obs, latHeap_obs]
      exact some_dist_some.mpr (fun m hm => by omega)
    · show ConstOnFilterMap.get? _ (latHeap (Later.next ⟨0⟩)) k'
          ≡{0}≡ ConstOnFilterMap.get? _ (latHeap (Later.next ⟨1⟩)) k'
      simp [ConstOnFilterMap.get?, latHeap, hk]
  · have h0 : Std.PartialMap.get? (latHeap (Later.next ⟨0⟩)) 0
        ≡ Std.PartialMap.get? (latHeap (Later.next ⟨1⟩)) 0 :=
      NonExpansive.eqv (f := fun m : LHeap => Std.PartialMap.get? m 0) h
    rw [latHeap_obs, latHeap_obs] at h0
    have hnext : (Later.next ⟨0⟩ : WL) ≡ Later.next ⟨1⟩ :=
      equiv_dist.mpr fun n => some_dist_some.mp h0.dist
    have hcar : (LeibnizO.mk 0 : LeibnizO ℕ) ≡ LeibnizO.mk 1 := hnext
    exact absurd (congrArg LeibnizO.car hcar) (by decide)

end LaterElim

end IrisMath.Demos.EventualValue
