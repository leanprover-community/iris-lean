/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Algebra
public import IrisMath.Instances.MeasureValuedMap

/-! # Demo — A grow-only counter / accumulator CRDT, *not* a memory heap

The generic Iris `HeapView` resource algebra is usually presented as a *memory heap*: keys are
locations, values are opaque cell contents, and `Frag k dq v` is a points-to.  This demo uses the
*very same* `HeapView` for a completely different purpose — **distributed-systems / CRDT
reasoning** — with no change to `HeapView`, `iOwn`, `Auth`, or the proof mode.

**The system.**  A **grow-only counter** (a G-Counter CRDT, or a concurrent accumulator/histogram).
A single logical counter at "region" `k` is shared by `N` *replicas*.  Each replica owns a
**fractional share** of the counter and a *local contribution* to its value.  Replicas run
independently; periodically they **merge**.  The merge must be commutative, associative, and
idempotent-free-of-conflict — exactly a conflict-free replicated data type.

We model this with `HeapView F Nat (Measure Ω) (Nat → Option ·)` — the heap whose value CMRA is the
additive commutative monoid of measures `(Measure Ω, +, 0)`:

* `Auth (own one) m`  — the **authority**: the converged global value of every counter `k`.
* `Frag k (own q) v`  — a **replica**: a fractional share `q` of counter `k`, carrying that
  replica's local contribution `v`.

The dictionary "memory heap → CRDT":

| `HeapView` notion        | CRDT meaning                                                 |
|--------------------------|--------------------------------------------------------------|
| value CMRA op `•` (`+`)  | the **merge** of two replicas' contributions (commutative)   |
| `Frag` fraction `q`      | a replica's **share** of the counter                         |
| `frag_add_op_equiv`      | **fork** one replica into two / **merge** two into one        |
| `update_add_mass`        | a replica **increments** its own contribution                |
| `auth … • frag (own 1)…` | the **converged** global value once all shares are reunited  |

The mathematics — `+` is commutative and associative, and *every* value is valid — is precisely what
makes concurrent merge a **frame-preserving, conflict-free** update.  Iris's separation conjunction
then gives **replica-local reasoning for free**: each `∗`-separated `Frag` is an independent
replica, mergeable in any order.

We prove the three laws of this CRDT logic:

1. **Split / fork & merge** (`split`, `merge`, `fork_iff`): a replica `q₁+q₂` carrying `v₁•v₂`
   `⊣⊢` two independent replicas `q₁ ↦ v₁` and `q₂ ↦ v₂`.  This is `HeapView.frag_add_op_equiv`
   — the heart of the demo.
2. **Local increment** (`increment`): a replica may bump its own contribution by `δ`, an `IProp`
   `|==>` update, via the proven camera update `MeasureStore.update_add_mass`.
3. **Global convergence / read** (`converged`): when one party holds the *full* share `own one` of
   counter `k`, the authority's recorded value equals that replica's value — the system has
   converged.  This is `HeapView.auth_op_frag_one_validN_iff`.
-/

@[expose] public section

namespace IrisMath.Demos.GrowingCounter

open Iris Iris.BI COFE MeasureTheory
open HeapView One DFrac
open IrisMath.Instances IrisMath.Instances.MeasureStore
open scoped IrisMath.Instances.MeasureValuedMap

-- A fixed measurable space of "increments", and a fraction type for replica shares.
variable (F : Type _) (Ω : Type _) [UFraction F] [MeasurableSpace Ω]

/-- The counter store: the plain function store keyed by counter id, with **measure values** as the
commutative-monoid payload (`+` is the CRDT merge). -/
abbrev H := (Nat → Option ·)

/-- The CRDT functor: `constOF` of the generic `HeapView` CMRA over the measure-valued store.  The
*identical* construction `Iris/Examples/IProp.lean` uses for a memory heap. -/
abbrev CounterF : COFE.OFunctorPre := constOF <| HeapView F Nat (Measure Ω) H

variable {GF} [ElemG GF (CounterF F Ω)]

/-- **The authority.**  Ownership of the converged global value of every counter. -/
noncomputable def auth (γ : GName) (m : H (Measure Ω)) : IProp GF :=
  iOwn (GF := GF) (F := CounterF F Ω) γ (Auth (own one) m)

/-- **A replica.**  Owning a fractional share `q` of counter `k`, holding this replica's local
contribution `v`.  The full share `q = one` is a counter with no other live replicas. -/
noncomputable def replica (γ : GName) (q : F) (k : Nat) (v : Measure Ω) : IProp GF :=
  iOwn (GF := GF) (F := CounterF F Ω) γ (Frag k (own q) v)

/-! ## Law 1 — Fork & merge a replica (the CRDT split lemma)

`HeapView.frag_add_op_equiv` says `Frag k (own (q₁+q₂)) (v₁•v₂) ≡ Frag k (own q₁) v₁ • Frag k (own
q₂) v₂`.  Under `iOwn` (which is non-expansive) this `≡` becomes a proof-mode `⊣⊢`, and `iOwn_op`
turns the camera `•` into a separating conjunction `∗`.  The result is the conflict-free
fork/merge rule of the CRDT: a single replica owning share `q₁+q₂` with merged contribution `v₁•v₂`
is *the same resource* as two independent replicas, and conversely two replicas merge into one. -/

/-- A replica's fragment, after forking, equals the `•` of the two child fragments — the pure
camera fact `frag_add_op_equiv` lifted under `iOwn`. -/
theorem replica_fork_eqv (γ : GName) (q1 q2 : F) (k : Nat) (v1 v2 : Measure Ω) :
    replica (GF := GF) F Ω γ (q1 + q2) k (v1 + v2) ⊣⊢
      iOwn (GF := GF) (F := CounterF F Ω) γ
        (Frag k (own q1) v1 • Frag k (own q2) v2) :=
  equiv_iff.mp (OFE.NonExpansive.eqv (f := iOwn (GF := GF) (F := CounterF F Ω) γ)
    HeapView.frag_add_op_equiv)

/-- **Fork / merge (the iff).**  A replica with share `q₁+q₂` carrying the merged contribution
`v₁ • v₂` is *exactly* two independent replicas: share `q₁` with `v₁`, and share `q₂` with `v₂`.
Read left-to-right it **forks** a replica; right-to-left it **merges** two replicas — and because
`•` (`+` on measures) is commutative and associative, the merge is order-independent and
conflict-free. -/
theorem fork_iff (γ : GName) (q1 q2 : F) (k : Nat) (v1 v2 : Measure Ω) :
    replica (GF := GF) F Ω γ (q1 + q2) k (v1 + v2) ⊣⊢
      replica (GF := GF) F Ω γ q1 k v1 ∗ replica (GF := GF) F Ω γ q2 k v2 :=
  (replica_fork_eqv F Ω γ q1 q2 k v1 v2).trans iOwn_op

/-- **Fork (split).**  The forward direction: split one replica into two that can run independently.
Each `∗`-conjunct is a self-contained replica, by separation logic. -/
theorem split (γ : GName) (q1 q2 : F) (k : Nat) (v1 v2 : Measure Ω) :
    replica (GF := GF) F Ω γ (q1 + q2) k (v1 + v2) ⊢
      replica (GF := GF) F Ω γ q1 k v1 ∗ replica (GF := GF) F Ω γ q2 k v2 :=
  (fork_iff F Ω γ q1 q2 k v1 v2).mp

/-- **Merge (join).**  The backward direction: two independent replicas of the same counter merge
into a single replica whose share is `q₁+q₂` and whose contribution is the *merged* `v₁ • v₂`.  This
is the CRDT's commutative join. -/
theorem merge (γ : GName) (q1 q2 : F) (k : Nat) (v1 v2 : Measure Ω) :
    replica (GF := GF) F Ω γ q1 k v1 ∗ replica (GF := GF) F Ω γ q2 k v2 ⊢
      replica (GF := GF) F Ω γ (q1 + q2) k (v1 + v2) :=
  (fork_iff F Ω γ q1 q2 k v1 v2).mpr

/-! ## Law 2 — A replica increments its own contribution

A replica holding the *full* share of counter `k` (currently `v`) may locally **increment** its
contribution by an increment `δ` (a fresh batch of measure / events), atomically updating both the
authority's record and its own fragment to the merged value `v + δ`.  Because the value monoid is
commutative and every value is valid, this is a frame-preserving `~~>` — lifted here to an `IProp`
fancy update `|==>` via `iOwn_update`.  Iterating yields `v + δ₁ + δ₂ + …`: contributions only ever
grow and never conflict — a genuine **grow-only counter**. -/

theorem increment (γ : GName) (m : H (Measure Ω)) (k : Nat) (v δ : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ replica (GF := GF) F Ω γ one k v ⊢
      |==> (auth (GF := GF) F Ω γ (Std.PartialMap.insert m k (v + δ))
            ∗ replica (GF := GF) F Ω γ one k (v + δ)) := by
  refine iOwn_op.mpr.trans ?_
  refine (iOwn_update (γ := γ)
    (MeasureStore.update_add_mass (F := F) (H := H) m k v δ)).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-! ## Law 3 — Global convergence / read

When a single party holds the **full** share `own one` of counter `k`, no other replica is live, so
the authority's recorded value *is* that replica's value: the system has converged at `k`.  This is
the generic `HeapView.auth_op_frag_one_validN_iff`, exposing — at step index `0` — that the
authoritative map's entry at `k` equals the replica's contribution. -/

theorem converged (γ : GName) (m : H (Measure Ω)) (k : Nat) (v : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ replica (GF := GF) F Ω γ one k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (HeapView.auth_op_frag_one_validN_iff.mp H).2.2

/-! ## The point

Every theorem above is an *ordinary* `HeapView`/`iOwn` fact — `frag_add_op_equiv`, `iOwn_op`,
`iOwn_update`, `auth_op_frag_one_validN_iff` — with **no new metatheory**.  What turns the
memory-heap into a **CRDT** is entirely the choice of value CMRA: the commutative measure monoid.

* Its operation `•` is the **merge**, so `frag_add_op_equiv` is the conflict-free fork/merge of
  replicas — commutativity and associativity make the merge order-independent.
* **Every value is valid**, so a replica may always increment without a stuck validity side
  condition: the counter is genuinely *grow-only*.
* When the shares reunite at `own one`, validity of `Auth • Frag` *forces* the authority to equal
  the merged value — **convergence** is just camera validity.

An Iris researcher therefore gets, for free, a verified CRDT logic — replica-local, conflict-free,
convergent — out of the generic heap resource algebra, with no notion of "memory" in sight. -/

end IrisMath.Demos.GrowingCounter
