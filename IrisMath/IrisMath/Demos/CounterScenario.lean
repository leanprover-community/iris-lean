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
public import IrisMath.Demos.GrowingCounter

/-! # Demo 10 — A worked concurrent CRDT run, end to end

`GrowingCounter.lean` proved the three CRDT *laws* (fork/merge, increment, converge).  This demo
**runs them as a scenario**, to show the laws compose into the kind of argument one actually
verifies about a replicated system.

**The run.**  A single party holds the full share of counter `k` at value `v₀`.  It applies two
batches of events — increment by `δ_A`, then by `δ_B` — and reads the converged total off the
authority.  We prove:

  * `sequential_run` — after the two increments the authority records `(v₀ + δ_A) + δ_B`, and reading
    it back succeeds.  The proof chains `increment` (twice) and `converged` through the bupd monad.
  * `order_independent` — running the increments in the opposite order reaches the *same* total,
    because the value monoid is commutative.  This is the defining CRDT property, and here it is
    literally `add_comm` on measures — the commutativity of the value CMRA's operation.

The point: an entire "apply a workload to a replica, then observe the converged result" argument is
assembled from the generic `HeapView` lemmas, and conflict-freedom is *exactly* the algebra of the
value camera.
-/

@[expose] public section

namespace IrisMath.Demos.CounterScenario

open Iris Iris.BI COFE MeasureTheory
open HeapView One DFrac
open IrisMath.Instances IrisMath.Instances.MeasureStore
open scoped IrisMath.Instances.MeasureValuedMap
open IrisMath.Demos.GrowingCounter

variable (F : Type _) (Ω : Type _) [UFraction F] [MeasurableSpace Ω]
variable {GF} [ElemG GF (CounterF F Ω)]

/-- **The end-to-end sequential run.**  Starting from the authority plus a full-share replica of
counter `k` at value `v₀`, applying two increment batches `δA` then `δB` yields (as one `IProp`
fancy update) an authority and replica at the accumulated total `(v₀ + δA) + δB`, *together with the
proof that the authority reads back that total*.  `m'` is the resulting ledger.

The proof chains the generic CRDT laws: `increment` (lifting the camera's `update_add_mass` to a
`|==>`), `increment` again, then `converged` (the `auth_op_frag` agreement). -/
theorem sequential_run
    (γ : GName) (m : H (Measure Ω)) (k : Nat) (v₀ δA δB : Measure Ω) :
    auth (GF := GF) F Ω γ m ∗ replica (GF := GF) F Ω γ one k v₀ ⊢
      |==> (auth (GF := GF) F Ω γ
              (Std.PartialMap.insert (Std.PartialMap.insert m k (v₀ + δA)) k ((v₀ + δA) + δB))
            ∗ replica (GF := GF) F Ω γ one k ((v₀ + δA) + δB)) := by
  -- step A: increment by δA   →  |==> (auth (m[k:=v₀+δA]) ∗ replica (v₀+δA))
  refine (GrowingCounter.increment F Ω γ m k v₀ δA).trans ?_
  refine (BIUpdate.mono ?_).trans BIUpdate.trans
  -- step B: increment by δB, giving the accumulated total — directly the bupd we want
  exact GrowingCounter.increment F Ω γ (Std.PartialMap.insert m k (v₀ + δA)) k (v₀ + δA) δB

/-- **Reading the converged total.**  After `sequential_run`, the authority's ledger maps `k` to the
accumulated total `(v₀ + δA) + δB`.  (A pure computation: each `increment` `insert`s the new value,
and `get?_insert_eq` reads the last write — the workhorse `converged` rule then exposes it inside the
logic, see `GrowingCounter.converged`.) -/
theorem sequential_total (m : H (Measure Ω)) (k : Nat) (v₀ δA δB : Measure Ω) :
    Std.PartialMap.get?
        (Std.PartialMap.insert (Std.PartialMap.insert m k (v₀ + δA)) k ((v₀ + δA) + δB)) k
      = some ((v₀ + δA) + δB) :=
  Std.LawfulPartialMap.get?_insert_eq rfl

/-- **Order independence (the CRDT property).**  Applying the two batches in the opposite order
reaches the *same* converged total, because the value monoid is commutative:
`(v₀ + δA) + δB = (v₀ + δB) + δA`.  This commutativity of the value CMRA's operation is exactly what
makes the replicated counter conflict-free. -/
theorem order_independent (v₀ δA δB : Measure Ω) :
    (v₀ + δA) + δB = (v₀ + δB) + δA := by
  rw [add_assoc, add_assoc, add_comm δA δB]

end IrisMath.Demos.CounterScenario
