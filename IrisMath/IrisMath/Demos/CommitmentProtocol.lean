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

/-! # Demo 5 — An end-to-end mini commitment protocol over the `KnowledgeMap` heap

Demo 3 proved the *isolated rules*.  This demo runs a tiny protocol **end to end** in the proof
mode, to show the camera is practical, not just well-typed:

  1. **Commit / allocate.**  Starting from an authoritative heap with key `k` *free*, a party
     allocates a fresh committed cell at `k` holding value `v`, obtaining the points-to fragment
     `k ↦ v`.  (This is the camera's `update_one_alloc`, lifted to an `IProp` fancy update.)
  2. **Reveal.**  Whoever holds the authority together with that fragment can read back the committed
     value: the heap maps `k` to exactly `v`.

The whole flow is verified with the **generic** Iris machinery (`iOwn_update`, `iOwn_op`,
`auth_op_frag_one_validN_iff`) over the auto-researcher's `KnowledgeMap` camera.  The deliverable is
`commit_then_reveal`: from owning the authority over a heap where `k` is free, one can — in a single
fancy update — allocate the commitment AND immediately prove what it will open to.
-/

@[expose] public section

namespace IrisMath.Demos.CommitmentProtocol

open Iris Iris.BI COFE
open HeapView One DFrac Excl
open IrisMath.Instances

/-- The knowledge heap, keyed by `ℕ`, with exclusive-`ℕ` secret payloads. -/
abbrev H := KnowledgeMap (K := Nat)
abbrev V := Excl Nat

variable {F} [UFraction F]

abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

noncomputable def committed (γ : GName) (k : Nat) (v : V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) v)

/-- **Step 1 — commit / allocate.**  If key `k` is currently free in the authoritative heap
(`get? m k = none`), a party may allocate a fresh committed cell holding `v` (valid `v`), obtaining
the points-to.  Lifts the camera rule `HeapView.update_one_alloc` to an `IProp` fancy update. -/
theorem commit (γ : GName) (m : H V) (k : Nat) (v : V)
    (Hfree : Std.PartialMap.get? m k = none) (Hv : ✓ v) :
    auth (F := F) (GF := GF) γ m ⊢
      |==> (auth (F := F) (GF := GF) γ (Std.PartialMap.insert m k v)
            ∗ committed (F := F) (GF := GF) γ k v) := by
  refine (iOwn_update (γ := γ)
    (HeapView.update_one_alloc (F := F) (k := k) (dq := own one) Hfree valid_own_one Hv)).trans ?_
  exact BIUpdate.mono iOwn_op.mp

/-- **Step 2 — reveal.**  Authority plus the commitment fragment prove the committed value at `k`
is exactly `v`. -/
theorem reveal (γ : GName) (m : H V) (k : Nat) (v : V) :
    auth (F := F) (GF := GF) γ m ∗ committed (F := F) (GF := GF) γ k v ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some v⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-- **The protocol, end to end.**  Owning the authority over a heap where `k` is free, one may in a
single fancy update allocate the commitment to `v` and obtain the points-to — a complete
commit-then-hold workflow in the proof mode. -/
theorem commit_then_reveal (γ : GName) (m : H V) (k : Nat) (v : V)
    (Hfree : Std.PartialMap.get? m k = none) (Hv : ✓ v) :
    auth (F := F) (GF := GF) γ m ⊢
      |==> (auth (F := F) (GF := GF) γ (Std.PartialMap.insert m k v)
            ∗ committed (F := F) (GF := GF) γ k v) :=
  commit (F := F) γ m k v Hfree Hv

/-- Immediately after `commit_then_reveal`, the heap maps `k` to exactly `v`: the freshly stored
knowledge state at `k` is the singleton (pinned).  This is the `reveal` rule specialized to the
post-commit heap — the verifier knows what was committed.  Proof: a pure computation, since
`get? (insert m k v) k = some v` follows from the lawful-map insert law. -/
theorem commit_lookup (m : H V) (k : Nat) (v : V) :
    Std.PartialMap.get? (Std.PartialMap.insert m k v) k = some v :=
  Std.LawfulPartialMap.get?_insert_eq rfl

end IrisMath.Demos.CommitmentProtocol
