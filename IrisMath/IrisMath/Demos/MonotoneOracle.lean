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

/-! # Demo — A monotone knowledge oracle / persistent lower-bound token (NOT a memory heap)

The previous `KnowledgeMap` demos use the generic Iris `HeapView` as a *heap*: cells that own
values and may be allocated, read, and overwritten.  This demo uses the **same** `HeapView`
machinery for something that is emphatically **not** a memory cell.

**The object.**  A *monotone knowledge oracle*: an abstract answer that an oracle has fixed once and
discloses lazily.  Once a key's value is *revealed* it never changes and never expires — and the
disclosed knowledge can be freely *shared* among arbitrarily many parties.  This is a
**persistent lower-bound knowledge token**: "I have learned that the value at `k` is `v`, this
knowledge is permanent, and anyone I tell also holds it permanently."  There is **no program heap**:
this is purely logical ghost state, useful for prophecy-like reasoning, contextual refinement, and
commit-reveal protocols.

**Why `KnowledgeMap` and not a `gmap`.**  The `KnowledgeMap` camera is genuinely *non-extensional*:
`get? m k = none` does not mean "absent" — it means **committed but not yet pinned** (the candidate
set has not collapsed to a singleton).  So the oracle can have *fixed* a key while its observation
is still `none`, and only later refine it to a singleton (`some v`).  That is exactly the "answer
committed, disclosed lazily" semantics a fixed `gmap` value cannot express.

**Why `Agree`-valued and `.discard`-fractioned.**  To make knowledge *permanent and shareable* we
need the resource to be a `CoreId` (duplicable) claim:

  * The fraction is `DFrac.discard` — a *persistent* claim, `CoreId .discard`.
  * The payload is `Agree (LeibnizO Nat)` — `toAgree a` is `CoreId`, and two `toAgree` fragments are
    compatible **iff they agree**, giving consistency for free.

Together, `Frag k .discard (toAgree v)` is a `CoreId` `HeapView` fragment, so `iOwn` of it is a
`Persistent` IProp: a *never-expiring, freely-copyable* knowledge token.

We prove the three rules of this "knowledge logic":

  1. **Knowledge implies determination** — holding the authority and a (full-fraction) token at `k`
     proves the oracle's value there is exactly `v`.
  2. **Knowledge is persistent / shareable** — a full token can be made `.discard` (permanent), and
     the resulting persistent token is *duplicable*: `tok ⊢ tok ∗ tok`.  Two parties can both hold
     "I know the value at `k` is `v`".
  3. **Consistency** — two tokens at the same key are compatible only if their values agree; an
     oracle never discloses two different answers.
-/

@[expose] public section

namespace IrisMath.Demos.MonotoneOracle

open Iris Iris.BI COFE
open HeapView One DFrac Agree LeibnizO
open IrisMath.Instances

/-- The knowledge container: `KnowledgeMap` over `ℕ` keys.  A cell holds a *set of candidate
values*; `get? m k = some v` iff that set has collapsed to the singleton `{v}` (the oracle has
*pinned* the answer at `k`), and `none` while the answer is *committed but not yet disclosed*. -/
abbrev H := KnowledgeMap (K := Nat)

/-- The oracle's disclosed answers are `Agree`-valued: `toAgree v` is a `CoreId` (duplicable) claim,
and two such claims are compatible *iff they agree* — exactly "an oracle commits to one answer." -/
abbrev V := Agree (LeibnizO Nat)

variable {F} [UFraction F]

/-- The functor — `constOF` of the generic `HeapView` CMRA over the knowledge container. -/
abbrev HeapF : COFE.OFunctorPre := constOF <| HeapView F Nat V H

variable {GF} [ElemG GF (HeapF (F := F))]

/-- Authoritative ownership of the whole oracle: the map `m : H V` records, at each key, the
oracle's *knowledge state* about its answer there (a `Set V`).  A key whose state is not yet a
singleton is "committed but undisclosed". -/
noncomputable def auth (γ : GName) (m : H V) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Auth (own one) m)

/-- A *full-fraction* disclosed token: "I exclusively know the oracle's answer at `k` is `v`." -/
noncomputable def revealed (γ : GName) (k : Nat) (n : Nat) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k (own one) (toAgree ⟨n⟩))

/-- A *persistent* disclosed token: the same knowledge, but with the `.discard` fraction — a
permanent, freely-copyable claim "the oracle's answer at `k` is `v`, and this never expires." -/
noncomputable def persistent_revealed (γ : GName) (k : Nat) (n : Nat) : IProp GF :=
  iOwn (GF := GF) (F := HeapF (F := F)) γ (Frag k .discard (toAgree ⟨n⟩))

/-! ## Theorem 1 — Knowledge implies determination -/

/-- **Knowledge implies determination.**  Holding the authority over the oracle `m` together with a
full-fraction disclosed token `revealed γ k n` proves the oracle's value at `k` is exactly
`toAgree ⟨n⟩`: the knowledge state at `k` has collapsed to the pinned singleton.  In oracle terms:
*possessing the disclosed answer proves what the oracle committed to.*  The proof is the generic
Iris lemma `auth_op_frag_one_validN_iff`. -/
theorem determines (γ : GName) (m : H V) (k : Nat) (n : Nat) :
    auth (F := F) (GF := GF) γ m ∗ revealed (F := F) (GF := GF) γ k n ⊢
      ⌜Std.PartialMap.get? m k ≡{0}≡ some (toAgree ⟨n⟩ : V)⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (auth_op_frag_one_validN_iff.mp H).2.2

/-! ## Theorem 2 — Knowledge is persistent and shareable -/

/-- **Make knowledge permanent.**  A full-fraction token can be turned into a *persistent*
(`.discard`-fractioned) token by a single fancy update — the camera rule `update_frag_discard`
lifted to `|==>`.  After this step the knowledge can never be reclaimed; it has become a permanent
fact of the ghost state. -/
theorem make_persistent (γ : GName) (k : Nat) (n : Nat) :
    revealed (F := F) (GF := GF) γ k n ⊢
      |==> persistent_revealed (F := F) (GF := GF) γ k n :=
  iOwn_update (γ := γ) (HeapView.update_frag_discard (F := F) (k := k) (dq := own one)
    (v1 := (toAgree ⟨n⟩ : V)))

/-- The persistent disclosed token is a `Persistent` IProp: `Frag k .discard (toAgree ⟨n⟩)` is a
`CoreId` `HeapView` fragment (both its fraction `.discard` and its payload `toAgree ⟨n⟩` are
`CoreId`), so `iOwn` of it is persistent. -/
instance persistent_revealed_persistent (γ : GName) (k : Nat) (n : Nat) :
    BI.Persistent (persistent_revealed (F := F) (GF := GF) γ k n) := by
  unfold persistent_revealed
  infer_instance

/-- **Knowledge is shareable (the heart of the demo).**  The persistent token is *duplicable*: from
one token one obtains two, so two independent parties can both hold "I know the oracle's answer at
`k` is `v`".  This is the defining feature of disclosed knowledge — once public, it is freely
copyable — and it follows purely from `CoreId (Frag k .discard (toAgree v))`, i.e. from the token
being a persistent IProp. -/
theorem shareable (γ : GName) (k : Nat) (n : Nat) :
    persistent_revealed (F := F) (GF := GF) γ k n ⊢
      persistent_revealed (F := F) (GF := GF) γ k n ∗
        persistent_revealed (F := F) (GF := GF) γ k n := by
  iintro #Htok
  isplit
  · iexact Htok
  · iexact Htok

/-! ## Theorem 3 — Consistency -/

/-- **Consistency.**  Two disclosed tokens at the *same* key are compatible only if their values
agree: the composite value `toAgree ⟨n⟩ • toAgree ⟨m⟩` must be valid, which for `Agree` forces
`n = m`.  An oracle never discloses two different answers.  Proof: the generic `frag_op_validN_iff`
extracts validity of the combined payload. -/
theorem consistent (γ : GName) (k : Nat) (n m : Nat) :
    persistent_revealed (F := F) (GF := GF) γ k n ∗
        persistent_revealed (F := F) (GF := GF) γ k m ⊢
      ⌜✓{0} ((toAgree ⟨n⟩ : V) • (toAgree ⟨m⟩ : V))⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  exact (frag_op_validN_iff.mp H).2

/-- **Consistency, sharpened: an oracle discloses at most one answer.**  From the compatibility of
two same-key tokens we extract the *concrete* equality `n = m`: distinct disclosed answers are
contradictory.  This uses that valid `Agree` composition forces equality of the underlying
(Leibniz) values. -/
theorem consistent_eq (γ : GName) (k : Nat) (n m : Nat) :
    persistent_revealed (F := F) (GF := GF) γ k n ∗
        persistent_revealed (F := F) (GF := GF) γ k m ⊢
      ⌜n = m⌝ := by
  refine iOwn_op.mpr.trans ?_
  refine iOwn_cmraValid.trans ?_
  refine (internalCmraValid_elim _).trans ?_
  iintro %H
  ipure_intro
  have hv : ✓{0} ((toAgree ⟨n⟩ : V) • (toAgree ⟨m⟩ : V)) := (frag_op_validN_iff.mp H).2
  have hd : (⟨n⟩ : LeibnizO Nat) ≡{0}≡ (⟨m⟩ : LeibnizO Nat) :=
    toAgree_op_validN_iff_dist.mp hv
  have he := dist_inj hd
  grind

/-! ## The point

`determines`, `shareable`, and `consistent`/`consistent_eq` are the rules of a *knowledge logic*,
and every one is proved by the **generic** Iris `HeapView`/`iOwn` machinery — no new metatheory.
What makes this a genuinely non-heap use:

  * The `KnowledgeMap` non-extensionality means a key can be **committed but unobservable**
    (`get? = none`) and only later refined to a pinned `some v` — "the oracle has fixed the answer
    but disclosed it lazily," impossible for a fixed `gmap` value.
  * The `DFrac.discard` fraction turns a token **persistent**, and the `Agree` payload makes it
    `CoreId`, so disclosed knowledge is **freely copyable** (`shareable`) and **never expires**.
  * `Agree` compatibility delivers **consistency** for free: an oracle never reveals two answers.

The result is *shareable, never-expiring, consistent knowledge as pure ghost state* — a building
block for prophecy-style reasoning, contextual refinement, and commit-reveal, with no memory cell in
sight. -/

end IrisMath.Demos.MonotoneOracle
