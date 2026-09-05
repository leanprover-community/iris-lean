/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.BI.Lib.Fractional
public import Iris.HeapLang.ProofMode
public import Iris.ProgramLogic.Atomic
public import Iris.Std.Namespaces

@[expose] public section

namespace Iris.HeapLang

open BI ProofMode Std Std.LawfulSet

/-! # A general logically atomic interface for a heap

All parameters are implicit, since it is expected that there is only one heap in scope that could
possibly apply. Only one instance of `AtomicHeap` should ever be in scope: to write a library that
is generic over the heap, add an `[A : AtomicHeap GF]` parameter around the code and an
`(H : A.atomicHeapG GF)` parameter around the proofs.

When writing an instance of this class, take care not to shadow the class projections, and do not
register it as an instance — make it a `def` that others can register later. -/

/-- The namespace that atomic heap implementations may use for their invariants (the `heapInv`
field of `AtomicHeap`).

It is hardcoded since one should have only one instance of `AtomicHeap`, so having it as a
parameter of this module is unnecessary. An alternative would be adding it as a field of the
class. That would however make it impossible for the client to open its own invariants around
heap operations, as they would not be able to prove disjointness between their namespaces and
the heap's. -/
@[rocq_alias heap_lang.atomic_heapN]
def atomicHeapN : Namespace := nroot .@ "atomic_heap"

/-- A logically atomic interface for a heap: the five operations, an invariant `heapInv` assumed
by all of them, and a points-to predicate.

Rocq quantifies every field over `heapGS_gen hlc Σ`; as for `Lock`, nothing here needs the heap
itself, so the weakest precondition only requires `IrisGS_gen`. -/
@[rocq_alias heap_lang.atomic_heap]
class AtomicHeap (GF : BundledGFunctors) [IrisGS_gen hlc Exp GF] where
  alloc : Val
  free : Val
  load : Val
  store : Val
  cmpXchg : Val

  /-- The assumptions about `GF`, and the singleton ghost names (if needed). -/
  atomicHeapG : BundledGFunctors → Type

  /-- `heapInv` is an invariant that is assumed to hold by all operations. It cannot be allocated
  through the interface; instead, implementations should provide an initialization lemma that
  builds `atomicHeapG` and `heapInv`, so that clients can obtain a closed proof once they have
  chosen an implementation.

  The invariant has to be allocated together with `atomicHeapG` since it is likely to contain
  singleton ghost state. The initialization lemma is not part of the interface as it can only be
  applied by providing an implementation-specific `GF`. -/
  heapInv : atomicHeapG GF → IProp GF
  heapInv_persistent (H : atomicHeapG GF) : Persistent (heapInv H)

  pointsTo : atomicHeapG GF → Loc → DFrac → Val → IProp GF

  pointsTo_timeless (H l dq v) : Timeless (pointsTo H l dq v)
  pointsTo_fractional (H l v) : Fractional fun q => pointsTo H l (.own q) v
  pointsTo_persistent (H l v) : Persistent (pointsTo H l .discard v)
  pointsTo_as_fractional (H l q v) :
    AsFractional (pointsTo H l (.own q) v) ioΦ (fun q => pointsTo H l (.own q) v) ioq q
  pointsTo_combine_sep_gives (H l dq₁ dq₂ v₁ v₂) :
    CombineSepGives (pointsTo H l dq₁ v₁) (pointsTo H l dq₂ v₂)
      iprop(⌜✓ (dq₁ • dq₂) ∧ v₁ = v₂⌝)
  pointsTo_combine_as (H l dq₁ dq₂ v₁ v₂) :
    CombineSepAs (pointsTo H l dq₁ v₁) (pointsTo H l dq₂ v₂) (pointsTo H l (dq₁ • dq₂) v₁)
  pointsTo_persist (H l dq v) :
    ⊢ iprop(pointsTo H l dq v ==∗ pointsTo H l .discard v)

  alloc_spec (H) (v : Val) :
    heapInv H ⊢ {{ True }} hl(&alloc &v) {{ l, RET hl_val(#l); pointsTo H l (.own 1) v }}
  /-- Rocq binds a fresh `l : unit` in the postcondition and returns `#l`, which is the same
  statement as returning `#()`. -/
  free_spec (H) (l : Loc) (v : Val) :
    heapInv H ⊢ {{ pointsTo H l (.own 1) v }} hl(&free #l) {{ RET hl_val(#()); True }}
  load_spec (H) (l : Loc) :
    heapInv H ⊢ iprop(<<{ ∀∀ (v : Val) (q : DFrac), pointsTo H l q v }>>
      hl(&load #l) @ (↑atomicHeapN) <<{ pointsTo H l q v | RET v }>>)
  store_spec (H) (l : Loc) (w : Val) :
    heapInv H ⊢ iprop(<<{ ∀∀ (v : Val), pointsTo H l (.own 1) v }>>
      hl(&store #l &w) @ (↑atomicHeapN) <<{ pointsTo H l (.own 1) w | RET hl_val(#()) }>>)
  /-- This spec is slightly weaker than it could be: it is sufficient for `w₁` *or* `v` to be
  unboxed. However, by writing it this way `Val.isUnboxed` is outside the atomic triple, which
  makes it much easier to use — and the spec is still good enough for all our applications.

  The postcondition deliberately does not use a boolean-valued equality test, so that users can
  case on `v = w₁` and have it simplify in both places. -/
  cmpXchg_spec (H) (l : Loc) (w₁ w₂ : Val) (hw₁ : w₁.isUnboxed) :
    heapInv H ⊢ iprop(<<{ ∀∀ (v : Val), pointsTo H l (.own 1) v }>>
      hl(&cmpXchg #l &w₁ &w₂) @ (↑atomicHeapN)
      <<{ if v = w₁ then pointsTo H l (.own 1) w₂ else pointsTo H l (.own 1) v
        | RET hl_val((&v, #(decide (v = w₁)))) }>>)

section Interface

variable [IrisGS_gen hlc Exp GF] [A : AtomicHeap GF] (H : A.atomicHeapG GF)

instance : Persistent (A.heapInv H) := A.heapInv_persistent H
instance : Timeless (A.pointsTo H l dq v) := A.pointsTo_timeless H l dq v
instance : Fractional fun q => A.pointsTo H l (.own q) v := A.pointsTo_fractional H l v
instance : Persistent (A.pointsTo H l .discard v) := A.pointsTo_persistent H l v

instance : AsFractional (A.pointsTo H l (.own q) v) ioΦ (fun q => A.pointsTo H l (.own q) v) ioq q :=
  A.pointsTo_as_fractional H l q v

instance : CombineSepGives (A.pointsTo H l dq₁ v₁) (A.pointsTo H l dq₂ v₂)
    iprop(⌜✓ (dq₁ • dq₂) ∧ v₁ = v₂⌝) :=
  A.pointsTo_combine_sep_gives H l dq₁ dq₂ v₁ v₂

/-- Lower priority than `combineSepAsFractional`, which kicks in for `DFrac.own`. -/
instance (priority := default - 15) :
    CombineSepAs (A.pointsTo H l dq₁ v₁) (A.pointsTo H l dq₂ v₂) (A.pointsTo H l (dq₁ • dq₂) v₁) :=
  A.pointsTo_combine_as H l dq₁ dq₂ v₁ v₂

end Interface

/-- Fetch-and-add, implemented on top of the compare-and-swap of an arbitrary atomic heap. -/
@[rocq_alias heap_lang.atomic_heap.faa_atomic]
def faaAtomic [IrisGS_gen hlc Exp GF] [A : AtomicHeap GF] : Val := hl_val%
  rec faa l n :=
    let m := &(A.load) l;
    if snd(&(A.cmpXchg) l m (m + n)) then m else faa l n

section Derived

variable [IrisGS_gen hlc Exp GF] [A : AtomicHeap GF] (H : A.atomicHeapG GF)

@[rocq_alias heap_lang.atomic_heap.pointsto_agree]
theorem pointsTo_agree (l : Loc) (dq₁ dq₂ v₁ v₂) :
    A.pointsTo H l dq₁ v₁ ⊢ A.pointsTo H l dq₂ v₂ -∗ ⌜v₁ = v₂⌝ := by
  iintro Hl1 Hl2
  icombine Hl1 Hl2 gives %⟨_, rfl⟩
  itrivial

@[rocq_alias heap_lang.atomic_heap.pointsto_combine]
theorem pointsTo_combine (l : Loc) (dq₁ dq₂ v₁ v₂) :
    A.pointsTo H l dq₁ v₁ ⊢
    A.pointsTo H l dq₂ v₂ -∗ A.pointsTo H l (dq₁ • dq₂) v₁ ∗ ⌜v₁ = v₂⌝ := by
  iintro Hl1 Hl2
  icombine Hl1 Hl2 as $ gives %⟨_, rfl⟩
  itrivial

@[rocq_alias heap_lang.cas_spec]
theorem cas_spec (l : Loc) (w₁ w₂ : Val) (hw₁ : w₁.isUnboxed) :
    A.heapInv H ⊢ iprop(<<{ ∀∀ (v : Val), A.pointsTo H l (.own 1) v }>>
      hl(snd(&(A.cmpXchg) #l &w₁ &w₂)) @ (↑atomicHeapN)
      <<{ if v = w₁ then A.pointsTo H l (.own 1) w₂ else A.pointsTo H l (.own 1) v
        | RET hl_val(#(decide (v = w₁))) }>>) := by
  iunfold atomic_wp
  iintro #Hheap %Φ AU
  awp_apply A.cmpXchg_spec H l w₁ w₂ hw₁ $$ Hheap
  iapply aacc_aupd_commit subset_refl $$ AU
  iintro %⟨v, ⟨⟩⟩ Hα
  iaaccintro %⟨v, .nil⟩ Hα
  · iintro $ !> AU !> //
  · isimp only [Tele.app_bind, Tele.app, texist_nil, tforall_nil, BIBase.wandM]
    iintro $ !> HΦ !>
    wp_pures
    iexact HΦ

@[rocq_alias heap_lang.faa_spec]
theorem faa_spec (l : Loc) (i₂ : Int) :
    A.heapInv H ⊢ iprop(<<{ ∀∀ (i₁ : Int), A.pointsTo H l (.own 1) hl_val(#i₁) }>>
      hl(&(faaAtomic (A := A)) #l #i₂) @ (↑atomicHeapN)
      <<{ A.pointsTo H l (.own 1) hl_val(#(i₁ + i₂)) | RET hl_val(#i₁) }>>) := by
  iunfold atomic_wp
  iintro #Hheap %Φ AU
  iunfold faaAtomic
  iloeb as IH
  wp_rec
  wp_pures
  awp_apply A.load_spec H l $$ Hheap
  iapply aacc_aupd_abort subset_refl $$ AU
  iintro %⟨i₁, ⟨⟩⟩ Hα
  isimp only [Tele.app] at Hα
  iaaccintro %⟨hl_val(#i₁), DFrac.own 1, .nil⟩ [Hα]
  · isimp only [Tele.app]
    iexact Hα
  · isimp only [Tele.app]
    iintro $ !> AU !> //
  · isimp only [Tele.app_bind, Tele.app, tforall_nil, BIBase.wandM]
    iintro $ !> AU !>
    wp_pures
    awp_apply cas_spec H l hl_val(#i₁) hl_val(#(i₁ + i₂)) rfl $$ Hheap
    iapply aacc_aupd subset_refl $$ AU
    iintro %⟨m, ⟨⟩⟩ Hα
    isimp only [Tele.app] at Hα
    iaaccintro %⟨hl_val(#m), .nil⟩ [Hα]
    · isimp only [Tele.app]
      iexact Hα
    · isimp only [Tele.app]
      iintro $ !> AU !> //
    · isimp only [Tele.app_bind, Tele.app, texist_nil, tforall_nil, BIBase.wandM]
      iintro Hβ !>
      obtain rfl | hm := Decidable.em (m = i₁)
      · isimp only [↓reduceIte] at Hβ
        isimp only [↓reduceIte, decide_true]
        iright
        iframe Hβ
        iintro Hpost !>
        wp_pures
        iexact Hpost
      · have hmv : (hl_val(#m) : Val) ≠ hl_val(#i₁) := by simp [hm]
        isimp only [hmv, ↓reduceIte] at Hβ
        isimp only [hmv, ↓reduceIte, decide_false]
        ileft
        iframe Hβ
        iintro AU !>
        wp_pure
        isimp only [Tele.app, tforall_nil, BIBase.wandM] at IH
        iapply IH $$ AU

end Derived

/-! ## The primitive physical operations of HeapLang satisfy the interface -/

@[rocq_alias heap_lang.primitive_alloc]
def primitiveAlloc : Val := hl_val% λ v, ref(v)

@[rocq_alias heap_lang.primitive_free]
def primitiveFree : Val := hl_val% λ v, free(v)

@[rocq_alias heap_lang.primitive_load]
def primitiveLoad : Val := hl_val% λ l, !l

@[rocq_alias heap_lang.primitive_store]
def primitiveStore : Val := hl_val% λ l x, l ← x

@[rocq_alias heap_lang.primitive_cmpxchg]
def primitiveCmpXchg : Val := hl_val% λ l e1 e2, cmpXchg(l, e1, e2)

section Primitive

variable [HeapLangGS hlc GF]

@[rocq_alias heap_lang.primitive_alloc_spec]
theorem primitiveAlloc_spec (v : Val) :
    (True : IProp GF) ⊢ {{ True }} hl(&primitiveAlloc &v) {{ l, RET hl_val(#l); l ↦ some v }} := by
  iintro _ %Φ !> _ HΦ
  wp_lam
  wp_alloc l with Hl
  iapply HΦ $$ %l Hl

@[rocq_alias heap_lang.primitive_free_spec]
theorem primitiveFree_spec (l : Loc) (v : Val) :
    (True : IProp GF) ⊢ {{ l ↦ some v }} hl(&primitiveFree #l) {{ RET hl_val(#()); True }} := by
  iintro _ %Φ !> Hl HΦ
  wp_lam
  wp_free
  iapply HΦ $$ [//]

@[rocq_alias heap_lang.primitive_load_spec]
theorem primitiveLoad_spec (l : Loc) :
    (True : IProp GF) ⊢ iprop(<<{ ∀∀ (v : Val) (q : DFrac), l ↦{q} some v }>>
      hl(&primitiveLoad #l) @ (↑atomicHeapN) <<{ l ↦{q} some v | RET v }>>) := by
  iunfold atomic_wp
  iintro _ %Φ AU
  wp_lam
  imod AU with ⟨%⟨v, q, _⟩, Hl, ⟨-, Hclose⟩⟩
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at Hl Hclose
  wp_load
  imod Hclose $$ [$Hl] with $

@[rocq_alias heap_lang.primitive_store_spec]
theorem primitiveStore_spec (l : Loc) (w : Val) :
    (True : IProp GF) ⊢ iprop(<<{ ∀∀ (v : Val), l ↦ some v }>>
      hl(&primitiveStore #l &w) @ (↑atomicHeapN) <<{ l ↦ some w | RET hl_val(#()) }>>) := by
  iunfold atomic_wp
  iintro _ %Φ AU
  wp_lam
  wp_let
  imod AU with ⟨%⟨v, _⟩, Hl, ⟨-, Hclose⟩⟩
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at Hl Hclose
  wp_store
  imod Hclose $$ [$Hl] with $

@[rocq_alias heap_lang.primitive_cmpxchg_spec]
theorem primitiveCmpXchg_spec (l : Loc) (w₁ w₂ : Val) (hw₁ : w₁.isUnboxed) :
    (True : IProp GF) ⊢ iprop(<<{ ∀∀ (v : Val), l ↦ some v }>>
      hl(&primitiveCmpXchg #l &w₁ &w₂) @ (↑atomicHeapN)
      <<{ if v = w₁ then l ↦ some w₂ else l ↦ some v
        | RET hl_val((&v, #(decide (v = w₁)))) }>>) := by
  iunfold atomic_wp
  iintro _ %Φ AU
  wp_lam
  wp_pures
  imod AU with ⟨%⟨v, _⟩, Hl, ⟨-, Hclose⟩⟩
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at Hl Hclose
  obtain rfl | hv := Decidable.em (v = w₁)
  · wp_cmpxchg_suc
    · simp [Val.compareSafe, hw₁]
    isimp only [↓reduceIte, decide_true] at Hclose
    imod Hclose $$ [$Hl] with $
  · wp_cmpxchg_fail
    · simp [Val.compareSafe, hw₁]
    isimp only [hv, ↓reduceIte, decide_false] at Hclose
    imod Hclose $$ [$Hl] with $

end Primitive

/-- Not registered as an instance because users should choose explicitly to use it. -/
@[reducible, rocq_alias heap_lang.primitive_atomic_heap]
def primitiveAtomicHeap [HeapLangGS hlc GF] : AtomicHeap GF where
  alloc := primitiveAlloc
  free := primitiveFree
  load := primitiveLoad
  store := primitiveStore
  cmpXchg := primitiveCmpXchg
  atomicHeapG _ := Unit
  heapInv _ := iprop(True)
  heapInv_persistent _ := inferInstance
  pointsTo _ l dq v := l ↦{dq} some v
  pointsTo_timeless _ _ _ _ := inferInstance
  pointsTo_fractional _ _ _ := inferInstance
  pointsTo_persistent _ _ _ := inferInstance
  pointsTo_as_fractional _ _ _ _ := inferInstance
  pointsTo_combine_sep_gives _ l dq₁ dq₂ v₁ v₂ := ⟨by
    iintro ⟨Hl1, Hl2⟩
    icombine Hl1 Hl2 gives %⟨hdq, hv⟩
    imodintro
    ipureintro
    grind⟩
  pointsTo_combine_as _ _ _ _ _ _ := inferInstance
  pointsTo_persist _ _ _ _ := pointsTo_persist
  alloc_spec _ := primitiveAlloc_spec
  free_spec _ := primitiveFree_spec
  load_spec _ := primitiveLoad_spec
  store_spec _ := primitiveStore_spec
  cmpXchg_spec _ := primitiveCmpXchg_spec

end Iris.HeapLang

end
