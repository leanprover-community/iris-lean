/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.Lib.AtomicHeap

@[expose] public section
namespace IrisTest.HeapLang.Atomic

open Iris HeapLang BI ProofMode Std

/-! Tests for `awp_apply`, against the logically atomic `load` of an arbitrary atomic heap. -/

variable {hlc : HasLC} {GF : BundledGFunctors} [IrisGS_gen hlc Exp GF] [A : AtomicHeap GF]
variable (H : A.atomicHeapG GF)

/-- `awp_apply` leaves an atomic accessor whose abort resource is the whole spatial context, so
`Q` has to be handed back on abort and is available on commit. -/
example (Q : IProp GF) (l : Loc) (v : Val) :
    A.heapInv H ⊢ Q -∗ A.pointsTo H l (.own 1) v -∗ WP hl(&(A.load) #l) {{ _v, Q }} := by
  iintro #Hheap HQ Hl
  awp_apply A.load_spec H l $$ Hheap
  iaaccintro %⟨v, DFrac.own 1, .nil⟩ [Hl]
  · isimp only [Tele.app]
    iexact Hl
  · isimp only [Tele.app]
    iintro Hl !>
    iframe
  · isimp only [Tele.app_bind, Tele.app, tforall_nil, BIBase.wandM]
    iintro Hl !>
    iexact HQ

/-- `awp_apply … without HQ` keeps `HQ` out of the abort resource — abort only owes the points-to
— and hands it back as a wand in the continuation. -/
example (Q : IProp GF) (l : Loc) (v : Val) :
    A.heapInv H ⊢ Q -∗ A.pointsTo H l (.own 1) v -∗ WP hl(&(A.load) #l) {{ _v, Q }} := by
  iintro #Hheap HQ Hl
  awp_apply A.load_spec H l $$ Hheap without HQ
  iaaccintro %⟨v, DFrac.own 1, .nil⟩ [Hl]
  · isimp only [Tele.app]
    iexact Hl
  · isimp only [Tele.app]
    iintro Hl !>
    iexact Hl
  · isimp only [Tele.app_bind, Tele.app, tforall_nil, BIBase.wandM]
    iintro Hl !>
    iintro $

end IrisTest.HeapLang.Atomic
end
