/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.Lib.AtomicHeap
public import Iris.HeapLang.Lib.Par
public import Iris.Instances.Lib.Invariants

@[expose] public section

namespace Iris.HeapLang

open BI Spawn Std Std.LawfulSet

/-! # Fetch-and-add on top of compare-and-swap preserves logical atomicity -/

/-! ## Logically atomic increment directly on top of the physical heap -/

@[rocq_alias heap_lang.incr_phy]
def incrPhy : Val := hl_val%
  rec incr l :=
    let oldv := !l;
    if cas(l, oldv, oldv + #1) then oldv else incr l

section IncrementPhysical

variable [HeapLangGS hlc GF]

@[rocq_alias heap_lang.incr_phy_spec]
theorem incrPhy_spec (l : Loc) :
    ⊢ iprop(<<{ ∀∀ (v : Int), l ↦ some hl_val(#v) }>> hl(&incrPhy #l) @ ∅
      <<{ l ↦ some hl_val(#(v + 1 : Int)) | RET hl_val(#v) }>>) := by
  iunfold atomic_wp
  iintro %Φ AU
  iloeb as IH
  wp_rec
  wp_bind !_
  imod AU with ⟨%⟨v, ⟨⟩⟩, Hl, ⟨Hclose, -⟩⟩
  isimp only [Tele.app] at Hl Hclose
  wp_load
  imod Hclose $$ Hl with AU
  imodintro
  wp_pures
  wp_bind cmpXchg(_, _, _)
  imod AU with ⟨%⟨w, ⟨⟩⟩, Hl, Hclose⟩
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at Hl Hclose
  obtain rfl | hw := Decidable.em (v = w)
  · wp_cmpxchg_suc
    icases Hclose with ⟨-, Hclose⟩
    imod Hclose $$ [$Hl]
    imodintro
    wp_pures
    iexact Hclose
  · wp_cmpxchg_fail
    · grind
    icases Hclose with ⟨Hclose, -⟩
    imod Hclose $$ Hl with AU
    imodintro
    wp_pures
    isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at IH
    iapply IH $$ AU

end IncrementPhysical

/-! ## Logically atomic increment on top of an arbitrary logically atomic heap -/

section Increment

variable [IrisGS_gen hlc Exp GF] [A : AtomicHeap GF]

@[rocq_alias heap_lang.increment.incr]
def incr : Val := hl_val%
  rec incr l :=
    let oldv := &(A.load) l;
    if snd(&(A.cmpXchg) l oldv (oldv + #1)) then oldv else incr l

/-- A "weak increment": assumes that there is no race. -/
@[rocq_alias heap_lang.weak_incr]
def weakIncr : Val := hl_val%
  rec weakIncr l :=
    let oldv := &(A.load) l;
    ((&(A.store) l (oldv + #1)); oldv)

variable (H : A.atomicHeapG GF)

/-- A proof of the `incr` specification that unfolds the definition of atomic accessors. This is
the style that most logically atomic proofs take. -/
@[rocq_alias heap_lang.incr_spec_direct]
theorem incr_spec_direct (l : Loc) :
    A.heapInv H ⊢ iprop(<<{ ∀∀ (v : Int), A.pointsTo H l (.own 1) hl_val(#v) }>>
      hl(&(incr (A := A)) #l) @ (↑atomicHeapN)
      <<{ A.pointsTo H l (.own 1) hl_val(#(v + 1 : Int)) | RET hl_val(#v) }>>) := by
  iunfold atomic_wp
  iintro #Hheap %Φ AU
  iloeb as IH
  wp_rec
  awp_apply A.load_spec H l $$ Hheap
  iunfold atomic_acc
  imod AU with ⟨%⟨v, ⟨⟩⟩, Hl, ⟨Hclose, -⟩⟩
  isimp only [Tele.app] at Hl Hclose
  imodintro
  iexists ⟨hl_val(#v), DFrac.own 1, .nil⟩
  isimp only [Tele.app]
  iframe Hl
  isplit
  · iexact Hclose
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM]
  iintro Hl
  imod Hclose $$ Hl with AU
  imodintro
  wp_pures
  awp_apply cas_spec H l hl_val(#v) hl_val(#(v + 1 : Int)) rfl $$ Hheap
  iunfold atomic_acc
  imod AU with ⟨%⟨w, ⟨⟩⟩, Hl, Hclose⟩
  isimp only [Tele.app] at Hl Hclose
  imodintro
  iexists ⟨hl_val(#w), .nil⟩
  isimp only [Tele.app]
  iframe Hl
  isplit
  · icases Hclose with ⟨Hclose, -⟩
    iexact Hclose
  isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM]
  iintro Hl
  obtain rfl | hw := Decidable.em (w = v)
  · icases Hclose with ⟨-, Hclose⟩
    isimp only [↓reduceIte] at Hl
    imod Hclose $$ %Tele.Arg.nil [$Hl]
    imodintro
    isimp only [Tele.bind, Tele.app, tforall_nil, BIBase.wandM] at Hclose
    isimp only [↓reduceIte, decide_true]
    wp_pures
    iexact Hclose
  · have hwv : (hl_val(#w) : Val) ≠ hl_val(#v) := by simp [hw]
    icases Hclose with ⟨Hclose, -⟩
    isimp only [hwv, ↓reduceIte] at Hl
    imod Hclose $$ Hl with AU
    imodintro
    isimp only [hwv, ↓reduceIte, decide_false]
    wp_pures
    isimp only [Tele.app] at IH
    iapply IH $$ AU

/-- A proof of the `incr` specification that uses the `aacc_aupd_*` lemmas to avoid reasoning
with the definition of atomic accessors. These lemmas are only usable here because the atomic
update we have and the one we try to prove are in 1:1 correspondence; most logically atomic
proofs will not be able to use them. -/
@[rocq_alias heap_lang.incr_spec]
theorem incr_spec (l : Loc) :
    A.heapInv H ⊢ iprop(<<{ ∀∀ (v : Int), A.pointsTo H l (.own 1) hl_val(#v) }>>
      hl(&(incr (A := A)) #l) @ (↑atomicHeapN)
      <<{ A.pointsTo H l (.own 1) hl_val(#(v + 1 : Int)) | RET hl_val(#v) }>>) := by
  iunfold atomic_wp
  iintro #Hheap %Φ AU
  iloeb as IH
  wp_rec
  awp_apply A.load_spec H l $$ Hheap
  iapply aacc_aupd_abort subset_refl $$ AU
  iintro %⟨x, ⟨⟩⟩ Hα
  isimp only [Tele.app] at Hα
  iaaccintro %⟨hl_val(#x), DFrac.own 1, .nil⟩ [Hα]
  · isimp only [Tele.app]
    iexact Hα
  · isimp only [Tele.app]
    iintro $ !> AU !> //
  · isimp only [Tele.app_bind, Tele.app, tforall_nil, BIBase.wandM]
    iintro $ !> AU !>
    wp_pures
    awp_apply cas_spec H l hl_val(#x) hl_val(#(x + 1 : Int)) rfl $$ Hheap
    iapply aacc_aupd subset_refl $$ AU
    iintro %⟨x', ⟨⟩⟩ Hα
    isimp only [Tele.app] at Hα
    iaaccintro %⟨hl_val(#x'), .nil⟩ [Hα]
    · isimp only [Tele.app]
      iexact Hα
    · isimp only [Tele.app]
      iintro $ !> AU !> //
    · isimp only [Tele.app_bind, Tele.app, texist_nil, tforall_nil, BIBase.wandM]
      iintro Hβ !>
      obtain rfl | hx := Decidable.em (x' = x)
      · isimp only [↓reduceIte] at Hβ
        isimp only [↓reduceIte, decide_true]
        iright
        iframe Hβ
        iintro Hpost !>
        wp_pures
        iexact Hpost
      · have hxv : (hl_val(#x') : Val) ≠ hl_val(#x) := by simp [hx]
        isimp only [hxv, ↓reduceIte] at Hβ
        isimp only [hxv, ↓reduceIte, decide_false]
        ileft
        iframe Hβ
        iintro AU !>
        wp_pures
        isimp only [Tele.app, tforall_nil, BIBase.wandM] at IH
        iapply IH $$ AU

/-- Logically atomic spec for the weak increment. Also an example for what TaDA calls a "private
precondition". -/
@[rocq_alias heap_lang.weak_incr_spec]
theorem weakIncr_spec (l : Loc) (v : Int) :
    A.heapInv H ⊢ A.pointsTo H l (.own (Qp.half 1)) hl_val(#v) -∗
      iprop(<<{ ∀∀ (v' : Int), A.pointsTo H l (.own (Qp.half 1)) hl_val(#v') }>>
        hl(&(weakIncr (A := A)) #l) @ (↑atomicHeapN)
        <<{ ⌜v = v'⌝ ∗ A.pointsTo H l (.own 1) hl_val(#(v + 1 : Int)) | RET hl_val(#v) }>>) := by
  iunfold atomic_wp
  iintro #Hheap Hl %Φ AU
  wp_rec
  ihave Hload := A.load_spec H l $$ Hheap
  wp_apply atomic_wp_seq $$ Hload %_ %⟨hl_val(#v), DFrac.own (Qp.half 1), .nil⟩ [Hl]
  · isimp only [Tele.app]
    iexact Hl
  isimp only [Tele.app, tforall_nil, BIBase.wandM]
  iintro Hl
  wp_pures
  awp_apply A.store_spec H l hl_val(#(v + 1 : Int)) $$ Hheap
  iapply aacc_aupd_commit subset_refl $$ AU
  iintro %⟨x, ⟨⟩⟩ Hα
  isimp only [Tele.app] at Hα
  ihave %hvx := pointsTo_agree H l _ _ _ _ $$ Hl Hα
  obtain rfl : x = v := by grind
  icombine Hl Hα as Hl
  iaaccintro %⟨hl_val(#x), .nil⟩ [Hl]
  · isimp only [Tele.app]
    iexact Hl
  · isimp only [Tele.app]
    iintro ⟨$, $⟩ !> AU !> //
  · isimp only [Tele.app_bind, Tele.app, texist_nil, tforall_nil, BIBase.wandM]
    iintro $ !> HΦ !>
    wp_pures
    iexact HΦ

end Increment

/-! ## A client of the logically atomic increment -/

section IncrementClient

variable [HeapLangGS hlc GF] [SpawnG GF]

/- The client runs against the physical heap, so that is the `AtomicHeap` instance `incr`
resolves to for the rest of this section. -/
attribute [local instance] primitiveAtomicHeap

@[rocq_alias heap_lang.incr_client]
def incrClient : Val := hl_val%
  λ x,
    let l := &((primitiveAtomicHeap (GF := GF)).alloc) x;
    (&(incr (GF := GF)) l ‖ &(incr (GF := GF)) l)

@[rocq_alias heap_lang.incr_client_safe]
theorem incrClient_safe (x : Int) :
    (primitiveAtomicHeap (GF := GF)).heapInv () ⊢
      WP hl(&(incrClient (GF := GF)) #x) {{ _v, (True : IProp GF) }} := by
  iintro #Hheap
  wp_rec
  wp_apply (primitiveAtomicHeap (GF := GF)).alloc_spec () hl_val(#x) $$ Hheap [//] with %l Hl
  wp_pures
  imod inv_alloc (nroot .@ "incr_client") ⊤
    iprop(∃ x' : Int, (primitiveAtomicHeap (GF := GF)).pointsTo () l (.own 1) hl_val(#x'))
    $$ [$Hl] with #Hinv
  ihave #Aupd : iprop(□ WP hl(&(incr (GF := GF)) #l) {{ _v, (True : IProp GF) }}) $$ []
  · iintro !>
    awp_apply incr_spec (A := primitiveAtomicHeap (GF := GF)) () l $$ Hheap
    iinv Hinv with ⟨%x', >Hl⟩
    · refine ⟨fun p hp => mem_diff.mpr ⟨CoPset.mem_full, fun h => ?_⟩, trivial⟩
      exact ndot_ne_disjoint nroot (x := "incr_client") (y := "atomic_heap") (by decide) p ⟨hp, h⟩
    iaaccintro %⟨x', .nil⟩ [Hl]
    · isimp only [Tele.app]
      iexact Hl
    · isimp only [Tele.app]
      iintro $ !> //
    · isimp only [Tele.app_bind, Tele.app, tforall_nil, BIBase.wandM]
      iintro $
  iapply Par.wp_par (fun _ => iprop(True)) (fun _ => iprop(True)) $$ Aupd Aupd
  · iintro ** !> //

end IncrementClient

end Iris.HeapLang

end
