/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.ProgramLogic.EctxLiftingTransfinite
public import Iris.ProgramLogic.Refinement.RefEctxLifting
public import Iris.ProgramLogic.AdequacyTransfinite
public import Iris.ProgramLogic.Refinement.RefAdequacy

/-! # HeapLang in Transfinite Iris

This file ports `theories/heap_lang/lifting.v` of Transfinite Iris: the heap_lang program logic
over any type of step-indices, for the weakest precondition `wp`, the strong weakest precondition
`swp`, the refinement weakest precondition `rwp` and the strong refinement weakest precondition
`rswp`. The state interpretation is the one of `Iris.HeapLang.PrimitiveLaws` (a generalized heap
and a prophecy map); the refinement program logic only uses the heap.

The rules are stated for `swp` and `rswp` (at any number `k` of logical steps) and derived for
`wp` (`swp_wp`) and `rwp` (`rwp_no_step`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.HeapLang.Transfinite

open Iris Iris.Transfinite ProgramLogic Language.Notation Iris.Std EctxLanguage Iris.BI FromMathlib

/-- The ghost state of heap_lang in Transfinite Iris (Rocq: `heapG`). -/
class HeapLangTGS (GF : BundledGFunctors) extends WsatGS GF where
  heap : genHeapGS Loc (Option Val) GF HeapF
  proph : prophMapGS ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangTGS.heap HeapLangTGS.proph

variable {GF : BundledGFunctors} [H : HeapLangTGS GF]

/-- Rocq: `heapG_irisG`. -/
instance heapIrisGS : IrisGS Exp GF where
  toWsatGS := H.toWsatGS
  stateInterp σ κs _ := iprop(genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId)
  forkPost _ := iprop(True)

/-- Rocq: `heapG_ref_irisG`. -/
instance heapRefIrisGS : RefIrisGS Exp GF where
  toWsatGS := H.toWsatGS
  refStateInterp σ _ := genHeapInterp σ.heap
  refForkPost _ := iprop(True)

theorem stateInterp_eq (σ : State) (κs : List Observation) (n : Nat) :
    (heapIrisGS (GF := GF)).stateInterp σ κs n =
      iprop(genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId) := rfl

theorem refStateInterp_eq (σ : State) (n : Nat) :
    (heapRefIrisGS (GF := GF)).refStateInterp σ n = genHeapInterp σ.heap := rfl

variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {k : Nat}

theorem loc_add_zero' (l : Loc) : l + (0 : Int) = l := by
  cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind

theorem allocCells_toSeq_pointsTo' {l : Loc} {v : Val} {n : Nat} :
    ([∗map] l' ↦ ov ∈ allocCells l n v, l' ↦ ov) ⊢@{IProp GF}
      [∗list] i ∈ List.range n, l + i ↦ v := by
  induction n with
  | zero => exact BI.BigSepM.bigSepM_empty.1.trans BI.BigSepL.bigSepL_nil.2
  | succ n ih =>
    rw [allocCells_succ, List.range_succ]
    refine (BI.BigSepM.bigSepM_insert get?_allocCells_self).1.trans ?_
    refine .trans ?_ BI.BigSepL.bigSepL_snoc.2
    exact BI.sep_comm.1.trans (BI.sep_mono ih .rfl)

theorem heapArray_toSeq_metaToken' {l : Loc} {vs : List (Option Val)} {n : Nat}
    (hlen : vs.length = n) :
    ([∗map] l' ↦ _ov ∈ heapArray l vs, metaToken l' ⊤) ⊢@{IProp GF}
      [∗list] i ∈ List.range n, metaToken (l + i) ⊤ := by
  subst n
  induction vs using List.reverseRec generalizing l with
  | nil => exact BI.BigSepM.bigSepM_empty.1.trans BI.BigSepL.bigSepL_nil.2
  | append_singleton vs v ih =>
    rw [heapArray_snoc, List.length_append, List.length_singleton, Nat.add_one, List.range_succ]
    refine (BI.BigSepM.bigSepM_insert (Φ := fun l' _ => iprop(metaToken l' ⊤))
      get?_heapArray_self).1.trans ?_
    refine .trans ?_ BI.BigSepL.bigSepL_snoc.2
    exact BI.sep_comm.1.trans (BI.sep_mono ih .rfl)

/-! ## `swp` and `wp` -/

section swp

variable {A : Type _} [src : Source GF A]

/-- Rocq: `swp_fork`. -/
theorem swp_fork {e : Exp} :
    ⊢ ▷ Iris.Transfinite.wp s ⊤ e (fun _ => iprop(True)) -∗ ▷ Φ (hl_val(#())) -∗
      swp k s E hl(fork(&e)) Φ := by
  iintro He HΦ
  iapply swp_lift_atomic_base_step k
  iintro %σ₁ %κ %κs %n Hσ
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  cases Hstep
  simp only [stateInterp_eq, List.nil_append, List.length_singleton]
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [HΦ]
  · iexists _
    iframe HΦ
    ipureintro; rfl
  · iapply BI.BigSepL.bigSepL_singleton
    iframe He

/-- Rocq: `wp_fork`. -/
theorem wp_fork {e : Exp} :
    ⊢ ▷ Iris.Transfinite.wp s ⊤ e (fun _ => iprop(True)) -∗ ▷ Φ (hl_val(#())) -∗ Iris.Transfinite.wp s E hl(fork(&e)) Φ := by
  iintro He HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_fork $$ He HΦ

/-- Rocq: `swp_load`. -/
theorem swp_load {l : Loc} {q} {v : Val} :
    ⊢ ▷ l ↦{q} some v -∗ (l ↦{q} some v -∗ Φ v) -∗ swp k s E hl(!v(#l)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], .val v, σ₁, [], by constructor; simp [Hpt]⟩
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `wp_load`. -/
theorem wp_load {l : Loc} {q} {v : Val} :
    ⊢ ▷ l ↦{q} some v -∗ (l ↦{q} some v -∗ Φ v) -∗ Iris.Transfinite.wp s E hl(!v(#l)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_load $$ Hpt HΦ


/-- Rocq: `swp_allocN` (with the cells as a sequence). -/
theorem swp_allocN_seq {v : Val} {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) -∗
        Φ hl_val(#(.loc l))) -∗ swp k s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %m ⟨Hσ, Hobs⟩
  obtain ⟨l, hfresh⟩ := exists_fresh_block σ₁.heap n
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], .ofVal (.lit (.loc l)), σ₁.initHeap l n v, [], .allocNS n v σ₁ l hn hfresh⟩
  inext
  iintro %v₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i l' _hn' hfresh'
  imod genHeap_alloc_big (allocCells l' n.toNat v) σ₁.heap (allocCells_disjoint hfresh') $$ Hσ
    with ⟨Hσ, Hpts, Htok⟩
  imodintro
  isplit; itrivial
  ihave Hσ := genHeapInterp_eqv (.symm _ _ initHeap_heap_eq) $$ Hσ
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists hl_val(#(BaseLit.loc _))
  isplit; ipureintro; rfl
  iapply HΦ
  iapply BI.BigSepL.bigSepL_sep_eqv.2
  isplitl [Hpts]
  · iapply allocCells_toSeq_pointsTo' $$ Hpts
  · iapply heapArray_toSeq_metaToken' $$ Htok
    grind

theorem wp_allocN_seq {v : Val} {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) -∗
        Φ hl_val(#(.loc l))) -∗ Iris.Transfinite.wp s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_allocN_seq hn $$ HΦ

/-- Rocq: `swp_alloc`. -/
theorem swp_alloc {v : Val} :
    ⊢ (∀ l : Loc, l ↦ some v -∗ Φ hl_val(#(.loc l))) -∗ swp k s E hl(ref(&v)) Φ := by
  iintro HΦ
  iapply swp_allocN_seq (by omega)
  iintro %l H
  iapply HΦ
  rw [Int.toNat_one, List.range_one, BI.BigSepL.bigSepL_singleton.to_eq]
  rw [show l + 0 = l from loc_add_zero l]
  icases H with ⟨H, -⟩
  iexact H

theorem wp_alloc {v : Val} :
    ⊢ (∀ l : Loc, l ↦ some v -∗ Φ hl_val(#(.loc l))) -∗ Iris.Transfinite.wp s E hl(ref(&v)) Φ := by
  iintro HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_alloc $$ HΦ

/-- Rocq: `swp_store`. -/
theorem swp_store {l : Loc} {v v' : Val} :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v -∗ Φ hl_val(#())) -∗ swp k s E hl(v(#l) ← &v) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    refine ⟨[], .val (.lit .unit), σ₁.initHeap l 1 v, [], BaseStep.storeS _ v' _ _ ?_⟩
    grind
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v'' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists hl_val(#())
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ Hpt

theorem wp_store {l : Loc} {v v' : Val} :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v -∗ Φ hl_val(#())) -∗
      Iris.Transfinite.wp s E hl(v(#l) ← &v) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_store $$ Hpt HΦ

/-- Rocq: `swp_cmpxchg_fail`. -/
theorem swp_cmpXchg_fail {l : Loc} {q} {v' v1 v2 : Val} (hne : v' ≠ v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦{q} some v' -∗ (l ↦{q} some v' -∗ Φ hl_val((&v', #false))) -∗
      swp k s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    refine ⟨[], hl(v((&v', #false))), σ₁, [], .cmpXchgS l v1 v2 v' σ₁ false Hpt hsafe ?_⟩
    simp [hne]
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = false := by simpa [hne] using Hdec.symm
  subst b
  imodintro
  simp only [show decide (v' = v1) = false by simp [hne], Bool.false_eq_true, ↓reduceIte]
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists hl_val((&v', #false))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

theorem wp_cmpXchg_fail {l : Loc} {q} {v' v1 v2 : Val} (hne : v' ≠ v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦{q} some v' -∗ (l ↦{q} some v' -∗ Φ hl_val((&v', #false))) -∗
      Iris.Transfinite.wp s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_cmpXchg_fail hne hsafe $$ Hpt HΦ

/-- Rocq: `swp_cmpxchg_suc`. -/
theorem swp_cmpXchg_suc {l : Loc} {v' v1 v2 : Val} (heq : v' = v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v2 -∗ Φ hl_val((&v', #true))) -∗
      swp k s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    refine ⟨[], hl(v((&v', #true))), σ₁.initHeap l 1 v2, [],
      .cmpXchgS l v1 v2 v' σ₁ true Hpt hsafe ?_⟩
    simp [heq]
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = true := by simpa [heq] using Hdec.symm
  subst b
  simp only [show decide (v' = v1) = true by simp [heq], ↓reduceIte, Int.toNat_one,
    List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := .some v2) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists hl_val((&v', #true))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

theorem wp_cmpXchg_suc {l : Loc} {v' v1 v2 : Val} (heq : v' = v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v2 -∗ Φ hl_val((&v', #true))) -∗
      Iris.Transfinite.wp s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_cmpXchg_suc heq hsafe $$ Hpt HΦ

/-- Rocq: `swp_faa`. -/
theorem swp_faa {l : Loc} {i1 i2 : Int} :
    ⊢ ▷ l ↦ some hl_val(#i1) -∗ (l ↦ some hl_val(#(i1 + i2)) -∗ Φ hl_val(#i1)) -∗
      swp k s E hl(faa(#l, #i2)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some (Val.lit (.int i1)))⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    refine ⟨[], .val (.lit (.int i1)), σ₁.initHeap l 1 (some hl_val(#(i1 + i2))), [],
      .faaS l i1 i2 σ₁ ?_⟩
    grind
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i i1' H
  obtain rfl : i1 = i1' := by
    simp only [Hpt, Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := some hl_val(#(i1 + i2))) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists Val.lit (.int i1)
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

theorem wp_faa {l : Loc} {i1 i2 : Int} :
    ⊢ ▷ l ↦ some hl_val(#i1) -∗ (l ↦ some hl_val(#(i1 + i2)) -∗ Φ hl_val(#i1)) -∗
      Iris.Transfinite.wp s E hl(faa(#l, #i2)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_faa $$ Hpt HΦ

/-- The exchange instruction. -/
theorem swp_xchg {l : Loc} {v w : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ some w -∗ Φ v) -∗ swp k s E hl(xchg(#l, &w)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    refine ⟨[], .val v, σ₁.initHeap l 1 w, [], .xchgS l v w σ₁ ?_⟩
    grind
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v' H
  obtain rfl : v = v' := by
    simp only [Hpt, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := some w) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

theorem wp_xchg {l : Loc} {v w : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ some w -∗ Φ v) -∗ Iris.Transfinite.wp s E hl(xchg(#l, &w)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_xchg $$ Hpt HΦ

/-- Deallocation. -/
theorem swp_free {l : Loc} {v : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ none -∗ Φ hl_val(#())) -∗ swp k s E hl(free(#l)) Φ := by
  iintro >Hpt HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hobs⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  isplitr
  · ipureintro
    exists [], hl_val(#()), σ₁.initHeap l 1 none, []
    refine BaseStep.freeS l v _ ?_
    grind
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  rcases Hstep with ⟨v'', H⟩
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := none) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  simp only [List.nil_append]
  iframe Hσ Hobs
  iexists hl_val(#())
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

theorem wp_free {l : Loc} {v : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ none -∗ Φ hl_val(#())) -∗
      Iris.Transfinite.wp s E hl(free(#l)) Φ := by
  iintro Hpt HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_free $$ Hpt HΦ

/-- Rocq: `swp_new_proph`. -/
theorem swp_new_proph :
    ⊢ (∀ (pvs : List (Val × Val)) (p : ProphId), proph p pvs -∗ Φ hl_val(#p)) -∗
      swp k s E hl(newProph()) Φ := by
  iintro HΦ
  iapply swp_lift_atomic_base_step_no_fork k
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hproph⟩
  obtain ⟨pf, Hpf⟩ := Iris.Std.List.fresh σ₁.usedProphId.toList
  have Hpf_contains : ¬ σ₁.usedProphId.contains pf := by
    intro hc; exact Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.newProphS σ₁ pf Hpf_contains⟩
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  cases Hstep
  rename_i p' Hp'
  simp only [List.nil_append]
  have Hp'_mem : p' ∉ σ₁.usedProphId :=
    fun hmem => Hp' (Std.ExtTreeSet.mem_iff_contains.symm.mp hmem)
  imod ProphMap.new_proph p' σ₁.usedProphId κs Hp'_mem $$ Hproph with ⟨Hproph', Htok⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  isplitl [Hproph']
  · rw [show σ₁.usedProphId.insert p' = {p'} ∪ σ₁.usedProphId by
        ext x; simp [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_union_iff]]
    iexact Hproph'
  · iexists hl_val(#(BaseLit.prophecy p'))
    isplit
    · ipureintro; simp [toVal]; rfl
    iapply HΦ $$ [$]

theorem wp_new_proph :
    ⊢ (∀ (pvs : List (Val × Val)) (p : ProphId), proph p pvs -∗ Φ hl_val(#p)) -∗
      Iris.Transfinite.wp s E hl(newProph()) Φ := by
  iintro HΦ
  iapply swp_wp (k := 0) rfl
  iapply swp_new_proph $$ HΦ


/-- Rocq: `wp_resolve`. -/
theorem wp_resolve {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    [hatom : Language.Atomic Language.Atomicity.StronglyAtomic e] (hne : toVal e = none) :
    ⊢ proph p pvs -∗
      Iris.Transfinite.wp s E e (fun r => iprop(∀ pvs', ⌜pvs = (r, w) :: pvs'⌝ -∗ proph p pvs' -∗
        Φ r)) -∗
      Iris.Transfinite.wp s E hl(resolve(&e, v(#p), v(&w))) Φ := by
  iintro Hp HWPe
  rw [Iris.Transfinite.wp_unfold s E hl(resolve(&e, v(#p), v(&w))) Φ, Iris.Transfinite.wp_unfold s E e]
  simp only [wpPre, hne]
  dsimp only [toVal]
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hκ⟩
  icases ProphMap.agree (κ ++ κs) σ₁.usedProphId p pvs $$ [$Hκ $Hp] with %Hagree
  have hredR : Stuckness.MaybeReducible s (e, σ₁) →
      Stuckness.MaybeReducible s (hl(resolve(&e, v(#p), v(&w))), σ₁) := fun Hred_e => by
    cases s <;> simp only [Stuckness.MaybeReducible] at Hred_e ⊢
    exact prim_step_reducible_resolve (Std.ExtTreeSet.mem_iff_contains.mp Hagree.1) Hred_e
  cases κ using List.reverseRec with
  | nil =>
    imod HWPe $$ %σ₁ %([] : List Observation) %κs %n [$Hσ $Hκ] with ⟨%Hred_e, -⟩
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %efs %Hstep
    exfalso
    obtain ⟨_, _, hκ_eq, _, _⟩ := step_resolve_decompose Hstep
    exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hκ_eq.symm).2
  | append_singleton init lastObs _ =>
    have hassoc : (init ++ [lastObs]) ++ κs = init ++ (lastObs :: κs) := by simp
    rw [hassoc]
    imod HWPe $$ %σ₁ %init %(lastObs :: κs) %n [$Hσ $Hκ] with ⟨%Hred_e, HWPe⟩
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %efs %Hstep
    obtain ⟨κ_inner, v_inner, hκ_eq, rfl, Hbase_e⟩ := step_resolve_decompose Hstep
    obtain ⟨rfl, rfl⟩ :=
      (by simpa using congrArg List.reverse hκ_eq : lastObs = _ ∧ init = κ_inner)
    imod HWPe $$ %_ %σ₂ %efs %(EctxLanguage.primStep_of_baseStep Hbase_e) with HWPe
    imodintro
    inext
    imod HWPe with ⟨⟨Hσ, Hκ⟩, HWPval, Hefs⟩
    imod Iris.Transfinite.wp_value_inv' s E _ v_inner $$ HWPval with HΦ
    imod ProphMap.resolve_proph p (v_inner, w) κs σ₂.usedProphId pvs $$ [$Hκ $Hp]
      with ⟨%pvs'', %hpvs, Hκ, Hp⟩
    imodintro
    iframe Hσ Hκ Hefs
    iapply Iris.Transfinite.wp_value' s E
    iapply HΦ $$ %pvs'' %hpvs Hp

/-- Rocq: `swp_resolve`. -/
theorem swp_resolve {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    [hatom : Language.Atomic Language.Atomicity.StronglyAtomic e] :
    ⊢ proph p pvs -∗
      swp k s E e (fun r => iprop(∀ pvs', ⌜pvs = (r, w) :: pvs'⌝ -∗ proph p pvs' -∗ Φ r)) -∗
      swp k s E hl(resolve(&e, v(#p), v(&w))) Φ := by
  iintro Hp HWPe
  unfold swp
  simp only [stateInterp_eq]
  iintro %σ₁ %κ %κs %n ⟨Hσ, Hκ⟩
  icases ProphMap.agree (κ ++ κs) σ₁.usedProphId p pvs $$ [$Hκ $Hp] with %Hagree
  have hredR : Stuckness.MaybeReducible s (e, σ₁) →
      Stuckness.MaybeReducible s (hl(resolve(&e, v(#p), v(&w))), σ₁) := fun Hred_e => by
    cases s <;> simp only [Stuckness.MaybeReducible] at Hred_e ⊢
    exact prim_step_reducible_resolve (Std.ExtTreeSet.mem_iff_contains.mp Hagree.1) Hred_e
  cases κ using List.reverseRec with
  | nil =>
    imod HWPe $$ %σ₁ %([] : List Observation) %κs %n [$Hσ $Hκ] with ⟨%Hred_e, -⟩
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %efs %Hstep
    exfalso
    obtain ⟨_, _, hκ_eq, _, _⟩ := step_resolve_decompose Hstep
    exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hκ_eq.symm).2
  | append_singleton init lastObs _ =>
    have hassoc : (init ++ [lastObs]) ++ κs = init ++ (lastObs :: κs) := by simp
    rw [hassoc]
    imod HWPe $$ %σ₁ %init %(lastObs :: κs) %n [$Hσ $Hκ] with ⟨%Hred_e, HWPe⟩
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %efs %Hstep
    obtain ⟨κ_inner, v_inner, hκ_eq, rfl, Hbase_e⟩ := step_resolve_decompose Hstep
    obtain ⟨rfl, rfl⟩ :=
      (by simpa using congrArg List.reverse hκ_eq : lastObs = _ ∧ init = κ_inner)
    imod HWPe $$ %_ %σ₂ %efs %(EctxLanguage.primStep_of_baseStep Hbase_e) with HWPe
    imodintro
    inext
    imod HWPe with ⟨⟨Hσ, Hκ⟩, HWPval, Hefs⟩
    imod Iris.Transfinite.wp_value_inv' s E _ v_inner $$ HWPval with HΦ
    imod ProphMap.resolve_proph p (v_inner, w) κs σ₂.usedProphId pvs $$ [$Hκ $Hp]
      with ⟨%pvs'', %hpvs, Hκ, Hp⟩
    imodintro
    iframe Hσ Hκ Hefs
    iapply Iris.Transfinite.wp_value' s E
    iapply HΦ $$ %pvs'' %hpvs Hp

end swp

/-! ## `rswp` and `rwp` -/

section rswp

variable {A : Type _} [src : Source GF A]

/-- Rocq: `rswp_fork`. -/
theorem rswp_fork {e : Exp} :
    ⊢ rwp (src := src) (ι := heapRefIrisGS) s ⊤ e (fun _ => iprop(True)) -∗ Φ (hl_val(#())) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(fork(&e)) Φ := by
  iintro He HΦ
  iapply rswp_lift_atomic_base_step
  iintro %σ₁ %n Hσ
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    exact ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  iintro %e₂ %σ₂ %efs %κ %Hstep
  cases Hstep
  simp only [refStateInterp_eq, List.length_singleton]
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl [HΦ]
  · iexists _
    iframe HΦ
    ipureintro; rfl
  · iapply BI.BigSepL.bigSepL_singleton
    iframe He

/-- Rocq: `rwp_fork`. -/
theorem rwp_fork {e : Exp} :
    ⊢ rwp (src := src) (ι := heapRefIrisGS) s ⊤ e (fun _ => iprop(True)) -∗ Φ (hl_val(#())) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(fork(&e)) Φ := by
  iintro He HΦ
  iapply rwp_no_step rfl
  iapply rswp_fork $$ He HΦ

/-- Rocq: `rswp_load`. -/
theorem rswp_load {l : Loc} {q} {v : Val} :
    ⊢ ▷ l ↦{q} some v -∗ (l ↦{q} some v -∗ Φ v) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(!v(#l)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    exact ⟨[], .val v, σ₁, [], by constructor; simp [Hpt]⟩
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i v' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_load`. -/
theorem rwp_load {l : Loc} {q} {v : Val} :
    ⊢ ▷ l ↦{q} some v -∗ (l ↦{q} some v -∗ Φ v) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(!v(#l)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_load $$ Hpt HΦ

/-- Rocq: `rswp_allocN` (with the cells as a sequence). -/
theorem rswp_allocN_seq {v : Val} {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) -∗
        Φ hl_val(#(.loc l))) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %m Hσ
  obtain ⟨l, hfresh⟩ := exists_fresh_block σ₁.heap n
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    exact ⟨[], .ofVal (.lit (.loc l)), σ₁.initHeap l n v, [], .allocNS n v σ₁ l hn hfresh⟩
  iintro %v₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i l' _hn' hfresh'
  imod genHeap_alloc_big (allocCells l' n.toNat v) σ₁.heap (allocCells_disjoint hfresh') $$ Hσ
    with ⟨Hσ, Hpts, Htok⟩
  imodintro
  isplit; itrivial
  ihave Hσ := genHeapInterp_eqv (.symm _ _ initHeap_heap_eq) $$ Hσ
  iframe Hσ
  iexists hl_val(#(BaseLit.loc _))
  isplit; ipureintro; rfl
  iapply HΦ
  iapply BI.BigSepL.bigSepL_sep_eqv.2
  isplitl [Hpts]
  · iapply allocCells_toSeq_pointsTo' $$ Hpts
  · iapply heapArray_toSeq_metaToken' $$ Htok
    grind

/-- Rocq: `rwp_allocN_seq`. -/
theorem rwp_allocN_seq {v : Val} {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) -∗
        Φ hl_val(#(.loc l))) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply rwp_no_step rfl
  iapply rswp_allocN_seq hn $$ HΦ

/-- Rocq: `rswp_alloc`. -/
theorem rswp_alloc {v : Val} :
    ⊢ (∀ l : Loc, l ↦ some v -∗ Φ hl_val(#(.loc l))) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(ref(&v)) Φ := by
  iintro HΦ
  iapply rswp_allocN_seq (by omega)
  iintro %l H
  iapply HΦ
  rw [Int.toNat_one, List.range_one, BI.BigSepL.bigSepL_singleton.to_eq]
  rw [show l + 0 = l from loc_add_zero l]
  icases H with ⟨H, -⟩
  iexact H

/-- Rocq: `rwp_alloc`. -/
theorem rwp_alloc {v : Val} :
    ⊢ (∀ l : Loc, l ↦ some v -∗ Φ hl_val(#(.loc l))) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(ref(&v)) Φ := by
  iintro HΦ
  iapply rwp_no_step rfl
  iapply rswp_alloc $$ HΦ

/-- Rocq: `rswp_store`. -/
theorem rswp_store {l : Loc} {v v' : Val} :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v -∗ Φ hl_val(#())) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(v(#l) ← &v) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    refine ⟨[], .val (.lit .unit), σ₁.initHeap l 1 v, [], BaseStep.storeS _ v' _ _ ?_⟩
    grind
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i v'' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists hl_val(#())
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_store`. -/
theorem rwp_store {l : Loc} {v v' : Val} :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v -∗ Φ hl_val(#())) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(v(#l) ← &v) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_store $$ Hpt HΦ

/-- Rocq: `rswp_cmpxchg_fail`. -/
theorem rswp_cmpXchg_fail {l : Loc} {q} {v' v1 v2 : Val} (hne : v' ≠ v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦{q} some v' -∗ (l ↦{q} some v' -∗ Φ hl_val((&v', #false))) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    refine ⟨[], hl(v((&v', #false))), σ₁, [], .cmpXchgS l v1 v2 v' σ₁ false Hpt hsafe ?_⟩
    simp [hne]
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = false := by simpa [hne] using Hdec.symm
  subst b
  imodintro
  simp only [show decide (v' = v1) = false by simp [hne], Bool.false_eq_true, ↓reduceIte]
  isplit; itrivial
  iframe Hσ
  iexists hl_val((&v', #false))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_cmpXchg_fail`. -/
theorem rwp_cmpXchg_fail {l : Loc} {q} {v' v1 v2 : Val} (hne : v' ≠ v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦{q} some v' -∗ (l ↦{q} some v' -∗ Φ hl_val((&v', #false))) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_cmpXchg_fail hne hsafe $$ Hpt HΦ

/-- Rocq: `rswp_cmpxchg_suc`. -/
theorem rswp_cmpXchg_suc {l : Loc} {v' v1 v2 : Val} (heq : v' = v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v2 -∗ Φ hl_val((&v', #true))) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    refine ⟨[], hl(v((&v', #true))), σ₁.initHeap l 1 v2, [],
      .cmpXchgS l v1 v2 v' σ₁ true Hpt hsafe ?_⟩
    simp [heq]
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = true := by simpa [heq] using Hdec.symm
  subst b
  simp only [show decide (v' = v1) = true by simp [heq], ↓reduceIte, Int.toNat_one,
    List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := .some v2) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists hl_val((&v', #true))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_cmpXchg_suc`. -/
theorem rwp_cmpXchg_suc {l : Loc} {v' v1 v2 : Val} (heq : v' = v1)
    (hsafe : v'.compareSafe v1) :
    ⊢ ▷ l ↦ some v' -∗ (l ↦ some v2 -∗ Φ hl_val((&v', #true))) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#l, &v1, &v2)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_cmpXchg_suc heq hsafe $$ Hpt HΦ

/-- Rocq: `rswp_faa`. -/
theorem rswp_faa {l : Loc} {i1 i2 : Int} :
    ⊢ ▷ l ↦ some hl_val(#i1) -∗ (l ↦ some hl_val(#(i1 + i2)) -∗ Φ hl_val(#i1)) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(faa(#l, #i2)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some (Val.lit (.int i1)))⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    refine ⟨[], .val (.lit (.int i1)), σ₁.initHeap l 1 (some hl_val(#(i1 + i2))), [],
      .faaS l i1 i2 σ₁ ?_⟩
    grind
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i i1' H
  obtain rfl : i1 = i1' := by
    simp only [Hpt, Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := some hl_val(#(i1 + i2))) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists Val.lit (.int i1)
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_faa`. -/
theorem rwp_faa {l : Loc} {i1 i2 : Int} :
    ⊢ ▷ l ↦ some hl_val(#i1) -∗ (l ↦ some hl_val(#(i1 + i2)) -∗ Φ hl_val(#i1)) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(faa(#l, #i2)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_faa $$ Hpt HΦ

/-- The exchange instruction. -/
theorem rswp_xchg {l : Loc} {v w : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ some w -∗ Φ v) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(xchg(#l, &w)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    refine ⟨[], .val v, σ₁.initHeap l 1 w, [], .xchgS l v w σ₁ ?_⟩
    grind
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep
  rename_i v' H
  obtain rfl : v = v' := by
    simp only [Hpt, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := some w) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_xchg`. -/
theorem rwp_xchg {l : Loc} {v w : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ some w -∗ Φ v) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(xchg(#l, &w)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_xchg $$ Hpt HΦ

/-- Deallocation. -/
theorem rswp_free {l : Loc} {v : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ none -∗ Φ hl_val(#())) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(free(#l)) Φ := by
  iintro >Hpt HΦ
  iapply rswp_lift_atomic_base_step_no_fork
  simp only [refStateInterp_eq]
  iintro %σ₁ %n Hσ
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  imodintro
  iapply laterN_intro
  isplitr
  · ipureintro
    exists [], hl_val(#()), σ₁.initHeap l 1 none, []
    refine BaseStep.freeS l v _ ?_
    grind
  iintro %e₂ %σ₂ %efs %κ' %Hstep
  rcases Hstep with ⟨v'', H⟩
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  rw [loc_add_zero']
  imod genHeap_update (v₂ := none) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  iframe Hσ
  iexists hl_val(#())
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

/-- Rocq: `rwp_free`. -/
theorem rwp_free {l : Loc} {v : Val} :
    ⊢ ▷ l ↦ some v -∗ (l ↦ none -∗ Φ hl_val(#())) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(free(#l)) Φ := by
  iintro Hpt HΦ
  iapply rwp_no_step rfl
  iapply rswp_free $$ Hpt HΦ

end rswp


/-! ## Adequacy -/

/-- The ghost state needed to allocate heap_lang's ghost state (Rocq: `heapPreG`). -/
class HeapLangTPreS (GF : BundledGFunctors) extends WsatGpreS GF where
  heap_pre : genHeapPreS Loc (Option Val) GF HeapF
  proph_pre : prophMapPreS ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangTPreS.heap_pre HeapLangTPreS.proph_pre

section Adequacy

variable {GF : BundledGFunctors}

/-- Adequacy of the heap_lang weakest precondition of Transfinite Iris (Rocq: `heap_adequacy`). -/
theorem heap_adequacy [SIdxTransfinite SI] [HeapLangTPreS GF] (s : Stuckness) (e : Exp)
    (σ : State) (φ : Val → Prop)
    (Hwp : ∀ [HeapLangTGS GF], ⊢ Iris.Transfinite.wp (GF := GF) s ⊤ e fun v => iprop(⌜φ v⌝)) :
    adequate s e σ (fun v _ => φ v) := by
  refine Iris.Transfinite.wp_adequacy (GF := GF) s e σ φ fun W κs => ?_
  imod genHeap_init (L := Loc) (V := Option Val) (GF := GF) (H := HeapF) σ.heap
    with ⟨%Gh, Hh, -, -⟩
  imod (ProphMap.init (H := ProphMapF) (GF := GF) κs σ.usedProphId) with ⟨%Gp, Hp⟩
  letI hl : HeapLangTGS GF := { toWsatGS := W, heap := Gh, proph := Gp }
  imodintro
  iexists (fun σ κs => iprop(genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId))
  iexists (fun _ => iprop(True))
  ihave #Hwp := (@Hwp hl)
  isplitl [Hh Hp]
  · isplitl [Hh]
    · iexact Hh
    · iexact Hp
  · iexact Hwp

end Adequacy

section SatAdd

/-- Rocq: `satisfiable_at_add`. -/
theorem satisfiableAt_add {E : CoPset} {P Q : IProp GF}
    (hsat : satisfiableAt E P) (hQ : ⊢ Q) : satisfiableAt E iprop(P ∗ Q) :=
  satisfiableAt_mono hsat (sep_emp.mpr.trans (sep_mono_right hQ))

/-- Rocq: `satisfiable_at_add'`. -/
theorem satisfiableAt_add' {E : CoPset} {Q : IProp GF}
    (hsat : satisfiableAt (GF := GF) E iprop(True)) (hQ : ⊢ Q) : satisfiableAt E Q :=
  satisfiableAt_mono hsat (Affine.affine.trans hQ)

end SatAdd

end Iris.HeapLang.Transfinite
