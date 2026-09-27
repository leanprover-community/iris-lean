/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.Termination.Derived

/-! # Adequacy of the termination logic

This file ports `theories/examples/termination/adequacy.v` of Transfinite Iris: a heap_lang
program `e` that is verified in the sequential termination logic, for some budget `tc α` of time
credits, is strongly normalizing (`heap_lang_ref_adequacy`).

The ghost state is allocated from the pre-instances with explicit ghost names; the choice of the
names uses the existential property of satisfiability, for which `SIdxLarge.{0} SI` follows from
`SIdxLarge.{w + 1} SI` (`SIdxLarge.down`).
-/

@[expose] public noncomputable section

universe w v u

namespace Iris.Transfinite.Termination

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Ordinal Relation

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

variable {GF : BundledGFunctors.{u}}

/-- Allocating ghost state with a name chosen by the existential property. -/
theorem satisfiableAt_alloc [W : WsatGS GF] {X : Type} [SIdxLarge.{0} SI] {P : IProp GF}
    {Q : X → IProp GF} (h : satisfiableAt ⊤ P) (hQ : ⊢ |==> ∃ x, Q x) :
    ∃ x, satisfiableAt ⊤ iprop(P ∗ Q x) := by
  refine satisfiableAt_exists (satisfiableAt_fupd (E1 := ⊤) (satisfiableAt_mono h ?_))
  iintro HP
  imod hQ with ⟨%x, HQ⟩
  imodintro
  iexists x
  iframe

/-- Rocq: `heap_lang_ref_adequacy`. -/
theorem heap_lang_ref_adequacy [hL : SIdxLarge.{w + 1} SI] [Hpre : HeapLangTPreS GF]
    [Hna : NaInvG GF]
    [Etc : ElemG GF (constOFU.{max u v} (Auth (OrdCam.{w} SI)))] (e : Exp) (σ : State)
    (Hwp : ∀ [Hh : HeapLangTGS GF] [Hs : SeqG GF] [Ht : TcGS.{w} GF],
      ⊢ ∃ α : Ordinal.{w}, tc (G := Ht) α -∗
        tseq.{w} (Hheap := Hh) (Htc := Ht) (Hseq := Hs) ⊤ e fun _ => iprop(True)) :
    StronglyNormalizing ErasedStep ([e], σ) := by
  -- (local instances are tried newest first, without backtracking on universe levels)
  have : SIdxLarge.{0} SI := SIdxLarge.down.{0, w + 1}
  -- allocate world satisfaction
  have h0 : UPred.satisfiable iprop(∃ γ γe γd : GName,
      wsat (W := WsatGS.ofNames (GF := GF) γ γe γd) ∗
        ownE (W := WsatGS.ofNames (GF := GF) γ γe γd) ⊤) :=
    UPred.satisfiable_bupd (UPred.satisfiable_intro (true_emp.mp.trans wsat_alloc_names))
  obtain ⟨γ, h0⟩ := UPred.satisfiable_exists h0
  obtain ⟨γe, h0⟩ := UPred.satisfiable_exists h0
  obtain ⟨γd, h0⟩ := UPred.satisfiable_exists h0
  let W : WsatGS GF := WsatGS.ofNames γ γe γd
  have h1 : satisfiableAt ⊤ iprop(True) :=
    UPred.satisfiable_mono h0 (sep_mono_right sep_emp.mpr |>.trans
      (sep_mono_right (sep_mono_right true_intro)))
  -- allocate the heap
  obtain ⟨γh, h2⟩ := satisfiableAt_alloc h1 (genHeap_init_names (L := Loc) (V := Option Val)
    (H := HeapF) (GF := GF) σ.heap)
  obtain ⟨γm, h2⟩ := satisfiableAt_exists (P := fun γm : GName =>
      genHeapInterp (G := (⟨γh, γm⟩ : genHeapGS Loc (Option Val) GF HeapF)) σ.heap)
    (satisfiableAt_mono h2 (by
      iintro ⟨-, %γm, Hh, -, -⟩
      iexists γm
      iexact Hh))
  let G : genHeapGS Loc (Option Val) GF HeapF := ⟨γh, γm⟩
  let Hheap : HeapLangTGS GF := { toWsatGS := W, heap := G, proph := ⟨0⟩ }
  -- allocate the pool of non-atomic invariants
  obtain ⟨p, h3⟩ := satisfiableAt_alloc h2 (NonAtomicInvariant.alloc (GF := GF))
  let Hseq : SeqG GF := { toNaInvG := Hna, name := p }
  -- allocate the time credits
  obtain ⟨γc, h4⟩ := satisfiableAt_alloc h3 (iOwn_alloc (E := Etc)
    (ULift.up ((● (⟨0⟩ : OrdCam.{w} SI)) • ◯ (⟨0⟩ : OrdCam.{w} SI)))
    (Auth.auth_both_valid_discrete.mpr ⟨CMRA.inc_refl _, trivial⟩))
  let Htc : TcGS.{w} GF := { elem := Etc, name := γc }
  -- choose the budget
  have h5 := satisfiableAt_add h4 (@Hwp Hheap Hseq Htc)
  obtain ⟨α, h5⟩ := have := hL
    satisfiableAt_exists (X := Ordinal.{w}) (P := fun α : Ordinal.{w} => iprop(
      (((genHeapInterp σ.heap ∗ NonAtomicInvariant.own p ⊤) ∗
        iOwn (E := Etc) γc (ULift.up ((● (⟨0⟩ : OrdCam.{w} SI)) • ◯ (⟨0⟩ : OrdCam.{w} SI)))) ∗
      (tc (GF := GF) α -∗ tseq.{w} ⊤ e fun _ => iprop(True)))))
    (satisfiableAt_mono h5 (by
    iintro ⟨H, %α, Hα⟩
    iexists α
    iframe))
  -- set the budget to `α` and run the program
  have h6 : satisfiableAt ⊤ iprop(tcAuth (GF := GF) α ∗
      heapRefIrisGS.refStateInterp σ 0 ∗
      rwp (src := tcSource.{w}) (ι := heapRefIrisGS) .NotStuck ⊤ e fun _ =>
        iprop(NonAtomicInvariant.own Hseq.name ⊤ ∗ True)) := by
    refine satisfiableAt_fupd (E1 := ⊤) (satisfiableAt_mono h5 ?_)
    iintro ⟨⟨⟨Hh, Hna⟩, Hc⟩, Hwp⟩
    have hlu : ((⟨0⟩ : OrdCam.{w} SI), (⟨0⟩ : OrdCam.{w} SI)) ~l~> (⟨α⟩, ⟨α⟩) := by
      refine (local_update_unital_discrete _ _ _ _).mpr fun z _ hz => ⟨trivial, ?_⟩
      have hz' : (0 : Ordinal.{w}) = 0 ♯ z.o := congrArg OrdCam.o hz
      have : z.o = 0 := (nadd_left_cancel (hz'.symm.trans (nadd_zero 0).symm))
      exact OrdCam.ext (by rw [OrdCam.op_o, this, nadd_zero])
    imod iOwn_update (ULift.update (Auth.auth_update hlu)) $$ Hc with Hc
    icases (iOwn_op (E := Etc)).mp $$ Hc with ⟨Ha, Hf⟩
    ihave Hwp := Hwp $$ [Hf]
    · unfold tc
      iexact Hf
    unfold tseq seq
    ihave Hwp := Hwp $$ Hna
    imodintro
    isplitl [Ha]
    · unfold tcAuth
      iexact Ha
    isplitl [Hh]
    · rw [refStateInterp_eq]
      iexact Hh
    iexact Hwp
  have := hL
  exact rwp_sn_preservation (src := tcSource.{w}) (tcSource_sn α) h6

end Iris.Transfinite.Termination
