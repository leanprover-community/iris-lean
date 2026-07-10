/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.BI
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.ThreadPool
public import Iris.ProgramLogic.AbstractWeakestPre
public import Iris.ProgramLogic.AbstractLangCompleteness
public import Iris.Instances.Lib.Invariants
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris Iris.BI Iris.Algebra Std FromMathlib
open Iris.ProgramLogic.PrimStep
open Language Language.Notation

@[expose] public section

section AbstractEctxCompleteness

variable {Expr State Obs Val Ectx : Type _}
variable [EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF Expr H]

public def ectxLangCompletenessStmt (wp : AbstractWP Expr Val GF)
    (heap_inv : List Expr → State → IProp GF) (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State)
    (K : Ectx) (E : CoPset) : IProp GF := iprop%
  ⌜BaseStep.Reducible (e₁, σ)⌝ -∗
  (n ↪thread (EvContext.fill K e₁)) -∗
  heap_inv C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
  ((⌜Atomic .WeaklyAtomic e₁⌝ ∗
    (∀ Φ,
      (▷ ∀ κ v₂ σ' efs,
        ⌜PrimStep.primStep (e₁, σ) κ (ToVal.ofVal v₂, σ', efs)⌝ -∗
        isThread n (.own 1) (EvContext.fill K e₁) -∗
        tpInv C ==∗
        (heap_inv ((C.set n (EvContext.fill K (ToVal.ofVal v₂))) ++ efs) σ' -∗ Φ v₂) ∗
        [∗list] _i ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True))) -∗
      wp E e₁ Φ))
  ∨
  (heap_inv C σ ∗ tpInv C ∗ ∀ Ψ,
    (▷ ∀ e₂ efs,
      (∀ σ₁ C₁,
          heap_inv C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
          ∃ κ σ₁',
            ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗
            isThread n (.own 1) (EvContext.fill K e₁) ∗
            tpInv C₁ ∗
            heap_inv ((C₁.set n (EvContext.fill K e₂)) ++ efs) σ₁') ={⊤}=∗
        wp ⊤ e₂ Ψ ∗
        ([∗list] _j ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True)))) -∗
    wp ⊤ e₁ Ψ))

public class AbstractEctxLangCompletenessGen
    (wp : AbstractWP Expr Val GF) [BindAbstractWP wp] where
  heap_inv : List Expr → State → IProp GF
  heap_inv_timeless (C : List Expr) (σ : State) : Timeless (heap_inv C σ)
  ectx_lang_completeness (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (K : Ectx) (E : CoPset) :
    ⊢ ectxLangCompletenessStmt wp heap_inv n C e₁ σ K E

attribute [instance] AbstractEctxLangCompletenessGen.heap_inv_timeless

end AbstractEctxCompleteness

/-! ### Lifting the ectx-level soundness equation to the prim level. -/

section Lifting

variable {Expr State Obs Val Ectx : Type _}
variable [EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF Expr H]
variable {wp : AbstractWP Expr Val GF}
variable [BWP : BindAbstractWP wp]
variable [AEC : AbstractEctxLangCompletenessGen wp]

theorem weakestpre_ectx_to_prim_completeness (n : Nat) (C : List Expr) (e₁ : Expr)
    (σ : State) (E : CoPset) :
    ⊢ abstractECTXLangComplete (TI := TI) wp AEC.heap_inv n C e₁ σ E := by
  iintro %Hred Htok ⟨Hheap, Htp, %Hsafe⟩
  obtain ⟨κ, e', σ', efs, hstep⟩ := Hred
  obtain @⟨e₁', e₂', K, Hbase⟩ := hstep
  have Hbred : BaseStep.Reducible (e₁', σ) := ⟨κ, e₂', σ', efs, Hbase⟩
  have key := AEC.ectx_lang_completeness n C e₁' σ K E
  unfold ectxLangCompletenessStmt at key
  imod key $$ %Hbred Htok [Hheap Htp] with (⟨%Hatom, HH⟩ | ⟨Hheap, Htp, HH⟩)
  · iframe Hheap Htp %Hsafe
  · clear key
    imodintro
    ileft
    iexists (fill (Expr := Expr) K), e₁'
    have Hctx : Context (fill (Expr := Expr) K) := inferInstance
    have Heq : fill (Expr := Expr) K e₁' = fill (Expr := Expr) K e₁' := rfl
    have Hnv : ToVal.toVal e₁' = none := EctxLanguage.val_stuck Hbase
    iframe %Hctx %Heq %Hnv %Hatom
    iintro %Ψ Hpre
    iapply HH $$ Hpre
  · clear key
    imodintro
    iright
    iframe Hheap Htp
    iintro %Ψ Hc
    iapply (BWP.wp_bind (K := fill (Expr := Expr) K) (e := e₁') (Φ := Ψ)).1
    iapply HH
    inext
    iintro %e₂ %efs H
    ihave Hprem : iprop(∀ σ₁ C₁,
        AEC.heap_inv C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
          ∃ κ σ₁', ⌜PrimSteps (fill (Expr := Expr) K e₁') σ₁ κ (fill (Expr := Expr) K e₂) σ₁' efs⌝ ∗
            (n ↪thread fill (Expr := Expr) K e₁') ∗ tpInv C₁ ∗
            AEC.heap_inv (C₁.set n (fill (Expr := Expr) K e₂) ++ efs) σ₁') $$ [H]
    · iintro %σ₁ %C₁ ⟨Hi, Htp1, %Hs⟩
      imod H $$ [Hi Htp1] with ⟨%κ', %σ₁', %Hps, Htok2, Htp1', Hhp⟩
      · iframe Hi Htp1 %Hs
      imodintro
      iexists κ', σ₁'
      iframe Htok2 Htp1' Hhp
      ipureintro
      exact Hps.fill
    imod Hc $$ Hprem with ⟨Hwp, Hlist⟩
    imodintro
    iframe
    iapply (BWP.wp_bind (K := fill (Expr := Expr) K) (e := e₂) (Φ := Ψ)).2 $$ Hwp

instance abstract_ectx_to_completeness :
    AbstractLangCompletenessGen wp where
  heap_inv := AEC.heap_inv
  heap_inv_timeless := AEC.heap_inv_timeless
  lang_completeness {n C e₁ σ E} := weakestpre_ectx_to_prim_completeness n C e₁ σ E

end Lifting

end

end Iris.ProgramLogic
