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

/-- The body of the `ectx_lang_completeness` field of
`AbstractEctxLangCompletenessGen`; mirrors `ectx_lang_completeness` in
`framework/abstract/abstract_ectx_lang_completeness.v` lines 13–31. -/
public def ectxLangCompletenessStmt [TI : TpinvGS GF Expr H] (wp : AbstractWP Expr Val GF)
    (heap_inv : List Expr → State → IProp GF) (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State)
    (K : Ectx) (E : CoPset) : IProp GF := iprop%
  ⌜BaseStep.Reducible (e₁, σ)⌝ -∗
  (n ↪thread (EvContext.fill K e₁)) -∗
  heap_inv C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
  ((⌜Iris.ProgramLogic.Language.Atomic Atomicity.WeaklyAtomic e₁⌝ ∗
    (∀ Φ,
      (▷ ∀ κ v₂ σ' efs,
        ⌜PrimStep.primStep (e₁, σ) κ ((ToVal.ofVal v₂ : Expr), σ', efs)⌝ -∗
        isThread n (.own 1) (EvContext.fill K e₁) -∗
        tpInv C ==∗
        (heap_inv ((C.set n (EvContext.fill K (ToVal.ofVal v₂))) ++ efs) σ' -∗
          Φ v₂) ∗
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

/-- *Abstract ectx-completeness theory*: the ectx-language specialization of
`AbstractLangCompletenessGen`. The soundness equation `ectx_lang_completeness`
is phrased for base steps rather than prim steps. -/
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
variable [BindAbstractWP wp] [InvOpenAbstractWP wp]
variable [AEC : AbstractEctxLangCompletenessGen wp]
variable [CInvG Qp GF]

omit [InvOpenAbstractWP wp] [CInvG Qp GF] in
/-- Lift the ectx-level reduction soundness equation to a prim-level one.
Mirrors `weakestpre_ectx_to_prim_completeness` in
`framework/abstract/abstract_ectx_lang_completeness.v` lines 37–53. -/
theorem weakestpre_ectx_to_prim_completeness :
  ∀ (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (E : CoPset),
    ⊢ abstractECTXLangComplete (TI := TI) wp AEC.heap_inv n C e₁ σ E := by
  iintro %n %C %e₁ %σ %E %Hred Htok ⟨Hheap, Htp, %Hsafe⟩
  obtain ⟨κ, e', σ', efs, hstep⟩ := Hred
  obtain ⟨Hbase⟩ := hstep
  rename_i e₁' e₂' K
  have Hbred : BaseStep.Reducible (e₁', σ) := ⟨κ, e₂', σ', efs, Hbase⟩
  have key := AEC.ectx_lang_completeness (wp := wp) n C e₁' σ K E
  unfold ectxLangCompletenessStmt at key
  imod key $$ %Hbred Htok [Hheap Htp]
    with (⟨%Hatom, HH⟩ | ⟨Hheap, Htp, HH⟩)
  · iframe Hheap Htp
    ipureintro; exact Hsafe
  · -- Atomic redex: package the context `fill K` and forward the magic premise.
    imodintro
    ileft
    iexists (fill (Expr := Expr) K), e₁'
    have Hctx : Context (fill (Expr := Expr) K) := inferInstance
    have Heq : fill (Expr := Expr) K e₁' = fill (Expr := Expr) K e₁' := rfl
    have Hnv : ToVal.toVal e₁' = none := EctxLanguage.val_stuck Hbase
    iframe %Hctx %Heq %Hnv %Hatom
    iintro %Ψ Hpre
    iapply HH $$ Hpre
  · -- Non-atomic redex: reduce the prim-level WP to the ectx-level one via `wp_bind`.
    imodintro
    iright
    iframe Hheap Htp
    iintro %Ψ Hc
    iapply ((‹BindAbstractWP wp›).wp_bind (K := fill (Expr := Expr) K) (e := e₁') (Φ := Ψ)).1
    iapply HH
    inext
    iintro %e₂ %efs H
    -- Lift the ectx-level step `H` (on the redex `e₁'`) to a prim-level step under `fill K`.
    ihave Hprem : iprop(∀ σ₁ C₁,
        AEC.heap_inv C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
          ∃ κ σ₁', ⌜PrimSteps (fill (Expr := Expr) K e₁') σ₁ κ (fill (Expr := Expr) K e₂) σ₁' efs⌝ ∗
            (n ↪thread fill (Expr := Expr) K e₁') ∗ tpInv C₁ ∗
            AEC.heap_inv (C₁.set n (fill (Expr := Expr) K e₂) ++ efs) σ₁') $$ [H]
    · iintro %σ₁ %C₁ ⟨Hi, Htp1, %Hs⟩
      imod H $$ [Hi Htp1] with ⟨%κ', %σ₁', %Hps, Htok2, Htp1', Hhp⟩
      · iframe Hi Htp1
        ipureintro; exact Hs
      imodintro
      iexists κ', σ₁'
      iframe Htok2 Htp1' Hhp
      ipureintro
      exact Hps.fill
    imod Hc $$ Hprem with ⟨Hwp, Hlist⟩
    imodintro
    isplitl [Hwp]
    · iapply ((‹BindAbstractWP wp›).wp_bind (K := fill (Expr := Expr) K) (e := e₂) (Φ := Ψ)).2 $$ Hwp
    · iexact Hlist

/-- Every `AbstractEctxLangCompletenessGen` gives an
`AbstractLangCompletenessGen`. -/
instance abstract_ectx_to_completeness :
    AbstractLangCompletenessGen wp where
  heap_inv := AEC.heap_inv
  heap_inv_timeless C σ := AEC.heap_inv_timeless C σ
  lang_completeness := weakestpre_ectx_to_prim_completeness _ _ _ _ _

end Lifting

end

end Iris.ProgramLogic
