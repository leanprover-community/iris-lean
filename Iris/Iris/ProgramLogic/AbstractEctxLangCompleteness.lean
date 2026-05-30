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
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]

/-- The body of the `ectx_lang_completeness` field of
`AbstractEctxLangCompletenessGen`; mirrors `ectx_lang_completeness` in
`framework/abstract/abstract_ectx_lang_completeness.v` lines 13–31. -/
public def ectxLangCompletenessStmt
    [TI : TpinvGS GF F Expr H]
    (wp : AbstractWP Expr Val GF)
    (heap_inv : List Expr → State → IProp GF)
    (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (K : Ectx) (E : CoPset) :
    IProp GF :=
  iprop(
    isThread n (.own 1) (EvContext.fill K e₁) -∗
    heap_inv C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
    ((⌜Iris.ProgramLogic.Language.Atomic Atomicity.WeaklyAtomic e₁⌝ ∗
      (∀ Φ,
        (▷ ∀ κ v₂ σ' efs,
          ⌜PrimStep.primStep (e₁, σ) κ ((ToVal.ofVal v₂ : Expr), σ', efs)⌝ -∗
          isThread n (.own 1) (EvContext.fill K e₁) -∗
          tpInv C ==∗
          (heap_inv ((C.set n (EvContext.fill K (ToVal.ofVal v₂))) ++ efs) σ' -∗
            Φ v₂) ∗
          [∗list] i ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True))) -∗
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
          ([∗list] j ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True)))) -∗
      wp ⊤ e₁ Ψ)))

/-- *Abstract ectx-completeness theory*: the ectx-language specialization of
`AbstractLangCompletenessGen`. The soundness equation `ectx_lang_completeness`
is phrased for base steps rather than prim steps. -/
public class AbstractEctxLangCompletenessGen
    (wp : AbstractWP Expr Val GF) [BindAbstractWP wp] where
  heap_inv : List Expr → State → IProp GF
  heap_inv_timeless (C : List Expr) (σ : State) : Timeless (heap_inv C σ)
  ectx_lang_completeness
      (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (K : Ectx) (E : CoPset)
      (_ : BaseStep.Reducible (e₁, σ)) :
    ⊢ ectxLangCompletenessStmt wp heap_inv n C e₁ σ K E

attribute [instance] AbstractEctxLangCompletenessGen.heap_inv_timeless

end AbstractEctxCompleteness

/-! ### Lifting and top-level completeness theorems. -/

section Lifting

variable {Expr State Obs Val Ectx : Type _}
variable [EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]
variable {wp : AbstractWP Expr Val GF}
variable [BindAbstractWP wp] [InvOpenAbstractWP wp]
variable [AEC : AbstractEctxLangCompletenessGen wp]
variable [CInvG F GF]

/-- Lift the ectx-level reduction soundness equation to a prim-level one.
Mirrors `weakestpre_ectx_to_prim_completeness` in
`framework/abstract/abstract_ectx_lang_completeness.v` lines 37–53. -/
theorem weakestpre_ectx_to_prim_completeness
    (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (E : CoPset)
    (_ : PrimStep.Reducible (e₁, σ)) :
    ⊢ langCompletenessStmt (TI := TI) wp AEC.heap_inv n C e₁ σ E := by
  sorry

/-- Every `AbstractEctxLangCompletenessGen` gives an
`AbstractLangCompletenessGen`. -/
instance abstract_ectx_to_completeness :
    AbstractLangCompletenessGen wp where
  heap_inv := AEC.heap_inv
  heap_inv_timeless C σ := AEC.heap_inv_timeless C σ
  lang_completeness n C e₁ σ E red := by
    exact weakestpre_ectx_to_prim_completeness n C e₁ σ E red

/-- **Top-level theorem**: `adequate` gives a WP with a pure postcondition.
This is the entry point consumed by the heap-lang case study. -/
theorem weakestpre_sem_completeness
    (e : Expr) (σ : State) (φ : Val → Prop)
    (Hade : adequate .NotStuck e σ (fun v _ => φ v)) :
    ⊢ tpInvIni (TI := TI) -∗
      AEC.heap_inv [e] σ -∗
      wp ⊤ e (fun v => iprop% ⌜φ v⌝) := by
  sorry

/-- Strong nofork variant. -/
theorem weakestpre_sem_completeness_nofork_strong
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      AEC.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State,
          tpInv (TI := TI) [ToVal.ofVal v] ∗
          isThread (TI := TI) 0 (.own 1) (ToVal.ofVal v) ∗
          AEC.heap_inv [ToVal.ofVal v] σ' ∗
          ⌜φ v σ'⌝) := by
  sorry

/-- User-facing nofork variant. -/
theorem weakestpre_sem_completeness_nofork
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      AEC.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State, AEC.heap_inv [ToVal.ofVal v] σ' ∗ ⌜φ v σ'⌝) := by
  sorry

end Lifting

end

end Iris.ProgramLogic
