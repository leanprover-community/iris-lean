/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.BI
public import Iris.ProofMode
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.ThreadPool
public import Iris.ProgramLogic.AbstractWeakestPre
public import Iris.Instances.Lib.Invariants
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris Iris.BI Iris.Algebra Std FromMathlib
open Iris.ProgramLogic.PrimStep
open Language Language.Notation

@[expose] public section

section AbstractCompleteness

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]

public def abstractECTXLangComplete (wp : AbstractWP Expr Val GF) (I : List Expr → State → IProp GF) :
    IProp GF := iprop%
  ∀ n C e₁ σ E ,
   ⌜PrimStep.Reducible (e₁, σ)⌝ -∗ (n ↪thread e₁) -∗ I C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
   ((∃ (K : Expr → Expr) (e₁' : Expr),
       ⌜Context K⌝ ∗ ⌜e₁ = K e₁'⌝ ∗ ⌜ToVal.toVal e₁' = none⌝ ∗ ⌜Atomic .WeaklyAtomic e₁'⌝ ∗
       ∀ Ψ,
         (▷ ∀ κ v₂ σ' efs,
           ⌜PrimStep.primStep (e₁', σ) κ ((ToVal.ofVal v₂ : Expr), σ', efs)⌝ -∗
           (n ↪thread e₁) -∗
           tpInv C ==∗
           (I ((C.set n (K (ToVal.ofVal v₂))) ++ efs) σ' -∗ Ψ v₂) ∗
           [∗list] _i ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop% True)) -∗
         wp E e₁' Ψ) ∨
     (I C σ ∗ tpInv C ∗ ∀ Ψ,
       (▷ ∀ e₂ efs,
         (∀ σ₁ C₁, I C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
            ∃ κ σ₁',
              ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗ (n ↪thread e₁) ∗ tpInv C₁ ∗
              I ((C₁.set n e₂) ++ efs) σ₁') ={⊤}=∗
           wp ⊤ e₂ Ψ ∗ ([∗list] _j ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop% True))) -∗
       wp ⊤ e₁ Ψ))

/-- A weakest precondition for a Language is complete -/
public class AbstractLangCompletenessGen
    (wp : AbstractWP Expr Val GF) [LawfulAbstractWP wp] where
  heap_inv : List Expr → State → IProp GF
  heap_inv_timeless (C : List Expr) (σ : State) : Timeless (heap_inv C σ)
  lang_completeness : ⊢ abstractECTXLangComplete wp heap_inv

attribute [instance] AbstractLangCompletenessGen.heap_inv_timeless

end AbstractCompleteness

section Completeness

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} {HLC : HasLC} [IrisGS_gen HLC Expr GF]
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable [TI : TpinvGS GF F Expr H]
variable {wp : AbstractWP Expr Val GF}
variable [LawfulAbstractWP wp] [InvOpenAbstractWP wp]
variable [ACG : AbstractLangCompletenessGen wp]
variable [CInvG F GF]

/-- Namespace under which the completeness invariant lives. -/
public def completenessN : Namespace := nroot .@ (1 : Pos)

/-- The configuration invariant: ownership of a current configuration
(thread pool + state) reachable from the initial one, with the heap and
thread-pool invariants. -/
public def cfgInv (Cini : List Expr × State) (f : Forking) : IProp GF := iprop%
  ∃ cfg : List Expr × State,
    ACG.heap_inv cfg.1 cfg.2 ∗ tpInv cfg.1 ∗ ⌜cfgSafeForking cfg f ∧ Cini -·->ₜₚ* cfg ⌝

/-- Cancelable invariant package wrapping `cfgInv`. -/
public def isCcfg (Cini : List Expr × State) (f : Forking) (γ : GName) : IProp GF :=
  CancelableInvariant.cinv (F := F) completenessN γ (cfgInv (wp := wp) Cini f)

/-- The core Löb-induction lemma. Internal infrastructure consumed by the
top-level corollaries below. -/
theorem weakestpre_completeness
    (Cini : List Expr × State) (f : Forking) (γ : GName) (q : Frac F)
    (n : Nat) (e : Expr) :
    isCcfg (TI := TI) (wp := wp) Cini f γ -∗
    CancelableInvariant.own γ q -∗
    isThread (TI := TI) n (.own 1) e -∗
    wp ⊤ e (fun v => iprop%
        isThread (TI := TI) n (.own 1) (ToVal.ofVal v) ∗
        ∃ q' : Frac F, CancelableInvariant.own γ q' ∗ ⌜f = .doesNotFork → q = q'⌝) := by
  sorry

/-- **Top-level theorem**: `adequate` gives a WP with a pure postcondition.
This is the entry point consumed by the heap-lang case study. Stated on the
generic `AbstractLangCompletenessGen`, carrying `[InvOpenAbstractWP wp]`
(mirrors Rocq's `abstract_weakestpre_gen_magic` hypothesis). -/
theorem weakestpre_sem_completeness
    (e : Expr) (σ : State) (φ : Val → Prop)
    (Hade : adequate .NotStuck e σ (fun v _ => φ v)) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v => iprop% ⌜φ v⌝) := by
  sorry

/-- Strong nofork variant. -/
theorem weakestpre_sem_completeness_nofork_strong
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State,
          tpInv (TI := TI) [ToVal.ofVal v] ∗
          isThread (TI := TI) 0 (.own 1) (ToVal.ofVal v) ∗
          ACG.heap_inv [ToVal.ofVal v] σ' ∗
          ⌜φ v σ'⌝) := by
  sorry

/-- User-facing nofork variant. -/
theorem weakestpre_sem_completeness_nofork
    (e : Expr) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork .NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ tpInvIni (TI := TI) -∗
      ACG.heap_inv [e] σ -∗
      wp ⊤ e (fun v =>
        iprop% ∃ σ' : State, ACG.heap_inv [ToVal.ofVal v] σ' ∗ ⌜φ v σ'⌝) := by
  sorry

end Completeness

end

end Iris.ProgramLogic
