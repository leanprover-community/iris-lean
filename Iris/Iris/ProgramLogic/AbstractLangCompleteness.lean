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

/-- The body of the abstract `lang_completeness` field, factored out so we
can write a long iprop without confusing Lean's class-field parser. Mirrors
the conclusion of `abstract_lang_completeness_gen.lang_completeness` in
`framework/abstract/abstract_lang_completeness.v` lines 14–33. -/
public def langCompletenessStmt
    [TI : TpinvGS GF F Expr H]
    (wp : AbstractWP Expr Val GF)
    (heap_inv : List Expr → State → IProp GF)
    (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (E : CoPset) : IProp GF :=
  iprop(
    isThread n (.own 1) e₁ -∗
    heap_inv C σ ∗ tpInv C ∗ ⌜cfgSafe (C, σ)⌝ ={E}=∗
    ((∃ (K : Expr → Expr) (e₁' : Expr),
        ⌜Context K⌝ ∗ ⌜e₁ = K e₁'⌝ ∗ ⌜ToVal.toVal e₁' = none⌝ ∗
        ⌜Atomic Atomicity.WeaklyAtomic e₁'⌝ ∗
        ∀ Ψ,
          (▷ ∀ κ v₂ σ' efs,
            ⌜PrimStep.primStep (e₁', σ) κ ((ToVal.ofVal v₂ : Expr), σ', efs)⌝ -∗
            isThread n (.own 1) e₁ -∗
            tpInv C ==∗
            (heap_inv ((C.set n (K (ToVal.ofVal v₂))) ++ efs) σ' -∗ Ψ v₂) ∗
            [∗list] i ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True))) -∗
          wp E e₁' Ψ)
      ∨
      (heap_inv C σ ∗ tpInv C ∗ ∀ Ψ,
        (▷ ∀ e₂ efs,
          (∀ σ₁ C₁,
              heap_inv C₁ σ₁ ∗ tpInv C₁ ∗ ⌜cfgSafe (C₁, σ₁)⌝ ={E}=∗
              ∃ κ σ₁',
                ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗
                isThread n (.own 1) e₁ ∗
                tpInv C₁ ∗
                heap_inv ((C₁.set n e₂) ++ efs) σ₁') ={⊤}=∗
            wp ⊤ e₂ Ψ ∗
            ([∗list] j ↦ etp ∈ efs, wp ⊤ etp (fun (_ : Val) => iprop(True)))) -∗
        wp ⊤ e₁ Ψ)))

/-- An *abstract completeness theory* for a language and an abstract WP `wp`:
ships a heap invariant `heap_inv` together with a soundness equation showing
that, under suitable conditions, an arbitrary thread can take a step (or open
the heap state for a sequence of steps) while preserving the WP.

Mirrors `abstract_lang_completeness_gen` from
`framework/abstract/abstract_lang_completeness.v`. -/
public class AbstractLangCompletenessGen
    (wp : AbstractWP Expr Val GF) [LawfulAbstractWP wp] where
  heap_inv : List Expr → State → IProp GF
  heap_inv_timeless (C : List Expr) (σ : State) : Timeless (heap_inv C σ)
  /-- The big disjunctive soundness equation. -/
  lang_completeness
      (n : Nat) (C : List Expr) (e₁ : Expr) (σ : State) (E : CoPset)
      (_ : PrimStep.Reducible (e₁, σ)) :
    ⊢ langCompletenessStmt wp heap_inv n C e₁ σ E

attribute [instance] AbstractLangCompletenessGen.heap_inv_timeless

end AbstractCompleteness

/-! ### The Löb-induction proof and its three top-level corollaries. -/

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
public def cfgInv (Cini : List Expr × State) (f : Forking) : IProp GF :=
  iprop(∃ cfg : List Expr × State,
    ACG.heap_inv cfg.1 cfg.2 ∗
    tpInv cfg.1 ∗
    ⌜cfgSafeForking cfg f ∧
      FromMathlib.Relation.ReflTransGen Language.ErasedStep Cini cfg⌝)

/-- Cancelable invariant package wrapping `cfgInv`. -/
public def isCcfg (Cini : List Expr × State) (f : Forking) (γ : GName) :
    IProp GF :=
  CancelableInvariant.cinv (F := F) completenessN γ (cfgInv (wp := wp) Cini f)

/-- The core Löb-induction lemma. Internal infrastructure consumed by the
top-level theorems in `AbstractEctxLangCompleteness.lean`. -/
theorem weakestpre_completeness
    (Cini : List Expr × State) (f : Forking) (γ : GName) (q : Frac F)
    (n : Nat) (e : Expr) :
    isCcfg (TI := TI) (wp := wp) Cini f γ -∗
    CancelableInvariant.own γ q -∗
    isThread (TI := TI) n (.own 1) e -∗
    wp ⊤ e (fun v =>
      iprop% isThread (TI := TI) n (.own 1) (ToVal.ofVal v) ∗
        ∃ q' : Frac F, CancelableInvariant.own γ q' ∗
          ⌜f = .doesNotFork → q = q'⌝) := by
  sorry

end Completeness

end

end Iris.ProgramLogic
