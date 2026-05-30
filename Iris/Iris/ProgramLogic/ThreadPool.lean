/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.ProgramLogic.Adequacy
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.FromMathlib

namespace Iris.ProgramLogic

open Iris.ProgramLogic.PrimStep
open Language Language.Notation Relation

@[expose] public section

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

/-! ### Multi-step prim reduction on a single thread -/

/-- Transitive closure of `primStep` with accumulated observations and forks. -/
inductive PrimSteps : Expr → State → List Obs → Expr → State → List Expr → Prop where
  | once {e₁ σ₁ κ e₂ σ₂ efs} :
      (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → PrimSteps e₁ σ₁ κ e₂ σ₂ efs
  | next {e₁ σ₁ κ₁ e₂ σ₂ efs₁ κ₂ e₃ σ₃ efs₂} :
      (e₁, σ₁) -<κ₁>-> (e₂, σ₂, efs₁) →
      PrimSteps e₂ σ₂ κ₂ e₃ σ₃ efs₂ →
      PrimSteps e₁ σ₁ (κ₁ ++ κ₂) e₃ σ₃ (efs₁ ++ efs₂)

/-! ### Configuration safety -/

inductive Forking where
  | doesFork
  | doesNotFork

/-- Every thread in the pool is not stuck at the current state. -/
def cfgNotStuck (C : List Expr × State) : Prop :=
  ∀ e ∈ C.1, NotStuck (e, C.2)

/-- If we declared the configuration `DoesNotFork`, every primitive step
of every thread emits empty forks. -/
def cfgForking (C : List Expr × State) (f : Forking) : Prop :=
  f = .doesNotFork →
    ∀ e ∈ C.1, ∀ {e' σ' κ efs},
      (e, C.2) -<κ>-> (e', σ', efs) → efs = []

/-- The configuration is safe under the given forking discipline:
every reachable configuration is not stuck and respects the forking constraint. -/
def cfgSafeForking (C : List Expr × State) (f : Forking) : Prop :=
  ∀ C₂, (C -·->ₜₚ* C₂) → cfgNotStuck C₂ ∧ cfgForking C₂ f

/-- The configuration is safe: every reachable configuration is not stuck. -/
def cfgSafe (C : List Expr × State) : Prop :=
  ∀ C₂, (C -·->ₜₚ* C₂) → cfgNotStuck C₂

theorem cfgSafe_of_cfgSafeForking {C : List Expr × State} {f : Forking}
    (H : cfgSafeForking C f) : cfgSafe C := by
  sorry

theorem primSteps_fill {K : Expr → Expr} [Context K]
    {e₁ σ₁ κ e₂ σ₂ efs} (_ : PrimSteps e₁ σ₁ κ e₂ σ₂ efs) :
    PrimSteps (K e₁) σ₁ κ (K e₂) σ₂ efs := by
  sorry

theorem cfg_step {tp : List Expr} {σ : State} {n : Nat} {e : Expr}
    {κ : List Obs} {e' : Expr} {σ' : State} {efs : List Expr}
    (Hlu : tp[n]? = some e) (Hprim : (e, σ) -<κ>-> (e', σ', efs)) :
    Step (tp, σ) κ (tp.set n e' ++ efs, σ') := by
  sorry

theorem cfg_stepsTc {tp : List Expr} {σ : State} {n e κ e' σ' efs}
    (Hlu : tp[n]? = some e) (Hprim : PrimSteps e σ κ e' σ' efs) :
    Relation.TransGen ErasedStep (tp, σ) (tp.set n e' ++ efs, σ') := by
  sorry

theorem cfg_steps {tp : List Expr} {σ : State} {n e κ e' σ' efs}
    (Hlu : tp[n]? = some e) (Hprim : PrimSteps e σ κ e' σ' efs) :
    (tp, σ) -·->ₜₚ* (tp.set n e' ++ efs, σ') := by
  sorry

theorem cfg_safeStep {tp : List Expr} {σ : State} {f n e κ e' σ' efs}
    (Hsafe : cfgSafeForking (tp, σ) f) (Hlu : tp[n]? = some e)
    (Hprim : (e, σ) -<κ>-> (e', σ', efs)) :
    cfgSafeForking (tp.set n e' ++ efs, σ') f ∧
    (f = .doesNotFork → efs = []) := by
  sorry

theorem cfg_safeSteps {tp : List Expr} {σ : State} {f n e κ e' σ' efs}
    (Hsafe : cfgSafeForking (tp, σ) f) (Hlu : tp[n]? = some e)
    (Hprim : PrimSteps e σ κ e' σ' efs) :
    cfgSafeForking (tp.set n e' ++ efs, σ') f ∧
    (f = .doesNotFork → efs = []) := by
  sorry

theorem nSteps_trans {n m : Nat} {ρ₁ ρ₂ ρ₃ : List Expr × State} {κa κb : List Obs}
    (H1 : ρ₁ -<κa>->ₜₚ^[n] ρ₂) (H2 : ρ₂ -<κb>->ₜₚ^[m] ρ₃) :
    ρ₁ -<(κa ++ κb)>->ₜₚ^[(n + m)] ρ₃ := by
  sorry

theorem nSteps_one {ρ₁ ρ₂ : List Expr × State} {κ : List Obs}
    (H : ρ₁ -<κ>->ₜₚ ρ₂) : ρ₁ -<κ>->ₜₚ^[1] ρ₂ := by
  sorry

theorem nSteps_r {n} {ρ₁ ρ₂ ρ₃ : List Expr × State} {κ κs : List Obs}
    (H1 : ρ₁ -<κs>->ₜₚ^[n] ρ₂) (H2 : ρ₂ -<κ>->ₜₚ ρ₃) :
    ρ₁ -<(κs ++ κ)>->ₜₚ^[(n + 1)] ρ₃ := by
  sorry

theorem primSteps_atomic {e : Expr} {σ κ e₂ σ' efs}
    (Hatom : Atomic .StronglyAtomic e)
    (Hsteps : PrimSteps e σ κ e₂ σ' efs) :
    ((e, σ) -<κ>-> (e₂, σ', efs)) ∧ (ToVal.toVal e₂).isSome := by
  sorry

end

/-! ### Thread-pool ghost-state invariant -/

section ghost
open Iris CMRA Std

variable {GF : BundledGFunctors}
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable {Expr : Type _}

/-- The ghost state needed to track a thread-pool invariant: a `ghost_map`
indexed by thread id (a `Nat`) carrying expressions, plus a designated ghost name. -/
public class TpinvGS (GF : BundledGFunctors) (F : outParam <| Type _) (Expr : Type _)
    (H : outParam <| Type _ → Type _) [UFraction F] [LawfulFiniteMap H Nat]
    extends GhostMapG GF F Nat Expr H where
  tp_name : GName

variable [TI : TpinvGS GF F Expr H]

/-- `n ↪thread{dq} e` says that thread `n` in the pool is the expression `e`. -/
public def isThread (n : Nat) (dq : DFrac F) (e : Expr) : IProp GF :=
  TI.tp_name ↪◯MAP[n]{dq} e

notation k " ↪thread{" dq "} " v => isThread k dq v
notation k " ↪thread "       v => isThread k (DFrac.own 1) v

/-- The initial thread-pool authority (empty pool). -/
public def tpInvIni : IProp GF :=
  TI.tp_name ↪●MAP (∅ : H Expr)

/-- The thread-pool invariant: the auth-side `ghost_map` agrees pointwise with
the operational thread list `tp`. -/
public def tpInv (tp : List Expr) : IProp GF :=
  iprop% ∃ m : H Expr,
    ⌜∀ n, PartialMap.get? m n = tp[n]?⌝ ∗ TI.tp_name ↪●MAP m

theorem tpInv_lookup (tp : List Expr) (n : Nat) (e₁ : Expr) (dq : DFrac F) :
    tpInv (TI := TI) tp ⊢ isThread (TI := TI) n dq e₁ -∗ ⌜tp[n]? = some e₁⌝ := by
  sorry

theorem tpInv_update (tp : List Expr) (n : Nat) (e₁ e₂ : Expr) :
    tpInv (TI := TI) tp ⊢
    isThread (TI := TI) n (.own 1) e₁ ==∗
    tpInv (TI := TI) (tp.set n e₂) ∗ isThread (TI := TI) n (.own 1) e₂ := by
  sorry

theorem tpInv_new_threads (efs tp : List Expr) :
    tpInv (TI := TI) tp ==∗
    tpInv (TI := TI) (tp ++ efs) ∗
      ([∗list] n ↦ e' ∈ efs, isThread (TI := TI) (tp.length + n) (.own 1) e') := by
  sorry

theorem tpInv_set (C : List Expr) :
    tpInvIni (TI := TI) ==∗
    tpInv (TI := TI) C ∗ ([∗list] n ↦ e ∈ C, isThread (TI := TI) n (.own 1) e) := by
  sorry

end ghost

/-! ### Allocation

Allocates the empty thread-pool authority and exposes a `TpinvGS` instance
parameterized by the freshly-chosen ghost name. -/

section alloc
open Iris CMRA Std

variable {GF : BundledGFunctors}
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulFiniteMap H Nat]
variable {Expr : Type _} [GhostMapG GF F Nat Expr H]

theorem tpInv_alloc :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      @tpInvIni GF F _ H _ Expr { toGhostMapG := inferInstance, tp_name := γ } := by
  sorry

end alloc

end Iris.ProgramLogic
