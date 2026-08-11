/-
Copyright (c) 2026 Fernando Leal, Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.ProofMode.Tactics.Monotone
public import Iris.BI.Lib.Fixpoint
public meta import Iris.ProofMode.Tactics.Fixpoint

namespace Iris

open ProgramLogic Language.Notation Std

@[expose] public section

export StateInterp (stateInterp)

variable {hlc : outParam HasLC} {Expr State Obs Val}
variable [Λ : Language Expr State Obs Val]
variable {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

abbrev Stuckness.MaybeReducibleNoObs : Stuckness → Expr × State → Prop
| .NotStuck, (e₁, σ₁) => PrimStep.ReducibleNoObs (e₁, σ₁)
| _, _ => True

@[rocq_alias twp_pre]
leastfix twp (s : Stuckness) [OFE CoPset] [OFE.Discrete CoPset] [OFE Expr] [OFE.Discrete Expr]
    (E : CoPset) (e₁ : Expr) (Φ : Val -> IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(∀ (σ₁ : State) (ns : Nat) (obs' : List Obs) (nt : Nat),
    stateInterp σ₁ ns obs' nt ={E,∅}=∗
    ⌜s.MaybeReducibleNoObs (e₁, σ₁)⌝ ∗
    ∀ obs e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>-> (e₂, σ₂, eₜ)⌝ ={E,∅}=∗
      ⌜obs = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
      twp E e₂ Φ ∗ [∗list] e' ∈ eₜ, twp ⊤ e' ι.forkPost)
