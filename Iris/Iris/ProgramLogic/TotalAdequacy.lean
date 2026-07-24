/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Adequacy

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Std FromMathlib LawfulSet
open Language Language.Notation

@[expose] public section

/-! ## Operational termination predicates

`Acc` takes the next configuration as its left argument, so the operational
relation is flipped.  This definition is constructive and means that every
reduction tree rooted at the configuration is finite (strong normalization),
not merely that some execution terminates.
-/

def StronglyNormalizing {α : Type _} (step : α → α → Prop) (x : α) : Prop :=
  Acc (flip step) x

namespace StronglyNormalizing

theorem intro {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, step x y → StronglyNormalizing step y) :
    StronglyNormalizing step x :=
  Acc.intro x H

theorem of_irreducible {α : Type _} {step : α → α → Prop} {x : α}
    (H : ∀ y, ¬ step x y) : StronglyNormalizing step x :=
  .intro fun y Hxy => (H y Hxy).elim

theorem tail {α : Type _} {step : α → α → Prop} {x y : α}
    (H : StronglyNormalizing step x) (Hxy : step x y) :
    StronglyNormalizing step y :=
  H.inv Hxy

end StronglyNormalizing

variable {Expr State Obs Val : Type _} [Λ : Language Expr State Obs Val]

/-- Erased single-thread reduction. Forked expressions remain visible in the
step witness; clients can rule them out with `LanguageNoFork`. -/
def ExprErasedStep : Expr × State → Expr × State → Prop
  | (e₁, σ₁), (e₂, σ₂) =>
      ∃ (κ : List Obs) (efs : List Expr), (e₁, σ₁) -<κ>-> (e₂, σ₂, efs)

/-- The single-threaded language contract used by the Wasm-facing adequacy
corollaries. -/
class LanguageNoFork (Expr State Obs Val : Type _)
    [Language Expr State Obs Val] : Prop where
  no_fork {e₁ e₂ : Expr} {σ₁ σ₂ : State} {κ : List Obs} {efs : List Expr} :
    (e₁, σ₁) -<κ>-> (e₂, σ₂, efs) → efs = []

theorem exprErasedStep_noFork [LanguageNoFork Expr State Obs Val] {e₁ σ₁ e₂ σ₂}
    (H : ExprErasedStep (Expr := Expr) (State := State) (Obs := Obs)
      (e₁, σ₁) (e₂, σ₂)) :
    ∃ κ, (e₁, σ₁) -<κ>-> (e₂, σ₂, []) := by
  obtain ⟨κ, efs, Hstep⟩ := H
  have := LanguageNoFork.no_fork Hstep
  subst efs
  exact ⟨κ, Hstep⟩

theorem value_stronglyNormalizing (v : Val) (σ : State) :
    StronglyNormalizing (ExprErasedStep (Expr := Expr) (Obs := Obs))
      ((v : Expr), σ) := by
  apply StronglyNormalizing.of_irreducible
  rintro ⟨e₂, σ₂⟩ ⟨κ, efs, Hstep⟩
  exact Language.prim_val_stuck Hstep

end
end Iris.ProgramLogic
