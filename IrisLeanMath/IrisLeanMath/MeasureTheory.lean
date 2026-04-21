module

public import Mathlib.Probability.Independence.Basic
public import Iris

@[expose] public section

noncomputable section

open Iris ProbabilityTheory MeasureTheory

variable {Ω : Type _} [MeasurableSpace Ω]

/-- Real-valued random variable -/
@[ext] structure RandomVariable (δ : Type _) (μ : Measure Ω) where
  car : Ω → δ

namespace RealRandomVariableMax

variable {μ : Measure Ω} (δ : Type _)

scoped instance aeOFE : OFE (Ω → δ) where
  Equiv x y := x =ᵐ[μ] y
  Dist _ x y := x =ᵐ[μ] y
  dist_eqv := {
    refl _ := ae_eq_rfl
    symm := (Filter.EventuallyEq.symm ·)
    trans := (ae_eq_trans · ·)
  }
  equiv_dist := .symm <| forall_const _
  dist_lt H _ := H

end RealRandomVariableMax
