module

public import Mathlib.Probability.Independence.Basic
public import Iris

/-! Measure Theoretic CMRA -/

@[expose] public section

noncomputable section

open Iris ProbabilityTheory MeasureTheory

variable {Ω : Type _} [MeasurableSpace Ω]

def aeSetoid (μ : Measure Ω) (δ : Type _) : Setoid (Ω → δ) where
  r x y := x =ᵐ[μ] y
  iseqv := ⟨fun _ => ae_eq_rfl, (Filter.EventuallyEq.symm ·), (ae_eq_trans · ·)⟩

def RandomVariable (δ : Type _) (μ : Measure Ω) : Type _ := Quotient (aeSetoid μ δ)

instance (δ : Type _) (μ : Measure Ω) : OFE (RandomVariable δ μ) where
  Dist _ := (· = ·)
  dist_eqv := eq_equivalence
  eq_dist := (forall_const _).symm
  dist_lt h _ := h
