module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Iris

@[expose] public section

noncomputable section

open Iris MeasureTheory

namespace IrisMath.AeCMRA

/-! # Almost-everywhere quotient as an OFE / UCMRA

This module exposes `Ω → δ` as an Iris `OFE` and `UCMRA` modulo a.e.-equality with respect to a
measure `μ : Measure Ω`. Two functions are deemed equivalent (and `n`-distant for every `n`) iff
they agree almost everywhere; the resulting OFE is discrete in the step index because the relation
does not depend on `n`. The CMRA operation is pointwise addition.

A sibling file `IrisMath.MeasureTheory` already defines `aeOFE` in the scope
`RealRandomVariableMax`. The instances here are placed in their own scope (`AeCMRA`) and given
distinct names to avoid clashes when both files are open.

We require the codomain to be an `AddCommGroup` rather than just `AddCommMonoid`: the CMRA
`extend` axiom needs to split `x` along `y₁ + y₂` and the cleanest splitting `z₁ := y₁`,
`z₂ := x - y₁` uses subtraction. This mirrors the convention in `IrisMath.PowerSeries`.

The structural template is the same as in `IrisMath.PowerSeries`: an OFE whose `Dist` is
independent of the step index (in `PowerSeries` it depends on `n` via the X-adic filtration;
here it does not depend on `n` at all), upgraded to a `UCMRA` with pointwise addition. Where
the X-adic story uses coefficient-wise equality below step `n`, the a.e. story uses
`=ᵐ[μ]` — both are equivalence relations preserved by the additive operation.
-/

variable {Ω : Type _} [MeasurableSpace Ω]

/-! ## OFE structure -/

section OFE
variable (δ : Type _)

/-- The a.e.-equality OFE on `Ω → δ`: two functions are equivalent (and `n`-distant for every `n`)
iff they coincide almost everywhere with respect to `μ`. -/
scoped instance instOFE (μ : Measure Ω) : OFE (Ω → δ) where
  Equiv x y := x =ᵐ[μ] y
  Dist _ x y := x =ᵐ[μ] y
  dist_eqv := {
    refl _ := ae_eq_rfl
    symm := (Filter.EventuallyEq.symm ·)
    trans := (ae_eq_trans · ·)
  }
  equiv_dist := .symm <| forall_const _
  dist_lt h _ := h

end OFE

/-! ## Bridge between the OFE structure and `=ᵐ[μ]` -/

section Bridge
variable {δ : Type _} {μ : Measure Ω} {x y : Ω → δ}

/-- Unfolding lemma: in the a.e.-equality OFE, `n`-distance is literally a.e.-equality. This
makes the bridge between the CMRA structure and Mathlib's `=ᵐ[μ]` explicit and is the natural
entry point for transferring lemmas across the two interfaces. -/
theorem dist_iff_aeEq {n : Nat} :
    letI : OFE (Ω → δ) := instOFE δ μ
    x ≡{n}≡ y ↔ x =ᵐ[μ] y := Iff.rfl

/-- Equivalence in the a.e.-equality OFE is literally a.e.-equality. -/
theorem equiv_iff_aeEq : OFE.Equiv (self := instOFE δ μ) x y ↔ x =ᵐ[μ] y := Iff.rfl

end Bridge

/-! ## CMRA structure

The CMRA operation is pointwise addition; the persistent core sends every element to the zero
function (which is the unit), and every element is trivially valid. -/

section CMRA
variable {δ : Type _} [AddCommGroup δ]

/-- The a.e.-equality CMRA on `Ω → δ` (`δ` an additive commutative group). The operation is
pointwise addition, the persistent core is constantly `some 0`, and every element is valid. -/
scoped instance instCMRA (μ : Measure Ω) : CMRA (Ω → δ) where
  toOFE := instOFE δ μ
  op := fun x y ω ↦ x ω + y ω
  pcore _ := some 0
  ValidN _ _ := True
  Valid _ := True
  op_ne := letI : OFE (Ω → δ) := instOFE δ μ
    { ne := fun _ _ _ h ↦ Filter.EventuallyEq.fun_add ae_eq_rfl h }
  pcore_ne {_ x y cx} _ h := by
    refine ⟨0, rfl, ?_⟩
    rw [Option.some.injEq] at h
    subst h
    exact ae_eq_rfl
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc {x y z} :=
    show (fun ω ↦ x ω + (y ω + z ω)) =ᵐ[μ] (fun ω ↦ (x ω + y ω) + z ω) from
    Filter.Eventually.of_forall fun _ ↦ (add_assoc _ _ _).symm
  comm {x y} :=
    show (fun ω ↦ x ω + y ω) =ᵐ[μ] (fun ω ↦ y ω + x ω) from
    Filter.Eventually.of_forall fun _ ↦ add_comm _ _
  pcore_op_left {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    change (fun ω ↦ (0 : δ) + x ω) =ᵐ[μ] x
    exact Filter.Eventually.of_forall fun _ ↦ zero_add _
  pcore_idem {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    exact ae_eq_rfl
  pcore_op_mono {x cx} h y := by
    rw [Option.some.injEq] at h
    subst h
    refine ⟨0, ?_⟩
    change ((fun _ ↦ (0 : δ)) : Ω → δ) =ᵐ[μ] (fun ω ↦ (0 : δ) + 0)
    exact Filter.Eventually.of_forall fun _ ↦ (zero_add _).symm
  extend {n x y₁ y₂} _ h := by
    -- Split: `z₁ := y₁`, `z₂ ω := x ω - y₁ ω`. On the a.e. set where `x ω = y₁ ω + y₂ ω`,
    -- we have `z₂ ω = y₂ ω`. Pointwise, `z₁ + z₂ = x`.
    refine ⟨y₁, fun ω ↦ x ω - y₁ ω, ?_, ae_eq_rfl, ?_⟩
    · change x =ᵐ[μ] (fun ω ↦ y₁ ω + (x ω - y₁ ω))
      exact Filter.Eventually.of_forall fun ω ↦ (add_sub_cancel (y₁ ω) (x ω)).symm
    · change (fun ω ↦ x ω - y₁ ω) =ᵐ[μ] y₂
      filter_upwards [h] with ω hω
      show x ω - y₁ ω = y₂ ω
      rw [show x ω = y₁ ω + y₂ ω from hω, add_sub_cancel_left]

/-- The a.e.-equality UCMRA on `Ω → δ` with unit the zero function. -/
scoped instance instUCMRA (μ : Measure Ω) : UCMRA (Ω → δ) where
  toCMRA := instCMRA μ
  unit := fun _ ↦ 0
  unit_valid := trivial
  unit_left_id := show ∀ {x : Ω → δ}, (fun ω ↦ (0 : δ) + x ω) =ᵐ[μ] x from
    fun {_} ↦ Filter.Eventually.of_forall fun _ ↦ zero_add _
  pcore_unit := ae_eq_rfl

end CMRA

/-! ## Non-expansive structure on the natural operations

Pointwise addition is non-expansive in both arguments (it is literally the CMRA op, but having
it as a `NonExpansive₂` instance is convenient for combining a.e. chains) and pointwise
negation is non-expansive (a.e.-equality is preserved by pointwise negation). -/

section NonExpansive
variable {δ : Type _} [AddCommGroup δ] {μ : Measure Ω}

/-- Pointwise addition `(fun ω ↦ x ω + y ω)` is non-expansive in both arguments under the
a.e.-equality OFE. This is the CMRA operation packaged as an explicit `NonExpansive₂`
instance for use when combining a.e. chains. -/
scoped instance instNonExpansive₂Add :
    letI : OFE (Ω → δ) := instOFE δ μ
    OFE.NonExpansive₂ (fun (x y : Ω → δ) ω ↦ x ω + y ω) :=
  letI : OFE (Ω → δ) := instOFE δ μ
  { ne := fun _ _ _ hx _ _ hy ↦ Filter.EventuallyEq.fun_add hx hy }

/-- Pointwise negation is non-expansive under the a.e.-equality OFE, because a.e.-equality
is preserved by pointwise negation. -/
scoped instance instNonExpansiveNeg :
    letI : OFE (Ω → δ) := instOFE δ μ
    OFE.NonExpansive (fun (x : Ω → δ) ω ↦ -x ω) :=
  letI : OFE (Ω → δ) := instOFE δ μ
  { ne := fun _ _ _ h ↦ h.neg }

end NonExpansive

/-! ## Core-identity elements

The persistent core sends every element to `some 0`, so an element is its own core iff it is
a.e.-equal to `0`. The zero function therefore is the canonical `CoreId`. -/

section CoreId
variable {δ : Type _} [AddCommGroup δ] {μ : Measure Ω}

/-- The zero function is its own persistent core in the a.e. CMRA. Since `pcore` is constantly
`some 0`, this is the only `CoreId` (up to a.e.-equality). -/
scoped instance instCoreIdZero :
    letI : CMRA (Ω → δ) := instCMRA μ
    CMRA.CoreId (0 : Ω → δ) :=
  letI : CMRA (Ω → δ) := instCMRA μ
  ⟨ae_eq_rfl⟩

end CoreId

end IrisMath.AeCMRA
