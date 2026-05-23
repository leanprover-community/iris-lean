module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Tactic.Ring
public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath.MvPolynomial

/-! # Multivariate polynomials as an OFE / CMRA

This module exposes Mathlib's `MvPolynomial σ R` (multivariate polynomials over `R` in
variables indexed by `σ`) as an Iris `OFE` and, when `R` is a commutative ring, as a
`UCMRA`. The metric is the total-degree one: two polynomials are `n`-equivalent iff their
coefficients agree at every multi-degree of total degree strictly less than `n`.

This file is the multivariate sibling of `IrisMath.Polynomial`. Like its univariate
counterpart, `MvPolynomial σ R` is **not** a COFE: a Cauchy chain whose coefficients
stabilise at each multi-degree but whose support grows without bound has no limit in
`MvPolynomial`. The natural completion lives in `MvPowerSeries`.

The headline feature is the `Contractive` instance for the endomap `x ↦ X i * x` for each
variable `i : σ`: multiplying by `X i` shifts every coefficient up by one in the `i`-th
component, so if the `DistLater n` hypothesis holds we get `X i * x ≡{n}≡ X i * y`.

## API

* `coeff_dist`: `n`-equivalence is coefficient-wise equality below total-degree `n`.
* `instNonExpansive₂Add`: addition is non-expansive in both arguments.
* `instContractiveXMul`: multiplication by `X i` is contractive for each `i : σ`.
-/

variable {R : Type _} {σ : Type _}

section OFE
variable [CommSemiring R]

/-- Total degree of a multi-degree: the sum of all variable exponents. -/
abbrev totalDeg (d : σ →₀ ℕ) : ℕ := d.sum fun _ k ↦ k

/-- The total-degree OFE on `MvPolynomial σ R`: two polynomials agree at step `n` iff
their coefficients at every multi-degree of total degree `< n` are equal. This is the
multivariate analogue of `IrisMath.Polynomial.instOFE`. -/
scoped instance instOFE : OFE (MvPolynomial σ R) where
  Equiv x y := x = y
  Dist n x y := ∀ d : σ →₀ ℕ, totalDeg d < n → MvPolynomial.coeff d x = MvPolynomial.coeff d y
  dist_eqv :=
    { refl _ _ _ := rfl
      symm h d hd := (h d hd).symm
      trans h₁ h₂ d hd := (h₁ d hd).trans (h₂ d hd) }
  equiv_dist := by
    refine ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ MvPolynomial.ext _ _ fun d ↦ ?_⟩
    exact h (totalDeg d + 1) d (Nat.lt_succ_self _)
  dist_lt h hmn d hd := h d (Nat.lt_trans hd hmn)

/-- Unfolding lemma: `n`-equivalence of multivariate polynomials is coefficient-wise
equality at every multi-degree of total degree `< n`. -/
theorem coeff_dist {n : ℕ} {d : σ →₀ ℕ} {x y : MvPolynomial σ R}
    (h : x ≡{n}≡ y) (hd : totalDeg d < n) :
    MvPolynomial.coeff d x = MvPolynomial.coeff d y := h d hd

/-- Addition on `MvPolynomial σ R` is non-expansive in both arguments. -/
instance instNonExpansive₂Add :
    OFE.NonExpansive₂ (fun (x y : MvPolynomial σ R) ↦ x + y) where
  ne _ _ _ hx _ _ hy d hd := by simp [MvPolynomial.coeff_add, hx d hd, hy d hd]

/-- Multiplication by `X i` is contractive on `MvPolynomial σ R` for every variable
`i : σ`. Concretely: if the `DistLater n` hypothesis holds between `x` and `y`, then
the coefficients of `X i * x` and `X i * y` agree at every multi-degree of total degree
`< n`, because every nonzero coefficient of `X i * x` at multi-degree `d` (with
`i ∈ d.support`) equals the coefficient of `x` at the strictly smaller multi-degree
`d - (fun₀ | i => 1)`. -/
instance instContractiveXMul (i : σ) :
    OFE.Contractive (fun (x : MvPolynomial σ R) ↦ MvPolynomial.X i * x) where
  distLater_dist {n x y} h := by
    classical
    intro d hd
    rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_mul']
    by_cases hi : i ∈ d.support
    · rw [if_pos hi, if_pos hi]
      set d' : σ →₀ ℕ := d - Finsupp.single i 1
      -- We need `coeff d' x = coeff d' y`. The total degree of `d'` is `totalDeg d - 1`.
      have hi' : d i ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      have hsum : totalDeg d' + 1 ≤ totalDeg d := by
        -- Drop a single unit from variable `i` in `d`.
        have : totalDeg d = totalDeg d' + 1 := by
          simp only [totalDeg, d']
          rw [show d = d' + Finsupp.single i 1 by
            ext j
            by_cases hj : j = i
            · subst hj
              simp [d', hi']
            · simp [d', hj]]
          rw [Finsupp.sum_add_index']
          · simp [Finsupp.sum_single_index]
          · intros; rfl
          · intros; rfl
        omega
      -- Now use `h` at total degree `totalDeg d - 1 < totalDeg d < n`.
      cases n with
      | zero => exact absurd hd (Nat.not_lt_zero _)
      | succ m =>
        -- `hd : totalDeg d < m + 1`, so `totalDeg d ≤ m`, so `totalDeg d' < m`.
        have hd' : totalDeg d' < m := by omega
        exact h m (Nat.lt_succ_self _) d' hd'
    · rw [if_neg hi, if_neg hi]

end OFE

section CMRA

/-! ## CMRA structure

When `R` is a commutative ring we obtain a `UCMRA` structure on `MvPolynomial σ R` by
taking the monoid operation to be addition, all elements trivially valid, and the unit
to be `0`. The persistent core is the constant function returning `some 0`, making every
element own its core.

Restricting to `[CommRing R]` (rather than just `[CommSemiring R]`) is essential for the
`extend` axiom, which requires subtraction in order to split a polynomial.
-/

variable [CommRing R]

/-- Auxiliary: addition is non-expansive in the total-degree OFE. -/
theorem add_dist {n : ℕ} {x y z : MvPolynomial σ R} (h : x ≡{n}≡ y) : x + z ≡{n}≡ y + z := by
  intro d hd
  simp [MvPolynomial.coeff_add, h d hd]

/-- Extend lemma for the total-degree OFE: given `x ≡{n}≡ y₁ + y₂`, we can find `z₁`, `z₂`
with `x = z₁ + z₂` and `zᵢ ≡{n}≡ yᵢ`. We use `z₁ := y₁` and `z₂ := x - y₁`, which works
because on every coefficient of total degree `< n`, `x - y₁` agrees with `y₂`. -/
noncomputable def extend_aux {n : ℕ} {x y₁ y₂ : MvPolynomial σ R} (h : x ≡{n}≡ y₁ + y₂) :
    (z₁ : MvPolynomial σ R) ×' (z₂ : MvPolynomial σ R) ×'
      x = z₁ + z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  refine ⟨y₁, x - y₁, ?_, ?_, ?_⟩
  · ring
  · intro _ _; rfl
  · intro d hd
    have hd' := h d hd
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add] at hd' ⊢
    rw [hd']; ring

/-- `MvPolynomial σ R` is a CMRA with addition as the monoid operation, all elements
valid, and persistent core constantly `0`. -/
noncomputable scoped instance instCMRA : CMRA (MvPolynomial σ R) where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by
    intro d hd
    simp [MvPolynomial.coeff_add, h d hd]
  pcore_ne {_ x y cx} _ h := by
    refine ⟨0, rfl, ?_⟩
    rw [Option.some.injEq] at h
    subst h
    exact fun _ _ ↦ rfl
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := show ∀ {x y z : MvPolynomial σ R}, x + (y + z) = (x + y) + z by intros; ring
  comm := show ∀ {x y : MvPolynomial σ R}, x + y = y + x by intros; ring
  pcore_op_left {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    change (0 : MvPolynomial σ R) + x = x
    ring
  pcore_idem {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    rfl
  pcore_op_mono {x cx} h y := by
    rw [Option.some.injEq] at h
    subst h
    refine ⟨0, ?_⟩
    show some ((0 : MvPolynomial σ R)) ≡ some (0 + 0)
    have : (0 : MvPolynomial σ R) + 0 = 0 := by ring
    rw [this]
  extend _ h := extend_aux h

/-- `MvPolynomial σ R` is a UCMRA with unit `0`. -/
noncomputable scoped instance instUCMRA : UCMRA (MvPolynomial σ R) where
  unit := 0
  unit_valid := show True from trivial
  unit_left_id := show ∀ {x : MvPolynomial σ R}, 0 + x = x by intros; ring
  pcore_unit := rfl

end CMRA

end IrisMath.MvPolynomial
