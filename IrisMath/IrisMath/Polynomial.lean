module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.PowerSeries.Basic
public import IrisMath.PowerSeries
public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath.Polynomial

/-! # Univariate polynomials as an OFE / CMRA

This module exposes Mathlib's `Polynomial R` (i.e. `R[X]`) as an Iris `OFE` and, when `R` is a
commutative ring, as a `UCMRA`. The metric is the X-adic one: two polynomials are `n`-equivalent
iff their first `n` coefficients coincide. This mirrors `IrisMath.PowerSeries` step for step.

The headline feature is the `Contractive` instance for the endomap `x ↦ X * x`: multiplying by
`X` shifts every coefficient up by one, so if the `DistLater n` hypothesis holds we get
`X * x ≡{n}≡ X * y`. This is the canonical step-indexed contractive map. By iteration, any
`X ^ k * x` for `k ≥ 1` is contractive — see `contractive_X_pow_mul`.

## Polynomials vs. power series

This file is the finite-support sibling of `IrisMath.PowerSeries`. The two carry the *same*
X-adic metric: at step `n`, polynomials and power series are compared by their first `n`
coefficients. The crucial difference is **completeness**:

* `PowerSeries R` is a COFE — a Cauchy chain converges, with limit constructed coefficient
  by coefficient.
* `Polynomial R` is **not** a COFE. A Cauchy chain whose coefficients stabilise at each index
  but with unbounded degree (e.g. the partial sums of a non-polynomial power series) has no
  limit in `Polynomial R`. The natural ambient space for X-adic step-indexing is therefore
  `PowerSeries R`, and `Polynomial R` embeds into it as the dense finite-support subspace.

That embedding is exposed as `toPowerSeriesHom : Polynomial R -n> PowerSeries R`, the
non-expansive incarnation of `Polynomial.toPowerSeries`. We deliberately skip the `IsCOFE`
instance on `Polynomial R`: the incompleteness is a feature illustrating *why* `PowerSeries`
is the completion.

## API

* `coeff_dist`: `n`-equivalence is coefficient-wise equality below step `n` — i.e. each
  `Polynomial.coeff k` is non-expansive at step `k + 1`.
* `instNonExpansive₂Add`: addition is non-expansive in both arguments.
* `instContractiveXMul`: multiplication by `X` is contractive (the canonical example).
* `contractive_X_pow_mul`: by iteration, `(X ^ k) * ·` is contractive for every `k ≥ 1`.
* `toPowerSeriesHom`: the inclusion `Polynomial R ↪ PowerSeries R` as an OFE morphism.
-/

variable {R : Type _}

section OFE
variable [Semiring R]

/-- The X-adic OFE on `Polynomial R`: two polynomials agree at step `n` iff their first
`n` coefficients are equal. This is the polynomial analogue of `IrisMath.PowerSeries.instOFE`,
sharing the same metric on the common finite-support subspace. -/
scoped instance instOFE : OFE (Polynomial R) where
  Equiv x y := x = y
  Dist n x y := ∀ k, k < n → Polynomial.coeff x k = Polynomial.coeff y k
  dist_eqv :=
    { refl _ _ _ := rfl
      symm h k hk := (h k hk).symm
      trans h₁ h₂ k hk := (h₁ k hk).trans (h₂ k hk) }
  equiv_dist := by
    refine ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ Polynomial.ext fun k ↦ ?_⟩
    exact h (k + 1) k (Nat.lt_succ_self k)
  dist_lt h hmn k hk := h k (Nat.lt_trans hk hmn)

/-- Unfolding lemma: `n`-equivalence of polynomials is coefficient-wise equality below
step `n`. Equivalently, `Polynomial.coeff k` is non-expansive at step `k + 1` — it does not
see anything beyond the first `n` coefficients.

Note that `Polynomial.coeff k` is *not* non-expansive in the usual sense (i.e. with no degree
restriction): comparing coefficients at index `k ≥ n` is not constrained by `n`-equivalence,
exactly as in `IrisMath.PowerSeries.coeff_dist`. -/
theorem coeff_dist {n k : ℕ} {x y : Polynomial R} (h : x ≡{n}≡ y) (hk : k < n) :
    Polynomial.coeff x k = Polynomial.coeff y k := h k hk

/-- Addition on `Polynomial R` is non-expansive in both arguments: bumping the first `n`
coefficients of either summand by `n`-equivalent polynomials leaves the sum `n`-equivalent.
This is the workhorse for combining step-indexed chains via `+`. -/
instance instNonExpansive₂Add :
    OFE.NonExpansive₂ (fun (x y : Polynomial R) ↦ x + y) where
  ne _ _ _ hx _ _ hy k hk := by simp [Polynomial.coeff_add, hx k hk, hy k hk]

/-- Multiplication by `X` is contractive on `Polynomial R`. Concretely: if the `DistLater n`
hypothesis holds between `x` and `y`, then the first `n` coefficients of `X * x` and `X * y`
agree, because every coefficient of `X * x` at index `k + 1` is the `k`-th coefficient of `x`.

This is the canonical contractive endomap for X-adic step-indexing on polynomials, matching
`IrisMath.PowerSeries.instContractiveXMul`. -/
instance instContractiveXMul :
    OFE.Contractive (fun (x : Polynomial R) ↦ Polynomial.X * x) where
  distLater_dist {n x y} h k hk := by
    match k with
    | 0 => simp
    | k + 1 =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
      exact h (k + 1) hk k (Nat.lt_succ_self k)

/-- Multiplication by `X ^ j` for `j ≥ 1` is contractive. This generalises `instContractiveXMul`
and gives the polynomial counterpart of "multiplying by a monomial of positive degree drops
us strictly deeper in the X-adic filtration".

We state this as a theorem rather than an instance to avoid spurious instance resolution on
`j` — use it explicitly when needed. -/
theorem contractive_X_pow_mul {j : ℕ} (hj : 1 ≤ j) :
    OFE.Contractive (fun (x : Polynomial R) ↦ Polynomial.X ^ j * x) where
  distLater_dist {n x y} h k hk := by
    rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, if_pos hjk]
      exact h k hk (k - j) (by omega)
    · rw [if_neg hjk, if_neg hjk]

end OFE

section Embedding
open IrisMath.PowerSeries
variable [Semiring R]

/-- The canonical embedding `Polynomial R ↪ PowerSeries R` as an OFE morphism: the inclusion
is non-expansive because at every step `n`, both sides are compared by the same first `n`
coefficients (via `Polynomial.coeff_coe`).

This exhibits `PowerSeries R` as the natural ambient COFE in which `Polynomial R` is a dense
finite-support subspace. -/
def toPowerSeriesHom : Polynomial R -n> PowerSeries R where
  f := Polynomial.toPowerSeries
  ne :=
    { ne := fun n x y h k hk ↦ by simpa [Polynomial.coeff_coe] using h k hk }

end Embedding

section CMRA

/-! ## CMRA structure

When `R` is a commutative ring we obtain a `UCMRA` structure on `Polynomial R` by taking the
monoid operation to be addition, all elements trivially valid, and the unit to be `0`. The
persistent core is the constant function returning `some 0`, making every element own its core.

Restricting to `[CommRing R]` (rather than just `[AddCommMonoid R]`) is essential for the
`extend` axiom, which requires subtraction in order to split a polynomial.
-/

variable [CommRing R]

/-- Addition is non-expansive on the left: bumping `x` to an `n`-equivalent `y` preserves
`n`-equivalence after adding the same `z`. Auxiliary helper for the CMRA `op_ne` field. -/
theorem add_dist {n : ℕ} {x y z : Polynomial R} (h : x ≡{n}≡ y) : x + z ≡{n}≡ y + z := by
  intro k hk
  simp [Polynomial.coeff_add, h k hk]

/-- Extend lemma for the X-adic OFE: given `x ≡{n}≡ y₁ + y₂`, we can find `z₁`, `z₂` with
`x = z₁ + z₂` and `zᵢ ≡{n}≡ yᵢ`. We use `z₁ := y₁` and `z₂ := x - y₁`, which works because
on the first `n` coefficients `x - y₁` agrees with `y₂`. -/
noncomputable def extend_aux {n : ℕ} {x y₁ y₂ : Polynomial R} (h : x ≡{n}≡ y₁ + y₂) :
    (z₁ : Polynomial R) ×' (z₂ : Polynomial R) ×'
      x = z₁ + z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  refine ⟨y₁, x - y₁, ?_, ?_, ?_⟩
  · ring
  · intro _ _; rfl
  · intro k hk
    have hk' := h k hk
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add] at hk' ⊢
    rw [hk']; ring

/-- `Polynomial R` is a CMRA with addition as the monoid operation, all elements valid,
and persistent core constantly `0`. -/
noncomputable scoped instance instCMRA : CMRA (Polynomial R) where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by
    intro k hk
    simp [Polynomial.coeff_add, h k hk]
  pcore_ne {_ x y cx} _ h := by
    refine ⟨0, rfl, ?_⟩
    rw [Option.some.injEq] at h
    subst h
    exact fun _ _ ↦ rfl
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := show ∀ {x y z : Polynomial R}, x + (y + z) = (x + y) + z by intros; ring
  comm := show ∀ {x y : Polynomial R}, x + y = y + x by intros; ring
  pcore_op_left {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    change (0 : Polynomial R) + x = x
    ring
  pcore_idem {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    rfl
  pcore_op_mono {x cx} h y := by
    rw [Option.some.injEq] at h
    subst h
    refine ⟨0, ?_⟩
    show some ((0 : Polynomial R)) ≡ some (0 + 0)
    have : (0 : Polynomial R) + 0 = 0 := by ring
    rw [this]
  extend _ h := extend_aux h

/-- `Polynomial R` is a UCMRA with unit `0`. -/
noncomputable scoped instance instUCMRA : UCMRA (Polynomial R) where
  unit := 0
  unit_valid := show True from trivial
  unit_left_id := show ∀ {x : Polynomial R}, 0 + x = x by intros; ring
  pcore_unit := rfl

end CMRA

end IrisMath.Polynomial
