module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Iris

@[expose] public section

open Iris

namespace IrisMath.PowerSeries

/-! # Formal power series as an OFE / COFE

This module exposes `PowerSeries R` (i.e. `R⟦X⟧`) as an Iris `OFE` and `COFE` with respect to
the natural X-adic topology: two series are `n`-equivalent iff their first `n` coefficients
coincide. This is the canonical step-indexed metric space — every Iris OFE intuition descends
from it. When `R` is a commutative ring we additionally upgrade the structure to a `UCMRA`
with operation given by series addition (so the unit is `0`).

The headline feature is the `Contractive` instance for multiplication by `X`: given
`x ≡{n}≡ y` we have `X * x ≡{n+1}≡ X * y`, because multiplying by `X` shifts every
coefficient up by one. This contractive endomap is the canonical witness that power
series are a non-trivial example of an Iris OFE — it is precisely what step-indexing is
designed to exploit (think Banach's fixed-point principle for contractive maps on a COFE).

## API

* `coeff_dist`: `n`-equivalence is coefficient-wise equality below step `n` — equivalently,
  each `PowerSeries.coeff k` is non-expansive at step `k + 1`.
* `instNonExpansive₂Add`: addition is non-expansive in both arguments.
* `instNonExpansive₂Mul`: multiplication is non-expansive in both arguments; `k < n`
  forces every antidiagonal index `(i, j)` with `i + j = k` to satisfy `i, j < n`, so the
  Cauchy product convolves only constrained coefficients.
* `instContractiveXMul`: multiplication by `X` is contractive (the canonical example).
* `contractive_X_pow_mul`: by iteration, `(X ^ j) * ·` is contractive for every `j ≥ 1`.
* `chainLimit` / `instIsCOFE`: the X-adic completion — a Cauchy chain converges to the
  series whose `k`-th coefficient is read off the chain at step `k + 1`.
* `instCMRA` / `instUCMRA`: the additive `UCMRA` over a `CommRing R`, with `0` as unit.

## Related files

* `IrisMath.Polynomial` is the finite-support sibling: same X-adic metric, but not a COFE.
  Its `toPowerSeriesHom` embeds `Polynomial R` into `PowerSeries R` as a dense subspace.
* `IrisMath.MvPowerSeries` generalises this construction to multivariate power series,
  where the step-`n` distance is given by the `n`-truncation in every variable.
* `IrisMath.AdicCompletion` realises the same step-indexed metric for an arbitrary ideal
  via the I-adic filtration — `PowerSeries R` is the X-adic case in disguise.
-/

variable {R : Type _}

section OFE
variable [Semiring R]

/-- The X-adic OFE on `PowerSeries R`: two series agree at step `n` iff their first
`n` coefficients are equal. -/
scoped instance instOFE : OFE (PowerSeries R) where
  Equiv x y := x = y
  Dist n x y := ∀ k, k < n → PowerSeries.coeff k x = PowerSeries.coeff k y
  dist_eqv := {
    refl _ _ _ := rfl
    symm h k hk := (h k hk).symm
    trans h₁ h₂ k hk := (h₁ k hk).trans (h₂ k hk)
  }
  equiv_dist := by
    refine ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ PowerSeries.ext fun k ↦ ?_⟩
    exact h (k + 1) k (Nat.lt_succ_self k)
  dist_lt h hmn k hk := h k (Nat.lt_trans hk hmn)

/-- Unfolding lemma: `n`-equivalence of power series is coefficient-wise equality below
step `n`. This is the elementary version of "`coeff k` is non-expansive at step `k+1`":
`coeff k` does not see anything beyond the first `n` coefficients. -/
theorem coeff_dist {n k : ℕ} {x y : PowerSeries R} (h : x ≡{n}≡ y) (hk : k < n) :
    PowerSeries.coeff k x = PowerSeries.coeff k y := h k hk

/-- Addition on `PowerSeries R` is non-expansive in both arguments: bumping the first `n`
coefficients of either summand by `n`-equivalent series leaves the sum `n`-equivalent.
This is the workhorse for combining step-indexed chains via `+`. -/
instance instNonExpansive₂Add :
    OFE.NonExpansive₂ (fun (x y : PowerSeries R) ↦ x + y) where
  ne _ _ _ hx _ _ hy k hk := by simp [map_add, hx k hk, hy k hk]

/-- Multiplication on `PowerSeries R` is non-expansive in both arguments. For `k < n`, the
Cauchy-product expansion of `coeff k (x * y)` ranges over `(i, j)` with `i + j = k`, so both
indices stay strictly below `n` and the assumed `n`-equivalences pin every factor.

Compare with `instContractiveXMul`: multiplying by the fixed power series `X` is strictly
stronger than just non-expansive — it is contractive. -/
instance instNonExpansive₂Mul :
    OFE.NonExpansive₂ (fun (x y : PowerSeries R) ↦ x * y) where
  ne _ _ _ hx _ _ hy k hk := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hx p.1 (by omega), hy p.2 (by omega)]

/-- Multiplication by `X` is contractive on `PowerSeries R`. Concretely: if the first `n`
coefficients of `x` and `y` agree (in fact, even the weaker `DistLater n x y` suffices),
then the first `n + 1` coefficients of `X * x` and `X * y` agree, because every coefficient
of `X * x` at index `k + 1` is the `k`-th coefficient of `x`.

This is the canonical contractive endomap on `PowerSeries R`: every Iris fixed-point /
guarded-recursion intuition for power series goes through this instance. -/
instance instContractiveXMul :
    OFE.Contractive (fun (x : PowerSeries R) ↦ PowerSeries.X * x) where
  distLater_dist {n x y} h k hk := by
    match k with
    | 0 => simp [PowerSeries.coeff_zero_X_mul]
    | k + 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      exact h (k + 1) hk k (Nat.lt_succ_self k)

/-- Multiplication by `X ^ j` for `j ≥ 1` is contractive. This generalises
`instContractiveXMul` and matches `IrisMath.Polynomial.contractive_X_pow_mul`: multiplying
by a monomial of positive degree drops every coefficient strictly deeper in the X-adic
filtration, so `DistLater n` upgrades to `n`-equivalence.

We state this as a theorem rather than an instance to avoid spurious instance resolution on
`j` — use it explicitly when needed. -/
theorem contractive_X_pow_mul {j : ℕ} (hj : 1 ≤ j) :
    OFE.Contractive (fun (x : PowerSeries R) ↦ PowerSeries.X ^ j * x) where
  distLater_dist {n x y} h k hk := by
    rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, if_pos hjk]
      exact h k hk (k - j) (by omega)
    · rw [if_neg hjk, if_neg hjk]

end OFE

section COFE
variable [Semiring R]

/-- The limit of a chain of power series: its `k`-th coefficient is the `k`-th coefficient
of `c (k + 1)`. Note that for `k < n`, the chain Cauchy property guarantees
`c (k + 1) ≡{k+1}≡ c n`, so this limit indeed agrees with `c n` up to step `n`. -/
noncomputable def chainLimit (c : Chain (PowerSeries R)) : PowerSeries R :=
  PowerSeries.mk fun k ↦ PowerSeries.coeff k (c.chain (k + 1))

/-- `PowerSeries R` is a COFE for the X-adic OFE. -/
noncomputable scoped instance instIsCOFE : IsCOFE (PowerSeries R) where
  compl := chainLimit
  conv_compl {n c} k hk := by
    show PowerSeries.coeff k (chainLimit c) = PowerSeries.coeff k (c.chain n)
    rw [chainLimit, PowerSeries.coeff_mk]
    -- We need `c (k+1) ≡{k+1}≡ c n` at coefficient `k`. Whichever index is larger
    -- gives us the chain Cauchy bound at step `k+1`.
    rcases Nat.lt_or_ge (k + 1) n with h | h
    · -- `k + 1 < n`, so `c n ≡{k+1}≡ c (k+1)`
      have := c.cauchy (n := k + 1) (i := n) (Nat.le_of_lt h)
      exact (this k (Nat.lt_succ_self k)).symm
    · -- `n ≤ k + 1`, so `c (k+1) ≡{n}≡ c n`. Since `k < n`, this gives equality at `k`.
      have := c.cauchy (n := n) (i := k + 1) h
      exact this k hk

end COFE

section CMRA

/-! ## CMRA structure

When `R` is a commutative ring we obtain a `UCMRA` structure on `PowerSeries R` by taking
the monoid operation to be series addition, all elements trivially valid, and the unit to be
`0`. The persistent core is the constant function returning `some 0`, making every element
own its core.

Restricting to `[CommRing R]` (rather than just `[AddCommMonoid R]`) is essential for the
`extend` axiom, which requires subtraction in order to split a series.
-/

variable [CommRing R]

/-- Auxiliary: addition is non-expansive in the X-adic OFE, because `coeff k` is additive. -/
theorem add_dist {n : ℕ} {x y z : PowerSeries R} (h : x ≡{n}≡ y) : x + z ≡{n}≡ y + z := by
  intro k hk
  simp [map_add, h k hk]

/-- Extend lemma for the X-adic OFE: given `x ≡{n}≡ y₁ + y₂`, we can find `z₁`, `z₂` with
`x = z₁ + z₂` and `zᵢ ≡{n}≡ yᵢ`. We use `z₁ := y₁` and `z₂ := x - y₁`, which works because
on the first `n` coefficients `x - y₁` agrees with `y₂`. -/
def extend_aux {n : ℕ} {x y₁ y₂ : PowerSeries R} (h : x ≡{n}≡ y₁ + y₂) :
    (z₁ : PowerSeries R) ×' (z₂ : PowerSeries R) ×'
      x = z₁ + z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  refine ⟨y₁, x - y₁, ?_, ?_, ?_⟩
  · ring
  · intro _ _; rfl
  · intro k hk
    have hk' := h k hk
    simp only [map_sub, map_add] at hk' ⊢
    rw [hk']; ring

/-- `PowerSeries R` is a CMRA with addition as the monoid operation, all elements valid,
and persistent core constantly `0`. -/
noncomputable scoped instance instCMRA : CMRA (PowerSeries R) where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by
    intro k hk
    simp [map_add, h k hk]
  pcore_ne {_ x y cx} _ h := by
    refine ⟨0, rfl, ?_⟩
    rw [Option.some.injEq] at h
    subst h
    exact fun _ _ ↦ rfl
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := show ∀ {x y z : PowerSeries R}, x + (y + z) = (x + y) + z by intros; ring
  comm := show ∀ {x y : PowerSeries R}, x + y = y + x by intros; ring
  pcore_op_left {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    change (0 : PowerSeries R) + x = x
    ring
  pcore_idem {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    rfl
  pcore_op_mono {x cx} h y := by
    rw [Option.some.injEq] at h
    subst h
    refine ⟨0, ?_⟩
    show some ((0 : PowerSeries R)) ≡ some (0 + 0)
    have : (0 : PowerSeries R) + 0 = 0 := by ring
    rw [this]
  extend _ h := extend_aux h

/-- `PowerSeries R` is a UCMRA with unit `0`. -/
noncomputable scoped instance instUCMRA : UCMRA (PowerSeries R) where
  unit := 0
  unit_valid := show True from trivial
  unit_left_id := show ∀ {x : PowerSeries R}, 0 + x = x by intros; ring
  pcore_unit := rfl

end CMRA

end IrisMath.PowerSeries
