module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.Ring
public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath.MvPowerSeries

/-! # Multivariate formal power series as an OFE / COFE / CMRA

This module exposes `MvPowerSeries σ R` (multivariate formal power series with variables indexed
by `σ` and coefficients in `R`) as an Iris `OFE`, `COFE` and (`U`)`CMRA`, mirroring
`IrisMath.PowerSeries` for the univariate case.

The OFE structure is the **total-degree truncation** metric: two series agree at step `n` iff
every coefficient indexed by a multi-degree `d : σ →₀ ℕ` whose total degree `d.sum (fun _ k ↦ k)`
is strictly less than `n` coincides between them. For `σ = Unit` (one variable) this collapses
to the univariate X-adic metric.

The COFE chain limit is built the same way as in the univariate case: the coefficient of the
limit at multi-degree `d` is the coefficient of `c (|d| + 1)` at `d`, where `|d|` is the total
degree of `d`. The chain Cauchy property then forces this to agree with `c n` for any `n` that
"sees" `d`.

When `R` is a commutative ring we obtain a `UCMRA` structure with operation given by series
addition (unit `0`), all elements trivially valid, and persistent core `some 0`.

Headline contractive example: multiplication by a single variable `X s` is contractive, since
multiplying by `X s` shifts every coefficient up by one in the `s`-th coordinate, hence increases
total degree by one. This is the canonical witness that `MvPowerSeries σ R` is a non-trivial
Iris OFE — exactly what step-indexing is designed to exploit.
-/

variable {σ : Type _} {R : Type _}

/-- The total degree of a multi-index `d : σ →₀ ℕ`. -/
def totalDegree (d : σ →₀ ℕ) : ℕ := d.sum fun _ k ↦ k

section OFE
variable [Semiring R]

/-- The total-degree OFE on `MvPowerSeries σ R`: two series agree at step `n` iff every
coefficient of total degree strictly less than `n` coincides. -/
scoped instance instOFE : OFE (MvPowerSeries σ R) where
  Equiv x y := x = y
  Dist n x y := ∀ d : σ →₀ ℕ, totalDegree d < n →
    MvPowerSeries.coeff (R := R) d x = MvPowerSeries.coeff d y
  dist_eqv := {
    refl _ _ _ := rfl
    symm h d hd := (h d hd).symm
    trans h₁ h₂ d hd := (h₁ d hd).trans (h₂ d hd)
  }
  equiv_dist := by
    refine ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ MvPowerSeries.ext fun d ↦ ?_⟩
    exact h (totalDegree d + 1) d (Nat.lt_succ_self _)
  dist_lt h hmn d hd := h d (Nat.lt_trans hd hmn)

/-- Unfolding lemma: `n`-equivalence of multivariate power series is coefficient-wise equality
at every multi-index of total degree below `n`. -/
theorem coeff_dist {n : ℕ} {d : σ →₀ ℕ} {x y : MvPowerSeries σ R}
    (h : x ≡{n}≡ y) (hd : totalDegree d < n) :
    MvPowerSeries.coeff d x = MvPowerSeries.coeff d y := h d hd

/-- Addition on `MvPowerSeries σ R` is non-expansive in both arguments. -/
instance instNonExpansive₂Add :
    OFE.NonExpansive₂ (fun (x y : MvPowerSeries σ R) ↦ x + y) where
  ne _ _ _ hx _ _ hy d hd := by simp [map_add, hx d hd, hy d hd]

end OFE

section COFE
variable [Semiring R]

/-- The limit of a chain of multivariate power series: its `d`-th coefficient is the `d`-th
coefficient of `c (|d| + 1)`, where `|d|` is the total degree of `d`. The chain Cauchy
property then guarantees this agrees with `c n` at every coefficient of total degree below
`n`. -/
noncomputable def chainLimit (c : Chain (MvPowerSeries σ R)) : MvPowerSeries σ R :=
  fun d ↦ MvPowerSeries.coeff (R := R) d (c.chain (totalDegree d + 1))

/-- `MvPowerSeries σ R` is a COFE for the total-degree OFE. -/
noncomputable scoped instance instIsCOFE : IsCOFE (MvPowerSeries σ R) where
  compl := chainLimit
  conv_compl {n c} d hd := by
    show MvPowerSeries.coeff d (chainLimit c) = MvPowerSeries.coeff d (c.chain n)
    change MvPowerSeries.coeff d (c.chain (totalDegree d + 1)) =
      MvPowerSeries.coeff d (c.chain n)
    rcases Nat.lt_or_ge (totalDegree d + 1) n with h | h
    · -- `|d| + 1 < n`, so `c n ≡{|d|+1}≡ c (|d|+1)`
      have := c.cauchy (n := totalDegree d + 1) (i := n) (Nat.le_of_lt h)
      exact (this d (Nat.lt_succ_self _)).symm
    · -- `n ≤ |d| + 1`, so `c (|d|+1) ≡{n}≡ c n`. Since `|d| < n`, this gives equality at `d`.
      have := c.cauchy (n := n) (i := totalDegree d + 1) h
      exact this d hd

end COFE

section CMRA

/-! ## CMRA structure

When `R` is a commutative ring we obtain a `UCMRA` structure on `MvPowerSeries σ R` by taking
the monoid operation to be series addition, all elements trivially valid, and the unit `0`.
The persistent core is the constant function returning `some 0`, making every element own its
core.

Restricting to `[CommRing R]` (rather than just `[AddCommMonoid R]`) is essential for the
`extend` axiom, which requires subtraction to split a series.
-/

variable [CommRing R]

/-- Auxiliary: addition is non-expansive in the total-degree OFE. -/
theorem add_dist {n : ℕ} {x y z : MvPowerSeries σ R} (h : x ≡{n}≡ y) : x + z ≡{n}≡ y + z := by
  intro d hd
  simp [map_add, h d hd]

/-- Extend lemma: given `x ≡{n}≡ y₁ + y₂`, we can find `z₁`, `z₂` with `x = z₁ + z₂` and
`zᵢ ≡{n}≡ yᵢ`. We use `z₁ := y₁` and `z₂ := x - y₁`, which works because on multi-indices of
total degree below `n` we have `x - y₁ = y₂`. -/
def extend_aux {n : ℕ} {x y₁ y₂ : MvPowerSeries σ R} (h : x ≡{n}≡ y₁ + y₂) :
    (z₁ : MvPowerSeries σ R) ×' (z₂ : MvPowerSeries σ R) ×'
      x = z₁ + z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  refine ⟨y₁, x - y₁, ?_, ?_, ?_⟩
  · ring
  · intro _ _; rfl
  · intro d hd
    have hd' := h d hd
    simp only [map_sub, map_add] at hd' ⊢
    rw [hd']; ring

/-- `MvPowerSeries σ R` is a CMRA with addition as the monoid operation, all elements valid,
and persistent core constantly `0`. -/
noncomputable scoped instance instCMRA : CMRA (MvPowerSeries σ R) where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by
    intro d hd
    simp [map_add, h d hd]
  pcore_ne {_ x y cx} _ h := by
    refine ⟨0, rfl, ?_⟩
    rw [Option.some.injEq] at h
    subst h
    exact fun _ _ ↦ rfl
  validN_ne _ _ := trivial
  valid_iff_validN := ⟨fun _ _ ↦ trivial, fun _ ↦ trivial⟩
  validN_succ _ := trivial
  validN_op_left _ := trivial
  assoc := show ∀ {x y z : MvPowerSeries σ R}, x + (y + z) = (x + y) + z by intros; ring
  comm := show ∀ {x y : MvPowerSeries σ R}, x + y = y + x by intros; ring
  pcore_op_left {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    change (0 : MvPowerSeries σ R) + x = x
    ring
  pcore_idem {x cx} h := by
    rw [Option.some.injEq] at h
    subst h
    rfl
  pcore_op_mono {x cx} h y := by
    rw [Option.some.injEq] at h
    subst h
    refine ⟨0, ?_⟩
    show some ((0 : MvPowerSeries σ R)) ≡ some (0 + 0)
    have : (0 : MvPowerSeries σ R) + 0 = 0 := by ring
    rw [this]
  extend _ h := extend_aux h

/-- `MvPowerSeries σ R` is a UCMRA with unit `0`. -/
noncomputable scoped instance instUCMRA : UCMRA (MvPowerSeries σ R) where
  unit := 0
  unit_valid := show True from trivial
  unit_left_id := show ∀ {x : MvPowerSeries σ R}, 0 + x = x by intros; ring
  pcore_unit := rfl

end CMRA

section Contractive

variable [CommSemiring R]

/-- Total degree behaves additively for `single s 1 + d`: it equals `totalDegree d + 1`. -/
theorem totalDegree_single_one_add (s : σ) (d : σ →₀ ℕ) :
    totalDegree (Finsupp.single s 1 + d) = totalDegree d + 1 := by
  classical
  unfold totalDegree
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
      Finsupp.sum_single_index rfl]
  ring

/-- Multiplication by `X s` is contractive: if `x` and `y` agree at every coefficient of
total degree below `n`, then `X s * x` and `X s * y` agree at every coefficient of total
degree below `n + 1`.

This is the canonical contractive endomap on `MvPowerSeries σ R`: every Iris fixed-point /
guarded-recursion intuition for multivariate power series goes through this instance. -/
instance instContractiveXMul (s : σ) :
    OFE.Contractive (fun (x : MvPowerSeries σ R) ↦ MvPowerSeries.X s * x) where
  distLater_dist {n x y} h d hd := by
    classical
    -- Either `d s = 0`, in which case both coefficients are zero, or we can subtract
    -- a unit in the `s`-th coordinate and use the hypothesis on the smaller total degree.
    by_cases hs : Finsupp.single s 1 ≤ d
    · -- We can write `d = single s 1 + (d - single s 1)`.
      set d' : σ →₀ ℕ := d - Finsupp.single s 1
      have hd_eq : d = Finsupp.single s 1 + d' := by
        rw [add_comm]; exact (tsub_add_cancel_of_le hs).symm
      have htd : totalDegree d' + 1 = totalDegree d := by
        rw [hd_eq, totalDegree_single_one_add]
      rw [MvPowerSeries.X, hd_eq]
      rw [MvPowerSeries.coeff_add_monomial_mul, MvPowerSeries.coeff_add_monomial_mul]
      congr 1
      -- We have `totalDegree d' + 1 = totalDegree d < n`, so `totalDegree d' < totalDegree d < n`.
      -- Use the DistLater hypothesis at step `totalDegree d`.
      have hd' : totalDegree d' < totalDegree d := by
        rw [← htd]; exact Nat.lt_succ_self _
      exact h (totalDegree d) hd d' hd'
    · -- `d s = 0` (in fact `¬ single s 1 ≤ d`), so both coefficients are zero.
      rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, if_neg hs,
          MvPowerSeries.coeff_monomial_mul, if_neg hs]

end Contractive

end IrisMath.MvPowerSeries
