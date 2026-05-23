module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Basic
public import Iris

@[expose] public section

noncomputable section

open Iris Filter

/-! # Ultrametric spaces as OFEs

This module exposes Mathlib's (metric) ultrametric spaces as Iris `OFE`s, via a thin
wrapper `UltraO α` that avoids clashing with any pre-existing OFE structure on `α`.

The step-indexed distance is defined as
```
x ≡{0}≡ y    ↔ True
x ≡{n+1}≡ y  ↔ dist x y ≤ (1/2 : ℝ)^n
```
so that the `n = 0` case is trivial and increasing `n` refines the relation. Because
`(1/2)^n → 0`, the equivalence `x ≡ y` is equivalent to plain equality.

Note: this is genuinely step-indexed, not discrete. The convention `Dist 0 x y := True`
means `0`-equivalence is trivial; declaring `OFE.Discrete (UltraO α)` would force `α`
to have at most one element. The OFE is, however, `OFE.Leibniz`: propositional
equivalence coincides with definitional equality.

When `α` is additionally `CompleteSpace`, every `Chain` in the OFE sense is a Cauchy
sequence in the metric sense, and we obtain a `COFE` (`IsCOFE`) structure on
`UltraO α` by extracting the metric limit.

As concrete examples, both `Padic p = ℚ_[p]` and `PadicInt p = ℤ_[p]` carry this
structure for any prime `p`.
-/

namespace IrisMath.Ultrametric

/-- Wrapper around an ultrametric space that carries the Iris `OFE` instance.

Definitionally equal to `α`, but uses a distinct type name so that `OFE` and related
instances on `UltraO α` do not clash with any pre-existing OFE structure on `α`. -/
def UltraO (α : Type*) : Type _ := α

/-- The canonical map `α → UltraO α` (definitionally the identity). -/
@[match_pattern] def UltraO.mk {α : Type*} (a : α) : UltraO α := a

/-- The inverse of `UltraO.mk` (definitionally the identity). -/
def UltraO.run {α : Type*} (a : UltraO α) : α := a

@[simp] theorem UltraO.run_mk {α : Type*} (a : α) : (UltraO.mk a).run = a := rfl
@[simp] theorem UltraO.mk_run {α : Type*} (a : UltraO α) : UltraO.mk a.run = a := rfl

instance {α : Type*} [PseudoMetricSpace α] : PseudoMetricSpace (UltraO α) :=
  inferInstanceAs (PseudoMetricSpace α)

instance {α : Type*} [MetricSpace α] : MetricSpace (UltraO α) :=
  inferInstanceAs (MetricSpace α)

instance {α : Type*} [PseudoMetricSpace α] [IsUltrametricDist α] :
    IsUltrametricDist (UltraO α) :=
  inferInstanceAs (IsUltrametricDist α)

instance {α : Type*} [PseudoMetricSpace α] [CompleteSpace α] : CompleteSpace (UltraO α) :=
  inferInstanceAs (CompleteSpace α)

namespace UltraO

variable {α : Type*}

/-- The step-indexed distance on `UltraO α`: `Dist 0` is trivial and `Dist (n+1)`
asks that `dist x y ≤ (1/2)^n`. -/
protected def Dist [MetricSpace α] : Nat → UltraO α → UltraO α → Prop
  | 0, _, _ => True
  | n + 1, x, y => dist x y ≤ (1 / 2 : ℝ) ^ n

@[simp] theorem Dist_zero [MetricSpace α] (x y : UltraO α) :
    UltraO.Dist 0 x y := trivial

@[simp] theorem Dist_succ [MetricSpace α] (n : Nat) (x y : UltraO α) :
    UltraO.Dist (n + 1) x y ↔ dist x y ≤ (1 / 2 : ℝ) ^ n := Iff.rfl

/-- `(1/2)^n` is positive for every natural number `n`. -/
theorem half_pow_pos (n : Nat) : (0 : ℝ) < (1 / 2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

/-- `(1/2)^n` is nonnegative for every natural number `n`. -/
theorem half_pow_nonneg (n : Nat) : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n :=
  (half_pow_pos n).le

/-- The sequence `n ↦ (1/2)^n` is antitone. -/
theorem half_pow_anti {m n : Nat} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- `(1/2)^n` tends to `0` as `n → ∞`. -/
theorem half_pow_tendsto :
    Tendsto (fun n : Nat => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

section Eqv
variable [MetricSpace α]

/-- `Dist n` is reflexive. -/
theorem Dist_refl (n : Nat) (x : UltraO α) : UltraO.Dist n x x := by
  cases n <;> simp [UltraO.Dist]

/-- `Dist n` is symmetric. -/
theorem Dist_symm {n : Nat} {x y : UltraO α} (h : UltraO.Dist n x y) :
    UltraO.Dist n y x := by
  cases n with
  | zero => trivial
  | succ _ => rw [UltraO.Dist, dist_comm]; exact h

variable [IsUltrametricDist α]

/-- `Dist n` is transitive on ultrametric spaces (uses the strong triangle inequality). -/
theorem Dist_trans {n : Nat} {x y z : UltraO α}
    (hxy : UltraO.Dist n x y) (hyz : UltraO.Dist n y z) : UltraO.Dist n x z := by
  cases n with
  | zero => trivial
  | succ _ => exact (dist_triangle_max x y z).trans (max_le hxy hyz)

/-- `Dist n` is an equivalence relation. -/
theorem Dist_equivalence (n : Nat) : Equivalence (α := UltraO α) (UltraO.Dist n) where
  refl := Dist_refl n
  symm := Dist_symm
  trans := Dist_trans

omit [IsUltrametricDist α] in
/-- Step-indexed distance is monotone in the index: `Dist n x y → m < n → Dist m x y`. -/
theorem Dist_lt {m n : Nat} {x y : UltraO α} (h : UltraO.Dist n x y) (hmn : m < n) :
    UltraO.Dist m x y := by
  match m, n, hmn with
  | 0, _, _ => trivial
  | m + 1, n + 1, hmn =>
    exact (show dist x y ≤ (1 / 2 : ℝ) ^ n from h).trans (half_pow_anti (by omega))

omit [IsUltrametricDist α] in
/-- Two points are step-indexed equivalent at every level iff they are equal. -/
theorem equiv_iff_eq {x y : UltraO α} :
    (∀ n, UltraO.Dist n x y) ↔ x = y := by
  refine ⟨fun h => ?_, ?_⟩
  · have hdist : ∀ n : Nat, dist x y ≤ (1 / 2 : ℝ) ^ n := fun n => h (n + 1)
    have h0 : dist x y ≤ 0 := ge_of_tendsto' half_pow_tendsto hdist
    exact dist_eq_zero.mp (le_antisymm h0 dist_nonneg)
  · rintro rfl n
    exact Dist_refl n x

end Eqv

end UltraO

/-- The Iris `OFE` structure on `UltraO α` for any metric ultrametric space. -/
instance instOFE {α : Type*} [MetricSpace α] [IsUltrametricDist α] :
    OFE (UltraO α) where
  Equiv x y := x = y
  Dist := UltraO.Dist
  dist_eqv := UltraO.Dist_equivalence _
  equiv_dist := UltraO.equiv_iff_eq.symm
  dist_lt := UltraO.Dist_lt

/-- The OFE on `UltraO α` is Leibniz: equivalence is just equality. -/
instance instLeibniz {α : Type*} [MetricSpace α] [IsUltrametricDist α] :
    OFE.Leibniz (UltraO α) where
  eq_of_eqv h := h

/-
We deliberately do not declare `OFE.Discrete (UltraO α)`. With our convention
`Dist 0 x y := True`, 0-equivalence is trivial and discreteness would force `α` to
have at most one element. The induced OFE is genuinely step-indexed.
-/

/-! ## Completeness (COFE)

If `α` is a complete metric ultrametric space, the OFE on `UltraO α` is also complete
in the Iris sense. The key observation is that an OFE-`Chain` over `UltraO α` is
exactly a metric Cauchy sequence: from `c.cauchy : n ≤ i → c i ≡{n}≡ c n` we recover
`dist (c i) (c n) ≤ (1/2)^(n-1)` for `n ≥ 1, i ≥ n`. We then take the metric limit
and verify it satisfies `compl c ≡{n}≡ c n`.
-/

namespace UltraO
variable {α : Type*} [MetricSpace α] [IsUltrametricDist α] [CompleteSpace α]

omit [CompleteSpace α] in
/-- A `Chain` in the OFE on `UltraO α` is a Cauchy sequence in the metric sense. -/
theorem chain_cauchySeq (c : Chain (UltraO α)) : CauchySeq (fun i => c i) := by
  refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp half_pow_tendsto) ε hε
  refine ⟨N + 1, fun n hn => ?_⟩
  -- `c n ≡{N+1}≡ c (N+1)` gives `dist (c n) (c (N+1)) ≤ (1/2)^N`
  have hcauchy : c n ≡{N + 1}≡ c (N + 1) := c.cauchy hn
  have hd : dist (c n) (c (N + 1)) ≤ (1 / 2 : ℝ) ^ N :=
    show UltraO.Dist (N + 1) (c n) (c (N + 1)) from hcauchy
  have hN' : (1 / 2 : ℝ) ^ N < ε := by
    have h := hN N (le_refl _)
    rwa [Real.dist_0_eq_abs, abs_of_nonneg (half_pow_nonneg N)] at h
  exact lt_of_le_of_lt hd hN'

/-- The completion of a chain: the metric limit of the underlying Cauchy sequence. -/
def chainLimit (c : Chain (UltraO α)) : UltraO α :=
  Classical.choose (cauchySeq_tendsto_of_complete (chain_cauchySeq c))

/-- The chain converges to `chainLimit c` in the underlying metric topology. -/
theorem chainLimit_tendsto (c : Chain (UltraO α)) :
    Tendsto (fun i => c i) atTop (nhds (chainLimit c)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (chain_cauchySeq c))

/-- The limit is `n`-close to `c n`, the defining property of an OFE completion. -/
theorem dist_chainLimit (c : Chain (UltraO α)) (n : Nat) :
    UltraO.Dist n (chainLimit c) (c n) := by
  cases n with
  | zero => trivial
  | succ n =>
    change dist (chainLimit c) (c (n + 1)) ≤ (1 / 2 : ℝ) ^ n
    -- the tail of the chain lies in the closed ball; the ball is closed, so does the limit.
    have hmem : ∀ᶠ i in atTop, c i ∈ Metric.closedBall (c (n + 1)) ((1 / 2 : ℝ) ^ n) := by
      refine eventually_atTop.mpr ⟨n + 1, fun i hi => ?_⟩
      simp only [Metric.mem_closedBall]
      have hcauchy : c i ≡{n + 1}≡ c (n + 1) := c.cauchy hi
      exact show UltraO.Dist (n + 1) (c i) (c (n + 1)) from hcauchy
    have hcl : IsClosed (Metric.closedBall (c (n + 1)) ((1 / 2 : ℝ) ^ n)) :=
      Metric.isClosed_closedBall
    have hlim : chainLimit c ∈ Metric.closedBall (c (n + 1)) ((1 / 2 : ℝ) ^ n) :=
      hcl.mem_of_tendsto (chainLimit_tendsto c) hmem
    simpa [Metric.mem_closedBall] using hlim

end UltraO

/-- The Iris `IsCOFE` structure on `UltraO α` for any complete metric ultrametric
space. -/
instance instIsCOFE {α : Type*} [MetricSpace α] [IsUltrametricDist α] [CompleteSpace α] :
    IsCOFE (UltraO α) where
  compl := UltraO.chainLimit
  conv_compl := UltraO.dist_chainLimit _ _

/-! ## Concrete examples: `p`-adic numbers and integers -/

/-- The Iris `OFE` instance for `ℚ_[p]`. -/
instance Padic.instOFE (p : ℕ) [Fact p.Prime] : OFE (UltraO (Padic p)) := inferInstance

/-- The Iris `COFE` (`IsCOFE`) instance for `ℚ_[p]`. -/
instance Padic.instIsCOFE (p : ℕ) [Fact p.Prime] : IsCOFE (UltraO (Padic p)) :=
  inferInstance

/-- The Iris `OFE` instance for `ℤ_[p]`. -/
instance PadicInt.instOFE (p : ℕ) [Fact p.Prime] : OFE (UltraO (PadicInt p)) :=
  inferInstance

/-- The Iris `COFE` (`IsCOFE`) instance for `ℤ_[p]`. -/
instance PadicInt.instIsCOFE (p : ℕ) [Fact p.Prime] : IsCOFE (UltraO (PadicInt p)) :=
  inferInstance

-- Sanity check that all instances are inferrable.
section sanityCheck
variable (p : ℕ) [Fact p.Prime]
example : OFE (UltraO (Padic p)) := inferInstance
example : IsCOFE (UltraO (Padic p)) := inferInstance
example : COFE (UltraO (Padic p)) := inferInstance
example : OFE (UltraO (PadicInt p)) := inferInstance
example : IsCOFE (UltraO (PadicInt p)) := inferInstance
example : COFE (UltraO (PadicInt p)) := inferInstance
example : OFE.Leibniz (UltraO (Padic p)) := inferInstance
end sanityCheck

end IrisMath.Ultrametric
