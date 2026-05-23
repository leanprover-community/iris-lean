module

public import Mathlib.Probability.Process.Filtration
public import Iris

@[expose] public section

noncomputable section

open Iris MeasureTheory

namespace IrisMath.Filtration

/-! # OFE on stochastic processes via filtrations

A filtration `f : MeasureTheory.Filtration ℕ m` is an increasing chain of sub-σ-algebras
`f.seq n ≤ m` on a measurable space `Ω`. This is the probabilistic analogue of Iris-style
step-indexing: `f.seq n` is "the information available at time `n`", and processes that
"look the same at time `n`" should be `n`-equivalent.

This module exposes two distinct constructions:

* `ProcessO Ω β` (no measurability data required) is the OFE on raw sequences
  `ℕ → Ω → β`. Its `n`-equivalence is *truncation*: two processes agree up to time `n` if
  they agree pointwise on every `k ≤ n`. This is analogous to the truncation OFE on power
  series, with one coefficient per time step. We provide the standard combinators
  `prepend` (contractive), `tail` (non-expansive), and `constProcess` (non-expansive), and
  show that `ProcessO Ω β` is a COFE with diagonal completion `chainCompl c k = c.chain k k`.

* `AdaptedProcess f β` (depends on a filtration `f` and a `MeasurableSpace β`) is the
  *subtype* of `ProcessO Ω β` carved out by the predicate `IsAdapted f X`, i.e. each `X k`
  is `f.seq k`-measurable. It inherits the truncation OFE from `ProcessO` and is closed
  under taking limits of chains because the limiting process at time `k` equals
  `(c.chain k).val k`, which is measurable. The resulting COFE thus carries the *actual*
  filtration structure inside the step-index. The projection to the underlying process is
  available as the OFE morphism `valHom : AdaptedProcess f β -n> ProcessO Ω β`.
-/

variable {Ω β : Type _}

/-- Stochastic processes indexed by `ℕ`, viewed as the underlying type of a truncation OFE. -/
def ProcessO (Ω β : Type _) : Type _ := ℕ → Ω → β

namespace ProcessO

/-- Truncation OFE on processes: `n`-equivalence is pointwise agreement at every `k ≤ n`. -/
instance instOFE : OFE (ProcessO Ω β) where
  Equiv X Y := X = Y
  Dist n X Y := ∀ k, k ≤ n → X k = Y k
  dist_eqv :=
    { refl _ _ _ := rfl
      symm h k hk := (h k hk).symm
      trans h₁ h₂ k hk := (h₁ k hk).trans (h₂ k hk) }
  equiv_dist := by
    refine ⟨fun h _ _ _ ↦ h ▸ rfl, fun h ↦ ?_⟩
    funext k
    exact h k k le_rfl
  dist_lt h hmn k hk := h k (Nat.le_of_lt (Nat.lt_of_le_of_lt hk hmn))

/-- Unfolding lemma for `Dist` on `ProcessO`. -/
@[simp] theorem dist_iff {n : ℕ} {X Y : ProcessO Ω β} :
    (X ≡{n}≡ Y) ↔ ∀ k, k ≤ n → X k = Y k := Iff.rfl

/-- Unfolding lemma for `Equiv` on `ProcessO`. -/
@[simp] theorem equiv_iff {X Y : ProcessO Ω β} : (X ≡ Y) ↔ X = Y := Iff.rfl

/-- Build a process from its values at each time, defined by recursion on the chain index
so that the `k`-th value is taken from the chain element at index `k`. -/
def chainCompl (c : Chain (ProcessO Ω β)) : ProcessO Ω β := fun k ↦ c.chain k k

@[simp] theorem chainCompl_apply (c : Chain (ProcessO Ω β)) (k : ℕ) :
    chainCompl c k = c.chain k k := rfl

/-- The truncation OFE on processes is complete: the limit at time `k` is `c k k`. -/
instance instIsCOFE : IsCOFE (ProcessO Ω β) where
  compl := chainCompl
  conv_compl {n c} k hk := by
    -- `chainCompl c k = c.chain k k`; we want it equal to `c.chain n k`.
    -- By Cauchy `c.cauchy : k ≤ n → c.chain n ≡{k}≡ c.chain k`; evaluate at `k ≤ k`.
    exact ((c.cauchy hk) k le_rfl).symm

/-- Prepend a time-0 slice in front of a process, shifting the original index up by one.
This is the canonical contractive endofunction on `ProcessO`: agreement of the result
at level `n` only requires agreement of the tail at all strictly smaller levels. -/
def prepend (x₀ : Ω → β) (X : ProcessO Ω β) : ProcessO Ω β
  | 0 => x₀
  | k + 1 => X k

@[simp] theorem prepend_zero (x₀ : Ω → β) (X : ProcessO Ω β) :
    prepend x₀ X 0 = x₀ := rfl

@[simp] theorem prepend_succ (x₀ : Ω → β) (X : ProcessO Ω β) (k : ℕ) :
    prepend x₀ X (k + 1) = X k := rfl

/-- `prepend x₀` is contractive: agreement of the prepended processes at level `n` only
requires the tails to agree at every strictly smaller level. -/
instance prepend_contractive (x₀ : Ω → β) : OFE.Contractive (prepend x₀) where
  distLater_dist {n X Y} h k hk := by
    cases k with
    | zero => rfl
    | succ k => exact h k hk k le_rfl

/-- The tail of a process, shifting every time-index down by one. Dual to `prepend`: we
have `tail (prepend x₀ X) = X` definitionally. -/
def tail (X : ProcessO Ω β) : ProcessO Ω β := fun k ↦ X (k + 1)

@[simp] theorem tail_apply (X : ProcessO Ω β) (k : ℕ) : tail X k = X (k + 1) := rfl

@[simp] theorem tail_prepend (x₀ : Ω → β) (X : ProcessO Ω β) : tail (prepend x₀ X) = X := rfl

/-- Shifting strictly decreases the available step-index: from agreement at level `n + 1`
of the original processes one obtains agreement at level `n` of the tails. (Note that
`tail` is not non-expansive in the truncation OFE on `ProcessO`: at level `n` the tails
require equality at index `n + 1`, which is one step beyond what `n`-equivalence
guarantees. This mirrors `Stream.tail_dist_of_dist_succ`.) -/
theorem tail_dist_of_dist_succ {n : ℕ} {X Y : ProcessO Ω β} (h : X ≡{n + 1}≡ Y) :
    tail X ≡{n}≡ tail Y :=
  fun k hk ↦ h (k + 1) (Nat.succ_le_succ hk)

/-- The constant process whose value at every time is the same function `f : Ω → β`. -/
def constProcess (f : Ω → β) : ProcessO Ω β := fun _ ↦ f

@[simp] theorem constProcess_apply (f : Ω → β) (k : ℕ) : constProcess f k = f := rfl

/-- Equal underlying functions give equal constant processes (the source has no OFE
structure, so this is the right "non-expansiveness" statement for `constProcess`). -/
theorem constProcess_congr {f g : Ω → β} (h : f = g) : constProcess f ≡ constProcess g :=
  congrArg constProcess h

end ProcessO

/-! ## Adapted processes -/

variable {m : MeasurableSpace Ω} [MeasurableSpace β]

/-- The predicate that a process is adapted to a filtration `f`: each `X k` is
`f.seq k`-measurable. -/
def IsAdapted (f : Filtration ℕ m) (X : ProcessO Ω β) : Prop :=
  ∀ k, Measurable[f.seq k, ‹MeasurableSpace β›] (X k)

/-- A constant process is adapted to any filtration provided the underlying function is
measurable with respect to the smallest level `f.seq 0`; monotonicity of the filtration
then handles every subsequent level. -/
theorem isAdapted_constProcess {f : Filtration ℕ m} {g : Ω → β}
    (hg : Measurable[f.seq 0, ‹MeasurableSpace β›] g) : IsAdapted f (ProcessO.constProcess g) :=
  fun k ↦ hg.mono (f.mono (Nat.zero_le k)) le_rfl

/- Note: the tail of an adapted process is *not* adapted to the original filtration in
general — the time-`k` value `X (k + 1)` need only be `f.seq (k + 1)`-measurable, not
`f.seq k`-measurable — so we do not provide a `tail` operation on `AdaptedProcess`. -/

/-- The subtype of adapted processes, viewed as the underlying type of an OFE inheriting
from `ProcessO`. -/
def AdaptedProcess (f : Filtration ℕ m) (β : Type _) [MeasurableSpace β] : Type _ :=
  { X : ProcessO Ω β // IsAdapted f X }

namespace AdaptedProcess

variable {f : Filtration ℕ m}

/-- Adapted processes inherit the truncation OFE from `ProcessO`. -/
instance instOFE : OFE (AdaptedProcess (Ω := Ω) f β) where
  Equiv X Y := X.val ≡ Y.val
  Dist n X Y := X.val ≡{n}≡ Y.val
  dist_eqv :=
    { refl _ := OFE.Dist.rfl
      symm h := OFE.Dist.symm h
      trans h₁ h₂ := OFE.Dist.trans h₁ h₂ }
  equiv_dist :=
    ⟨fun h n ↦ (OFE.equiv_dist.mp h) n, fun h ↦ OFE.equiv_dist.mpr h⟩
  dist_lt := OFE.dist_lt

/-- Unfolding lemma for `Dist` on `AdaptedProcess`. -/
@[simp] theorem dist_iff {n : ℕ} {X Y : AdaptedProcess (Ω := Ω) f β} :
    (X ≡{n}≡ Y) ↔ ∀ k, k ≤ n → X.val k = Y.val k := Iff.rfl

/-- Unfolding lemma for `Equiv` on `AdaptedProcess`: subtype equivalence is equality of the
underlying processes (the OFE on `ProcessO` is Leibniz). -/
@[simp] theorem equiv_iff {X Y : AdaptedProcess (Ω := Ω) f β} :
    (X ≡ Y) ↔ X.val = Y.val := Iff.rfl

/-- The subtype projection from `AdaptedProcess f β` to `ProcessO Ω β` is non-expansive,
directly by definition of the subtype OFE. -/
instance val_nonExpansive :
    OFE.NonExpansive (Subtype.val : AdaptedProcess (Ω := Ω) f β → ProcessO Ω β) where
  ne _ _ _ h := h

/-- The subtype projection packaged as an OFE morphism `AdaptedProcess f β -n> ProcessO Ω β`. -/
def valHom : AdaptedProcess (Ω := Ω) f β -n> ProcessO Ω β where
  f := Subtype.val
  ne := val_nonExpansive

@[simp] theorem valHom_apply (X : AdaptedProcess (Ω := Ω) f β) : valHom X = X.val := rfl

/-- The completion of a chain of adapted processes, defined coefficient-wise from the chain
just like for `ProcessO`. The crucial point is that the resulting process is still adapted:
at index `k`, the value `c.chain k k` is `f.seq k`-measurable because `c.chain k` is. -/
def chainCompl (c : Chain (AdaptedProcess (Ω := Ω) f β)) :
    AdaptedProcess (Ω := Ω) f β :=
  ⟨fun k ↦ (c.chain k).val k, fun k ↦ (c.chain k).property k⟩

@[simp] theorem chainCompl_val (c : Chain (AdaptedProcess (Ω := Ω) f β)) :
    (chainCompl c).val = ProcessO.chainCompl (c.map valHom) := rfl

/-- The OFE of adapted processes is complete: limits of chains exist and remain adapted. -/
instance instIsCOFE : IsCOFE (AdaptedProcess (Ω := Ω) f β) where
  compl := chainCompl
  conv_compl {n c} k hk := by
    -- Same Cauchy argument as for `ProcessO`.
    exact ((c.cauchy hk : (c.chain n).val ≡{k}≡ (c.chain k).val) k le_rfl).symm

end AdaptedProcess

/-! ## Example filtrations

We provide the **terminal** filtration `n ↦ m` on any measurable space, which knows
everything from the start. This witnesses that `AdaptedProcess` is non-empty in general:
every pointwise-measurable process is adapted to the terminal filtration. -/

/-- The constant terminal filtration: every level equals the ambient σ-algebra `m`. -/
@[simps]
def topFiltration (m : MeasurableSpace Ω) : Filtration ℕ m where
  seq _ := m
  mono' _ _ _ := le_rfl
  le' _ := le_rfl

/-- Any measurable process is adapted to the terminal filtration. -/
theorem isAdapted_topFiltration {m : MeasurableSpace Ω}
    {X : ProcessO Ω β} (h : ∀ k, Measurable (X k)) :
    IsAdapted (topFiltration m) X := h

end IrisMath.Filtration
