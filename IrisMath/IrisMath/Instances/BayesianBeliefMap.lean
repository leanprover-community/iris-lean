/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Iris

/-! # A Bayesian-belief heap: conditioning as an observation-CHANGING update

This file builds a `LawfulPartialMap` whose *values* are **unnormalized beliefs** — finitely
supported nonnegative weight vectors `α →₀ ℝ≥0` — observed through their **normalized posterior**
`prob w a = w a / total w`.  It is a sibling of `DistributionMap.lean`, sharing the
`WeightVec`/`prob`/`total`/CMRA scaffolding, but the headline here is a *different kind* of update.

## The two flavours of update, and why Bayes is the interesting one

Most non-extensional maps in this repository have only **invisible** updates: they change a hidden
representative while the observation `get?` stays fixed (e.g. rewriting `w` to `c • w` — the
normalized distribution is unchanged, so the update is logically inert through the interface).

**Bayesian conditioning is the opposite.**  Updating a belief `w` by a *likelihood*
`ℓ : α → ℝ≥0` via pointwise multiplication `w ↦ w * ℓ` is the unnormalized Bayes rule
`posterior ∝ prior × likelihood`, and it **genuinely moves the observation**:

```
prob w a = w a / total w          -- prior
   ↓  condition on ℓ
prob (w * ℓ) a = (w a * ℓ a) / total (w * ℓ)   -- posterior
```

The `get?` readout *changes* from the prior to the posterior in the structured Bayesian way — this
is a *live* frame-preserving update, not an invisible rewrite.  We prove the underlying arithmetic
(`prob_mul_likelihood`, the Bayes formula) **`sorry`-free**, prove it actually changes the
observation on a worked example (`bayes_changes_observation`, **`sorry`-free**), and lift it to the
heap-level frame-preserving update `update_condition` (the local-update lift, sharing
`DistributionMap`'s machinery).

## Non-extensionality (sorry-free)

As in `DistributionMap`, the store is non-extensional because it carries the *unnormalized* weight
but exposes only the *normalized* posterior: `prob (c • w) = prob w` for `c > 0`, so distinct raw
beliefs (different total evidence) denote the same distribution.  `equiv_ne` witnesses this with
`w` vs `w + w`.

## Summary of the prize

`prob_mul_likelihood` lifts **Bayes' rule** from Mathlib-level `Finsupp` arithmetic into a
frame-preserving update on a non-extensional belief heap.  The belief is non-extensional
(unnormalized, scale-invariant) **and** carries a genuinely observation-changing update
(conditioning moves `get?` from prior to posterior).
-/

@[expose] public section

namespace IrisMath.Instances

open Iris Iris.Std

open scoped NNReal

/-! ## The value type: unnormalized beliefs `α →₀ ℝ≥0`

A belief is a finitely supported nonnegative weight over outcomes `α`.  We reuse exactly the
`WeightVec` carrier of `DistributionMap` (re-declared here so this file is self-contained), with its
`total`/`prob` readouts and the cancellative-monoid CMRA scaffolding. -/

/-- An unnormalized belief over outcomes `α`: a finitely supported nonnegative weight vector.
Identical carrier to `DistributionMap.WeightVec`. -/
abbrev Belief (α : Type _) : Type _ := α →₀ ℝ≥0

namespace Belief

variable {α : Type _}

/-- The total mass (evidence) of a belief: `∑ a, w a`. -/
def total (w : Belief α) : ℝ≥0 := w.sum (fun _ x => x)

/-- A belief is *proper* (normalizable) when it has strictly positive total mass. -/
def Proper (w : Belief α) : Prop := 0 < w.total

/-- The **normalized posterior** probability assigned to outcome `a`: `w a / total w` (as an
`ℝ≥0`).  When `w = 0` this is `0` everywhere.  This is the only thing a client can observe. -/
noncomputable def prob (w : Belief α) (a : α) : ℝ≥0 := w a / w.total

@[simp] theorem total_zero : (0 : Belief α).total = 0 := by simp [total]

/-- The total mass is additive: fusing evidence adds total masses. -/
theorem total_add (w₁ w₂ : Belief α) : (w₁ + w₂).total = w₁.total + w₂.total := by
  classical
  simp only [total]
  exact Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; ring)

/-! ### (1) BAYES — the observation-changing update (arithmetic core)

Conditioning a belief `w` on a likelihood `ℓ` is pointwise multiplication `w * ℓ` of `Finsupp`s
(the codomain `ℝ≥0` is a `MulZeroClass`, so `(w * ℓ) a = w a * ℓ a` by `Finsupp.mul_apply`).
The normalized posterior of the conditioned belief is exactly **Bayes' rule**:
`posterior a = (prior a · likelihood a) / Z` with normalizer `Z = ∑_b w b · ℓ b`. -/

/-- The normalizer / model evidence `Z = ∑_b w b · ℓ b = total (w * ℓ)`, expressed as a `Finsupp`
sum over the conditioned belief.  Sorry-free. -/
theorem total_mul (w ℓ : Belief α) :
    (w * ℓ).total = (w * ℓ).sum (fun _ x => x) := rfl

/-- **Bayes' rule (arithmetic core), sorry-free.**  The normalized posterior of the conditioned
belief `w * ℓ` is `posterior a = (w a · ℓ a) / Z`, where the normalizer `Z = total (w * ℓ)` is the
model evidence `∑_b w b · ℓ b`.  This is `posterior ∝ prior × likelihood`, with the normalizing
constant supplied for free by `prob`. -/
theorem prob_mul_likelihood (w ℓ : Belief α) (a : α) :
    prob (w * ℓ) a = (w a * ℓ a) / (w * ℓ).total := by
  simp only [prob, Finsupp.mul_apply]

/-- The same Bayes formula with the normalizer written explicitly as the **sum of
`prior · likelihood` over the support** (`∑_b w b · ℓ b`), making the normalizing constant
manifest.  Sorry-free. -/
theorem prob_mul_likelihood_sum (w ℓ : Belief α) (a : α) :
    prob (w * ℓ) a = (w a * ℓ a) / (w * ℓ).sum (fun _ x => x) := by
  rw [prob_mul_likelihood, total_mul]

/-! ### (1b) Scale-invariance (powers BOTH the posterior contrast and non-extensionality) -/

/-- Scaling a belief by a nonzero constant leaves the normalized posterior unchanged:
`prob (w + w) = prob w`.  This is the scale-invariance at the heart of non-extensionality, and it is
exactly why a plain rescale is an *invisible* update — contrast `prob_mul_likelihood`, which moves
the observation. -/
theorem prob_double (w : Belief α) : prob (w + w) = prob w := by
  classical
  funext a
  simp only [prob, total_add, Finsupp.add_apply]
  by_cases hw : w.total = 0
  · simp [hw]
  · rw [← two_mul, ← two_mul, mul_div_mul_left _ _ (by norm_num : (2 : ℝ≥0) ≠ 0)]

end Belief

/-! ## `Belief α` is a discrete Leibniz cancellative additive commutative monoid

Identical scaffolding to `DistributionMap.WeightVec`: the Iris monoid typeclasses for pointwise `+`
with the zero belief, the discrete-of-equality OFE, and `LeftCancelAdd` (inherited from `ℝ≥0`
pointwise).  These feed `Iris.CommMonoidLike` to produce the CMRA. -/

namespace Belief

open _root_.Std (Associative Commutative LawfulLeftIdentity)

variable {α : Type _}

scoped instance instCOFE : COFE (Belief α) := COFE.ofDiscrete _ Eq_Equivalence
scoped instance instDiscreteOFE : OFE.Discrete (Belief α) := ⟨congrArg id⟩
scoped instance instLeibniz : OFE.Leibniz (Belief α) := ⟨congrArg id⟩

scoped instance instAssoc : Associative (Add.add (α := Belief α)) where
  assoc {x y z} := add_assoc x y z

scoped instance instComm : Commutative (Add.add (α := Belief α)) where
  comm {x y} := add_comm x y

scoped instance instLawfulLeftId : LawfulLeftIdentity (Add.add (α := Belief α)) (0 : Belief α) where
  left_id {x} := zero_add x

scoped instance instLeftCancelAdd : LeftCancelAdd (Belief α) where
  cancel_left {_ _ _} h := add_left_cancel h

end Belief

/-! ## The CMRA / UCMRA on `Belief α` (via `CommMonoidLike`) -/

namespace Belief

variable {α : Type _}

noncomputable scoped instance instCMRA : CMRA (Belief α) := CommMonoidLike.instCMRA
noncomputable scoped instance instUCMRA : UCMRA (Belief α) := CommMonoidLike.instUCMRA
scoped instance instDiscrete : CMRA.Discrete (Belief α) := CommMonoidLike.instDiscrete
scoped instance instCancelable (w : Belief α) : CMRA.Cancelable w :=
  CommMonoidLike.instCancelableOfLeftCancelAdd

end Belief

/-! ## (3) The `LawfulPartialMap` instance: the belief heap

Reuse the existing function-store `PartialMap`/`LawfulPartialMap` from
`Iris/Iris/Std/HeapInstances.lean`, specialized so that values are unnormalized beliefs. -/

/-- The belief store: keys `K` to optional beliefs over outcomes `α`. -/
abbrev BeliefStore (K α : Type _) : Type _ := K → Option (Belief α)

section LawfulInstance

variable {K α : Type _} [DecidableEq K]

/-- (3) **A real `LawfulPartialMap`, no `sorry`.**  The function store at belief-typed values. -/
instance instLawfulPartialMapBeliefStore : LawfulPartialMap (K → Option ·) K := inferInstance

/-- Sanity check that the specialized instance really applies. -/
example (m : K → Option (Belief α)) (k : K) (w : Belief α) :
    PartialMap.get? (M := (K → Option ·)) (PartialMap.insert (M := (K → Option ·)) m k w) k
      = some w :=
  LawfulPartialMap.get?_insert_eq rfl

end LawfulInstance

/-! ## (1, lifted) Bayesian conditioning as a frame-preserving heap update

With the function store as `LawfulPartialMap H` and `Belief α` as the value `CMRA`, `HeapView` gives
an authoritative/fragment resource algebra.  Conditioning a region's belief on a likelihood is the
local update `(w, w) ~l~> (w * ℓ, w * ℓ)` — it holds because belief addition is cancellative — lifted
via `HeapView.update_of_local_update`.  Crucially, this update **changes the observed posterior**
(by `prob_mul_likelihood`), so it is a *live* move, not an invisible rewrite. -/

namespace BeliefStore

open Iris HeapView CMRA DFrac One Belief
open scoped CommMonoidLike

variable {K α : Type _}
variable {F : Type _} [UFraction F]
variable {H : Type _ → Type _} [LawfulPartialMap H K]

/-- **Local update: condition on likelihood `ℓ`.**  Because belief addition is cancellative,
replacing `w` by the conditioned belief `w * ℓ` in lock-step (authoritative and fragment) is a local
update.  This is the engine of the heap-level Bayes update. -/
theorem condition_local_update (w ℓ : Belief α) :
    (w, w) ~l~> (w * ℓ, w * ℓ) := by
  refine CommMonoidLike.leftCancelAdd_local_update ?_
  show w + (w * ℓ) = (w * ℓ) + w
  exact add_comm _ _

/-- **(THE PRIZE) Bayesian conditioning is a frame-preserving update that CHANGES the observation.**

Owning the authoritative belief heap and the full fragment for region `k` (currently holding the
*prior* belief `w`), we may atomically condition that region on a likelihood `ℓ`, replacing `w` with
the *posterior* belief `w * ℓ`.  Through the normalized interface this moves the observed
distribution from `prob w` (prior) to `prob (w * ℓ)` (posterior, = Bayes' rule by
`prob_mul_likelihood`) — a genuinely observation-changing update.

Stated for an arbitrary `LawfulPartialMap H` (so in particular the function store).  This is
`HeapView.update_of_local_update` applied to `condition_local_update`. -/
theorem update_condition (m : H (Belief α)) (k : K) (w ℓ : Belief α)
    (Hl : PartialMap.get? m k = some w) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F K (Belief α) H) ~~>
      Auth (.own one) (PartialMap.insert m k (w * ℓ)) • Frag k (.own one) (w * ℓ) :=
  HeapView.update_of_local_update Hl (condition_local_update w ℓ)

/-- Confirmation that the concrete `AssocList`-backed resource algebra is a genuine `CMRA`, so `~~>`
is meaningful. -/
noncomputable example [UFraction F] :
    CMRA (HeapView F Nat (Belief α) AssocList) := inferInstance

/-- The Bayes update **materialized on the concrete resource algebra** (`AssocList`-backed):
conditioning region `k`'s belief on `ℓ` is a frame-preserving update. -/
theorem update_condition_concrete
    (m : AssocList (Belief α)) (k : Nat) (w ℓ : Belief α)
    (Hl : PartialMap.get? m k = some w) :
    (Auth (.own one) m • Frag k (.own one) w : HeapView F Nat (Belief α) AssocList) ~~>
      Auth (.own one) (PartialMap.insert m k (w * ℓ)) • Frag k (.own one) (w * ℓ) :=
  update_condition (H := AssocList) m k w ℓ Hl

end BeliefStore

/-! ## (1c) The observation genuinely MOVES: a worked, sorry-free example

To make "observation-changing" concrete (and to contrast with the invisible rescale `prob_double`),
we exhibit a prior, a likelihood, and a key outcome where the posterior probability differs from the
prior probability.  Concretely on the two-point outcome space `Bool`: a uniform prior, a likelihood
that favours `true` 3:1, yields a posterior strictly larger on `true`.  Sorry-free. -/

namespace Belief

open scoped NNReal

/-- Uniform prior over `Bool`: weight `1` on each of `false`, `true`. -/
noncomputable def uniformBool : Belief Bool := Finsupp.single false 1 + Finsupp.single true 1

/-- Likelihood favouring `true` 3:1: `ℓ false = 1`, `ℓ true = 3`. -/
noncomputable def likeBool : Belief Bool := Finsupp.single false 1 + Finsupp.single true 3

/-- **The Bayes update changes the observation (sorry-free worked example).**  Under the uniform
prior, `prob true = 1/2`; after conditioning on the 3:1 likelihood, the posterior `prob true = 3/4`.
The observed `get?` value at outcome `true` genuinely *moves* `1/2 ↦ 3/4` — this is a live update,
not an invisible rewrite (which would leave `prob` fixed, cf. `prob_double`). -/
theorem bayes_changes_observation :
    prob uniformBool true = 1 / 2 ∧
      prob (uniformBool * likeBool) true = 3 / 4 ∧
      prob uniformBool true ≠ prob (uniformBool * likeBool) true := by
  classical
  -- Total of the uniform prior is `2`.
  have htot_prior : uniformBool.total = 2 := by
    simp only [total, uniformBool]
    rw [Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; ring)]
    simp [Finsupp.sum_single_index]; norm_num
  -- The conditioned belief `uniform * like` is `single false 1 + single true 3`.
  have hcond : uniformBool * likeBool
      = Finsupp.single false (1 : ℝ≥0) + Finsupp.single true 3 := by
    ext b
    rw [Finsupp.mul_apply]
    simp only [uniformBool, likeBool, Finsupp.add_apply, Finsupp.single_apply]
    cases b <;> norm_num
  -- Total of the conditioned belief is `4` (the model evidence Z).
  have htot_cond : (uniformBool * likeBool).total = 4 := by
    rw [hcond]
    simp only [total]
    rw [Finsupp.sum_add_index' (by simp) (by intro a b₁ b₂; ring)]
    simp [Finsupp.sum_single_index]; norm_num
  have hnum_prior : uniformBool true = 1 := by
    simp only [uniformBool, Finsupp.add_apply, Finsupp.single_apply]; norm_num
  have hprior : prob uniformBool true = 1 / 2 := by
    rw [prob, htot_prior, hnum_prior]
  have hnum_post : uniformBool true * likeBool true = 3 := by
    simp only [uniformBool, likeBool, Finsupp.add_apply, Finsupp.single_apply]; norm_num
  have hpost : prob (uniformBool * likeBool) true = 3 / 4 := by
    rw [prob_mul_likelihood, htot_cond, hnum_post]
  exact ⟨hprior, hpost, by rw [hprior, hpost]; norm_num⟩

end Belief

/-! ## (2) Non-extensionality: unnormalized beliefs modulo normalization (sorry-free)

A *normalized-observation* store carries raw beliefs but `get?` returns only the normalized
posterior.  Since `prob (c • w) = prob w`, distinct raw beliefs that are positive scalar multiples
are indistinguishable through the interface — the intrinsic non-extensionality.  Mirrors
`DistributionMap.NormStore.equiv_ne`. -/

/-- The observed (normalized posterior) value: a belief is observed as its normalized probability
vector `fun a => w a / total w`. -/
abbrev ObsPost (α : Type _) : Type _ := α → ℝ≥0

/-- A normalized-observation belief store: carries raw beliefs as data, but lookups return only the
normalized posterior. -/
def PostStore (K α : Type _) : Type _ := K → Option (Belief α)

namespace PostStore

variable {K α : Type _} [DecidableEq K]

/-- Lookup returns the *normalized posterior*, discarding the raw scale (total evidence). -/
noncomputable def get? (m : PostStore K α) (k : K) : Option (ObsPost α) :=
  (m k).map Belief.prob

omit [DecidableEq K] in
@[simp] theorem get?_eq (m : PostStore K α) (k : K) :
    get? m k = (m k).map Belief.prob := rfl

/-- **Non-extensionality witness (sorry-free).**  For any belief `w` with strictly positive
evidence, the two singleton stores holding `w` and its double `w + w` at the same key are
`PartialMap.equiv` through the normalized-posterior interface — both observe the same posterior
`prob w = prob (w + w)` — yet are unequal as raw data (`w + w ≠ w` for `w ≠ 0`).

The store remembers *how much* total evidence it has accumulated (the scale), but a client can only
read the *shape* (the normalized posterior).  `w` and `w + w` carry different evidence yet denote the
same belief.  Contrast `Belief.bayes_changes_observation`, where a *Bayes* update genuinely moves the
observation. -/
theorem equiv_ne {w : Belief α} (hw : w ≠ 0) (k₀ : K) :
    let m₁ : PostStore K α := fun k => if k = k₀ then some w else none
    let m₂ : PostStore K α := fun k => if k = k₀ then some (w + w) else none
    (∀ k, get? m₁ k = get? m₂ k) ∧ m₁ ≠ m₂ := by
  classical
  intro m₁ m₂
  refine ⟨?_, ?_⟩
  · intro k
    simp only [get?_eq, m₁, m₂]
    by_cases h : k = k₀
    · subst h
      simp only [if_true, Option.map_some, Option.some.injEq]
      exact (Belief.prob_double w).symm
    · simp [h]
  · intro hcontra
    have hk₀ := congrFun hcontra k₀
    simp only [m₁, m₂, if_pos rfl, Option.some.injEq] at hk₀
    apply hw
    exact add_right_cancel (a := w) (b := w) (c := 0) (by simpa using hk₀)

end PostStore

end IrisMath.Instances
