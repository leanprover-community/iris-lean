import Bluebell.Algebra.HyperAssertion
import Bluebell.Algebra.PSpPm
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Bluebell

open Iris ProbabilityTheory MeasureTheory HyperAssertion

variable {I α V : Type*} [Nonempty V]

noncomputable section

/-- Ownership of an indexed tuple of probability spaces `P : I → ProbabilitySpace (α → V)`
and permissions `p : I → PermissionRat α`, given compatibility witnesses. -/
def ownIndexedTuple (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) (p : I → PermissionRat α) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun h : ∀ i, PSp.compatiblePermRat (WithTop.some (P i)) (p i) =>
    own (M := IndexedPSpPmRat I α V) (fun i => ⟨WithTop.some (P i), p i, h i⟩))

/-- Ownership of an indexed probability spaces `P : I → ProbabilitySpace (α → V)`,
defined as the existence of a compatible indexed permission. -/
def ownIndexedProb (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun p : I → PermissionRat α => ownIndexedTuple (I := I) (α := α) (V := V) P p)

variable [DecidableEq I] [Nonempty V]

/-- The hyper-assertion `E⟨i⟩ ∼ μ`. -/
def assertSampledFrom {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) (μ : PMF β) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun P : I → ProbabilityTheory.ProbabilitySpace (α → V) =>
    sep (ownIndexedProb (I := I) (α := α) (V := V) P)
      (pure (@AEMeasurable _ _ _ (P i).σAlg E (P i).μ ∧
        μ.toMeasure = @Measure.map _ _ (P i).σAlg _ E (P i).μ)))

/-- Assertion that the expected value of `E` at index `i` is `ev`. -/
def assertExpectation {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [AddCommMonoid β] [SMul ENNReal β]
    (i : I) (E : (α → V) → β) (ev : β) : HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun μ => sep (assertSampledFrom (I := I) (α := α) (V := V) i E μ)
    (pure (ev = ∑' b, (μ b) • b)))

/-- Assertion that the probability of a Boolean-valued expression `E` at index `i` is `prob`. -/
def assertProbability (i : I) (E : (α → V) → Bool) (prob : ENNReal) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun μ => sep (assertSampledFrom (I := I) (α := α) (V := V) i E μ)
    (pure (prob = μ true)))

/-- Assertion that `E` is true almost surely. -/
noncomputable def assertTrue (i : I) (E : (α → V) → Bool) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  assertSampledFrom (I := I) (α := α) (V := V) i E (PMF.pure true)

/-- Assertion that we own `E` (but its distribution is not known). -/
def assertOwn {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun μ => assertSampledFrom (I := I) (α := α) (V := V) i E μ)

/-- Assertion that the variable `x : α` at index `i` has permission `q : ℚ≥0`. -/
def assertPermissionVar (i : I) (x : α) (q : ℚ≥0) : HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun Pp : IndexedPSpPmRat I α V =>
    sep (own (M := IndexedPSpPmRat I α V) Pp)
        (pure ((Pp i).perm x = q)))

/-- Conjoin a `P` with ownership derived from a compatible `p`. -/
def assertPermission (P : HyperAssertion (IndexedPSpPmRat I α V)) (p : I → PermissionRat α) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  and P <|
    «exists»
      (fun compatP :
        {P : I → ProbabilityTheory.ProbabilitySpace (α → V) //
          ∀ i, PSp.compatiblePermRat (WithTop.some (P i)) (p i)} =>
      own (M := IndexedPSpPmRat I α V) (fun i => ⟨WithTop.some (compatP.1 i), p i, compatP.2 i⟩))

end

open HyperAssertion

variable {I α V : Type*} [Nonempty V]

/-! ### Ownership rules (moved from Basic) -/

section Rules

variable [DecidableEq I]

/-- If `P` and `Q` affect disjoint sets of indices, then `P ∧ Q` entails `P ∗ Q`. -/
theorem sep_of_and [Fintype I]
    {P Q : HyperAssertion (IndexedPSpPmRat I α V)}
    (h : HyperAssertion.relevantIndices P ∩ HyperAssertion.relevantIndices Q = ∅) :
    HyperAssertion.entails (HyperAssertion.and P Q) (HyperAssertion.sep P Q) := by
  sorry

/-- If `E⟨i⟩` is sampled from both `μ` and `μ'`, then `⌜ μ = μ' ⌝` holds as a proposition. -/
theorem sampledFrom_inj {β : Type*} [MeasurableSpace β]
    {i : I} {E : (α → V) → β} {μ μ' : PMF β} :
    HyperAssertion.entails
      (HyperAssertion.and
        (assertSampledFrom (I := I) (α := α) (V := V) i E μ)
        (assertSampledFrom (I := I) (α := α) (V := V) i E μ'))
      (HyperAssertion.pure (μ = μ')) := by
  sorry

/-- `E₁⟨i⟩` and `E₂⟨i⟩` are both true iff `E₁⟨i⟩ ∧ E₂⟨i⟩` is true. -/
theorem sep_assertTrue_iff {i : I} {E₁ E₂ : (α → V) → Bool} :
    HyperAssertion.equiv
      (HyperAssertion.sep
        (assertTrue (I := I) (α := α) (V := V) i E₁)
        (assertTrue (I := I) (α := α) (V := V) i E₂))
      (assertTrue (I := I) (α := α) (V := V) i (fun x => E₁ x ∧ E₂ x)) := by
  sorry

/-- If `pabs(𝑃, pvar(𝐸⟨𝑖⟩))` (to be defined), then `assertTrue i E ∧ P` entails `assertTrue i E ∗ P`. -/
theorem sep_of_and_assertTrue {i : I} {E : (α → V) → Bool}
    {P : HyperAssertion (IndexedPSpPmRat I α V)} (h : True) :
    HyperAssertion.entails
      (HyperAssertion.sep
        (assertTrue (I := I) (α := α) (V := V) i E)
        P)
      (HyperAssertion.and
        (assertTrue (I := I) (α := α) (V := V) i E)
        P) := by
  sorry

/-- Sampling on a product splits into sampling each component. -/
theorem sampledFrom_prod {β₁ β₂ : Type _}
    [MeasurableSpace β₁] [MeasurableSpace β₂] {i : I}
    (E₁ : (α → V) → β₁) (E₂ : (α → V) → β₂)
    (μ₁ : PMF β₁) (μ₂ : PMF β₂) :
    HyperAssertion.entails
      (assertSampledFrom (I := I) (α := α) (V := V) i (fun x => (E₁ x, E₂ x))
        (Prod.mk <$> μ₁ <*> μ₂))
      (HyperAssertion.sep
        (assertSampledFrom (I := I) (α := α) (V := V) i E₁ μ₁)
        (assertSampledFrom (I := I) (α := α) (V := V) i E₂ μ₂)) := by
  sorry

end Rules

end Bluebell
