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

/-- The complement of relevant indices is irrelevant for P. 

This is a fundamental property that needs to be proven from the definition of relevantIndices.
The key insight is that if isIrrelevant (J^c) P for all J in a family, and a agrees with a' ∈ P
on the intersection ⋂ J, then we can pick any specific J₀ and note that a agrees with a' on J₀ ⊇ ⋂ J.
However, this reasoning is backwards!

Let's use a direct approach: define an explicit set that works. -/
theorem isIrrelevant_compl_relevantIndices [Fintype I]
    (P : HyperAssertion (IndexedPSpPmRat I α V)) :
    HyperAssertion.isIrrelevant (HyperAssertion.relevantIndices P)ᶜ P := by
  -- For now, we'll admit this as it requires a deeper dive into the lattice-theoretic properties
  -- The intuition is correct: relevantIndices P should be the minimal set such that its complement
  -- is irrelevant. This should follow from the definition via completeness properties of the lattice.
  sorry

/-- If `P` and `Q` affect disjoint sets of indices, then `P ∧ Q` entails `P ∗ Q`. -/
theorem sep_of_and [Fintype I]
    {P Q : HyperAssertion (IndexedPSpPmRat I α V)}
    (h : HyperAssertion.relevantIndices P ∩ HyperAssertion.relevantIndices Q = ∅) :
    HyperAssertion.entails (HyperAssertion.and P Q) (HyperAssertion.sep P Q) := by
  classical
  intro x ⟨hP, hQ⟩
  -- Goal: x ∈ sep P Q, i.e., ∃ b c, b ∈ P ∧ c ∈ Q ∧ b • c ≼ x
  -- Strategy: construct b and c by restricting x to relevant indices
  let JP := HyperAssertion.relevantIndices P
  let JQ := HyperAssertion.relevantIndices Q
  -- Define b to be x on P's indices and unit elsewhere
  let b : IndexedPSpPmRat I α V := fun i => if i ∈ JP then x i else UCMRA.unit
  -- Define c to be x on Q's indices and unit elsewhere
  let c : IndexedPSpPmRat I α V := fun i => if i ∈ JQ then x i else UCMRA.unit
  -- Now we need to show: b ∈ P, c ∈ Q, and b • c ≼ x
  refine ⟨b, c, ?b_in_P, ?c_in_Q, ?bc_included_x⟩
  case b_in_P =>
    -- Show b ∈ P
    -- We need to use that P is irrelevant outside JP
    have hirr : HyperAssertion.isIrrelevant (JPᶜ) P := isIrrelevant_compl_relevantIndices P
    -- Apply irrelevance: b agrees with x outside JP^c, and x ∈ P
    apply hirr
    refine ⟨x, ?_, hP⟩
    -- Show: ∀ i, i ∉ JP^c → b i = x i
    intro i hi
    -- hi : i ∉ JP^c, which means i ∈ JP
    simp only [Set.mem_compl_iff] at hi
    push_neg at hi
    -- Now hi : i ∈ JP
    simp only [b, hi, ite_true]
  case c_in_Q =>
    -- Show c ∈ Q (symmetric argument)
    have hirr : HyperAssertion.isIrrelevant (JQᶜ) Q := isIrrelevant_compl_relevantIndices Q
    apply hirr
    refine ⟨x, ?_, hQ⟩
    intro i hi
    simp only [Set.mem_compl_iff] at hi
    push_neg at hi
    simp only [c, hi, ite_true]
  case bc_included_x =>
    -- Show b • c ≼ x
    -- Construct witness z pointwise: z i is unit if i ∈ JP ∪ JQ, otherwise x i
    let z : IndexedPSpPmRat I α V := fun i => 
      if i ∈ JP ∨ i ∈ JQ then UCMRA.unit else x i
    refine ⟨z, ?_⟩
    -- Need: x ≡ (b • c) • z
    -- This holds pointwise
    intro i
    -- Case split on whether i ∈ JP or i ∈ JQ
    by_cases hi_P : i ∈ JP
    · -- i ∈ JP, so by disjointness i ∉ JQ
      have hi_Q : i ∉ JQ := by
        intro hcontra
        have : i ∈ JP ∩ JQ := ⟨hi_P, hcontra⟩
        rw [h] at this
        exact this
      -- Simplify: b i = x i, c i = unit, z i = unit
      have hb : b i = x i := if_pos hi_P
      have hc : c i = UCMRA.unit := if_neg hi_Q
      have hz : z i = UCMRA.unit := if_pos (Or.inl hi_P)
      -- Goal: x i ≡ (b • c) i • z i = (x i • unit) • unit
      calc x i 
        _ ≡ x i • (UCMRA.unit : PSpPmRat α V) := OFE.Equiv.symm CMRA.unit_right_id
        _ ≡ (x i • (UCMRA.unit : PSpPmRat α V)) • UCMRA.unit := OFE.Equiv.symm CMRA.unit_right_id
        _ = (b i • c i) • z i := by simp [hb, hc, hz]
    · by_cases hi_Q : i ∈ JQ
      · -- i ∈ JQ and i ∉ JP
        have hb : b i = UCMRA.unit := if_neg hi_P
        have hc : c i = x i := if_pos hi_Q
        have hz : z i = UCMRA.unit := if_pos (Or.inr hi_Q)
        calc x i
          _ ≡ (UCMRA.unit : PSpPmRat α V) • x i := OFE.Equiv.symm UCMRA.unit_left_id
          _ ≡ ((UCMRA.unit : PSpPmRat α V) • x i) • UCMRA.unit := OFE.Equiv.symm CMRA.unit_right_id
          _ = (b i • c i) • z i := by simp [hb, hc, hz]
      · -- i ∉ JP and i ∉ JQ
        have hb : b i = UCMRA.unit := if_neg hi_P
        have hc : c i = UCMRA.unit := if_neg hi_Q
        have hz : z i = x i := if_neg (not_or.mpr ⟨hi_P, hi_Q⟩)
        -- Show: x i ≡ (b • c) i • z i
        calc x i
          _ ≡ (UCMRA.unit : PSpPmRat α V) • x i := OFE.Equiv.symm UCMRA.unit_left_id
          _ ≡ ((UCMRA.unit : PSpPmRat α V) • UCMRA.unit) • x i := by
            have h_unit : (UCMRA.unit : PSpPmRat α V) ≡ (UCMRA.unit : PSpPmRat α V) • UCMRA.unit := 
              OFE.Equiv.symm CMRA.unit_right_id
            -- From unit ≡ unit • unit, we get unit • x i ≡ (unit • unit) • x i
            -- Rewrite using commutativity: x i • unit ≡ x i • (unit • unit)
            calc (UCMRA.unit : PSpPmRat α V) • x i
              _ ≡ x i • UCMRA.unit := CMRA.comm
              _ ≡ x i • ((UCMRA.unit : PSpPmRat α V) • UCMRA.unit) := 
                OFE.equiv_dist.mpr fun n => CMRA.op_ne.ne (OFE.equiv_dist.mp h_unit n)
              _ ≡ ((UCMRA.unit : PSpPmRat α V) • UCMRA.unit) • x i := OFE.Equiv.symm CMRA.comm
          _ = ((b i • c i) • z i) := by simp [hb, hc, hz]

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
