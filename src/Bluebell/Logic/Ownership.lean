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

/-- Union closure for isIrrelevant: if K₁ and K₂ are both irrelevant, so is K₁ ∪ K₂. -/
lemma isIrrelevant_union [Fintype I] (P : HyperAssertion (IndexedPSpPmRat I α V))
    {K₁ K₂ : Set I} (h₁ : isIrrelevant K₁ P) (h₂ : isIrrelevant K₂ P) :
    isIrrelevant (K₁ ∪ K₂) P := by
  classical
  intro a ⟨a', hagree, ha'P⟩
  let a'' : I → PSpPmRat α V := fun i => if i ∈ K₁ then a' i else a i
  have hagree'' : ∀ i, i ∉ K₂ → a'' i = a' i := by
    intro i hi₂
    by_cases hi₁ : i ∈ K₁
    · simp only [a'', if_pos hi₁]
    · simp only [a'', if_neg hi₁]
      apply hagree
      simp only [Set.mem_union, not_or]
      exact ⟨hi₁, hi₂⟩
  have ha''P : a'' ∈ P := h₂ a'' ⟨a', hagree'', ha'P⟩
  have hagree_a_a'' : ∀ i, i ∉ K₁ → a i = a'' i := by
    intro i hi₁
    simp only [a'', if_neg hi₁]
  exact h₁ a ⟨a'', hagree_a_a'', ha''P⟩

/-- Empty set is trivially irrelevant. -/
lemma isIrrelevant_empty [Fintype I] (P : HyperAssertion (IndexedPSpPmRat I α V)) :
    isIrrelevant ∅ P := by
  intro a ⟨a', hagree, ha'P⟩
  have : a = a' := funext fun i => hagree i (Set.notMem_empty i)
  rw [this]
  exact ha'P

/-- Main lemma: if each differing coordinate can be covered by an irrelevant set, then a ∈ P.
This is proved by strong induction on the number of differing coordinates. -/
lemma mem_of_agree_outside_covered [Fintype I] (P : HyperAssertion (IndexedPSpPmRat I α V))
    (a' : I → PSpPmRat α V) (ha'P : a' ∈ P)
    (S : Set (Set I)) (hS : ∀ K ∈ S, isIrrelevant K P)
    (a : I → PSpPmRat α V)
    (h_cover : ∀ i, a i ≠ a' i → ∃ K ∈ S, i ∈ K) : a ∈ P := by
  classical
  -- Count differing coordinates
  let diffSet := fun (b : I → PSpPmRat α V) => Finset.univ.filter fun i => b i ≠ a' i

  -- Strong induction on the cardinality of differing set
  have key : ∀ (n : ℕ) (b : I → PSpPmRat α V),
    (∀ i, b i ≠ a' i → ∃ K ∈ S, i ∈ K) →
    (diffSet b).card = n → b ∈ P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b h_b_cover hcard
      -- Case: no differing coordinates
      by_cases h_empty : (diffSet b) = ∅
      · have hb_eq : b = a' := funext fun i => by
          by_contra h
          have hi : i ∈ diffSet b := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
          rw [h_empty] at hi
          exact Finset.notMem_empty i hi
        rw [hb_eq]
        exact ha'P
      · -- There's at least one differing coordinate
        have hD_nonempty : (diffSet b).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
        obtain ⟨x, hx⟩ := hD_nonempty
        have hx_diff : b x ≠ a' x := (Finset.mem_filter.mp hx).2

        -- Get covering set for x
        obtain ⟨K, hKS, hxK⟩ := h_b_cover x hx_diff
        have hK_irr : isIrrelevant K P := hS K hKS

        -- Define b_mid: replace b on K with a'
        let b_mid : I → PSpPmRat α V := fun i => if i ∈ K then a' i else b i

        -- b agrees with b_mid outside K
        have h_agree_b_bmid : ∀ i, i ∉ K → b i = b_mid i := by
          intro i hi
          simp only [b_mid, if_neg hi]

        -- b_mid has strictly fewer differing coordinates
        have h_bmid_fewer : (diffSet b_mid).card < (diffSet b).card := by
          apply Finset.card_lt_card
          constructor
          · -- diffSet b_mid ⊆ diffSet b
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, diffSet, b_mid] at hi ⊢
            by_cases hiK : i ∈ K
            · simp only [if_pos hiK] at hi; exact absurd rfl hi
            · simp only [if_neg hiK] at hi; exact hi
          · -- diffSet b_mid ≠ diffSet b (x is in diffSet b but not in diffSet b_mid)
            intro h_subs
            have hx_in_db : x ∈ diffSet b := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx_diff⟩
            have hx_in_db_mid : x ∈ diffSet b_mid := h_subs hx_in_db
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, diffSet, b_mid] at hx_in_db_mid
            simp only [if_pos hxK] at hx_in_db_mid
            exact hx_in_db_mid rfl

        -- b_mid satisfies the covering property
        have h_bmid_cover : ∀ i, b_mid i ≠ a' i → ∃ K ∈ S, i ∈ K := by
          intro i hi
          simp only [b_mid] at hi
          by_cases hiK : i ∈ K
          · simp only [if_pos hiK] at hi; exact absurd rfl hi
          · simp only [if_neg hiK] at hi; exact h_b_cover i hi

        -- By IH, b_mid ∈ P
        have h_bmid_P : b_mid ∈ P := by
          apply ih (diffSet b_mid).card
          · calc (diffSet b_mid).card
                 _ < (diffSet b).card := h_bmid_fewer
                 _ = n := hcard
          · exact h_bmid_cover
          · rfl

        -- Apply irrelevance of K
        exact hK_irr b ⟨b_mid, h_agree_b_bmid, h_bmid_P⟩

  exact key (diffSet a).card a h_cover rfl

/-- The complement of relevant indices is irrelevant for P.

This is a fundamental structural property that should hold for the definition of relevantIndices.
The proof shows that irrelevance is closed under arbitrary unions (equivalently, intersections
of the family of sets with irrelevant complements form an irrelevant complement).

The strategy is:
1. Show isIrrelevant is closed under binary unions (`isIrrelevant_union`)
2. Use strong induction on the number of differing coordinates (`mem_of_agree_outside_covered`)
3. For each differing coordinate, use its covering irrelevant set to "fix" it -/
theorem isIrrelevant_compl_relevantIndices [Fintype I]
    (P : HyperAssertion (IndexedPSpPmRat I α V)) :
    HyperAssertion.isIrrelevant (HyperAssertion.relevantIndices P)ᶜ P := by
  classical
  simp only [relevantIndices]
  let S := {J : Set I | isIrrelevant Jᶜ P}

  have h_eq : (sInf S : Set I)ᶜ = ⋃₀ (Set.compl '' S) := Set.compl_sInter S
  rw [h_eq]

  intro a ⟨a', hagree, ha'P⟩

  let T := Set.compl '' S

  have hT : ∀ K ∈ T, isIrrelevant K P := by
    intro K hK
    obtain ⟨J, hJS, rfl⟩ := hK
    exact hJS

  have h_cover : ∀ i, a i ≠ a' i → ∃ K ∈ T, i ∈ K := by
    intro i hi
    have h : i ∈ ⋃₀ T := by
      by_contra h_not_in
      exact hi (hagree i h_not_in)
    exact Set.mem_sUnion.mp h

  exact mem_of_agree_outside_covered P a' ha'P T hT a h_cover

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
