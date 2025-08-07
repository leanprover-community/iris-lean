import Iris
import Iris.Algebra.CMRA
import Bluebell.ProbabilityTheory.Coupling
import Bluebell.ProbabilityTheory.IndepProduct

/-! # Formalizing the Bluebell paper

This is a copy from an initial attempt in VCV-io. We comment out most of this since there are lots of errors due to updates in Iris. -/

open Iris ProbabilityTheory MeasureTheory

-- Indexed tuples
def indexedTuple (α : Type*) (I : Finset ℕ) := I → α

def indexedTuple.remove (α : Type*) (I : Finset ℕ) (J : Finset ℕ) (_ : J ⊆ I) :
    indexedTuple α I → indexedTuple α (I \ J) :=
  fun x i => x ⟨i.1, by aesop⟩

-- /-- A typeclass for expressing that a type `M` has a validity predicate `✓` -/
-- class Valid (M : Type*) where
--   valid : M → Prop

-- export Valid (valid)

-- prefix:50 "✓" => Valid.valid

-- instance {α : Type*} [Valid α] (p : α → Prop) : Valid (Subtype p) where
--   valid := fun x => Valid.valid x.1

-- instance {α β : Type*} [Valid α] [Valid β] : Valid (α × β) where
--   valid := fun x => Valid.valid x.1 ∧ Valid.valid x.2

-- /-- The class of **discrete** cameras, which do not care about step-indexing

-- TODO: use `Discrete` instance from `CMRA` -/
-- class DiscreteCMRA (α : Type*) extends CommSemigroup α, Valid α where
--   equiv : α → α → Prop
--   pcore : α → Option α

--   is_equiv : Equivalence equiv

--   mul_equiv {x y z} : equiv y z → equiv (x * y) (x * z)
--   pcore_equiv {x y cx} : equiv x y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ equiv cx cy

--   pcore_left {x cx} : pcore x = some cx → equiv (cx * x) x
--   pcore_idem {x cx} : pcore x = some cx → equiv x cx
--   pcore_mono' {x y cx} : pcore x = some cx → ∃ cy, pcore (x * y) = some (cx * cy)

--   -- TODO: check whether these are stated correctly
--   valid_equiv {x y} : equiv x y → valid x → valid y
--   valid_mul {x y} : valid (x * y) → valid x

-- section DiscreteCMRA

-- variable {α : Type*} [DiscreteCMRA α] {x y₁ y₂ : α}
-- open DiscreteCMRA

-- lemma valid_extend : valid x → equiv x (y₁ * y₂) → ∃ z₁ z₂, equiv x (z₁ * z₂) := by tauto

-- lemma valid_l_of_equiv_mul (h₁ : valid x) (h₂ : equiv x (y₁ * y₂)) : valid y₁ :=
--                            valid_mul (valid_equiv h₂ h₁)

-- lemma valid_r_of_equiv_mul (h₁ : valid x) (h₂ : equiv x (y₁ * y₂)) : valid y₂ :=
--                            valid_mul (valid_equiv (mul_comm y₁ y₂ ▸ h₂) h₁)

-- example : valid x → equiv x (y₁ * y₂) → ∃ z₁ z₂, equiv x (z₁ * z₂) ∧ valid z₁ ∧ valid z₂ :=
--   λ h₁ h₂ ↦ let ⟨z₁, z₂, h⟩ := valid_extend h₁ h₂
--             ⟨z₁, z₂, h, valid_l_of_equiv_mul h₁ h, valid_r_of_equiv_mul h₁ h⟩

-- end DiscreteCMRA

-- instance DiscreteCMRA.instOFE (α : Type*) [DiscreteCMRA α] : OFE α where
--   Equiv := equiv
--   Dist := fun _ ↦ equiv
--   dist_eqv := by simp [DiscreteCMRA.is_equiv]
--   equiv_dist := by simp
--   dist_lt := fun h _ ↦ h

-- /-- A discrete CMRA can be converted to a regular CMRA -/
-- instance DiscreteCMRA.instCMRA {α : Type*} [DiscreteCMRA α] : CMRA α :=
--   {
--     pcore := pcore
--     op := (·*·)
--     ValidN := fun _ x ↦ valid x
--     Valid := valid
--     op_ne := ⟨fun _ _ _ h ↦ mul_equiv h⟩
--     pcore_ne := pcore_equiv
--     validN_ne := valid_equiv
--     valid_iff_validN := by simp
--     validN_succ := by simp
--     assoc := by simp [mul_assoc]
--     comm := by simp [mul_comm]
--     pcore_op_left := pcore_left
--     pcore_idem := λ h ↦ by obtain ⟨_, h₁, h₂⟩ := pcore_equiv (pcore_idem h) h
--                            exact h₁ ▸ OFE.Equiv.symm h₂
--     pcore_op_mono := pcore_mono'
--     validN_op_left := valid_mul
--     extend {_ _ y₁ y₂ _ _} := by use y₁, y₂; simpa
--   }

-- -- class DiscreteUnitalCMRA (α : Type*) extends DiscreteCMRA α, One α where

-- /-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
-- `1 * a = a` on the left.

-- This is a unbundled version of `MulOneClass` where we don't require `a * 1 = a` on the right. -/
-- class MulOneLeftClass (M : Type*) extends One M, Mul M where
--   /-- One is a left neutral element for multiplication -/
--   protected one_mul : ∀ a : M, 1 * a = a

-- attribute [simp] MulOneLeftClass.one_mul

-- instance {M : Type*} [MulOneClass M] : MulOneLeftClass M where
--   one_mul := one_mul

-- /-- An ordered unital resource algebra is a type with a multiplication, a one, a preorder `≤`,
--   and a validity predicate `✓`, such that:

--   - `1` is valid
--   - validity is downward closed: `a ≤ b → ✓ b → ✓ a`
--   - validity of multiplication cancels on the right: `✓ (a * b) → ✓ a`
--   - multiplication on the right is monotone: `a ≤ b → a * c ≤ b * c` -/
-- class OrderedUnitalResourceAlgebra (M : Type*) extends
--     MulOneLeftClass M, Valid M, Preorder M, MulRightMono M where
--   valid_one : ✓ (1 : M)
--   valid_mono {a b} : a ≤ b → ✓ b → ✓ (a : M)
--   valid_mul {a b} : ✓ (a * b : M) → ✓ a

-- export OrderedUnitalResourceAlgebra (valid_one valid_mono valid_mul)

-- attribute [simp] valid_one

-- namespace OrderedUnitalResourceAlgebra

-- variable {I M : Type*} [OrderedUnitalResourceAlgebra M]

-- instance : MulRightMono M := ⟨fun _ _ _ h ↦ mul_right_mono h⟩

-- /-- Lifting the validity predicate to indexed tuples by requiring all elements to be valid -/
-- @[simp]
-- instance [Valid M] : Valid (I → M) where
--   valid := fun x => ∀ i, ✓ x i

-- /-- A resource algebra on `M` is lifted pointwise to a resource algebra on `I → M` -/
-- instance {I : Type*} : OrderedUnitalResourceAlgebra (I → M) where
--   one_mul := by intro a; funext i; simp only [Pi.mul_apply, Pi.one_apply, MulOneLeftClass.one_mul]
--   valid_one := by intro i; exact valid_one
--   valid_mono := by intro _ _ hab hb i; exact valid_mono (hab i) (hb i)
--   valid_mul := by intro _ _ hab i; exact valid_mul (hab i)
--   elim := by intro _ _ _ h; exact fun i => mul_right_mono (h i)

-- /-- Define a discrete `CMRA` instance given an `OrderedUnitalResourceAlgebra` instance -/
-- instance instCMRA : DiscreteCMRA M := sorry

-- end OrderedUnitalResourceAlgebra


-- /-! ## Permissions -/

-- /-- A permission on type `α` is a map from `α` to the non-negative rationals `ℚ≥0`.

-- We need to have the `Multiplicative` tag in order to specify that multiplication is pointwise
-- addition, and unit is the constant zero map. -/
-- @[reducible] def Permission (α : Type*) := Multiplicative (α → ℚ≥0)

-- variable {α : Type*}

-- -- instance : Preorder (Permission α) := inferInstanceAs (Preorder (Multiplicative (α → ℚ≥0)))
-- -- instance : MulOneClass (Permission α) := inferInstanceAs (MulOneClass (Multiplicative (α → ℚ≥0)))
-- -- instance : MulLeftMono (Permission α) := inferInstanceAs (MulLeftMono (Multiplicative (α → ℚ≥0)))

-- /-- Permissions form an `OrderedUnitalResourceAlgebra` where `≤` is defined pointwise, a resource is valid iff it's below `1` pointwise, and composition is pointwise multiplication -/
-- instance : OrderedUnitalResourceAlgebra (Permission α) where
--   valid := fun p => p ≤ 1
--   valid_one := by simp
--   valid_mul := by intro a b hab; simp_all only [le_one_iff_eq_one, LeftCancelMonoid.mul_eq_one,
--     le_refl]
--   valid_mono := by intro a b h h'; simp_all only [le_one_iff_eq_one]
--   -- mul_right_mono := by intro a b c h i; sorry

-- /-! ## Probability spaces -/

-- variable {Ω : Type*}

-- noncomputable section

-- -- We want the trivial `{∅, Ω}` sigma algebra, upon which the measure is defined to be `0` on `∅`
-- -- and `1` on `Ω`
-- instance [inst : Nonempty Ω] : One (ProbabilitySpace Ω) where
--   one := @ProbabilitySpace.mk Ω (@MeasureSpace.mk Ω ⊥ (@Measure.dirac _ ⊥ (Classical.choice inst)))
--     (by constructor; simp [Measure.dirac])

-- abbrev PSp (Ω : Type*) := WithTop (ProbabilitySpace Ω)

-- @[simp]
-- instance : Valid (PSp Ω) where
--   valid := fun x => match x with | some _ => True | none => False

-- instance [inst : Nonempty Ω] : OrderedUnitalResourceAlgebra (PSp Ω) where
--   mul := fun x y => match x, y with
--     | some x, some y => if h : (x.indepProduct y).isSome then (x.indepProduct y).get h else none
--     | _, _ => none
--   valid_one := by simp
--   valid_mul := by intro a b hab; cases a <;> cases b <;> simp_all
--   valid_mono := by
--     intro a b h h'; cases a <;> cases b <;> simp_all
--     have h' : (⊤ : PSp Ω) ≤ WithTop.some _ := h
--     contrapose! h'
--     simp
--   one_mul := sorry
--   elim := sorry
--   -- mul_right_mono := sorry

-- variable {V : Type*}

-- -- Needs to encode the term `P = P' ⊗ 𝟙_ (p.support → V)` in the paper
-- /-- Compatibility of a probability space with a permission, defined as the existence of a splitting between:

-- - the trivial probability space on the zero part of the permission `𝟙_ ({a // p a = 0} → V)`
-- - another probability space `P'` on the non-zero part of the permission -/
-- def ProbabilityTheory.ProbabilitySpace.compatiblePerm (_P : ProbabilitySpace (α → V)) (p : Permission α) : Prop :=
--   ∃ _P' : ProbabilitySpace ({a // p a > 0} → V), True

-- /-- Generalize compatibility of `ProbabilitySpace` with `Permission` to `PSp` by letting `⊤` be
--   compatible with all permission maps -/
-- def PSp.compatiblePerm (P : PSp (α → V)) (p : Permission α) : Prop := match P with
--   | some P => ProbabilitySpace.compatiblePerm P p
--   | none => True

-- /-- The joint structure of a probability space and a permission that are compatible.

-- This is given a resource algebra structure by pointwise product of the underlying probability space
-- and permission RAs, up to compatibility. -/
-- @[reducible]
-- def PSpPm (α : Type*) (V : Type*) :=
--   {Pp : PSp (α → V) × Permission α // Pp.1.compatiblePerm Pp.2}

-- namespace PSpPm

-- /-- Lift a probability space to a probability space-permission pair, via coupling it with the
--   all-one permission -/
-- def liftProb (μ : ProbabilitySpace (α → V)) : PSpPm α V :=
--   ⟨⟨μ, 1⟩, by sorry⟩

-- @[simp]
-- instance [Nonempty V] : One (PSpPm α V) where
--   one := ⟨⟨One.one, One.one⟩, by simp [One.one, PSp.compatiblePerm, ProbabilitySpace.compatiblePerm]⟩

-- /-- Multiplication is pointwise product of the probability space and the permission -/
-- @[simp]
-- instance [Nonempty V] : Mul (PSpPm α V) where
--   -- TODO: need to prove product preserves compatibility
--   mul Pp₁ Pp₂ := ⟨⟨Pp₁.1.1 * Pp₂.1.1, Pp₁.1.2 * Pp₂.1.2⟩, by sorry⟩

-- -- instance : Valid (PSpPm α V) := inferInstanceAs <|
-- --   Valid (Subtype (fun Pp : PSp (α → V) × Permission α => Pp.1.compatiblePerm Pp.2))

-- /-- The resource algebra instance on `PSpPm α V` -/
-- instance [Nonempty V] : OrderedUnitalResourceAlgebra (PSpPm α V) where
--   one_mul := by simp; intro P p h; sorry
--   valid_one := by simp [Valid.valid, One.one]; sorry
--   valid_mul := by sorry
--   valid_mono := by sorry
--   elim := by sorry

-- end PSpPm

-- end

-- /-- The main model of Bluebell is a function type `I → PSpPm α V`, where `I` is the index set of (independent) program executions. The resource algebra structure is lifted pointwise from `PSpPm`.

-- To handle multiple programs drawn from index set `I`, we use the RA `I → PSpPm` where
-- operations are lifted pointwise -/
-- abbrev IndexedPSpPm (I α V : Type*) := I → PSpPm α V

-- namespace IndexedPSpPm

-- variable {I α V : Type*}

-- /-- Lift an indexed set of probability spaces to an indexed set of probability space-permission
--   pairs, via pointwise lifting -/
-- def liftProb (μ : I → ProbabilitySpace (α → V)) : IndexedPSpPm I α V :=
--   fun i => PSpPm.liftProb (μ i)

-- instance : FunLike (IndexedPSpPm I α V) I (PSpPm α V) where
--   coe := fun x => x
--   coe_injective' := by intro x y h; simp [h]

-- noncomputable instance [Nonempty V] : OrderedUnitalResourceAlgebra (IndexedPSpPm I α V) :=
--   inferInstanceAs (OrderedUnitalResourceAlgebra (I → PSpPm α V))

-- end IndexedPSpPm

-- /-- A hyper-assertion is an upward closed predicate on `IndexedPSpPm I α V`.

-- We re-use the existing Lean structure `UpperSet`, so an element of this type has:

-- - a carrier (a `Set`, equivalent to a predicate)
-- - a proof that the set is upward closed -/
-- abbrev HyperAssertion (I α V : Type*) := UpperSet (IndexedPSpPm I α V)
--   -- {ha : IndexedPSpPm I α V → Prop // ∀ x y, x ≤ y → ha x → ha y}

-- /-- `FunLike` instance for `HyperAssertion` so that we can write `P a` instead of `a ∈ P` -/
-- instance {I α V : Type*} : FunLike (HyperAssertion I α V) (IndexedPSpPm I α V) Prop where
--   coe := fun P => P.carrier
--   coe_injective' := by intro P Q h; aesop

-- namespace HyperAssertion

-- variable {I α V : Type*}

-- /-- The predicate underlying a hyper-assertion -/
-- def pred (P : HyperAssertion I α V) : IndexedPSpPm I α V → Prop := (· ∈ P.carrier)

-- /-- A hyper-assertion `P` is irrelevant for a finite set of indices `J` if it is entailed by the set
--   of all probability spaces that are compatible with the permission at each index.

--   Note that there may be multiple such `J`. -/
-- def isIrrelevant [DecidableEq I] [Fintype I] (J : Set I) (P : HyperAssertion I α V) : Prop :=
--   ∀ a, (∃ a' : IndexedPSpPm I α V,
--   -- The paper writes `a = a' \ J`, but it's not clear what this operation is (should there be a
--   -- "default" value for all unused indices?)
--     valid a' ∧ (a = a') ∧ P a') → P a

-- /-- The relevant indices `idx(P)` of a hyper-assertion `P` is the smallest subset of `I` whose
--   complement is irrelevant for `P`. -/
-- def relevantIndices [DecidableEq I] [Fintype I] (P : HyperAssertion I α V) : Set I :=
--   sInf (setOf (fun J : Set I => isIrrelevant J.compl P))

-- /-- The empty hyper-assertion -/
-- def emp : HyperAssertion I α V := ⟨setOf (fun _ => False), fun _ _ _ h => h⟩

-- /-- The entailment relation on hyper-assertions:
--   `P ⊢ Q` if for any valid resource `a`, if `P` holds for `a`, then `Q` holds for `a`. -/
-- def entails (P Q : HyperAssertion I α V) : Prop :=
--   ∀ a, ✓ a → P a → Q a

-- /-- Equivalence between hyper-assertions is defined as mutual entailment, denoted `P ⊣⊢ Q` -/
-- def equiv (P Q : HyperAssertion I α V) : Prop :=
--   entails P Q ∧ entails Q P

-- /-- Lift a proposition to a hyper-assertion, `⌜ φ ⌝` -/
-- def pure (φ : Prop) : HyperAssertion I α V := ⟨setOf (fun _ => φ), fun _ _ _ ha => ha⟩

-- alias lift := pure

-- /-- Conjunction of two hyper-assertions, defined pointwise -/
-- def and (P Q : HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => P a ∧ Q a), fun _ _ hab ⟨hP, hQ⟩ => ⟨P.upper' hab hP, Q.upper' hab hQ⟩⟩

-- /-- Disjunction of two hyper-assertions, defined pointwise -/
-- def or (P Q : HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => P a ∨ Q a), fun _ _ hab h => match h with
--     | Or.inl hP => Or.inl (P.upper' hab hP)
--     | Or.inr hQ => Or.inr (Q.upper' hab hQ)⟩

-- -- Note: don't think we can define implication `→` or negation `¬`, since upward closedness gives the
-- -- wrong direction

-- -- Not sure how to define these either
-- def sForall (P : HyperAssertion I α V → Prop) : HyperAssertion I α V := sorry
--   -- ⟨setOf (fun a => P (fun b => a ≤ b)), fun _ _ hab h b hb => P.upper' (hab b) hb⟩

-- def sExists (P : HyperAssertion I α V → Prop) : HyperAssertion I α V := sorry

-- /-- Existential quantification over hyper-assertions -/
-- def «exists» {β : Sort*} (P : β → HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => ∃ b, P b a), fun _ _ hab ⟨b, h⟩ => ⟨b, (P b).upper' hab h⟩⟩

-- /-- Universal quantification over hyper-assertions -/
-- def «forall» {β : Sort*} (P : β → HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => ∀ b, P b a), fun _ _ hab h b => (P b).upper' hab (h b)⟩

-- /-- Separating conjunction of two hyper-assertions, `P ∗ Q`, defined for every `a` as the existence of elements
--   `b₁ ∈ P` and `b₂ ∈ Q` respectively, such that `b₁ * b₂ ≤ a`. -/
-- def sep (P : HyperAssertion I α V) (Q : HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => ∀ b, valid (a * b) → P b → Q (a * b)), fun a a' ha h b hb₁ hb₂ => by
--     simp_all; sorry⟩

-- /-- Separating implication of two hyper-assertions, `P -∗ Q`, defined for every `a` as the existence of elements
--   `b₁ ∈ P` and `b₂ ∈ Q` respectively, such that `b₁ * b₂ ≤ a`. -/
-- def wand (P : HyperAssertion I α V) (Q : HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => ∃ b₁ b₂, (b₁ * b₂) ≤ a ∧ b₁ ∈ P ∧ b₂ ∈ Q),
--     fun _ _ hab ⟨b₁, b₂, h, hb₁, hb₂⟩ => ⟨b₁, b₂, le_trans h hab, hb₁, hb₂⟩⟩

-- open Iris.BI in
-- instance : BIBase (HyperAssertion I α V) where
--   Entails := entails
--   emp := emp
--   pure := pure
--   and := and
--   or := or
--   imp := sorry
--   sForall := sorry
--   sExists := sorry
--   sep := sep
--   wand := wand
--   persistently := sorry
--   later := sorry

-- section Ownership

-- /-! ### Ownership-related hyper-assertions -/

-- /-- Ownership of a resource `b : IndexedPSpPm I α V`, defined for every `a` as the predicate `b ≤ a`. -/
-- def own (b : IndexedPSpPm I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => b ≤ a), fun _ _ hab ha => le_trans ha hab⟩

-- /-- Ownership of an indexed tuple of probability spaces `P : I → PSp (α → V)` and permissions
--   `p : I → Permission α`, defined as the existence of compatibility proofs `h` for each element, such
--   that we have ownership of the overall tuple (with the compatibility proof). -/
-- def ownIndexedTuple (P : I → ProbabilitySpace (α → V)) (p : I → Permission α) : HyperAssertion I α V :=
--   «exists» (fun h : ∀ i, (P i).compatiblePerm (p i) => own (fun i => ⟨⟨P i, p i⟩, h i⟩))

-- variable [DecidableEq I] [Nonempty V] {β : Type*} [MeasurableSpace β]

-- /-- Ownership of an indexed probability spaces `P : I → PSp (α → V)`, defined as the
--   existence of a compatible indexed permission `p : I → Permission α` such that we have
--   ownership of the overall tuple. -/
-- def ownIndexedProb (P : I → ProbabilitySpace (α → V)) : HyperAssertion I α V :=
--   «exists» (fun p : I → Permission α => ownIndexedTuple P p)

-- /-- The hyper-assertion `E⟨i⟩ ∼ μ`, for some expression `E : (α → V) → β`, index `i : I`,
--   and discrete probability distribution `μ : PMF β`, is defined as
--   `∃ P, Own P ∗ lift ((E⟨i⟩ is a.e. measurable for (P i)) ∧ μ = (P i).μ.map E)`-/
-- def assertSampledFrom (i : I) (E : (α → V) → β) (μ : PMF β) : HyperAssertion I α V :=
--   «exists» (fun P : I → ProbabilitySpace (α → V) =>
--     sep (ownIndexedProb P)
--       (lift (@AEMeasurable _ _ _ (P i).σAlg E (P i).μ ∧ μ.toMeasure = @Measure.map _ _ (P i).σAlg _ E (P i).μ)))

-- /-- Assertion that the expected value of `E` at index `i` is `ev` -/
-- def assertExpectation [TopologicalSpace β] [AddCommMonoid β] [SMul ENNReal β]
--     (i : I) (E : (α → V) → β) (ev : β) : HyperAssertion I α V :=
--   «exists» (fun μ => sep (assertSampledFrom i E μ) (lift (ev = ∑' b, (μ b) • b)))

-- /-- Assertion that the probability of a Boolean-valued expression `E` at index `i` is `prob` -/
-- def assertProbability (i : I) (E : (α → V) → Bool) (prob : ENNReal) : HyperAssertion I α V :=
--   «exists» (fun μ => sep (assertSampledFrom i E μ) (lift (prob = μ true)))

-- /-- Assertion that `E` is true almost surely -/
-- noncomputable def assertTrue (i : I) (E : (α → V) → Bool) : HyperAssertion I α V :=
--   assertSampledFrom i E (PMF.pure true)

-- /-- Assertion that we own `E` (but its distribution is not known) -/
-- def assertOwn (i : I) (E : (α → V) → β) : HyperAssertion I α V :=
--   «exists» (fun μ => assertSampledFrom i E μ)

-- /-- Assertion that the variable `x : α` at index `i` has permission `q : ℚ≥0` -/
-- def assertPermissionVar (i : I) (x : α) (q : ℚ≥0) : HyperAssertion I α V :=
--   «exists» (fun Pp : IndexedPSpPm I α V => sep (own Pp) (lift ((Pp i).1.2 x = q)))

-- /-- Assertion that a hyper-assertion `P` holds alongside an ownership of an indexed permission `p`

-- This is useful when defining pre-conditions at the beginning of the program (where we have a
-- precondition `P` and all variables have permission `1`) -/
-- def assertPermission (P : HyperAssertion I α V) (p : I → Permission α) : HyperAssertion I α V :=
--   and P <|
--     «exists» (fun compatP : {P : I → ProbabilitySpace (α → V) // ∀ i, (P i).compatiblePerm (p i)} =>
--       own (fun i => ⟨⟨compatP.1 i, p i⟩, compatP.2 i⟩))

-- end Ownership

-- def isPermissionAbstract (X : Set (I × α)) (P : HyperAssertion I α V) : Prop := sorry
--   -- ∀ Pp : IndexedPSpPm I α V, ∀ q : ℚ≥0, ∀ n : ℕ+, P Pp ≤ P → ∃ Pp' : IndexedPSpPm I α V, Pp' ≤ P ∧ Pp = Pp' ∧ True

-- /-- The joint conditioning modality -/
-- def jointCondition {β : Type*} [MeasurableSpace β] [MeasurableSpace V] (μ : PMF β) (K : β → HyperAssertion I α V) :
--     HyperAssertion I α V := sorry
--   -- «exists» (fun P : I → ProbabilitySpace (α → V) => sorry)
--   -- ⟨setOf (fun a => ∃ P : I → ProbabilitySpace (α → V),
--   --   ∃ p : I → Permission α,
--   --   ∃ h : ∀ i, (P i).compatiblePerm (p i),
--   --   ∃ κ : (i : I) → β → @Measure (α → V) (P i).σAlg,
--   --   (fun i => ⟨⟨P i, p i⟩, h i⟩ : IndexedPSpPm I α V) ≤ a ∧ ∀ i, (P i).μ = μ.toMeasure.bind (κ i) ∧
--   --     ∀ v ∈ μ.support, K v (fun j => ⟨⟨@ProbabilitySpace.mk _ (P j).σAlg (κ j v) sorry, p j⟩, h j⟩)), by sorry⟩

-- notation "𝑪_" => jointCondition

-- /-- The lifting of a relation `R : Set (s → V)`, where `s : Set (I × α)`, to a hyper-assertion -/
-- noncomputable def liftRelation [DecidableEq V] [MeasurableSpace V]
--     (s : Set (I × α)) (R : Set (s → V)) : HyperAssertion I α V :=
--   «exists» (fun μ : PMF (s → V) =>
--     sep (lift (∑' x : R, μ x = 1))
--       (𝑪_ μ (fun v : s → V =>
--         «forall» (fun x : s => assertTrue x.1.1 (fun y => v x = y x.1.2)))))

-- /-- Weakest precondition of a program -/
-- def wp (t : IndexedPSpPm I α V → IndexedPSpPm I α V) (Q : HyperAssertion I α V) : HyperAssertion I α V :=
--   ⟨setOf (fun a => ∀ μ₀ c, (a * c) ≤ IndexedPSpPm.liftProb μ₀ →
--     ∃ b, (b * c) ≤ t (IndexedPSpPm.liftProb μ₀) ∧ Q b), by sorry⟩

-- section ProgramLogic

-- /-! ### The program logic of Bluebell -/

-- -- TODO: we also need to state the regular rules of separation logic, so stuff like
-- theorem and_comm {P Q : HyperAssertion I α V} : P ∧ Q ⊣⊢ Q ∧ P := sorry

-- /-- If `P` and `Q` affect disjoint sets of indices, then `P ∧ Q` entails `P ∗ Q` -/
-- theorem sep_of_and [DecidableEq I] [Fintype I] {P Q : HyperAssertion I α V}
--     (h : relevantIndices P ∩ relevantIndices Q = ∅) : (P ∧ Q) ⊢ (P ∗ Q) := by
--   sorry

-- /-- If `E⟨i⟩` is sampled from both `μ` and `μ'`, then `⌜ μ = μ' ⌝` holds as a proposition -/
-- theorem sampledFrom_inj {β : Type*} [MeasurableSpace β] {i : I} {E : (α → V) → β} {μ μ' : PMF β} :
--     (assertSampledFrom i E μ) ∧ (assertSampledFrom i E μ') ⊢ ⌜ μ = μ' ⌝ := by
--   sorry

-- /-- `E₁⟨i⟩` and `E₂⟨i⟩` are both true if and only if `E₁⟨i⟩ ∧ E₂⟨i⟩` is true -/
-- theorem sep_assertTrue_iff {i : I} {E₁ E₂ : (α → V) → Bool} :
--     (assertTrue i E₁) ∗ (assertTrue i E₂) ⊣⊢ assertTrue i (fun x => E₁ x ∧ E₂ x) := by
--   sorry

-- /-- If `pabs(𝑃, pvar(𝐸⟨𝑖⟩))` (need to define this), then `assertTrue i E ∧ P` entails `assertTrue i E ∗ P` -/
-- theorem sep_of_and_assertTrue {i : I} {E : (α → V) → Bool} {P : HyperAssertion I α V}
--     (h : True) : (assertTrue i E) ∗ P ⊢ (assertTrue i E) ∧ P := by
--   sorry

-- /-- Sampling hyper-assertions `(E₁⟨i⟩, E₂⟨i⟩) ∼ (μ₁, μ₂)` for a product space can be split
--   into sampling `E₁⟨i⟩ ∼ μ₁` and `E₂⟨i⟩ ∼ μ₂` -/
-- theorem sampledFrom_prod {β₁ β₂ : Type _} [MeasurableSpace β₁] [MeasurableSpace β₂] {i : I}
--     (E₁ : (α → V) → β₁) (E₂ : (α → V) → β₂) (μ₁ : PMF β₁) (μ₂ : PMF β₂) :
--       assertSampledFrom i (fun x => (E₁ x, E₂ x)) (Prod.mk <$> μ₁ <*> μ₂) ⊢
--         (assertSampledFrom i E₁ μ₁) ∗ (assertSampledFrom i E₂ μ₂) := by
--   sorry

-- section JointConditioning

-- variable {β : Type*} [MeasurableSpace β] {μ : PMF β} {K K₁ K₂ : β → HyperAssertion I α V}
--   [MeasurableSpace V]

-- theorem C_conseq (h : ∀ v, K₁ v ⊢ K₂ v) : 𝑪_ μ K₁ ⊢ 𝑪_ μ K₂ := by
--   sorry

-- theorem C_frame {P : HyperAssertion I α V} : P ∗ 𝑪_ μ K ⊢ 𝑪_ μ (fun v => sep P (K v)) := by
--   sorry

-- theorem C_unit_left [Countable β] [MeasurableSingletonClass β] {v₀ : β} :
--     𝑪_ (Measure.dirac v₀).toPMF K ⊣⊢ K v₀ := by
--   sorry

-- theorem C_unit_right [DecidableEq β] {i : I} {E : (α → V) → β} {μ : PMF β} :
--     assertSampledFrom i E μ ⊣⊢ 𝑪_ μ (fun v => assertTrue i (fun x => E x = v)) := by
--   sorry

-- theorem C_assoc {β₁ β₂ : Type _} [MeasurableSpace β₁] [MeasurableSpace β₂]
--     {μ : PMF β₁} {κ : β₁ → PMF β₂} {K : β₁ × β₂ → HyperAssertion I α V} :
--       𝑪_ μ (fun v => 𝑪_ (κ v) (fun w => K (v, w))) ⊢
--         𝑪_ (do let v ← μ; let w ← κ v; return (v, w)) K := by
--   sorry

-- theorem C_unassoc {β₁ β₂ : Type _} [MeasurableSpace β₁] [MeasurableSpace β₂]
--     {μ : PMF β₁} {κ : β₁ → PMF β₂} {K : β₂ → HyperAssertion I α V} :
--       𝑪_ (μ.bind κ) (fun w => K w) ⊢ 𝑪_ μ (fun v => 𝑪_ (κ v) (fun w => K w)) := by
--   sorry

-- theorem C_and [DecidableEq I] [Fintype I] (h : ∀ v, relevantIndices (K₁ v) ∩ relevantIndices (K₂ v) = ∅) :
--     𝑪_ μ K₁ ∧ 𝑪_ μ K₂ ⊢ 𝑪_ μ (fun v => and (K₁ v) (K₂ v)) := by
--   sorry

-- /-- Also requires that the measurable space on `β` is the top one -/
-- theorem C_exists {γ : Type*} {Q : β × γ → HyperAssertion I α V} :
--     𝑪_ μ (fun v => ∃ x, Q (v, x)) ⊢ ∃ f : β → γ, 𝑪_ μ (fun v => Q (v, f v)) := by
--   sorry

-- theorem C_forall {γ : Type*} {Q : β × γ → HyperAssertion I α V} :
--     𝑪_ μ (fun v => «forall» (fun x => Q (v, x))) ⊢ ∀ x, 𝑪_ μ (fun v => Q (v, x)) := by
--   sorry

-- theorem C_transfer {β' : Type*} [MeasurableSpace β'] {μ' : PMF β'} (f : μ'.support ≃ μ.support)
--     (h : ∀ b, (hb : b ∈ μ'.support) → μ' b = μ (f ⟨b, hb⟩).1) :
--       𝑪_ μ K ⊢ 𝑪_ μ' (fun b => K (f ⟨b, sorry⟩)) := by
--   sorry

-- theorem C_sep_assertTrue {i : I} {E : (α → V) → Bool} :
--     𝑪_ μ (fun v => sep (K v) (assertTrue i E)) ⊢ assertTrue i E ∗ 𝑪_ μ K := by
--   sorry

-- theorem C_pure {s : Set β} :
--     ⌜ ∑' x : s, μ x = 1 ⌝ ∗ 𝑪_ μ K ⊣⊢ 𝑪_ μ (fun v => sep (pure (v ∈ s)) (K v)) := by
--   sorry

-- end JointConditioning

-- section WeakestPrecondition

-- variable {I α V : Type*} [MeasurableSpace V] {t t₁ t₂ : IndexedPSpPm I α V → IndexedPSpPm I α V}
--   {P Q Q' Q₁ Q₂ : HyperAssertion I α V}

-- theorem wp_conseq (h : Q ⊢ Q') : (wp t Q) ⊢ (wp t Q') := by sorry

-- theorem wp_frame : P ∗ (wp t Q) ⊢ (wp t (sep P Q)) := by sorry

-- theorem wp_comp : (wp t₁ (wp t₂ Q)) ⊣⊢ (wp (t₁ ∘ t₂) Q) := by sorry

-- -- TODO: need to express `|t|`, the set of relevant indices of a program `t`, and `t₁ + t₂`, the
-- -- combined execution of `t₁` and `t₂` if they affect disjoint sets of indices (so we must model `t`
-- -- as an AST which is then interpreted into a function)
-- -- Required conditions: `(h1 : relevantIndices Q₁ ∩ |t₂| ⊆ |t₁|) (h2 : relevantIndices Q₂ ∩ |t₁| ⊆ |t₂|)`
-- theorem wp_conj : (wp t₁ Q₁) ∧ (wp t₂ Q₂) ⊣⊢ (wp (sorry) (and Q₁ Q₂)) := by sorry

-- -- TODO: what is `own_α` exactly (`own_𝕏` in the paper)?
-- theorem C_wp_swap {β : Type*} [MeasurableSpace β] {μ : PMF β} {K : β → HyperAssertion I α V} :
--     𝑪_ μ (fun v => wp t (K v)) ∧ sorry ⊢ wp t (𝑪_ μ K) := by sorry

-- -- Add wp rules for the program syntax

-- end WeakestPrecondition

-- end ProgramLogic

-- end HyperAssertion
