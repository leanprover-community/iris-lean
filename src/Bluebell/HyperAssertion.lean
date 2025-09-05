import Mathlib
import Iris

namespace Bluebell

/-- A hyper-assertion over a model `M` (ordered by `≤`) is an upward-closed predicate on `M`.

We re-use the existing Lean structure `UpperSet`, so an element of this type has:

- a carrier (a `Set`, equivalent to a predicate)
- a proof that the set is upward closed

We write `x ∈ P` to mean that the hyper-assertion `P` holds of the resource `x`. -/
abbrev HyperAssertion (M : Type*) [LE M] := UpperSet M

namespace HyperAssertion

section Defs

variable {M : Type*} [LE M]

/-- The predicate underlying a hyper-assertion. -/
def pred (P : HyperAssertion M) : M → Prop := (· ∈ P.carrier)

/-- The empty hyper-assertion. -/
def emp : HyperAssertion M := ⟨{x | False}, by intro _ _ _ h; exact h⟩

/-- Lift a proposition to a hyper-assertion, often written `⌜φ⌝`. -/
def pure (φ : Prop) : HyperAssertion M := ⟨{x | φ}, by intro _ _ _ h; exact h⟩

/-- Conjunction of two hyper-assertions, defined pointwise. -/
def and (P Q : HyperAssertion M) : HyperAssertion M :=
  ⟨{x | x ∈ P ∧ x ∈ Q}, by
    intro x y hxy hx; exact And.intro (P.upper hxy hx.left) (Q.upper hxy hx.right)⟩

/-- Disjunction of two hyper-assertions, defined pointwise. -/
def or (P Q : HyperAssertion M) : HyperAssertion M :=
  ⟨{x | x ∈ P ∨ x ∈ Q}, by
    intro x y hxy hx; cases hx with
    | inl h => exact Or.inl (P.upper hxy h)
    | inr h => exact Or.inr (Q.upper hxy h)⟩

/-- Existential quantification over hyper-assertions. -/
def «exists» {β : Sort*} (P : β → HyperAssertion M) : HyperAssertion M :=
  ⟨{x | ∃ b, x ∈ P b}, by
    intro x y hxy ⟨b, hb⟩; exact ⟨b, (P b).upper hxy hb⟩⟩

/-- Universal quantification over hyper-assertions. -/
def «forall» {β : Sort*} (P : β → HyperAssertion M) : HyperAssertion M :=
  ⟨{x | ∀ b, x ∈ P b}, by
    intro x y hxy hx b; exact (P b).upper hxy (hx b)⟩

/-- Entailment of hyper-assertions: `P ⊢ Q` iff `∀ x, P x → Q x`. -/
def entails (P Q : HyperAssertion M) : Prop := ∀ x, x ∈ P → x ∈ Q

/-- Equivalence of hyper-assertions as mutual entailment, written `P ⊣⊢ Q`. -/
def equiv (P Q : HyperAssertion M) : Prop := entails P Q ∧ entails Q P

end Defs

variable {I M : Type*} [LE M]

/-- A hyper-assertion `P` is irrelevant for a finite set of indices `J` if it is entailed by the set
of all resources that agree with some `a'` outside `J`.

Note: the original paper writes `a = a' \ J`. Here we keep the same equality-based placeholder as
in the original attempt until a default value for unused indices is fixed. -/
def isIrrelevant [DecidableEq I] [Fintype I]
    (J : Set I) (P : HyperAssertion (I → M)) : Prop :=
  ∀ a, (∃ a' : I → M, (∀ i, i ∉ J → a i = a' i) ∧ a' ∈ P) → a ∈ P

/-- The relevant indices `idx(P)` of a hyper-assertion `P` is the smallest subset of `I` whose
complement is irrelevant for `P`. -/
def relevantIndices [DecidableEq I] [Fintype I]
    (P : HyperAssertion (I → M)) : Set I :=
  sInf (setOf (fun J : Set I => isIrrelevant (Jᶜ) P))

end HyperAssertion

/-! ## CMRA-based separating connectives -/

open Iris

section CMRAModel

variable {M : Type*} [CMRA M]

/-- Use CMRA inclusion `≼` as the order on `M` so `UpperSet M` matches upward-closed predicates. -/
scoped instance : LE M := ⟨fun x y => CMRA.Included x y⟩

namespace HyperAssertion

/-- Ownership of a CMRA resource `b`, defined as the upward-closed predicate `b ≼ a`. -/
def own (b : M) : HyperAssertion M :=
  ⟨{a | (b : M) ≼ a}, by
    intro a a' haa' hba
    exact CMRA.Included.trans hba haa'⟩

/-- Separating conjunction of two hyper-assertions, `P ∗ Q`, defined at `a` as the
existence of `b ∈ P` and `c ∈ Q` such that `b • c ≼ a`. -/
def sep (P Q : HyperAssertion M) : HyperAssertion M :=
  ⟨{a | ∃ b c, b ∈ P ∧ c ∈ Q ∧ (b • c : M) ≼ a}, by
    intro a a' haa' ⟨b, c, hb, hc, hbc⟩
    exact ⟨b, c, hb, hc, CMRA.Included.trans hbc haa'⟩⟩

/-- Separating implication (magic wand), `P -∗ Q`, defined at `a` as:
for all `b ∈ P`, we have `b • a ∈ Q`. -/
def wand (P Q : HyperAssertion M) : HyperAssertion M :=
  ⟨{a | ∀ b, b ∈ P → (b • a : M) ∈ Q}, by
    intro a a' haa' ha b hb
    have : (b • a : M) ≼ (b • a') := CMRA.op_mono_right b haa'
    exact Q.upper this (ha b hb)⟩

/-- Implication between hyper-assertions, Kripke-style: at `a`, it holds if for all `a' ≥ a`,
`a' ∈ P` implies `a' ∈ Q`. This makes `imp` upward-closed. -/
def imp (P Q : HyperAssertion M) : HyperAssertion M :=
  ⟨{a | ∀ a', a ≤ a' → a' ∈ P → a' ∈ Q}, by
    intro a b hab ha a' hba'
    -- Using CMRA inclusion transitivity: a ≤ b ≤ a' ⇒ a ≤ a'
    exact ha a' (CMRA.Included.trans hab hba')⟩

/-- ∀-quantification at the meta-level over a family of hyper-assertions. -/
def sForall {β : Sort*} (F : β → HyperAssertion M) : HyperAssertion M :=
  ⟨{a | ∀ x, a ∈ F x}, by
    intro a a' haa' ha x
    exact (F x).upper haa' (ha x)⟩

/-- ∃-quantification at the meta-level over a family of hyper-assertions. -/
def sExists {β : Sort*} (F : β → HyperAssertion M) : HyperAssertion M :=
  ⟨{a | ∃ x, a ∈ F x}, by
    intro a a' haa' ⟨x, hx⟩; exact ⟨x, (F x).upper haa' hx⟩⟩

end HyperAssertion

end CMRAModel

/-! ## Lemmas for CMRA-backed hyper-assertions -/

section CMRALemmas

open HyperAssertion

variable {M : Type*} [CMRA M]

/-- If `b ≼ c`, then `own c ⊢ own b`. -/
theorem own_entails_of_included {b c : M} (hbc : b ≼ c) : entails (own (M := M) c) (own b) := by
  intro a hac; exact CMRA.Included.trans hbc hac

/-- `own b ∗ own c ⊢ own (b • c)`. -/
theorem sep_own_own_entails_own_op (b c : M) : entails (sep (own (M := M) b) (own c)) (own (b • c)) := by
  intro a
  rintro ⟨r', s, hr, hs, hrs⟩
  -- hr : b ≼ r', hs : c ≼ s, hrs : r' • s ≼ a
  have h_op : b • c ≼ r' • s := CMRA.op_mono hr hs
  exact CMRA.Included.trans h_op hrs

/-- Commutativity of separating conjunction up to entailment. -/
theorem sep_comm {P Q : HyperAssertion M} : entails (sep P Q) (sep Q P) := by
  intro a
  rintro ⟨b, c, hPb, hQc, hinc⟩
  have hcb : c • b ≼ a := CMRA.inc_of_eqv_of_inc (CMRA.comm (x:=c) (y:=b)) hinc
  exact ⟨c, b, hQc, hPb, hcb⟩

/-- Associativity of separating conjunction up to entailment. -/
theorem sep_assoc {P Q R : HyperAssertion M} [CMRA.IsTotal M] :
    entails (sep (sep P Q) R) (sep P (sep Q R)) := by
  intro a
  rintro ⟨x, z, hx, hz, hxz⟩
  rcases hx with ⟨b, c, hPb, hQc, hbc⟩
  -- From b • c ≼ x and x • z ≼ a, obtain (b • c) • z ≼ a
  have h1 : (b • c) • z ≼ a :=
    CMRA.Included.trans (CMRA.op_mono_left z hbc) hxz
  -- Convert by associativity to b • (c • z) ≼ a
  have h2 : b • (c • z) ≼ a :=
    (CMRA.inc_of_eqv_of_inc (CMRA.assoc (x:=b) (y:=c) (z:=z))) h1
  -- Build witnesses for sep P (sep Q R)
  refine ⟨b, (c • z), hPb, ?_, h2⟩
  exact ⟨c, z, hQc, hz, CMRA.inc_refl (x := c • z)⟩

/-- Commutativity of conjunction. -/
theorem and_comm {P Q : HyperAssertion M} : entails (and P Q) (and Q P) := by
  intro a; intro h; exact And.intro h.right h.left

/-- Commutativity of disjunction. -/
theorem or_comm {P Q : HyperAssertion M} : entails (or P Q) (or Q P) := by
  intro a; intro h; cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ

end CMRALemmas

/-! ## BI wiring (no step-indexing) -/

section BI

open Iris

variable {M : Type*} [CMRA M]

namespace HyperAssertion

/-- In the non-step-indexed model, we stub `persistently` as identity. -/
def persistently (P : HyperAssertion M) : HyperAssertion M := P

/-- In the non-step-indexed model, we stub `later` as identity. -/
def later (P : HyperAssertion M) : HyperAssertion M := P

end HyperAssertion

open HyperAssertion Iris.BI

/-- BIBase instance over `HyperAssertion M` using our CMRA-backed connectives.
`persistently` and `later` are stubs (identity) in this non-step-indexed model. -/
instance : BIBase (HyperAssertion M) where
  Entails := entails
  emp := emp
  pure := pure
  and := and
  or := or
  imp := imp
  sForall := fun (X : HyperAssertion M → Prop) =>
    ⟨{a | ∀ P, X P → a ∈ P}, by
      intro a a' haa' ha P hXP
      exact P.upper haa' (ha P hXP)⟩
  sExists := fun (X : HyperAssertion M → Prop) =>
    ⟨{a | ∃ P, X P ∧ a ∈ P}, by
      intro a a' haa'
      rintro ⟨P, hXP, haP⟩
      exact ⟨P, hXP, P.upper haa' haP⟩⟩
  sep := sep
  wand := wand
  persistently := persistently
  later := later

end BI

end Bluebell
