import Iris
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion
import Bluebell.Logic.JointCondition

open Iris ProbabilityTheory

namespace Bluebell
namespace HyperAssertion

variable {I α V : Type*} [Nonempty V] [MeasurableSpace V]

/-!
Weakest precondition (WP), ported from the paper (Section "Weakest Precondition").

Given a program transformer `t : Model → Model` (we use it as the program
semantics `⟦t⟧`) and a postcondition `Q`, `wp t Q` is the upward-closed set of
resources `a` such that for every global input distribution `μ₀` and every
frame `c`, if the current resources and frame embed into the global state,
then there exists an updated resource `b` satisfying the postcondition and
whose composition with the same frame embeds into the output state `t μ₀`.

This matches the paper's definition (Def. "Weakest Precondition"):

  WP t Q (a) ≜ ∀ μ₀. ∀ c. (a • c) ≤ μ₀ → ∃ b, (b • c) ≤ ⟦t⟧(μ₀) ∧ Q(b)

In our formalization, we use `IndexedPSpPmRat.liftProb` to embed an indexed family
of probability spaces `μ₀ : I → ProbabilitySpace (α → V)` into the model by
pairing it with full permissions at every index.

We use `IndexedPSpPmRat` (with rational permissions) instead of `IndexedPSpPm`
because it has a UCMRA instance with a unit element, which is needed for the
frame rule proof. -/
noncomputable def wp (t : IndexedPSpPmRat I α V → IndexedPSpPmRat I α V)
    (Q : HyperAssertion (IndexedPSpPmRat I α V)) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  ⟨setOf (fun a =>
      ∀ μ₀ c,
        (a • c) ≤ IndexedPSpPmRat.liftProb μ₀ →
        ∃ b, (b • c) ≤ t (IndexedPSpPmRat.liftProb μ₀) ∧ Q b), by
    -- Upward-closure: if a ≤ a' and WP holds at a, then it holds at a'.
    intro a a' haa' ha μ₀ c hinc
    -- From a ≤ a', we have (a • c) ≤ (a' • c), then compose with hinc.
    have h_pre : (a • c) ≤ IndexedPSpPmRat.liftProb μ₀ :=
      CMRA.Included.trans (CMRA.op_mono_left c haa') hinc
    rcases ha μ₀ c h_pre with ⟨b, hb, hQ⟩
    exact ⟨b, hb, hQ⟩
  ⟩

variable {t t₁ t₂ : IndexedPSpPmRat I α V → IndexedPSpPmRat I α V}
  {P Q Q' Q₁ Q₂ : HyperAssertion (IndexedPSpPmRat I α V)}

omit [MeasurableSpace V] in
theorem wp_conseq (h : Q ⊢ Q') : (wp t Q) ⊢ (wp t Q') := by
  intro x hx μ₀ c hinc
  rcases hx μ₀ c hinc with ⟨b, hb, hQ⟩
  exact ⟨b, hb, h b hQ⟩

omit [MeasurableSpace V] in
theorem wp_frame : P ∗ (wp t Q) ⊢ (wp t (sep P Q)) := by
  rintro x ⟨p, w, hp, hw, hpw⟩ μ₀ c hinc
  have hframe : w • (p • c) ≼ IndexedPSpPmRat.liftProb μ₀ := calc
    w • (p • c) ≡ (p • w) • c                 := CMRA.op_left_comm.symm
    _           ≼ x • c                       := CMRA.op_mono_left c hpw
    _           ≼ IndexedPSpPmRat.liftProb μ₀ := hinc
  rcases hw μ₀ (p • c) hframe with ⟨b, hb, hQ⟩
  refine ⟨p • b, ?_, p, b, hp, hQ, CMRA.inc_refl _⟩
  calc (p • b) • c ≡ b • (p • c)                 := CMRA.op_left_comm
    _              ≼ t (IndexedPSpPmRat.liftProb μ₀) := hb

theorem wp_comp : (wp t₁ (wp t₂ Q)) ⊣⊢ (wp (t₁ ∘ t₂) Q) := by sorry

/-- TODO: `relevantIndices` of a program and program composition placeholder -/
theorem wp_conj : (wp t₁ Q₁) ∧ (wp t₂ Q₂) ⊣⊢ (wp (sorry) (and Q₁ Q₂)) := by sorry

/- TODO: C_wp_swap requires integrating jointCondition with IndexedPSpPmRat.
   This can be done by either:
   1. Defining a version of jointCondition for PermissionRat
   2. Creating a typeclass abstraction over the permission type
   For now, this theorem is commented out since the main goal is wp_frame.

theorem C_wp_swap {β : Type*} [MeasurableSpace β] {μ : PMF β}
    {K : β → HyperAssertion (IndexedPSpPmRat I α V)} :
    𝑪_ μ (fun v => wp t (K v)) ∧ sorry ⊢ wp t (𝑪_ μ K) := by sorry
-/

end HyperAssertion
end Bluebell
