import Iris
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion
import Bluebell.Logic.JointCondition

open Iris ProbabilityTheory

namespace Bluebell
namespace HyperAssertion

variable {I α V F : Type*} [Nonempty V] [MeasurableSpace V] [UFraction F]

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

In our formalization, we use `IndexedPSpPm.liftProb` to embed an indexed family
of probability spaces `μ₀ : I → ProbabilitySpace (α → V)` into the model by
pairing it with full permissions at every index. -/
noncomputable def wp (t : IndexedPSpPm I α V F → IndexedPSpPm I α V F)
    (Q : HyperAssertion (IndexedPSpPm I α V F)) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  ⟨setOf (fun a =>
      ∀ μ₀ c,
        (a • c) ≤ IndexedPSpPm.liftProb μ₀ →
        ∃ b, (b • c) ≤ t (IndexedPSpPm.liftProb μ₀) ∧ Q b), by
    -- Upward-closure: if a ≤ a' and WP holds at a, then it holds at a'.
    intro a a' haa' ha
    intro μ₀ c hinc
    -- From a ≤ a', we have (a • c) ≤ (a' • c), then compose with hinc.
    have h_pre : (a • c) ≤ IndexedPSpPm.liftProb μ₀ :=
      CMRA.Included.trans (CMRA.op_mono_left c haa') hinc
    rcases ha μ₀ c h_pre with ⟨b, hb, hQ⟩
    exact ⟨b, hb, hQ⟩
  ⟩

variable {t t₁ t₂ : IndexedPSpPm I α V F → IndexedPSpPm I α V F}
  {P Q Q' Q₁ Q₂ : HyperAssertion (IndexedPSpPm I α V F)}

theorem wp_conseq (h : Q ⊢ Q') : (wp t Q) ⊢ (wp t Q') := by sorry

theorem wp_frame : P ∗ (wp t Q) ⊢ (wp t (sep P Q)) := by sorry

theorem wp_comp : (wp t₁ (wp t₂ Q)) ⊣⊢ (wp (t₁ ∘ t₂) Q) := by sorry

/-- TODO: `relevantIndices` of a program and program composition placeholder -/
theorem wp_conj : (wp t₁ Q₁) ∧ (wp t₂ Q₂) ⊣⊢ (wp (sorry) (and Q₁ Q₂)) := by sorry

/-- TODO: what is `own_α` exactly (`own_𝕏` in the paper)? -/
theorem C_wp_swap {β : Type*} [MeasurableSpace β] {μ : PMF β}
    {K : β → HyperAssertion (IndexedPSpPm I α V F)} :
    𝑪_ μ (fun v => wp t (K v)) ∧ sorry ⊢ wp t (𝑪_ μ K) := by sorry

end HyperAssertion
end Bluebell
