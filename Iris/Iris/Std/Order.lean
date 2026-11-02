/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init
import all Init.Internal.Order.Basic

/-! # Order theory for `partial_fixpoint`

General facts about `Lean.Order` chain-complete partial orders and their fixpoints. -/

@[expose] public section

namespace Iris
open Lean.Order

/-! ## Order theory -/

section Order
variable {α β : Sort _}

theorem monotone_conj [PartialOrder α] [PartialOrder β] {F : α → α} {G : β → β}
    (e : α → β) (e' : β → α) (he : monotone e) (he' : monotone e') (hG : monotone G)
    (h : ∀ a, F a = e' (G (e a))) : monotone F :=
  fun a b hab => by rw [h, h]; exact he' _ _ (hG _ _ (he _ _ hab))

/-- A fixpoint moves across an order isomorphism. -/
theorem fix_iso [CCPO α] [CCPO β] {F : α → α} {G : β → β} (hF : monotone F) (hG : monotone G)
    (e : α → β) (e' : β → α) (he : monotone e)
    (h1 : ∀ b, e (e' b) = b) (h2 : ∀ a, e' (e a) = a) (hcomm : ∀ a, e (F a) = G (e a)) :
    e (fix F hF) = fix G hG := by
  have hF' : fix F hF ⊑ e' (fix G hG) := by
    refine fix_induct hF (· ⊑ e' (fix G hG)) (fun c hc h => csup_le hc h) fun a ha => ?_
    refine PartialOrder.rel_trans (hF _ _ ha) (PartialOrder.rel_of_eq ?_)
    rw [← h2 (F _), hcomm, h1, ← fix_eq hG]
  have hG' : fix G hG ⊑ e (fix F hF) := by
    refine fix_induct hG (· ⊑ e (fix F hF)) (fun c hc h => csup_le hc h) fun b hb => ?_
    refine PartialOrder.rel_trans (hG _ _ hb) (PartialOrder.rel_of_eq ?_)
    rw [← hcomm, ← fix_eq hF]
  have := he _ _ hF'
  rw [h1] at this
  exact PartialOrder.rel_antisymm this hG'

/-- The sup of a chain of functions is below `P` at `x` when every function is. -/
theorem csup_apply_le [CCPO β] {c : (α → β) → Prop} (hc : chain c) (x : α) {P : β}
    (h : ∀ f, c f → f x ⊑ P) : CCPO.csup hc x ⊑ P := by
  rw [← fun_csup_eq]
  exact csup_le (chain_apply hc x) fun _ ⟨f, hf, e⟩ => e ▸ h f hf

/-! The quantifier rewrites that turn statements about predicates on tuples into curried ones. -/

theorem forall_iso (e : α → β) (e' : β → α) (h : ∀ b, e (e' b) = b) {P : β → Prop} :
    (∀ b, P b) ↔ ∀ a, P (e a) :=
  ⟨fun hP _ => hP _, fun hP b => h b ▸ hP (e' b)⟩

theorem forall_psigma {β : α → Sort _} {P : PSigma β → Prop} :
    (∀ p, P p) ↔ ∀ x x', P ⟨x, x'⟩ :=
  ⟨fun h _ _ => h _, fun h p => h p.1 p.2⟩

theorem forall_punit {P : PUnit → Prop} : (∀ p, P p) ↔ P ⟨⟩ := ⟨fun h => h _, fun h _ => h⟩

/-! The sup of a chain of predicates is, at each point, the sup of their values there. -/

theorem csup_apply_eq [CCPO β] {c : (α → β) → Prop} (hc : chain c) {x : α}
    {sup : (β → Prop) → β} (hsup : ∀ c, is_sup c (sup c)) :
    CCPO.csup hc x = sup fun P => ∃ f, c f ∧ f x = P := by
  rw [← fun_csup_eq]
  exact is_sup_unique (CCPO.csup_spec (chain_apply hc x)) (hsup _)

/-- The fixpoint of a pair of functions is the pair of their fixpoints. -/
theorem fix_pprod [CCPO α] [CCPO β] {F : α → α} {G : β → β} (hF : monotone F) (hG : monotone G)
    (hFG : monotone fun p : α ×' β => (⟨F p.1, G p.2⟩ : α ×' β)) :
    fix _ hFG = ⟨fix F hF, fix G hG⟩ := by
  have hP := fix_eq hFG
  refine PartialOrder.rel_antisymm ?_ (show _ ∧ _ from ⟨?_, ?_⟩)
  · refine fix_induct hFG (· ⊑ ⟨fix F hF, fix G hG⟩) (fun c hc h => csup_le hc h) fun q hq => ?_
    rw [fix_eq hF, fix_eq hG]
    exact ⟨hF _ _ hq.1, hG _ _ hq.2⟩
  · refine fix_induct hF (· ⊑ (fix _ hFG).1) (fun c hc h => csup_le hc h) fun f hf => ?_
    rw [hP]
    exact hF _ _ hf
  · refine fix_induct hG (· ⊑ (fix _ hFG).2) (fun c hc h => csup_le hc h) fun g hg => ?_
    rw [hP]
    exact hG _ _ hg

end Order

end Iris
