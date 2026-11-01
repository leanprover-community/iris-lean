/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Iris.BI.Lib.Fixpoint
public import Lean.Meta.Order
import all Init.Internal.Order.Basic

/-! # Lattice-based Iris Fixpoints

These lattices over Iris types let us define Iris fixpoints using `partial_fixpoint`.
-/

@[expose] public section

namespace Iris
open Iris.Std BI OFE Lean.Order

variable [BI PROP]

/-- `fix` is below every prefixed point. -/
theorem fix_le_of_prefixed {α : Sort _} [CCPO α] {f : α → α} (hf : monotone f) {y : α}
    (hy : f y ⊑ y) : fix f hf ⊑ y :=
  fix_induct hf _ (fun _ hc h => csup_le hc h) fun _ hx => PartialOrder.rel_trans (hf _ _ hx) hy

/-- `fix` commutes with order isomorphisms. -/
theorem fix_iso {α β : Sort _} [CCPO α] [CCPO β]
    (e : α → β) (e' : β → α) (he : monotone e) (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ y, e (e' y) = y)
    {f : α → α} (hf : monotone f) {g : β → β} (hg : monotone g)
    (hfg : ∀ x, e (f x) = g (e x)) :
    e (fix f hf) = fix g hg := by
  apply PartialOrder.rel_antisymm
  · have hfix : f (e' (fix g hg)) = e' (fix g hg) := by
      rw [← h₁ (f _), hfg, h₂, ← fix_eq hg]
    have h := he _ _ (fix_le_of_prefixed hf (PartialOrder.rel_of_eq hfix))
    rw [h₂] at h
    exact h
  · apply fix_le_of_prefixed hg
    rw [← hfg, ← fix_eq hf]

namespace MonotoneFixpoint

scoped instance instPartialOrderMonoProp : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

theorem sExists_is_sup (c : PROP → Prop) :
      is_sup c (sExists c) := by
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact (sExists_intro hy).trans h
    · exact sExists_elim h

scoped instance instCCPOMonoProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sExists_is_sup c⟩

/-- Equivalence between CCPO supremum with the Iris supremum (`exists`). -/
theorem csup_eq_exists {c : PROP → Prop} (hc : chain c) : CCPO.csup hc = sExists c :=
   is_sup_unique (CCPO.csup_spec hc) (sExists_is_sup c)

theorem admissible_nonExpansive [OFE A] : admissible (fun f : A → PROP => NonExpansive f) := by
  intro c hc hfix
  rw [← fun_csup_eq c hc]
  refine ⟨fun n x₁ x₂ hx => ?_⟩
  simp only [fun_csup, csup_eq_exists]
  refine sExists_ne ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f x₂, ⟨f, hf, rfl⟩, (hfix f hf).ne hx⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f x₁, ⟨f, hf, rfl⟩, (hfix f hf).ne hx⟩

/-- The least fixpoint is nonexpansive when the body preserves nonexpansiveness. -/
theorem fix_nonExpansive [OFE A] (F : (A → PROP) → (A → PROP)) (hm : monotone F)
    (hF : ∀ f, NonExpansive f → NonExpansive (F f)) : NonExpansive (fix F hm) :=
  fix_induct hm _ admissible_nonExpansive hF

/-- The least fixpoint coincides with the BI least fixpoint. -/
theorem fix_eq_bi_least_fixpoint [OFE A] (F : (A → PROP) → (A → PROP)) (hm : monotone F)
    [BIMonoPred F] : fix F hm = bi_least_fixpoint F := by
  apply PartialOrder.rel_antisymm
  · apply fix_le_of_prefixed hm
    exact PartialOrder.rel_of_eq (funext fun _ => (least_fixpoint_unfold F).symm)
  · intro x
    have : NonExpansive (fix F hm) := fix_nonExpansive F hm fun _ _ => mono_pred_ne
    have h := least_fixpoint_iter F (Φ := fix F hm)
    rw [← fix_eq hm] at h
    change bi_least_fixpoint F x ⊢ fix F hm x
    iintro H
    iapply h $$ [] H
    iintro !> %y Hy
    iexact Hy

/-- Transport `fix_eq_bi_least_fixpoint` along an order isomorphism `e`, e.g. uncurrying. -/
theorem fix_eq_bi_least_fixpoint_of_iso [OFE A] {α : Sort _} [CCPO α]
    (e : α → A → PROP) (e' : (A → PROP) → α) (he : monotone e) (he' : monotone e')
    (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ y, e (e' y) = y) (F : α → α) (hF : monotone F)
    (G : (A → PROP) → (A → PROP)) [BIMonoPred G] (hFG : ∀ x, e (F x) = G (e x)) :
    e (fix F hF) = bi_least_fixpoint G := by
  have hG : monotone G := by
    intro a b h
    have := he _ _ (hF _ _ (he' _ _ h))
    rwa [hFG, hFG, h₂, h₂] at this
  rw [fix_iso e e' he h₁ h₂ hF hG hFG]
  exact fix_eq_bi_least_fixpoint G hG

/-- Fixpoint iteration, transported along an order isomorphism `e`. -/
theorem fix_iter_of_iso [OFE A] {α : Sort _} [CCPO α]
    (e : α → A → PROP) (e' : (A → PROP) → α) (he : monotone e) (he' : monotone e')
    (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ y, e (e' y) = y) (F : α → α) (hF : monotone F)
    (G : (A → PROP) → (A → PROP)) [BIMonoPred G] (hFG : ∀ x, e (F x) = G (e x))
    (Φ : α) (hΦ : NonExpansive (e Φ)) :
    ⊢ □ (∀ p, e (F Φ) p -∗ e Φ p) -∗ ∀ p, e (fix F hF) p -∗ e Φ p := by
  rw [fix_eq_bi_least_fixpoint_of_iso e e' he he' h₁ h₂ F hF G hFG, hFG]
  exact least_fixpoint_iter G (I := hΦ)

section Monotone
variable [PartialOrder α]

@[partial_fixpoint_monotone]
theorem monotone_sep (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∗ g x)) :=
  fun _ _ h => sep_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_and (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∧ g x)) :=
  fun _ _ h => and_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_or (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∨ g x)) :=
  fun _ _ h => or_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_wand (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P -∗ g x)) :=
  fun _ _ h => wand_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_imp (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P → g x)) :=
  fun _ _ h => imp_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_exists {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∃ b, f x b)) :=
  fun _ _ h => exists_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_forall {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∀ b, f x b)) :=
  fun _ _ h => forall_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_later (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(▷ f x)) :=
  fun _ _ h => later_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_laterN (n : Nat) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(▷^[n] f x)) :=
  fun _ _ h => laterN_mono n (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_except0 (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(◇ f x)) :=
  fun _ _ h => except0_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_persistently (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<pers> f x)) :=
  fun _ _ h => persistently_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_affinely (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<affine> f x)) :=
  fun _ _ h => affinely_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_absorbingly (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<absorb> f x)) :=
  fun _ _ h => absorbingly_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_intuitionistically (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(□ f x)) :=
  fun _ _ h => intuitionistically_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bupd [BIUpdate PROP] (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|==> f x)) :=
  fun _ _ h => bupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={E1,E2}=> f x)) :=
  fun _ _ h => fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupd [BIFUpdate PROP] (Eo Ei : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={Eo}[Ei]▷=> f x)) :=
  fun _ _ h => step_fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupdN [BIFUpdate PROP] (n : Nat) (Eo Ei : CoPset) (f : α → PROP)
    (hf : monotone f) : monotone (fun x => iprop(|={Eo}[Ei]▷=>^[n] f x)) :=
  fun _ _ h => step_fupdN_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bigSepL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigSepL.bigSepL_mono_of_forall fun {k a} => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigAndL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∧list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigAndL.bigAndL_mono fun k a _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigOrL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∨list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigOrL.bigOrL_mono fun {k a} _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigSepL2 {A B : Type _} (l1 : List A) (l2 : List B)
    (f : α → Nat → A → B → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a;b ∈ l1;l2, f x k a b)) :=
  fun _ _ h => BigSepL2.bigSepL2_mono fun {k a b} _ _ => hf _ _ h k a b

@[partial_fixpoint_monotone]
theorem monotone_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (f : α → K → V → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗map] k ↦ v ∈ m, f x k v)) :=
  fun _ _ h => BigSepM.bigSepM_mono_of_forall fun {k v} => hf _ _ h k v

@[partial_fixpoint_monotone]
theorem monotone_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (f : α → A → PROP)
    (hf : monotone f) : monotone (fun x => iprop([∗set] a ∈ X, f x a)) :=
  fun _ _ h => BigSepS.bigSepS_mono_of_forall fun a => hf _ _ h a

end Monotone

end MonotoneFixpoint

namespace CoMonotoneFixpoint

scoped instance instPartialOrderAntiProp : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

theorem sForall_is_sup (c : PROP → Prop) :
      is_sup c (sForall c) := by
    refine fun x => ⟨fun h y hy => ?_, fun h => ?_⟩
    · exact h.trans (sForall_elim hy)
    · exact sForall_intro h

scoped instance instCCPOAntiProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sForall_is_sup c⟩

/-- Equivalence between CCPO supremum with the Iris infimum (`forall`). -/
theorem csup_eq_forall {c : PROP → Prop} (hc : chain c) : CCPO.csup hc = sForall c :=
   is_sup_unique (CCPO.csup_spec hc) (sForall_is_sup c)

theorem admissible_nonExpansive [OFE A] : admissible (fun f : A → PROP => NonExpansive f) := by
  intro c hc hfix
  rw [← fun_csup_eq c hc]
  refine ⟨fun n x₁ x₂ hx => ?_⟩
  simp only [fun_csup, csup_eq_forall]
  refine sForall_ne ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f x₂, ⟨f, hf, rfl⟩, (hfix f hf).ne hx⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨f x₁, ⟨f, hf, rfl⟩, (hfix f hf).ne hx⟩


/-- The greatest fixpoint is nonexpansive when the body preserves nonexpansiveness. -/
theorem fix_nonExpansive [OFE A] (F : (A → PROP) → (A → PROP)) (hm : monotone F)
    (hF : ∀ f, NonExpansive f → NonExpansive (F f)) : NonExpansive (fix F hm) :=
  fix_induct hm _ admissible_nonExpansive hF

/-- The greatest fixpoint coincides with the BI greatest fixpoint. -/
theorem fix_eq_bi_greatest_fixpoint [OFE A] (F : (A → PROP) → (A → PROP)) (hm : monotone F)
    [BIMonoPred F] : fix F hm = bi_greatest_fixpoint F := by
  apply PartialOrder.rel_antisymm
  · -- `bi_greatest_fixpoint F` is a fixpoint, so `fix` is above it.
    apply fix_le_of_prefixed hm
    exact PartialOrder.rel_of_eq (funext fun _ => (greatest_fixpoint_unfold F).symm)
  · -- Use `fix F hm` as the coinduction hypothesis.
    intro x
    have : NonExpansive (fix F hm) := fix_nonExpansive F hm fun _ _ => mono_pred_ne
    have h := greatest_fixpoint_coiter F (fix F hm)
    rw [← fix_eq hm] at h
    change fix F hm x ⊢ bi_greatest_fixpoint F x
    iintro H
    iapply h $$ [] H
    iintro !> %y Hy
    iexact Hy

/-- Transport `fix_eq_bi_greatest_fixpoint` along an order isomorphism `e`, e.g. uncurrying. -/
theorem fix_eq_bi_greatest_fixpoint_of_iso [OFE A] {α : Sort _} [CCPO α]
    (e : α → A → PROP) (e' : (A → PROP) → α) (he : monotone e) (he' : monotone e')
    (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ y, e (e' y) = y) (F : α → α) (hF : monotone F)
    (G : (A → PROP) → (A → PROP)) [BIMonoPred G] (hFG : ∀ x, e (F x) = G (e x)) :
    e (fix F hF) = bi_greatest_fixpoint G := by
  have hG : monotone G := by
    intro a b h
    have := he _ _ (hF _ _ (he' _ _ h))
    rwa [hFG, hFG, h₂, h₂] at this
  rw [fix_iso e e' he h₁ h₂ hF hG hFG]
  exact fix_eq_bi_greatest_fixpoint G hG

/-- Fixpoint coiteration, transported along an order isomorphism `e`. -/
theorem fix_coiter_of_iso [OFE A] {α : Sort _} [CCPO α]
    (e : α → A → PROP) (e' : (A → PROP) → α) (he : monotone e) (he' : monotone e')
    (h₁ : ∀ x, e' (e x) = x) (h₂ : ∀ y, e (e' y) = y) (F : α → α) (hF : monotone F)
    (G : (A → PROP) → (A → PROP)) [BIMonoPred G] (hFG : ∀ x, e (F x) = G (e x))
    (Φ : α) (hΦ : NonExpansive (e Φ)) :
    ⊢ □ (∀ p, e Φ p -∗ e (F Φ) p) -∗ ∀ p, e Φ p -∗ e (fix F hF) p := by
  rw [fix_eq_bi_greatest_fixpoint_of_iso e e' he he' h₁ h₂ F hF G hFG, hFG]
  exact greatest_fixpoint_coiter G (e Φ) (I := hΦ)

section Monotone
variable [PartialOrder α]

@[partial_fixpoint_monotone]
theorem monotone_sep (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∗ g x)) :=
  fun _ _ h => sep_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_and (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∧ g x)) :=
  fun _ _ h => and_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_or (f g : α → PROP) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => iprop(f x ∨ g x)) :=
  fun _ _ h => or_mono (hf _ _ h) (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_wand (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P -∗ g x)) :=
  fun _ _ h => wand_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_imp (P : PROP) (g : α → PROP) (hg : monotone g) :
    monotone (fun x => iprop(P → g x)) :=
  fun _ _ h => imp_mono_right (hg _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_exists {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∃ b, f x b)) :=
  fun _ _ h => exists_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_forall {β : Sort _} (f : α → β → PROP) (hf : monotone f) :
    monotone (fun x => iprop(∀ b, f x b)) :=
  fun _ _ h => forall_mono fun b => monotone_apply b f hf _ _ h

@[partial_fixpoint_monotone]
theorem monotone_later (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(▷ f x)) :=
  fun _ _ h => later_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_laterN (n : Nat) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(▷^[n] f x)) :=
  fun _ _ h => laterN_mono n (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_except0 (f : α → PROP) (hf : monotone f) : monotone (fun x => iprop(◇ f x)) :=
  fun _ _ h => except0_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_persistently (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<pers> f x)) :=
  fun _ _ h => persistently_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_affinely (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<affine> f x)) :=
  fun _ _ h => affinely_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_absorbingly (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(<absorb> f x)) :=
  fun _ _ h => absorbingly_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_intuitionistically (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(□ f x)) :=
  fun _ _ h => intuitionistically_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bupd [BIUpdate PROP] (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|==> f x)) :=
  fun _ _ h => bupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_fupd [BIFUpdate PROP] (E1 E2 : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={E1,E2}=> f x)) :=
  fun _ _ h => fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupd [BIFUpdate PROP] (Eo Ei : CoPset) (f : α → PROP) (hf : monotone f) :
    monotone (fun x => iprop(|={Eo}[Ei]▷=> f x)) :=
  fun _ _ h => step_fupd_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_step_fupdN [BIFUpdate PROP] (n : Nat) (Eo Ei : CoPset) (f : α → PROP)
    (hf : monotone f) : monotone (fun x => iprop(|={Eo}[Ei]▷=>^[n] f x)) :=
  fun _ _ h => step_fupdN_mono (hf _ _ h)

@[partial_fixpoint_monotone]
theorem monotone_bigSepL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigSepL.bigSepL_mono_of_forall fun {k a} => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigAndL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∧list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigAndL.bigAndL_mono fun k a _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigOrL {A : Type _} (l : List A) (f : α → Nat → A → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∨list] k ↦ a ∈ l, f x k a)) :=
  fun _ _ h => BigOrL.bigOrL_mono fun {k a} _ => hf _ _ h k a

@[partial_fixpoint_monotone]
theorem monotone_bigSepL2 {A B : Type _} (l1 : List A) (l2 : List B)
    (f : α → Nat → A → B → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗list] k ↦ a;b ∈ l1;l2, f x k a b)) :=
  fun _ _ h => BigSepL2.bigSepL2_mono fun {k a b} _ _ => hf _ _ h k a b

@[partial_fixpoint_monotone]
theorem monotone_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] (m : M V)
    (f : α → K → V → PROP) (hf : monotone f) :
    monotone (fun x => iprop([∗map] k ↦ v ∈ m, f x k v)) :=
  fun _ _ h => BigSepM.bigSepM_mono_of_forall fun {k v} => hf _ _ h k v

@[partial_fixpoint_monotone]
theorem monotone_bigSepS {S A : Type _} [LawfulFiniteSet S A] (X : S) (f : α → A → PROP)
    (hf : monotone f) : monotone (fun x => iprop([∗set] a ∈ X, f x a)) :=
  fun _ _ h => BigSepS.bigSepS_mono_of_forall fun a => hf _ _ h a

end Monotone

end CoMonotoneFixpoint

end Iris
