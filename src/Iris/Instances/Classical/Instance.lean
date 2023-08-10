/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Instances.Data

namespace Iris.Instances.Classical
open Iris.BI Iris.Instances.Data

/- Instance of `BIBase` and `BI` for classical (non-affine) separation logic. -/

abbrev HeapProp (Val : Type) := State Val → Prop

instance : BIBase (HeapProp Val) where
  entails P Q    := ∀ σ, P σ → Q σ
  emp            := fun σ => σ = ∅
  pure φ         := fun _ => φ
  and P Q        := fun σ => P σ ∧ Q σ
  or P Q         := fun σ => P σ ∨ Q σ
  imp P Q        := fun σ => P σ → Q σ
  «forall» Ψ     := fun σ => ∀ a, Ψ a σ
  «exists» Ψ     := fun σ => ∃ a, Ψ a σ
  sep P Q        := fun σ => ∃ σ1 σ2 , σ = σ1 ∪ σ2 ∧ σ1 || σ2 ∧ P σ1 ∧ Q σ2
  wand P Q       := fun σ => ∀ σ', σ || σ' → P σ' → Q (σ ∪ σ')
  persistently P := fun _ => P ∅

instance : BI (HeapProp Val) where
  entails_preorder := {
    refl := by
      simp only [BIBase.entails]
      intro _ _ h
      exact h
    trans := by
      simp only [BIBase.entails]
      intro _ _ _ h_xy h_yz σ h_x
      apply h_yz σ
      apply h_xy σ
      exact h_x
  }

  equiv_entails := by
    simp only [BIBase.entails]
    intro P Q
    constructor
    case mp =>
      intro h
      rw [h]
      constructor
      all_goals
        intro _ h_Q
        exact h_Q
    case mpr =>
      intro ⟨h_P, h_Q⟩
      apply funext
      intro σ
      apply propext
      constructor
      · exact h_P σ
      · exact h_Q σ

  pure_intro := by
    simp only [BIBase.entails, BIBase.pure]
    intro _ _ h _ _
    exact h
  pure_elim' := by
    simp only [BIBase.entails, BIBase.pure]
    intro _ _ h_φP σ h_φ
    apply h_φP h_φ σ
    simp

  and_elim_l := by
    intros
    simp only [BIBase.entails, BIBase.and]
    intro _ h
    exact h.left
  and_elim_r := by
    simp only [BIBase.entails, BIBase.and]
    intro _ _ _ h
    exact h.right
  and_intro := by
    simp only [BIBase.entails, BIBase.and]
    intro _ _ _ h_PQ h_PR σ h_P
    constructor
    · exact h_PQ σ h_P
    · exact h_PR σ h_P

  or_intro_l := by
    simp only [BIBase.entails, BIBase.or]
    intro _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BIBase.entails, BIBase.or]
    intro _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BIBase.entails, BIBase.or]
    intro _ _ _ h_PR h_QR σ h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR σ h_P
    case inr h_Q =>
      exact h_QR σ h_Q

  imp_intro := by
    simp only [BIBase.entails, BIBase.imp, BIBase.and]
    intro _ _ _ h_PQR σ h_P h_Q
    exact h_PQR σ ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BIBase.entails, BIBase.imp, BIBase.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    exact h_PQR σ h_P h_Q

  forall_intro := by
    simp only [BIBase.entails, BIBase.forall]
    intro _ _ _ h_PΨ σ h_P a
    exact h_PΨ a σ h_P
  forall_elim := by
    simp only [BIBase.entails, BIBase.forall]
    intro _ _ a _ h_Ψ
    exact h_Ψ a

  exists_intro := by
    simp only [BIBase.entails, BIBase.exists]
    intro _ _ a _ Ψ
    apply Exists.intro a
    exact Ψ
  exists_elim := by
    simp only [BIBase.entails, BIBase.exists]
    intro _ _ _ h_ΦQ σ ⟨a, h_Φ⟩
    exact h_ΦQ a σ h_Φ

  sep_mono := by
    simp only [BIBase.entails, BIBase.sep]
    intro _ _ _ _ h_PQ h_P'Q' _ ⟨σ₁, σ₂, h_union, h_disjoint, h_P, h_P'⟩
    apply Exists.intro σ₁
    apply Exists.intro σ₂
    constructor
    · exact h_union
    constructor
    · exact h_disjoint
    constructor
    · exact h_PQ σ₁ h_P
    · exact h_P'Q' σ₂ h_P'
  emp_sep_2 := by
    simp only [BIBase.entails, BIBase.sep, BIBase.emp]
    intro _ σ h_P
    apply Exists.intro ∅
    apply Exists.intro σ
    constructor
    · exact empty_union
    constructor
    · exact empty_disjoint
    constructor
    · rfl
    · exact h_P
  emp_sep_1 := by
    simp only [BIBase.entails, BIBase.sep, BIBase.emp]
    intro _ _ ⟨σ₁, σ₂, h_union, _, h_emp, h_P⟩
    rw [h_emp] at h_union
    rw [← empty_union] at h_union
    rw [h_union]
    exact h_P
  sep_symm := by
    simp only [BIBase.entails, BIBase.sep]
    intro _ _ _ ⟨σ₁, σ₂, h_union, h_disjoint, h_P, h_Q⟩
    apply Exists.intro σ₂
    apply Exists.intro σ₁
    constructor
    · rw [union_comm] ; exact h_union
    constructor
    · rw [disjoint_comm] ; exact h_disjoint
    constructor
    · exact h_Q
    · exact h_P
  sep_assoc_l := by
    simp only [BIBase.entails, BIBase.sep]
    intro _ _ _ _ ⟨σ₁, σ₂, h_union₁₂, h_disjoint₁₂, ⟨σ₃, σ₄, h_union₃₄, h_disjoint₃₄, h_P, h_Q⟩, h_R⟩
    apply Exists.intro σ₃
    apply Exists.intro (σ₄ ∪ σ₂)
    constructor
    · rw [h_union₃₄] at h_union₁₂
      rw [← union_assoc]
      exact h_union₁₂
    constructor
    · apply disjoint_union
      · exact h_disjoint₃₄
      · rw [h_union₃₄] at h_disjoint₁₂
        let h_disjoint := disjoint_assoc h_disjoint₁₂ h_disjoint₃₄
        exact h_disjoint.left
    constructor
    · exact h_P
    apply Exists.intro σ₄
    apply Exists.intro σ₂
    constructor
    · rw [union_comm]
    constructor
    · rw [h_union₃₄] at h_disjoint₁₂
      let h_disjoint := disjoint_assoc h_disjoint₁₂ h_disjoint₃₄
      exact h_disjoint.right
    constructor
    · exact h_Q
    · exact h_R

  wand_intro := by
    simp only [BIBase.entails, BIBase.wand, BIBase.sep]
    intro _ _ _ h_PQR σ h_P σ' h_disjoint h_Q
    apply h_PQR (σ ∪ σ')
    apply Exists.intro σ
    apply Exists.intro σ'
    constructor
    · rfl
    constructor
    · exact h_disjoint
    constructor
    · exact h_P
    · exact h_Q
  wand_elim := by
    simp only [BIBase.entails, BIBase.wand, BIBase.sep]
    intro _ _ _ h_PQR _ ⟨σ, σ', h_union, h_disjoint, h_P, h_Q⟩
    rw [h_union]
    exact h_PQR σ h_P σ' h_disjoint h_Q

  persistently_mono := by
    simp only [BIBase.entails, BIBase.persistently]
    intro _ _ h_PQ _ h_P
    exact h_PQ ∅ h_P
  persistently_idem_2 := by
    simp only [BIBase.entails, BIBase.persistently]
    intro _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BIBase.entails, BIBase.persistently, BIBase.emp]
    intro _ _
    simp
  persistently_and_2 := by
    simp only [BIBase.entails, BIBase.persistently, BIBase.and]
    intro _ _ _ h
    exact h
  persistently_exists_1 := by
    simp only [BIBase.entails, BIBase.persistently, BIBase.exists]
    intro _ _ _ h
    exact h
  persistently_absorb_l := by
    simp only [BIBase.entails, BIBase.persistently, BIBase.sep]
    intro _ _ _ ⟨_, _, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BIBase.entails, BIBase.persistently, BIBase.and, BIBase.sep]
    intro _ _ σ ⟨h_P, h_Q⟩
    apply Exists.intro ∅
    apply Exists.intro σ
    constructor
    · exact empty_union
    constructor
    · exact empty_disjoint
    constructor
    · exact h_P
    · exact h_Q

end Iris.Instances.Classical
