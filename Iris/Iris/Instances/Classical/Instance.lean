/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public import Iris.BI
public import Iris.Instances.Data
public import Iris.Std.Equivalence

@[expose] public section

namespace Iris.Instances.Classical
open Iris.BI Iris.Instances.Data Iris.Std

/- Instance of `BIBase` and `BI` for classical (non-affine) separation logic. -/

abbrev HeapProp (Val : Type _) := State Val → Prop

section BIInstance

/-- `BIBase` data; only reachable globally through `BI.toBIBase`. -/
@[reducible] def instBIBaseHeapProp : BIBase (HeapProp Val) where
  Entails P Q      := ∀ σ, P σ → Q σ
  emp            σ := σ = ∅
  pure φ         _ := φ
  and P Q        σ := P σ ∧ Q σ
  or P Q         σ := P σ ∨ Q σ
  imp P Q        σ := P σ → Q σ
  sForall Ψ      σ := ∀ p, Ψ p → p σ
  sExists Ψ      σ := ∃ p, Ψ p ∧ p σ
  sep P Q        σ := ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 || σ2 ∧ P σ1 ∧ Q σ2
  wand P Q       σ := ∀ σ', σ || σ' → P σ' → Q (σ ∪ σ')
  persistently P _ := P ∅
  later _        _ := True

attribute [local instance] instBIBaseHeapProp

instance heapPropPreorder : Std.IsPreorder (HeapProp Val) where
  le_refl := by
    intro _ _ h
    exact h
  le_trans := by
    intro _ _ _ h_xy h_yz σ h_x
    apply h_yz σ
    apply h_xy σ
    exact h_x

instance : COFE Nat (HeapProp Val) := COFE.ofDiscrete _

instance : BI (HeapProp Val) where
  toBIBase := instBIBaseHeapProp
  entails_refl := heapPropPreorder.le_refl _
  entails_trans := heapPropPreorder.le_trans _ _ _
  equiv_iff {P Q} := ⟨
    fun h => h ▸ ⟨Std.IsPreorder.le_refl P, Std.IsPreorder.le_refl P⟩,
    fun ⟨h₁, h₂⟩ => funext fun σ => propext ⟨h₁ σ, h₂ σ⟩
  ⟩

  pure_intro h _ _ := h
  pure_elim' h_φP σ h_φ := h_φP h_φ σ ⟨⟩

  and_elim_l := by
    intros
    simp only [BI.Entails, BI.and]
    intro _ h
    exact h.left
  and_elim_r := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h
    exact h.right
  and_intro := by
    simp only [BI.Entails, BI.and]
    intro _ _ _ h_PQ h_PR σ h_P
    constructor
    · exact h_PQ σ h_P
    · exact h_PR σ h_P

  or_intro_l := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inl
    exact h
  or_intro_r := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h
    apply Or.inr
    exact h
  or_elim := by
    simp only [BI.Entails, BI.or]
    intro _ _ _ h_PR h_QR σ h_PQ
    cases h_PQ
    case inl h_P =>
      exact h_PR σ h_P
    case inr h_Q =>
      exact h_QR σ h_Q

  imp_intro := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ h_P h_Q
    exact h_PQR σ ⟨h_P, h_Q⟩
  imp_elim := by
    simp only [BI.Entails, BI.imp, BI.and]
    intro _ _ _ h_PQR σ ⟨h_P, h_Q⟩
    exact h_PQR σ h_P h_Q

  sForall_intro := by
    simp only [BI.Entails]
    intro _ _ h_PΨ σ h_P p hp
    exact h_PΨ p hp σ h_P
  sForall_elim := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact h_Ψ p hp

  sExists_intro := by
    simp only [BI.Entails]
    intro _ p hp _ h_Ψ
    exact ⟨p, hp, h_Ψ⟩
  sExists_elim := by
    simp only [BI.Entails]
    intro _ _ h_ΦQ σ ⟨p, hp, h_Φ⟩
    exact h_ΦQ p hp σ h_Φ

  sep_mono := by
    simp only [BI.Entails, BI.sep]
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
  emp_sep.mp := by
    simp only [BI.Entails, BI.sep, BI.emp]
    intro _ ⟨σ₁, σ₂, h_union, _, h_emp, h_P⟩
    rw [h_emp] at h_union
    rw [← empty_union] at h_union
    rw [h_union]
    exact h_P
  emp_sep.mpr := by
    simp only [BI.Entails, BI.sep, BI.emp]
    intro σ h_P
    apply Exists.intro ∅
    apply Exists.intro σ
    constructor
    · exact empty_union
    constructor
    · exact empty_disjoint
    constructor
    · rfl
    · exact h_P
  sep_symm := by
    simp only [BI.Entails, BI.sep]
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
    simp only [BI.Entails, BI.sep]
    intro _ _ _ _
      ⟨σ₁, σ₂, h_union₁₂, h_disjoint₁₂, ⟨σ₃, σ₄, h_union₃₄, h_disjoint₃₄, h_P, h_Q⟩, h_R⟩
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
    simp only [BI.Entails, BI.wand, BI.sep]
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
    simp only [BI.Entails, BI.wand, BI.sep]
    intro _ _ _ h_PQR _ ⟨σ, σ', h_union, h_disjoint, h_P, h_Q⟩
    rw [h_union]
    exact h_PQR σ h_P σ' h_disjoint h_Q

  persistently_mono := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h_PQ _ h_P
    exact h_PQ ∅ h_P
  persistently_idem_2 := by
    simp only [BI.Entails, BI.persistently]
    intro _ _ h
    exact h
  persistently_emp_2 := by
    simp only [BI.Entails, BI.persistently, BI.emp]
    intro _ _
    simp
  persistently_and_2 := by
    simp only [BI.Entails, BI.persistently, BI.and]
    intro _ _ _ h
    exact h
  persistently_absorb_l := by
    simp only [BI.Entails, BI.persistently, BI.sep]
    intro _ _ _ ⟨_, _, _, _, h_P, _⟩
    exact h_P
  persistently_and_l := by
    simp only [BI.Entails, BI.persistently, BI.and, BI.sep]
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

  later_mono _ _ h := h
  later_intro _ _ := trivial
  later_sForall_2 _ _ := trivial
  later_false_sExists _ h :=
    let ⟨p, hΦ, hp⟩ := h trivial
    ⟨_, ⟨p, rfl⟩, hΦ, fun _ => hp⟩
  later_false_sep _ h :=
    let ⟨σ1, σ2, hu, hd, hP, hQ⟩ := h trivial
    ⟨σ1, σ2, hu, hd, fun _ => hP, fun _ => hQ⟩
  later_sep_2 _ _ := trivial
  later_persistently := ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  later_false_em _ _ := .inl trivial

instance : BIStepIndexed Nat (HeapProp Val) where
  and_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  or_ne           := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  imp_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  sep_ne          := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  wand_ne         := ⟨by rintro _ _ _ h1 _ _ h2; exact (h1 : _ = _) ▸ (h2 : _ = _) ▸ rfl⟩
  persistently_ne := ⟨by rintro _ _ _ h; exact (h : _ = _) ▸ rfl⟩
  later_ne        := ⟨fun _ _ _ _ => rfl⟩
  sForall_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  sExists_ne {_ P Q} h := (liftRel_eq.1 (h : liftRel Eq P Q)) ▸ rfl
  later_sExists_false _ _ := .inl trivial
  later_sep_1 σ _ := ⟨∅, σ, empty_union, empty_disjoint, trivial, trivial⟩

end BIInstance
end Classical

end Instances

end Iris
