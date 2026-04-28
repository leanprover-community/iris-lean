/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI

@[expose] public section

namespace Iris
open Iris.Std BI OFE

section Laws

@[rocq_alias fixpoint_plain]
theorem fixpoint_plain [Sbi PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Plain (F Φ x))) → ∀ x, Plain (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Plain (f x)) ?_
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  · intro _ _ H HP x
    refine ⟨.trans (.trans (equiv_iff.mp (H x)).mpr (HP x).plain) ?_⟩
    exact plainly_mono (equiv_iff.mp (H x)).mp
  · refine LimitPreserving.forall _ (fun _ => ?_)
    exact limitPreserving_plain _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_persistent]
theorem fixpoint_persistent [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Persistent (f x)) ?_
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  · intro _ _ H HP x
    refine ⟨.trans (.trans (equiv_iff.mp (H x)).mpr (HP x).persistent) ?_⟩
    exact persistently_mono (equiv_iff.mp (H x)).mp
  · refine LimitPreserving.forall _ (fun _ => ?_)
    exact limitPreserving_persistent _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_absorbing]
theorem fixpoint_absorbing [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Absorbing (f x)) ?_
      (fun _ => iprop(True)) inferInstance HΦ ?_
  · intro _ _ H HP x
    refine ⟨.trans (absorbingly_mono (equiv_iff.mp (H x)).mpr) ?_⟩
    exact (HP x).absorbing.trans (equiv_iff.mp (H x)).mp
  · refine LimitPreserving.forall _ (fun _ => ?_)
    exact limitPreserving_absorbing _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_affine]
theorem fixpoint_affine [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x))) → ∀ x, Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Affine (f x)) ?_
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  · intro _ _ H HP x
    exact ⟨.trans (.trans (equiv_iff.mp (H x)).mpr (HP x).affine) .rfl⟩
  · refine LimitPreserving.forall _ (fun _ => ?_)
    exact limitPreserving_affine _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_persistent_absorbing]
theorem fixpoint_persistent_absorbing [BI PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Absorbing (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Persistent (f x) ∧ Absorbing (f x)) ?_
      (fun _ => iprop(True)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  · intro _ _ H HP x
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · refine .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).left.persistent) ?_
      exact persistently_mono (equiv_iff.mp (H x)).mp
    · refine (absorbingly_mono (equiv_iff.mp (H x)).mpr).trans ?_
      exact (HP x).right.absorbing.trans (equiv_iff.mp (H x)).mp
  · refine LimitPreserving.forall _ (fun _ => ?_)
    refine LimitPreserving.and ?_ ?_
    · exact limitPreserving_persistent _ ⟨fun _ _ _ h => h _⟩
    · exact limitPreserving_absorbing _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_persistent_affine]
theorem fixpoint_persistent_affine [BI PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Affine (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Persistent (f x) ∧ Affine (f x)) ?_
      (fun _ => iprop(emp)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  · intro _ _ H HP x
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · refine .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).left.persistent) ?_
      exact persistently_mono (equiv_iff.mp (H x)).mp
    · exact .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).right.affine) .rfl
  · refine LimitPreserving.forall _ (fun _ => ?_)
    refine LimitPreserving.and ?_ ?_
    · exact limitPreserving_persistent _ ⟨fun _ _ _ h => h _⟩
    · exact limitPreserving_affine _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_plain_absorbing]
theorem fixpoint_plain_absorbing [Sbi PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Absorbing (Φ x)) →
      (∀ x, Plain (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Plain (f x) ∧ Absorbing (f x)) ?_
      (fun _ => iprop(True)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  · intro _ _ H HP x
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · refine .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).left.plain) ?_
      exact plainly_mono (equiv_iff.mp (H x)).mp
    · refine (absorbingly_mono (equiv_iff.mp (H x)).mpr).trans ?_
      exact (HP x).right.absorbing.trans (equiv_iff.mp (H x)).mp
  · refine LimitPreserving.forall _ (fun _ => ?_)
    refine LimitPreserving.and ?_ ?_
    · exact limitPreserving_plain _ ⟨fun _ _ _ h => h _⟩
    · exact limitPreserving_absorbing _ ⟨fun _ _ _ h => h _⟩

@[rocq_alias fixpoint_plain_affine]
theorem fixpoint_plain_affine [Sbi PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Affine (Φ x)) →
      (∀ x, Plain (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Plain (f x) ∧ Affine (f x)) ?_
      (fun _ => iprop(emp)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  · intro _ _ H HP x
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · refine .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).left.plain) ?_
      exact plainly_mono (equiv_iff.mp (H x)).mp
    · exact .trans (.trans (equiv_iff.mp (H x)).mpr (HP x).right.affine) .rfl
  · refine LimitPreserving.forall _ (fun _ => ?_)
    refine LimitPreserving.and ?_ ?_
    · exact limitPreserving_plain _ ⟨fun _ _ _ h => h _⟩
    · exact limitPreserving_affine _ ⟨fun _ _ _ h => h _⟩

end Laws

end Iris
