/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.BI

@[expose] public section

namespace Iris
open Iris.Std BI BI.BIBase OFE

section Laws

@[rocq_alias fixpoint_plain]
theorem fixpoint_plain [Sbi PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Plain (F Φ x))) → ∀ x, Plain (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Plain (f x))
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  exact limitPreserving_plain _

@[rocq_alias fixpoint_persistent]
theorem fixpoint_persistent [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Persistent (f x))
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  exact limitPreserving_persistent _

@[rocq_alias fixpoint_absorbing]
theorem fixpoint_absorbing [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Absorbing (f x))
      (fun _ => iprop(True)) inferInstance HΦ ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  exact limitPreserving_absorbing _

@[rocq_alias fixpoint_affine]
theorem fixpoint_affine [BI PROP] {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x))) → ∀ x, Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (fun f => ∀ x, Affine (f x))
      (fun _ => iprop(emp)) inferInstance HΦ ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  exact limitPreserving_affine _

-- FIXME: typo in Iris-Rocq
@[rocq_alias fixpoint_persistent_absoring]
theorem fixpoint_persistent_absorbing [BI PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Absorbing (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Persistent (f x) ∧ Absorbing (f x))
      (fun _ => iprop(True)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  refine LimitPreserving.and ?_ ?_
  · exact limitPreserving_persistent _
  · exact limitPreserving_absorbing _

@[rocq_alias fixpoint_persistent_affine]
theorem fixpoint_persistent_affine [BI PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Affine (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Persistent (f x) ∧ Affine (f x))
      (fun _ => iprop(emp)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  refine LimitPreserving.and ?_ ?_
  · exact limitPreserving_persistent _
  · exact limitPreserving_affine _

-- FIXME: typo in Iris-Rocq
@[rocq_alias fixpoint_plain_absoring]
theorem fixpoint_plain_absorbing [Sbi PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Absorbing (Φ x)) →
      (∀ x, Plain (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Absorbing (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Plain (f x) ∧ Absorbing (f x))
      (fun _ => iprop(True)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  refine LimitPreserving.and ?_ ?_
  · exact limitPreserving_plain _
  · exact limitPreserving_absorbing _

@[rocq_alias fixpoint_plain_affine]
theorem fixpoint_plain_affine [Sbi PROP] {A : Type _}
    (F : (A → PROP) → A → PROP) [Contractive F] :
    (∀ Φ, (∀ x, Plain (Φ x)) → (∀ x, Affine (Φ x)) →
      (∀ x, Plain (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Plain (fixpoint F x) ∧ Affine (fixpoint F x) := by
  intro HΦ
  refine ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩
      (fun f => ∀ x, Plain (f x) ∧ Affine (f x))
      (fun _ => iprop(emp)) (fun _ => ⟨inferInstance, inferInstance⟩)
      (fun x H => HΦ _ (fun x => (H x).left) (fun x => (H x).right)) ?_
  refine LimitPreserving.forall _ (fun _ => ?_)
  refine LimitPreserving.and ?_ ?_
  · exact limitPreserving_plain _
  · exact limitPreserving_affine _

end Laws

/-! ## Moving a fixpoint across an isomorphism

`iguarded` uses these to restate the laws above for a fixpoint of several curried arguments. -/

section Conj

variable {α β : Type _} [OFE α] [OFE β]

/-- Conjugating a contractive map by non-expansive maps keeps it contractive. -/
theorem contractive_conj {F : α → α} [Contractive F] (e : α → β) (e' : β → α) [NonExpansive e]
    [NonExpansive e'] : Contractive fun b => e (F (e' b)) :=
  ⟨fun h => NonExpansive.ne (Contractive.distLater_dist fun m hm => NonExpansive.ne (h m hm))⟩

/-- The fixpoint moves across an isomorphism, whatever the default points. -/
theorem fixpoint_conj [IsCOFE α] [IsCOFE β] {iα : Inhabited α} {iβ : Inhabited β} {F : α → α}
    [Contractive F] (e : α → β) (e' : β → α) [NonExpansive e] [NonExpansive e']
    (h : ∀ a, e' (e a) = a) :
    e (fixpoint F) = @fixpoint β _ iβ (fun b => e (F (e' b))) (contractive_conj e e') := by
  haveI := contractive_conj (F := F) e e'
  refine @fixpoint_unique β _ iβ (fun b => e (F (e' b))).toContractiveHom _ ?_
  change e (fixpoint F) = e (F (e' (e (fixpoint F))))
  rw [h]
  exact congrArg e (fixpoint_unfold F.toContractiveHom)

end Conj

end Iris
