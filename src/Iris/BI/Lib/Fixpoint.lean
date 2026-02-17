/-
Copyright (c) 2026 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI
import Iris.ProofMode

namespace Iris
open Iris.Std BI OFE


class BIMonoPred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  mono_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x
  mono_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export BIMonoPred (mono_pred mono_pred_ne)
attribute [instance] mono_pred_ne

-- PORTING NOTE: This is an `abbrev` because of typeclass inference
abbrev bi_least_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∀ (Φ : A -n> PROP), □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)

def bi_greatest_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∃ (Φ : A -n> PROP), □ (∀ x, Φ x -∗ F Φ x) ∗ Φ x)

/-- Porting note: The Rocq version of this theorem has an additional
  `∀ Φ, NonExpansive Φ → NonExpansive (F Φ)` hypothesis. Not sure why! -/
instance [BI PROP] [OFE A] {F : (A → PROP) → (A → PROP)} : NonExpansive (bi_least_fixpoint F) where
  ne {_ _ _} Hx := by
    refine forall_ne fun _ => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    exact NonExpansive.ne Hx

section LeastFixpoint

variable [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP))

theorem least_fixpoint_unfold_2 [BIMonoPred F] {x} :
    F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x := by
  iintro Hf %Φ #Hincl
  iapply Hincl
  iapply mono_pred (Φ := bi_least_fixpoint F) $$ [], [Hf]
  · iintro !> %_ H
    iapply H
    iexact Hincl
  · iexact Hf

theorem least_fixpoint_unfold_1 {x} [BIMonoPred F] :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x := by
  iintro Hf
  ispecialize Hf $$ %(Hom.mk (F (bi_least_fixpoint F)) mono_pred_ne)
  iapply Hf
  iintro !> %y Hy
  iapply mono_pred (Φ := F (bi_least_fixpoint F)) $$ [], [Hy]
  · iintro !> %z Hz
    apply least_fixpoint_unfold_2
  · iexact Hy

theorem least_fixpoint_unfold {x} [BIMonoPred F] :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x :=
  equiv_iff.mpr ⟨least_fixpoint_unfold_1 _, least_fixpoint_unfold_2 _⟩

theorem least_fixpoint_iter {Φ : A → PROP} [I : NonExpansive Φ] :
    ⊢ □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HΦ %x HF
  iapply HF $$ %(Hom.mk Φ I)
  iexact HΦ

instance least_fixpoint_affine [Ia : ∀ x, Affine (F (fun _ => emp) x)] {x : A} :
    Affine (bi_least_fixpoint F x) where
  affine := by
    revert x
    iapply least_fixpoint_iter (Φ := fun _ => emp)
    iintro !> %y H
    iapply (Ia y).affine $$ H

instance least_fixpoint_absorbing [BIMonoPred F]
    [∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))] {x : A} :
    Absorbing (bi_least_fixpoint F x) where
  absorbing := by
    iapply wand_elim'
    revert x
    letI _ : NonExpansive fun x => iprop(True -∗ bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => wand_ne.ne .rfl (NonExpansive.ne H)⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y HF HT
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := (fun x : A => iprop(True -∗ bi_least_fixpoint F x))) $$ [], [HF, HT]
    · iintro !> %x HF
      iapply HF
      exact true_intro
    · iclear HT
      iexact HF

instance least_fixpoint_persistent_affine [BIMonoPred F]
    [∀ Φ, [∀ x, Affine (Φ x)] → (∀ x, Affine (F Φ x))]
    [∀ Φ, [∀ x, Persistent (Φ x)] → (∀ x, Persistent (F Φ x))]
    {x : A} : Persistent (bi_least_fixpoint F x) where
  persistent := by
    refine .trans ?_ persistently_of_intuitionistically
    revert x
    letI _ : NonExpansive fun x => iprop(□ bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => intuitionistically_ne.ne (NonExpansive.ne H)⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y #HY !>
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := fun x => iprop(□ bi_least_fixpoint F x))
    · iintro !> %_ #Hx
      iexact Hx
    · exact intuitionistically_elim

instance least_fixpoint_persistent_absorbing [BIMonoPred F]
    [Habsorb : ∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))]
    [∀ Φ, [∀ x, Persistent (Φ x)] → (∀ x, Persistent (F Φ x))]
    {x : A} : Persistent (bi_least_fixpoint F x) where
  persistent := by
    revert x
    letI _ : NonExpansive fun x => iprop(<pers> bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => persistently_ne.ne <| NonExpansive.ne H⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y #HF !>
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := fun x => iprop(<pers> bi_least_fixpoint F x)) $$ [], HF
    letI _ := @least_fixpoint_absorbing _ _ _ _ _ _ Habsorb
    iintro !> %x #H
    iexact H

theorem least_fixpoint_strong_mono (G : (A → PROP) → (A → PROP)) [BIMonoPred G] :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, bi_least_fixpoint F x -∗ bi_least_fixpoint G x := by
  iintro #Hmon
  iapply least_fixpoint_iter
  · infer_instance -- FIXME: Issue #156
  iintro !> %y IH
  iapply least_fixpoint_unfold
  · infer_instance -- FIXME: Issue #156
  iapply Hmon $$ IH

section Strong

variable [IF : BIMonoPred F] (Φ : A → PROP) [IN : NonExpansive Φ]

local instance wf_pred_mono :
    BIMonoPred (fun (Ψ : A → PROP) (a : A) => iprop(Φ a ∧ F Ψ a)) where
  mono_pred := by
    intro Ψ Ψ' Hne Hne'
    iintro #HM %x Ha
    isplit
    · icases Ha with ⟨H, -⟩
      iexact H
    · icases Ha with ⟨-, H⟩
      iapply (mono_pred (F := F) (Φ := Ψ)) $$ [], H
      iexact HM
  mono_pred_ne.ne _ _ _ H := and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)

theorem least_fixpoint_ind_wf :
    ⊢ □ (∀ y, F (bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM %x
  -- Porting note: Generalized rewriting in the left-hand side of the wand in the goal.
  ihave Hthis : (F (bi_least_fixpoint F) x -∗ Φ x) -∗ (bi_least_fixpoint F x -∗ Φ x) $$ []
  · iintro H1 H2
    iapply H1
    iapply least_fixpoint_unfold
    · infer_instance
    iexact H2
  iapply Hthis
  iintro HF
  iapply HM
  iapply mono_pred (Φ := (bi_least_fixpoint F)) $$ [], HF
  imodintro
  iapply least_fixpoint_iter
  · infer_instance -- FIXME: Issue #156
  iintro !> %y Hy
  iapply least_fixpoint_unfold
  · exact wf_pred_mono (F := F) (Φ := Φ)
  isplit
  · iapply HM $$ Hy
  · iexact Hy

theorem least_fixpoint_ind :
    ⊢ □ (∀ y, F (fun x => iprop(Φ x ∧ bi_least_fixpoint F x)) y -∗ Φ y) -∗
      ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM
  iapply least_fixpoint_ind_wf
  · infer_instance
  · infer_instance
  iintro !> %y Hy
  iapply HM
  letI _ : NonExpansive fun x => iprop(Φ x ∧ bi_least_fixpoint F x) :=
    ⟨fun _ _ _ H => and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)⟩
  iapply mono_pred (Φ := (bi_least_fixpoint fun Ψ a => iprop(Φ a ∧ F Ψ a))) $$ [], Hy
  iintro !> %x Hx
  isplit
  · iclear HM
    exact (least_fixpoint_unfold_1 ..).trans and_elim_l
  · iapply least_fixpoint_strong_mono $$ [], Hx
    · infer_instance
    iintro !> %_ %_ ⟨-, H⟩
    iexact H

end Strong
end LeastFixpoint
