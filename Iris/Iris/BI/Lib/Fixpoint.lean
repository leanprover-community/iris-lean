/-
Copyright (c) 2026 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris
open Iris.Std BI OFE


@[rocq_alias BiMonoPred]
class BIMonoPred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  mono_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x
  mono_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export BIMonoPred (mono_pred mono_pred_ne)
attribute [instance] mono_pred_ne

-- PORTING NOTE: This is an `abbrev` because of typeclass inference
@[rocq_alias bi_least_fixpoint]
abbrev bi_least_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∀ (Φ : A -n> PROP), □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)

@[rocq_alias bi_greatest_fixpoint]
abbrev bi_greatest_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∃ (Φ : A -n> PROP), □ (∀ x, Φ x -∗ F Φ x) ∗ Φ x)

/-- Porting note: The Rocq version of this theorem has an additional
  `∀ Φ, NonExpansive Φ → NonExpansive (F Φ)` hypothesis. Not sure why! -/
@[rocq_alias least_fixpoint_ne']
instance [BI PROP] [OFE A] {F : (A → PROP) → (A → PROP)} :
    NonExpansive (bi_least_fixpoint F) where
  ne {_ _ _} Hx := by
    refine forall_ne fun _ => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    exact NonExpansive.ne Hx

@[rocq_alias greatest_fixpoint_ne']
instance [BI PROP] [OFE A] {F : (A → PROP) → (A → PROP)} :
    NonExpansive (bi_greatest_fixpoint F) where
  ne {_ _ _} Hx := by
    refine exists_ne fun _ => ?_
    refine sep_ne.ne (.of_eq rfl) ?_
    exact NonExpansive.ne Hx

section LeastFixpoint

variable [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP))

@[rocq_alias least_fixpoint_unfold_2]
theorem least_fixpoint_unfold_mpr [BIMonoPred F] {x} :
    F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x := by
  iintro Hf %Φ #Hincl
  iapply Hincl
  iapply mono_pred (Φ := bi_least_fixpoint F) $$ [] [Hf]
  · iintro !> %_ H
    iapply H
    iexact Hincl
  · iexact Hf

@[rocq_alias least_fixpoint_unfold_1]
theorem least_fixpoint_unfold_mp {x} [BIMonoPred F] :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x := by
  iintro Hf
  ispecialize Hf $$ %(Hom.mk (F (bi_least_fixpoint F)) mono_pred_ne)
  iapply Hf
  iintro !> %y Hy
  iapply mono_pred (Φ := F (bi_least_fixpoint F)) $$ [] [Hy]
  · iintro !> %z Hz
    apply least_fixpoint_unfold_mpr
  · iexact Hy

@[rocq_alias least_fixpoint_unfold]
theorem least_fixpoint_unfold {x} [BIMonoPred F] :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x :=
  equiv_iff.mpr ⟨least_fixpoint_unfold_mp _, least_fixpoint_unfold_mpr _⟩

@[rocq_alias least_fixpoint_iter]
theorem least_fixpoint_iter {Φ : A → PROP} [I : NonExpansive Φ] :
    ⊢ □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HΦ %x HF
  iapply HF $$ %(Hom.mk Φ I)
  iexact HΦ

@[rocq_alias least_fixpoint_affine]
instance least_fixpoint_affine [Ia : ∀ x, Affine (F (fun _ => emp) x)] {x : A} :
    Affine (bi_least_fixpoint F x) where
  affine := by
    revert x
    iapply least_fixpoint_iter (Φ := fun _ => emp)
    iintro !> %y H
    iapply (Ia y).affine $$ H

@[rocq_alias least_fixpoint_absorbing]
instance least_fixpoint_absorbing [BIMonoPred F]
    [∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))] {x : A} :
    Absorbing (bi_least_fixpoint F x) where
  absorbing := by
    iapply wand_elim_swap
    revert x
    letI _ : NonExpansive fun x => iprop(True -∗ bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => wand_ne.ne .rfl (NonExpansive.ne H)⟩
    iapply least_fixpoint_iter
    iintro !> %y HF HT
    iapply least_fixpoint_unfold
    iapply mono_pred (Φ := (fun x : A => iprop(True -∗ bi_least_fixpoint F x))) $$ [] [HF HT]
    · iintro !> %x HF
      iapply HF
      exact true_intro
    · iclear HT
      iexact HF

@[rocq_alias least_fixpoint_persistent_affine]
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
    iintro !> %y #HY !>
    iapply least_fixpoint_unfold
    iapply mono_pred (Φ := fun x => iprop(□ bi_least_fixpoint F x))
    · iintro !> %_ #Hx
      iexact Hx
    · exact intuitionistically_elim

@[rocq_alias least_fixpoint_persistent_absorbing]
instance least_fixpoint_persistent_absorbing [BIMonoPred F]
    [Habsorb : ∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))]
    [∀ Φ, [∀ x, Persistent (Φ x)] → (∀ x, Persistent (F Φ x))]
    {x : A} : Persistent (bi_least_fixpoint F x) where
  persistent := by
    revert x
    letI _ : NonExpansive fun x => iprop(<pers> bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => persistently_ne.ne <| NonExpansive.ne H⟩
    iapply least_fixpoint_iter
    iintro !> %y #HF !>
    iapply least_fixpoint_unfold
    iapply mono_pred (Φ := fun x => iprop(<pers> bi_least_fixpoint F x)) $$ [] HF
    letI _ := @least_fixpoint_absorbing _ _ _ _ _ _ Habsorb
    iintro !> %x #H
    iexact H

@[rocq_alias least_fixpoint_strong_mono]
theorem least_fixpoint_strong_mono (G : (A → PROP) → (A → PROP)) [BIMonoPred G] :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, bi_least_fixpoint F x -∗ bi_least_fixpoint G x := by
  iintro #Hmon
  iapply least_fixpoint_iter
  iintro !> %y IH
  iapply least_fixpoint_unfold
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
      iapply (mono_pred (F := F) (Φ := Ψ)) $$ [] H
      iexact HM
  mono_pred_ne.ne _ _ _ H := and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)

@[rocq_alias least_fixpoint_ind_wf]
theorem least_fixpoint_ind_wf :
    ⊢ □ (∀ y, F (bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM %x
  -- Porting note: Generalized rewriting in the left-hand side of the wand in the goal.
  ihave Hthis : (F (bi_least_fixpoint F) x -∗ Φ x) -∗ (bi_least_fixpoint F x -∗ Φ x) $$ []
  · iintro H1 H2
    iapply H1
    iapply least_fixpoint_unfold
    iexact H2
  iapply Hthis
  iintro HF
  iapply HM
  iapply mono_pred (Φ := (bi_least_fixpoint F)) $$ [] HF
  imodintro
  iapply least_fixpoint_iter
  iintro !> %y Hy
  iapply least_fixpoint_unfold
  isplit
  · iapply HM $$ Hy
  · iexact Hy

@[rocq_alias least_fixpoint_ind]
theorem least_fixpoint_ind :
    ⊢ □ (∀ y, F (fun x => iprop(Φ x ∧ bi_least_fixpoint F x)) y -∗ Φ y) -∗
      ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM
  iapply least_fixpoint_ind_wf
  iintro !> %y Hy
  iapply HM
  letI _ : NonExpansive fun x => iprop(Φ x ∧ bi_least_fixpoint F x) :=
    ⟨fun _ _ _ H => and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)⟩
  iapply mono_pred (Φ := (bi_least_fixpoint fun Ψ a => iprop(Φ a ∧ F Ψ a))) $$ [] Hy
  iintro !> %x Hx
  isplit
  · iclear HM
    exact (least_fixpoint_unfold_mp ..).trans and_elim_l
  · iapply least_fixpoint_strong_mono $$ [] Hx
    iintro !> %_ %_ ⟨-, H⟩
    iexact H

end Strong
end LeastFixpoint

section GreatestFixpoint

variable [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP))

@[rocq_alias greatest_fixpoint_ne_outer]
theorem greatest_fixpoint_ne_outer {F1 F2 : (A → PROP) → (A → PROP)}
    (HF : ∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) (Hx : x1 ≡{n}≡ x2) :
    bi_greatest_fixpoint F1 x1 ≡{n}≡ bi_greatest_fixpoint F2 x2 := by
  refine exists_ne fun _ => ?_
  refine sep_ne.ne ?_ (NonExpansive.ne Hx)
  refine intuitionistically_ne.ne ?_
  refine forall_ne fun _ => ?_
  refine wand_ne.ne (.of_eq rfl) ?_
  exact (HF _ _ n)

@[rocq_alias greatest_fixpoint_unfold_1]
theorem greatest_fixpoint_unfold_mp {x} [BIMonoPred F] :
    bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x := by
  iintro ⟨%Φ, #Hincl, HΦ⟩
  iapply mono_pred (Φ := Φ) $$ [] [HΦ]
  · iintro !> %_ H
    iexists Φ
    isplitr
    · iassumption
    · iassumption
  · iapply Hincl $$ HΦ

@[rocq_alias greatest_fixpoint_unfold_2]
theorem greatest_fixpoint_unfold_mpr {x} [BIMonoPred F] :
    F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x := by
  iintro Hf
  iexists (Hom.mk (F (bi_greatest_fixpoint F)) mono_pred_ne)
  isplitr
  · iintro !> %y Hy
    iapply mono_pred (Φ := (bi_greatest_fixpoint F)) $$ [] Hy
    iintro !> %z Hz
    iapply greatest_fixpoint_unfold_mp $$ Hz
  · iexact Hf

@[rocq_alias greatest_fixpoint_unfold]
theorem greatest_fixpoint_unfold {x} [BIMonoPred F] :
    bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x :=
  equiv_iff.mpr ⟨greatest_fixpoint_unfold_mp _, greatest_fixpoint_unfold_mpr _⟩

@[rocq_alias greatest_fixpoint_coiter]
theorem greatest_fixpoint_coiter (Φ : A → PROP) [I : NonExpansive Φ] :
    ⊢ □ (∀ y, Φ y -∗ F Φ y) -∗ ∀ x, Φ x -∗ bi_greatest_fixpoint F x := by
  iintro #HΦ %x Hx
  iexists ⟨Φ, I⟩
  isplitr [Hx]
  · iassumption
  · iassumption

@[rocq_alias greatest_fixpoint_absorbing]
instance greatest_fixpoint_absorbing [BIMonoPred F]
    [∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))] {x : A} :
    Absorbing (bi_greatest_fixpoint F x) where
  absorbing := by
    revert x
    letI _ : NonExpansive fun x => iprop(<absorb> bi_greatest_fixpoint F x) :=
      ⟨fun _ _ _ H => absorbingly_ne.ne (NonExpansive.ne H)⟩
    iapply greatest_fixpoint_coiter
    iintro !> %y >HF
    ihave HF : F (bi_greatest_fixpoint F) y $$ [HF]
    · iapply greatest_fixpoint_unfold_mp $$ HF
    iapply mono_pred $$ [] HF
    iintro !> %_ HF !>
    iassumption

@[rocq_alias greatest_fixpoint_strong_mono]
theorem greatest_fixpoint_strong_mono (G : (A → PROP) → (A → PROP)) [BIMonoPred F] :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, bi_greatest_fixpoint F x -∗ bi_greatest_fixpoint G x := by
  iintro #Hmon
  iapply greatest_fixpoint_coiter
  iintro !> %y IH
  iapply Hmon
  iapply greatest_fixpoint_unfold_mp
  iexact IH

section Coind

variable [IF : BIMonoPred F] (Φ : A → PROP) [IN : NonExpansive Φ]

local instance paco_mono : BIMonoPred (fun (Ψ : A → PROP) (a : A) => iprop(Φ a ∨ F Ψ a)) where
  mono_pred {Ψ Ψ' HΨ HΨ'} := by
    iintro #Hmon %x ⟨H|H⟩
    · ileft
      iexact H
    · iright
      iapply mono_pred (Φ := Ψ) $$ Hmon H
  mono_pred_ne.ne _ _ _ H := or_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)

@[rocq_alias greatest_fixpoint_paco]
theorem greatest_fixpoint_paco :
    ⊢ □ (∀ y, Φ y -∗ F (bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ F Ψ a))) y) -∗
      ∀ x, Φ x -∗ bi_greatest_fixpoint F x := by
  iintro #Hmon %x HΦ
  iapply greatest_fixpoint_unfold_mpr
  iapply mono_pred (Φ := (bi_greatest_fixpoint fun Ψ a => iprop(Φ a ∨ F Ψ a))) $$ [] [HΦ]
  · iintro !> %y Hy
    iapply greatest_fixpoint_coiter $$ [] Hy
    iintro !> %z Hz
    ihave Hcase : Φ z ∨ F (bi_greatest_fixpoint (fun Ψ a => iprop(Φ a ∨ F Ψ a))) z $$ [Hz]
    · iapply greatest_fixpoint_unfold_mp $$ Hz
    icases Hcase with ⟨H|H⟩
    · iapply Hmon $$ H
    · iapply H
  · iapply Hmon $$ HΦ

@[rocq_alias greatest_fixpoint_coind]
theorem greatest_fixpoint_coind [_HF : NonExpansive F] :
    ⊢ □ (∀ y, Φ y -∗ F (fun x => iprop(Φ x ∨ bi_greatest_fixpoint F x)) y) -∗
      ∀ x, Φ x -∗ bi_greatest_fixpoint F x := by
  iintro #Ha
  iapply greatest_fixpoint_paco
  iintro !> %y Hy
  letI _ : NonExpansive fun Ψ a => iprop(Φ a ∨ F Ψ a) :=
    ⟨fun _ _ _ H x => or_ne.ne (.of_eq rfl) (_HF.ne H x)⟩
  letI _ : NonExpansive fun x => iprop(Φ x ∨ bi_greatest_fixpoint F x) :=
    ⟨fun _ _ _ H => or_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)⟩
  iapply mono_pred (Φ := (fun x => iprop(Φ x ∨ bi_greatest_fixpoint F x))) $$ [] [Ha Hy]
  · iintro !> %x ⟨HΦ|Hf⟩
    · iapply greatest_fixpoint_unfold_mpr
      ileft
      iexact HΦ
    · iapply greatest_fixpoint_strong_mono (F := F) $$ [] Hf
      iintro !> %_ %_ HF
      iright
      iexact HF
  · iapply Ha $$ Hy

end Coind
end GreatestFixpoint
