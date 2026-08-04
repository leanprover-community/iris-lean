/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes

@[expose] public section

open Iris BI OFE

abbrev MonotonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop :=
  ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

abbrev AntitonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop :=
  ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x

section monotone

theorem monotone_const [BI PROP] [OFE A] : MonotonePred (λ_ : A → PROP => Ω) := by
  unfold MonotonePred
  intros
  iintro #H1 %x H2
  iexact H2

theorem monotone_const' [BI PROP] [OFE A] (y : A) : MonotonePred (λΦ : A → PROP => λ_ : A => Φ y) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  simp
  iapply H1
  iexact H2

theorem monotone_id [BI PROP] [OFE A] : MonotonePred (λΦ : A → PROP => Φ) := by
  unfold MonotonePred
  intros
  iintro #H %x HΦ
  iapply H
  iexact HΦ

theorem monotone_id' [BI PROP] [OFE A] (F : A → A) : MonotonePred (λΦ : A → PROP => λx : A => Φ (F x)) := by
  unfold MonotonePred
  intros
  iintro #H %x HΦ
  iapply H
  iexact HΦ

theorem monotone_comp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
    (hf : MonotonePred F) (hg : MonotonePred G) : MonotonePred (λΦ => F (G Φ)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H %x HΦ
  iapply hf (G Φ)
  · imodintro
    iapply hg
    iexact H
  · iexact HΦ

theorem monotone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : MonotonePred F) (hg : MonotonePred G) :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  isplit
  · iapply hf Φ Ψ
    iexact H1
    iexact H2
  · iapply hg Φ Ψ
    iexact H1
    iexact H2

theorem monotone_forall [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      (hf : ∀y, MonotonePred (F y)) :
    MonotonePred (λΦ : A → PROP => λx : A => BI.forall (λy : B => F y Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  iintro %y
  iapply hf y Φ
  · iexact H1
  · iexact H2

theorem monotone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP) (E1 E2 : A → CoPset)
      (hf : MonotonePred F) :
    MonotonePred (λΦ : A → PROP => λx : A => fupd (E1 x) (E2 x) (F Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BIFUpdate.mono (P := F Φ x)
  · iintro H
    iapply hf Φ Ψ
    · sorry -- ⊢ □ ∀ x, Φ x -∗ Ψ x
    · iexact H
  · iexact H2

theorem monotone_bigSepL_mono [BI PROP] [OFE A] (l : List B) (F : Nat → B → (A → PROP) → A → PROP)
      (hf : ∀n y, MonotonePred (F n y)) :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepL (λn y => F n y Φ x) l) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL.bigSepL_mono (Φ := λn y => F n y Φ x)
  intro k y h
  · iintro H
    iapply hf (Φ := Φ)
    · sorry -- ⊢ □ ∀ x, Φ x -∗ Ψ x
    · iexact H
  · iexact H2

theorem monotone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : MonotonePred F) (hg : MonotonePred G) :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H %x (HF | HG)
  · ileft
    iapply hf Φ Ψ
    iexact H
    iexact HF
  · iright
    iapply hg Φ Ψ
    iexact H
    iexact HG

theorem monotone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : AntitonePred F) (hg : MonotonePred G) :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2 #HF
  iapply hg Φ Ψ
  · iexact H1
  · iapply (@intuitionistically_wand _ _ (F Φ x)).mpr $$ [H2]
    iexact H2
    imodintro
    iapply hf Φ Ψ
    · iexact H1
    · iexact HF

theorem monotone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : MonotonePred F) (hg : MonotonePred G) :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H %x ⟨HF, HG⟩
  isplitl [HF]
  · iapply hf Φ Ψ
    iexact H
    iexact HF
  · iapply hg Φ Ψ
    iexact H
    iexact HG

theorem monotone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : AntitonePred F) (hg : MonotonePred G) :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2 HF
  iapply hg Φ Ψ
  · iexact H1
  · iapply H2
    iapply hf Φ Ψ
    · iexact H1
    · iexact HF

theorem monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    (hf : MonotonePred F) : MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf Φ Ψ
  iexact H1
  iexact H2

theorem monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    (hf : MonotonePred F) : MonotonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) := by
  unfold MonotonePred
  intros Φ Ψ
  iintro #H1 %x H2
  inext
  iapply hf Φ Ψ
  iexact H1
  iexact H2

end monotone

section antitone

theorem antitone_const [BI PROP] [OFE A] : AntitonePred (λ_ : A → PROP => Ω) := by
  unfold AntitonePred
  intros
  iintro #H1 %x H2
  iexact H2

theorem antitone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : AntitonePred F) (hg : AntitonePred G) :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H1 %x H2
  isplit
  · iapply hf Φ Ψ
    iexact H1
    iexact H2
  · iapply hg Φ Ψ
    iexact H1
    iexact H2

theorem antitone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : AntitonePred F) (hg : AntitonePred G) :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H %x (HF | HG)
  · ileft
    iapply hf Φ Ψ
    iexact H
    iexact HF
  · iright
    iapply hg Φ Ψ
    iexact H
    iexact HG

theorem antitone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : MonotonePred F) (hg : AntitonePred G) :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H1 %x H2 #HF
  iapply hg Φ Ψ
  · iexact H1
  · iapply (@intuitionistically_wand _ _ (F Ψ x)).mpr $$ [H2]
    iexact H2
    imodintro
    iapply hf Φ Ψ
    · iexact H1
    · iexact HF

theorem antitone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : AntitonePred F) (hg : AntitonePred G) :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H %x ⟨HF, HG⟩
  isplitl [HF]
  · iapply hf Φ Ψ
    iexact H
    iexact HF
  · iapply hg Φ Ψ
    iexact H
    iexact HG

theorem antitone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      (hf : MonotonePred F) (hg : AntitonePred G) :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H1 %x H2 HF
  iapply hg Φ Ψ
  · iexact H1
  · iapply H2
    iapply hf Φ Ψ
    · iexact H1
    · iexact HF

theorem antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    (hf : AntitonePred F) : AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf Φ Ψ
  iexact H1
  iexact H2

theorem antitone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    (hf : AntitonePred F) : AntitonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) := by
  unfold AntitonePred
  intros Φ Ψ
  iintro #H1 %x H2
  inext
  iapply hf Φ Ψ
  iexact H1
  iexact H2

end antitone
