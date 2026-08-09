/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.ProofMode

@[expose] public section

open Iris BI OFE Iris.Std

class MonotonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop where
  monotone : ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

class AntitonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop where
  antitone : ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x

section const

instance monotone_const [BI PROP] [OFE A] : MonotonePred (λ_ : A → PROP => Ω) := by
  constructor
  intros
  iintro #H1 %x H2
  iexact H2

instance monotone_const' [BI PROP] [OFE A] (y : A) : MonotonePred (λΦ : A → PROP => λ_ : A => Φ y) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply H1
  iexact H2

instance antitone_const [BI PROP] [OFE A] : AntitonePred (λ_ : A → PROP => Ω) := by
  constructor
  intros
  iintro #H1 %x H2
  iexact H2

end const

section id

instance monotone_id [BI PROP] [OFE A] : MonotonePred (λΦ : A → PROP => Φ) := by
  constructor
  intros
  iintro #H %x HΦ
  iapply H
  iexact HΦ

instance monotone_id' [BI PROP] [OFE A] (F : A → A) : MonotonePred (λΦ : A → PROP => λx : A => Φ (F x)) := by
  constructor
  intros
  iintro #H %x HΦ
  iapply H
  iexact HΦ

end id

section comp

instance monotone_comp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
    [hf : MonotonePred F] [hg : MonotonePred G] : MonotonePred (λΦ => F (G Φ)) := by
  constructor
  intros Φ Ψ
  iintro #H %x HΦ
  iapply hf.monotone (G Φ)
  · imodintro
    iapply hg.monotone
    iexact H
  · iexact HΦ

end comp

section and

instance monotone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  isplit
  · iapply hf.monotone Φ Ψ
    iexact H1
    iexact H2
  · iapply hg.monotone Φ Ψ
    iexact H1
    iexact H2

instance antitone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∧ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  isplit
  · iapply hf.antitone Φ Ψ
    iexact H1
    iexact H2
  · iapply hg.antitone Φ Ψ
    iexact H1
    iexact H2

end and

section or

instance monotone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H %x (HF | HG)
  · ileft
    iapply hf.monotone Φ Ψ
    iexact H
    iexact HF
  · iright
    iapply hg.monotone Φ Ψ
    iexact H
    iexact HG

instance antitone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∨ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H %x (HF | HG)
  · ileft
    iapply hf.antitone Φ Ψ
    iexact H
    iexact HF
  · iright
    iapply hg.antitone Φ Ψ
    iexact H
    iexact HG

end or

section sep

instance monotone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H %x ⟨HF, HG⟩
  isplitl [HF]
  · iapply hf.monotone Φ Ψ
    iexact H
    iexact HF
  · iapply hg.monotone Φ Ψ
    iexact H
    iexact HG

instance antitone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x ∗ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H %x ⟨HF, HG⟩
  isplitl [HF]
  · iapply hf.antitone Φ Ψ
    iexact H
    iexact HF
  · iapply hg.antitone Φ Ψ
    iexact H
    iexact HG

end sep

section wand

instance monotone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2 HF
  iapply hg.monotone Φ Ψ
  · iexact H1
  · iapply H2
    iapply hf.antitone Φ Ψ
    · iexact H1
    · iexact HF

instance antitone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(F Φ x -∗ G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2 HF
  iapply hg.antitone Φ Ψ
  · iexact H1
  · iapply H2
    iapply hf.monotone Φ Ψ
    · iexact H1
    · iexact HF

end wand

section pers_imp

instance monotone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2 #HF
  iapply hg.monotone Φ Ψ
  · iexact H1
  · iapply (@intuitionistically_wand _ _ (F Φ x)).mpr $$ [H2]
    iexact H2
    imodintro
    iapply hf.antitone Φ Ψ
    · iexact H1
    · iexact HF

instance antitone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x → G Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2 #HF
  iapply hg.antitone Φ Ψ
  · iexact H1
  · iapply (@intuitionistically_wand _ _ (F Ψ x)).mpr $$ [H2]
    iexact H2
    imodintro
    iapply hf.monotone Φ Ψ
    · iexact H1
    · iexact HF

end pers_imp

section «forall»

instance monotone_forall [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀y, MonotonePred (F y)] :
    MonotonePred (λΦ : A → PROP => λx : A => BI.forall (λy : B => F y Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iintro %y
  iapply (hf y).monotone Φ
  · iexact H1
  · iexact H2

instance antitone_forall [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀y, AntitonePred (F y)] :
    AntitonePred (λΦ : A → PROP => λx : A => BI.forall (λy : B => F y Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iintro %y
  iapply (hf y).antitone Φ
  · iexact H1
  · iexact H2

end «forall»

section «exists»

instance monotone_exists [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀y, MonotonePred (F y)] :
    MonotonePred (λΦ : A → PROP => λx : A => BI.exists (λy : B => F y Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x ⟨%y, H2⟩
  iexists y
  iapply (hf y).monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_exists [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀y, AntitonePred (F y)] :
    AntitonePred (λΦ : A → PROP => λx : A => BI.exists (λy : B => F y Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x ⟨%y, H2⟩
  iexists y
  iapply (hf y).antitone Φ Ψ
  iexact H1
  iexact H2

end «exists»

section persistently

instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end persistently

section affinely

instance monotone_affinely [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(<affine> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_affinely [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(<affine> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imodintro
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end affinely

section absorbingly

instance monotone_absorbingly [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(<absorb> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x >H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_absorbingly [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(<absorb> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x >H2
  imodintro
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end absorbingly

section intuitionistically

instance monotone_intuitionistically [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(□ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_intuitionistically [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(□ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end intuitionistically

section later

instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  inext
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  inext
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end later

section except0

instance monotone_except0 [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(◇ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x >H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance antitone_except0 [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(◇ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x >H2
  imodintro
  iapply hf.antitone Φ Ψ
  iexact H1
  iexact H2

end except0

section fupd

instance monotone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      (E1 E2 : A → CoPset) [hf : MonotonePred F] :
    MonotonePred (λΦ : A → PROP => λx : A => fupd (E1 x) (E2 x) (F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imod H2
  imodintro
  iapply hf.monotone Φ $$ H1 H2

instance antitone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      (E1 E2 : A → CoPset) [hf : AntitonePred F] :
    AntitonePred (λΦ : A → PROP => λx : A => fupd (E1 x) (E2 x) (F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imod H2
  imodintro
  iapply hf.antitone Φ $$ H1 H2

end fupd

section bupd

instance monotone_bupd [BI PROP] [BIUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      [hf : MonotonePred F] :
    MonotonePred (λΦ : A → PROP => λx : A => iprop(|==> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imod H2
  imodintro
  iapply hf.monotone Φ $$ H1 H2

instance antitone_bupd [BI PROP] [BIUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      [hf : AntitonePred F] :
    AntitonePred (λΦ : A → PROP => λx : A => iprop(|==> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imod H2
  imodintro
  iapply hf.antitone Φ $$ H1 H2

end bupd

section bigSepL

instance monotone_bigSepL [BI PROP] [OFE A] (l : List B)
      (F : Nat → B → (A → PROP) → A → PROP) [hf : ∀n y, MonotonePred (F n y)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepL (λn y => F n y Φ x) l) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL.bigSepL_impl (Φ := λn y => F n y Φ x) $$ H2
  iintro !> %k %y #H2 H3
  iapply (hf k y).monotone Φ $$ H1 H3

instance antitone_bigSepL [BI PROP] [OFE A] (l : List B)
      (F : Nat → B → (A → PROP) → A → PROP) [hf : ∀n y, AntitonePred (F n y)] :
    AntitonePred (λΦ : A → PROP => λx : A => bigSepL (λn y => F n y Φ x) l) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL.bigSepL_impl (Φ := λn y => F n y Ψ x) $$ H2
  iintro !> %k %y #H2 H3
  iapply (hf k y).antitone Φ $$ H1 H3

end bigSepL

section bigSepL2

instance monotone_bigSepL2 [BI PROP] [OFE A] (l1 : List B) (l2 : List C)
      (F : Nat → B → C → (A → PROP) → A → PROP) [hf : ∀n y z, MonotonePred (F n y z)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepL2 (λn y z => F n y z Φ x) l1 l2) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL2.bigSepL2_impl (Φ := λn y z => F n y z Φ x) $$ H2
  iintro !> %k %y %z #_ #_ H3
  iapply (hf k y z).monotone Φ $$ H1 H3

instance antitone_bigSepL2 [BI PROP] [OFE A] (l1 : List B) (l2 : List C)
      (F : Nat → B → C → (A → PROP) → A → PROP) [hf : ∀n y z, AntitonePred (F n y z)] :
    AntitonePred (λΦ : A → PROP => λx : A => bigSepL2 (λn y z => F n y z Φ x) l1 l2) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL2.bigSepL2_impl (Φ := λn y z => F n y z Ψ x) $$ H2
  iintro !> %k %y %z #_ #_ H3
  iapply (hf k y z).antitone Φ $$ H1 H3

end bigSepL2

section bigSepM

instance monotone_bigSepM [BI PROP] [OFE A] [LawfulFiniteMap M K]
      (m : M V) (F : K → V → (A → PROP) → A → PROP) [hf : ∀k v, MonotonePred (F k v)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepM (λk v => F k v Φ x) m) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepM.bigSepM_impl (Φ := λk v => F k v Φ x) $$ H2
  iintro !> %k %v #_ H3
  iapply (hf k v).monotone Φ $$ H1 H3

instance antitone_bigSepM [BI PROP] [OFE A] [LawfulFiniteMap M K]
      (m : M V) (F : K → V → (A → PROP) → A → PROP) [hf : ∀k v, AntitonePred (F k v)] :
    AntitonePred (λΦ : A → PROP => λx : A => bigSepM (λk v => F k v Φ x) m) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepM.bigSepM_impl (Φ := λk v => F k v Ψ x) $$ H2
  iintro !> %k %v #_ H3
  iapply (hf k v).antitone Φ $$ H1 H3

end bigSepM

section bigSepS

instance monotone_bigSepS [BI PROP] [OFE A] [LawfulFiniteSet S B] (X : S)
      (F : B → (A → PROP) → A → PROP) [hf : ∀y, MonotonePred (F y)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepS (λy => F y Φ x) X) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepS.bigSepS_impl (Φ := λy => F y Φ x) $$ H2
  iintro !> %y #_ H3
  iapply (hf y).monotone Φ $$ H1 H3

instance antitone_bigSepS [BI PROP] [OFE A] [LawfulFiniteSet S B] (X : S)
      (F : B → (A → PROP) → A → PROP) [hf : ∀y, AntitonePred (F y)] :
    AntitonePred (λΦ : A → PROP => λx : A => bigSepS (λy => F y Φ x) X) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepS.bigSepS_impl (Φ := λy => F y Ψ x) $$ H2
  iintro !> %y #_ H3
  iapply (hf y).antitone Φ $$ H1 H3

end bigSepS

section bigSepMS

instance monotone_bigSepMS [BI PROP] [OFE A] [LawfulFiniteMultiSet MS B] (X : MS)
      (F : B → (A → PROP) → A → PROP) [hf : ∀y, MonotonePred (F y)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepMS (λy => F y Φ x) X) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepMS.bigSepMS_impl (Φ := λy => F y Φ x) $$ H2
  iintro !> %y #_ H3
  iapply (hf y).monotone Φ $$ H1 H3

instance antitone_bigSepMS [BI PROP] [OFE A] [LawfulFiniteMultiSet MS B] (X : MS)
      (F : B → (A → PROP) → A → PROP) [hf : ∀y, AntitonePred (F y)] :
    AntitonePred (λΦ : A → PROP => λx : A => bigSepMS (λy => F y Φ x) X) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepMS.bigSepMS_impl (Φ := λy => F y Ψ x) $$ H2
  iintro !> %y #_ H3
  iapply (hf y).antitone Φ $$ H1 H3

end bigSepMS
