/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.ProofMode

@[expose] public section

open Iris BI OFE

class MonotonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop where
  monotone : ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

class AntitonePred [BI PROP] [OFE A]
    (F : (A → PROP) → (A → PROP)) : Prop where
  antitone : ∀ (Φ Ψ : A → PROP),
    ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x

section monotone

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

instance monotone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP) (E1 E2 : A → CoPset)
      [hf : MonotonePred F] :
    MonotonePred (λΦ : A → PROP => λx : A => fupd (E1 x) (E2 x) (F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  imod H2
  imodintro
  iapply hf.monotone Φ $$ H1 H2

instance monotone_bigSepL [BI PROP] [OFE A] (l : List B) (F : Nat → B → (A → PROP) → A → PROP)
      [hf : ∀n y, MonotonePred (F n y)] :
    MonotonePred (λΦ : A → PROP => λx : A => bigSepL (λn y => F n y Φ x) l) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  iapply BigSepL.bigSepL_impl (Φ := λn y => F n y Φ x) $$ H2
  iintro !> %k %y #H2 H3
  iapply (hf k y).monotone Φ $$ H1 H3

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

instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (λΦ : A → PROP => λx : A => iprop(▷ F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x H2
  inext
  iapply hf.monotone Φ Ψ
  iexact H1
  iexact H2

end monotone

section antitone

instance antitone_const [BI PROP] [OFE A] : AntitonePred (λ_ : A → PROP => Ω) := by
  constructor
  intros
  iintro #H1 %x H2
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

instance antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (λΦ : A → PROP => λx : A => iprop(<pers> F Φ x)) := by
  constructor
  intros Φ Ψ
  iintro #H1 %x #H2
  imodintro
  iapply hf.antitone Φ Ψ
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

end antitone
