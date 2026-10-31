/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public import Iris.ProofMode

@[expose] public section

open Iris BI OFE Iris.Std

namespace MonoInstances

class MonotonePred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) : Prop where
  monotone {Φ Ψ : A → PROP} : ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

class AntitonePred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) : Prop where
  antitone {Φ Ψ : A → PROP} : ⊢ (□ ∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Ψ x -∗ F Φ x

section const

instance monotone_constant [BI PROP] [OFE A] : MonotonePred (fun _ : A → PROP => Ω) where
  monotone {Φ Ψ} := by iintro _ %_ $

instance monotone_constant' [BI PROP] [OFE A] (y : A) :
    MonotonePred (fun Φ : A → PROP => fun _ : A => Φ y) where
  monotone {Φ Ψ} := by
    iintro #H %_
    iapply H

instance antitone_constant [BI PROP] [OFE A] : AntitonePred (fun _ : A → PROP => Ω) where
  antitone {Φ Ψ} := by iintro _ %_ $

end const

section id

instance monotone_id [BI PROP] [OFE A] : MonotonePred (fun Φ : A → PROP => Φ) where
  monotone {Φ Ψ} := by
    iintro #H %x
    iapply H

instance monotone_id' [BI PROP] [OFE A] (F : A → A) : MonotonePred (fun Φ : A → PROP => fun x : A => Φ (F x)) where
  monotone {Φ Ψ} := by
    iintro #H %x
    iapply H

end id

section comp

instance monotone_comp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
    [hf : MonotonePred F] [hg : MonotonePred G] : MonotonePred (fun Φ => F (G Φ)) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    ihave #HG := hg.monotone $$ H
    iapply hf.monotone $$ HG HF

end comp

section and

instance monotone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∧ G Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HFG
    isplit
    · iapply hf.monotone $$ H HFG
    · iapply hg.monotone $$ H HFG

instance antitone_and [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∧ G Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HFG
    isplit
    · iapply hf.antitone $$ H HFG
    · iapply hg.antitone $$ H HFG

end and

section or

instance monotone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∨ G Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x (HF | HG)
    · ileft; iapply hf.monotone $$ H HF
    · iright; iapply hg.monotone $$ H HG

instance antitone_or [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∨ G Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x (HF | HG)
    · ileft; iapply hf.antitone $$ H HF
    · iright; iapply hg.antitone $$ H HG

end or

section sep

instance monotone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : MonotonePred G] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∗ G Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x ⟨HF, HG⟩
    isplitl [HF]
    · iapply hf.monotone $$ H HF
    · iapply hg.monotone $$ H HG

instance antitone_sep [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : AntitonePred G] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x ∗ G Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x ⟨HF, HG⟩
    isplitl [HF]
    · iapply hf.antitone $$ H HF
    · iapply hg.antitone $$ H HG

end sep

section wand

instance monotone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x -∗ G Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HFG HF
    ihave HF' := hf.antitone $$ H HF
    iapply hg.monotone $$ H (HFG $$ HF')

instance antitone_wand [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(F Φ x -∗ G Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HFG HF
    ihave HF' := hf.monotone $$ H HF
    iapply hg.antitone $$ H (HFG $$ HF')

end wand

section pers_imp

instance monotone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : AntitonePred F] [hg : MonotonePred G] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(<pers> F Φ x → G Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HFG #HF
    ihave #HF' := hf.antitone $$ H HF
    iapply hg.monotone $$ H (HFG $$ HF')

instance antitone_pers_imp [BI PROP] [OFE A] (F G : (A → PROP) → A → PROP)
      [hf : MonotonePred F] [hg : AntitonePred G] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(<pers> F Φ x → G Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HFG #HF
    ihave #HF' := hf.monotone $$ H HF
    iapply hg.antitone $$ H (HFG $$ HF')

end pers_imp

section «forall»

instance monotone_forall [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀ y, MonotonePred (F y)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => BI.forall (fun y : B => F y Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HF %y
    iapply (hf y).monotone $$ H HF

instance antitone_forall [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀ y, AntitonePred (F y)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => BI.forall (fun y : B => F y Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HF %y
    iapply (hf y).antitone $$ H HF

end «forall»

section «exists»

instance monotone_exists [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀ y, MonotonePred (F y)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => BI.exists (fun y : B => F y Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x ⟨%y, HF⟩
    iexists y
    iapply (hf y).monotone $$ H HF

instance antitone_exists [BI PROP] [OFE A] (F : B → (A → PROP) → A → PROP)
      [hf : ∀ y, AntitonePred (F y)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => BI.exists (fun y : B => F y Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x ⟨%y, HF⟩
    iexists y
    iapply (hf y).antitone $$ H HF

end «exists»

section persistently

instance monotone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(<pers> F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x #HF !>
    iapply hf.monotone $$ H HF

instance antitone_persistently [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(<pers> F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x #HF !>
    iapply hf.antitone $$ H HF

end persistently

section affinely

instance monotone_affinely [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(<affine> F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HF !>
    iapply hf.monotone $$ H HF

instance antitone_affinely [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(<affine> F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HF !>
    iapply hf.antitone $$ H HF

end affinely

section absorbingly

instance monotone_absorbingly [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(<absorb> F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.monotone $$ H HF

instance antitone_absorbingly [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(<absorb> F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.antitone $$ H HF

end absorbingly

section intuitionistically

instance monotone_intuitionistically [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(□ F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x #HF !>
    iapply hf.monotone $$ H HF

instance antitone_intuitionistically [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(□ F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x #HF !>
    iapply hf.antitone $$ H HF

end intuitionistically

section later

instance monotone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(▷ F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x HF !>
    iapply hf.monotone $$ H HF

instance antitone_later [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(▷ F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x HF !>
    iapply hf.antitone $$ H HF

end later

section except0

instance monotone_except0 [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : MonotonePred F] : MonotonePred (fun Φ : A → PROP => fun x : A => iprop(◇ F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.monotone $$ H HF

instance antitone_except0 [BI PROP] [OFE A] (F : (A → PROP) → A → PROP)
    [hf : AntitonePred F] : AntitonePred (fun Φ : A → PROP => fun x : A => iprop(◇ F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.antitone $$ H HF

end except0

section fupd

instance monotone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      (E1 E2 : A → CoPset) [hf : MonotonePred F] :
    MonotonePred (fun Φ : A → PROP => fun x : A => fupd (E1 x) (E2 x) (F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.monotone $$ H HF

instance antitone_fupd [BI PROP] [BIFUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      (E1 E2 : A → CoPset) [hf : AntitonePred F] :
    AntitonePred (fun Φ : A → PROP => fun x : A => fupd (E1 x) (E2 x) (F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.antitone $$ H HF

end fupd

section bupd

instance monotone_bupd [BI PROP] [BIUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      [hf : MonotonePred F] :
    MonotonePred (fun Φ : A → PROP => fun x : A => iprop(|==> F Φ x)) where
  monotone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.monotone $$ H HF

instance antitone_bupd [BI PROP] [BIUpdate PROP] [OFE A] (F : (A → PROP) → A → PROP)
      [hf : AntitonePred F] :
    AntitonePred (fun Φ : A → PROP => fun x : A => iprop(|==> F Φ x)) where
  antitone {Φ Ψ} := by
    iintro #H %x >HF !>
    iapply hf.antitone $$ H HF

end bupd

section bigSepL

instance monotone_bigSepL [BI PROP] [OFE A] (l : List B)
      (F : Nat → B → (A → PROP) → A → PROP) [hf : ∀ n y, MonotonePred (F n y)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => bigSepL (fun n y => F n y Φ x) l) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepL.bigSepL_impl $$ HF
    iintro !> %k %y _ HG
    iapply (hf k y).monotone $$ H HG

instance antitone_bigSepL [BI PROP] [OFE A] (l : List B)
      (F : Nat → B → (A → PROP) → A → PROP) [hf : ∀ n y, AntitonePred (F n y)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => bigSepL (fun n y => F n y Φ x) l) where
  antitone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepL.bigSepL_impl $$ HF
    iintro !> %k %y _ HG
    iapply (hf k y).antitone $$ H HG

end bigSepL

section bigSepL2

instance monotone_bigSepL2 [BI PROP] [OFE A] (l1 : List B) (l2 : List C)
      (F : Nat → B → C → (A → PROP) → A → PROP) [hf : ∀ n y z, MonotonePred (F n y z)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => bigSepL2 (fun n y z => F n y z Φ x) l1 l2) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepL2.bigSepL2_impl $$ HF
    iintro !> %k %y %z _ _ HG
    iapply (hf k y z).monotone $$ H HG

instance antitone_bigSepL2 [BI PROP] [OFE A] (l1 : List B) (l2 : List C)
      (F : Nat → B → C → (A → PROP) → A → PROP) [hf : ∀ n y z, AntitonePred (F n y z)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => bigSepL2 (fun n y z => F n y z Φ x) l1 l2) where
  antitone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepL2.bigSepL2_impl $$ HF
    iintro !> %k %y %z _ _ HG
    iapply (hf k y z).antitone $$ H HG

end bigSepL2

section bigSepM

instance monotone_bigSepM [BI PROP] [OFE A] [LawfulFiniteMap M K]
      (m : M V) (F : K → V → (A → PROP) → A → PROP) [hf : ∀ k v, MonotonePred (F k v)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => bigSepM (fun k v => F k v Φ x) m) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepM.bigSepM_impl $$ HF
    iintro !> %k %v _ HG
    iapply (hf k v).monotone $$ H HG

instance antitone_bigSepM [BI PROP] [OFE A] [LawfulFiniteMap M K]
      (m : M V) (F : K → V → (A → PROP) → A → PROP) [hf : ∀ k v, AntitonePred (F k v)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => bigSepM (fun k v => F k v Φ x) m) where
  antitone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepM.bigSepM_impl $$ HF
    iintro !> %k %v _ HG
    iapply (hf k v).antitone $$ H HG

end bigSepM

section bigSepS

instance monotone_bigSepS [BI PROP] [OFE A] [LawfulFiniteSet S B] (X : S)
      (F : B → (A → PROP) → A → PROP) [hf : ∀ y, MonotonePred (F y)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => bigSepS (fun y => F y Φ x) X) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepS.bigSepS_impl $$ HF
    iintro !> %y _ HG
    iapply (hf y).monotone $$ H HG

instance antitone_bigSepS [BI PROP] [OFE A] [LawfulFiniteSet S B] (X : S)
      (F : B → (A → PROP) → A → PROP) [hf : ∀ y, AntitonePred (F y)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => bigSepS (fun y => F y Φ x) X) where
  antitone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepS.bigSepS_impl $$ HF
    iintro !> %y _ HG
    iapply (hf y).antitone $$ H HG

end bigSepS

section bigSepMS

instance monotone_bigSepMS [BI PROP] [OFE A] [LawfulFiniteMultiSet MS B] (X : MS)
      (F : B → (A → PROP) → A → PROP) [hf : ∀ y, MonotonePred (F y)] :
    MonotonePred (fun Φ : A → PROP => fun x : A => bigSepMS (fun y => F y Φ x) X) where
  monotone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepMS.bigSepMS_impl $$ HF
    iintro !> %y _ HG
    iapply (hf y).monotone $$ H HG

instance antitone_bigSepMS [BI PROP] [OFE A] [LawfulFiniteMultiSet MS B] (X : MS)
      (F : B → (A → PROP) → A → PROP) [hf : ∀ y, AntitonePred (F y)] :
    AntitonePred (fun Φ : A → PROP => fun x : A => bigSepMS (fun y => F y Φ x) X) where
  antitone {Φ Ψ} := by
    iintro #H %x HF
    iapply BigSepMS.bigSepMS_impl $$ HF
    iintro !> %y _ HG
    iapply (hf y).antitone $$ H HG

end bigSepMS

end MonoInstances
