/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.BI
import Iris.BI.BIBase
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.Algebra
import Iris.BI.Plainly
import Iris.Std.CoPset

namespace Iris
open Iris.Std BI

class BUpd (PROP : Type _) where
  bupd : PROP → PROP
export BUpd (bupd)

syntax "|==> " term:40 : term
syntax term:26 " ==∗ " term:25 : term

macro_rules
  | `(iprop(|==> $P))  => ``(BUpd.bupd iprop($P))
  | `(iprop($P ==∗ $Q))  => ``(BIBase.wand iprop($P) (BUpd.bupd iprop($Q)))

delab_rule BUpd.bupd
  | `($_ $P) => do ``(iprop(|==> $(← Iris.BI.unpackIprop P)))
-- delab_rule WandUpdate ??
--   | `($_ $P $Q) => ``(iprop($P ==∗ $Q))

class FUpd (PROP : Type _) where
  fupd : CoPset → CoPset → PROP → PROP
export FUpd (fupd)

syntax "|={ " term " , " term " }=> " term : term
syntax term "={ " term " , " term " }=∗ " term : term
syntax "|={ " term " }=> " term : term
syntax term "={ " term " }=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 , $E2 }=> $P))  => ``(FUpd.fupd $E1 $E2 iprop($P))
  | `(iprop($P ={ $E1 , $E2 }=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E2 iprop($Q)))
  | `(iprop(|={ $E1 }=> $P))  => ``(FUpd.fupd $E1 $E1 iprop($P))
  | `(iprop($P ={ $E1 }=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E1 iprop($Q)))

-- Delab rules

syntax "|={ " term " }[ " term " ]▷=> " term : term
syntax term "={ " term " }[ " term " ]▷=∗ " term : term
syntax "|={ " term " }▷=> " term : term
syntax term "={ " term " }▷=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷=> $P))  => ``(iprop(|={$E1, $E2}=> ▷ (|={ $E2, $E1 }=> iprop($P))))
  | `(iprop($P ={ $E1 }[ $E2 ]▷=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={ $E1 }▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={ $E1 }▷=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷=∗ iprop($Q)))

-- Delab rules

syntax "|={ " term " }[ " term " ]▷^" term "=> " term : term
syntax term "={ " term " }[ " term " ]▷^" term "=∗ " term : term
syntax "|={ " term " }▷^" term "=> " term : term
syntax term "={ " term " }▷^" term "=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷^$n=> $P))  => ``(iprop(|={$E1, $E2}=> ▷^[$n] (|={ $E2, $E1 }=> iprop($P))))
  | `(iprop($P ={ $E1 }[ $E2 ]▷^$n=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={ $E1 }▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={ $E1 }▷^$n=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷^$n=∗ iprop($Q)))

-- Delab rules

class BIUpdate (PROP : Type _) [BI PROP] extends BUpd PROP where
  [bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP))]
  intro {P : PROP} : iprop(P ⊢ |==> P)
  mono {P Q : PROP} : iprop(P ⊢ Q) → iprop(|==> P ⊢ |==> Q)
  trans {P : PROP} : iprop(|==> |==> P ⊢ |==> P)
  frame_r {P R : PROP} : iprop((|==> P) ∗ R ⊢ |==> (P ∗ R))

class BIFUpdate (PROP : Type _) [BI PROP] extends FUpd PROP where
  [ne {E1 E2 : CoPset} : OFE.NonExpansive (FUpd.fupd E1 E2 (PROP := PROP))]
  subset {E1 E2 : CoPset} : Subset E2 E1 → ⊢ |={E1, E2}=> |={E2, E1}=> (emp : PROP)
  except0 {E1 E2 : CoPset} (P : PROP) : (◇ |={E1, E2}=> P) ⊢ |={E1, E2}=> P
  trans {E1 E2 E3 : CoPset} (P : PROP) : (|={E1, E2}=> |={E2, E3}=> P) ⊢ |={E1, E3}=> P
  mask_frame_r' {E1 E2 Ef : CoPset} (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={CoPset.union E1 Ef, CoPset.union E2 Ef}=> P
  frame_r {E1 E2 : CoPset} (P R : PROP) :
    iprop((|={E1, E2}=> P) ∗ R ⊢ |={E1, E2}=> P ∗ R)

class BIUpdateFUpdate (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] where
  fupd_of_bupd {P : PROP} {E : CoPset} : iprop(⊢ |==> P) → iprop(⊢ |={E}=> P)

class BIBUpdatePlainly (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIPlainly PROP] where
  bupd_plainly {P : PROP} : iprop((|==> ■ P)) ⊢ P

class BIFUpdatePlainly (PROP : Type _) [BI PROP] [BIFUpdate PROP] [BIPlainly PROP] where
  fupd_plainly_keep_l (E E' : CoPset) (P R : PROP) : (R ={E,E'}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R
  fupd_plainly_later (E : CoPset) (P : PROP) : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P
  fupd_plainly_sForall_2 (E : CoPset) (Φ : PROP → Prop) :
    (∀ p, ⌜Φ p⌝ → |={E}=> ■ p) ⊢ |={E}=> sForall Φ

section BUpdLaws

variable [BI PROP] [BIUpdate PROP]

open BIUpdate

theorem bupd_frame_l {P Q : PROP} : iprop(P ∗ |==> Q ⊢ |==> (P ∗ Q)) :=
  sep_symm.trans <| frame_r.trans <| mono sep_symm

theorem bupd_frame_r {P Q : PROP} : iprop(|==> P ∗ Q ⊢ |==> (P ∗ Q)) :=
  frame_r

theorem bupd_wand_l {P Q : PROP} : iprop((P -∗ Q) ∗ (|==> P) ⊢ |==> Q) :=
  bupd_frame_l.trans <| mono <| wand_elim .rfl

theorem bupd_wand_r {P Q : PROP} : iprop((|==> P) ∗ (P -∗ Q) ⊢ |==> Q) :=
  sep_symm.trans bupd_wand_l

theorem bupd_sep {P Q : PROP} : iprop((|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q)) :=
  bupd_frame_l.trans <| (mono <| frame_r).trans BIUpdate.trans

theorem bupd_idem {P : PROP} : iprop((|==> |==> P) ⊣⊢ |==> P) :=
  ⟨BIUpdate.trans, BIUpdate.intro⟩

theorem bupd_or {P Q: PROP} : iprop((|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q)) :=
  or_elim (mono or_intro_l) (mono or_intro_r)

theorem bupd_and {P Q : PROP} : iprop((|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q)) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

theorem bupd_exist {Φ : A → PROP} : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x :=
  exists_elim (mono <| exists_intro ·)

theorem bupd_forall {Φ : A → PROP} :
    iprop(|==> «forall» fun x : A => Φ x) ⊢ «forall» fun x : A => iprop(|==> Φ x) :=
  forall_intro (mono <| forall_elim ·)

theorem bupd_except0 {P : PROP} : iprop(◇ (|==> P) ⊢ (|==> ◇ P)) :=
  or_elim (or_intro_l.trans intro) (mono or_intro_r)

instance {P : PROP} [Absorbing P] : Absorbing iprop(|==> P) :=
  ⟨bupd_frame_l.trans <| mono sep_elim_r⟩

section BUpdPlainlyLaws

variable [BIPlainly PROP] [BIBUpdatePlainly PROP]

theorem bupd_elim {P : PROP} [Plain P] : |==> P ⊢ P :=
  (mono Plain.plain).trans BIBUpdatePlainly.bupd_plainly

theorem bupd_plain_forall (Φ : A → PROP) [∀ x, Plain (Φ x)] :
    (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x) := by
  refine ⟨bupd_forall, ?_⟩
  refine .trans ?_ intro
  exact (forall_intro fun a => (forall_elim a).trans  bupd_elim)

instance {P : PROP} [Plain P] : Plain iprop(|==> P) :=
  ⟨(mono Plain.plain).trans <| (bupd_elim).trans <| BIPlainly.mono intro⟩

end BUpdPlainlyLaws
end BUpdLaws
