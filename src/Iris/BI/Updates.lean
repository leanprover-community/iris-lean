/-
Copyright (c) 2025 Markus de Medeiros, Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Remy Seassau, Yunsong Yang
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.Algebra
public import Iris.BI.Plainly
public import Iris.Std.CoPset

@[expose] public section

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

syntax "|={" term "," term "}=> " term : term
syntax term "={" term "," term "}=∗ " term : term
syntax "|={" term "}=> " term : term
syntax term "={" term "}=∗ " term : term

macro_rules
  | `(iprop(|={$E1,$E2}=> $P))  => ``(FUpd.fupd $E1 $E2 iprop($P))
  | `(iprop($P ={$E1,$E2}=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E2 iprop($Q)))
  | `(iprop(|={$E1}=> $P))  => ``(FUpd.fupd $E1 $E1 iprop($P))
  | `(iprop($P ={$E1}=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E1 iprop($Q)))

delab_rule FUpd.fupd
  | `($_ $E1 $E2 $P) => do
      let P ← Iris.BI.unpackIprop P
      if E1 == E2 then ``(iprop(|={$E1}=> $P))
      else ``(iprop(|={$E1,$E2}=> $P))

syntax "|={" term "}[" term "]▷=> " term : term
syntax term "={" term "}[" term "]▷=∗ " term : term
syntax "|={" term "}▷=> " term : term
syntax term "={" term "}▷=∗ " term : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷=> $P))  => ``(iprop(|={$E1,$E2}=> ▷ (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={$E1}▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={$E1}▷=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷=∗ iprop($Q)))

-- Delab rules

syntax "|={" term "}[" term "]▷^" term "=> " term : term
syntax term "={" term "}[" term "]▷^" term "=∗ " term : term
syntax "|={" term "}▷^" term "=> " term : term
syntax term "={" term "}▷^" term "=∗ " term : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷^$n=> $P))  => ``(iprop(|={$E1,$E2}=> ▷^[$n] (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷^$n=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={$E1}▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={$E1}▷^$n=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷^$n=∗ iprop($Q)))

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
  intro {P : PROP} : P ⊢ |==> P
  mono {P Q : PROP} : (P ⊢ Q) → |==> P ⊢ |==> Q
  trans {P : PROP} : |==> |==> P ⊢ |==> P
  frame_r {P R : PROP} : (|==> P) ∗ R ⊢ |==> (P ∗ R)

class BIFUpdate (PROP : Type _) [BI PROP] extends FUpd PROP where
  [ne {E1 E2 : CoPset} : OFE.NonExpansive (FUpd.fupd E1 E2 (PROP := PROP))]
  subset {E1 E2 : CoPset} : E2 ⊆ E1 → ⊢ |={E1,E2}=> |={E2,E1}=> (emp : PROP)
  except0 {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> P
  mono {E1 E2 : CoPset} {P Q : PROP} : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q
  trans {E1 E2 E3 : CoPset} {P : PROP} : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P
  mask_frame_r' {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P
  frame_r {E1 E2 : CoPset} {P R : PROP} : (|={E1,E2}=> P) ∗ R ⊢ |={E1,E2}=> P ∗ R

class BIUpdateFUpdate (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] where
  fupd_of_bupd {P : PROP} {E : CoPset} : (|==> P) ⊢ |={E}=> P

class BIBUpdatePlainly (PROP : Type _) [BI PROP] [BIUpdate PROP] [Sbi PROP] where
  bupd_plainly {P : PROP} : (|==> ■ P) ⊢ P

class BIFUpdatePlainly (PROP : Type _) [BI PROP] [BIFUpdate PROP] [Sbi PROP] where
  fupd_plainly_keep_l (E E' : CoPset) (P R : PROP) : (R ={E,E'}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R
  fupd_plainly_later (E : CoPset) (P : PROP) : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P
  fupd_plainly_sForall_2 (E : CoPset) (Φ : PROP → Prop) :
    (∀ p, ⌜Φ p⌝ → |={E}=> ■ p) ⊢ |={E}=> sForall Φ

section BUpdLaws

variable [BI PROP] [BIUpdate PROP]

open BIUpdate

theorem bupd_frame_l {P Q : PROP} : P ∗ |==> Q ⊢ |==> (P ∗ Q) :=
  sep_symm.trans <| frame_r.trans <| mono sep_symm

theorem bupd_frame_r {P Q : PROP} : |==> P ∗ Q ⊢ |==> (P ∗ Q) :=
  frame_r

theorem bupd_wand_l {P Q : PROP} : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q :=
  bupd_frame_l.trans <| mono <| wand_elim .rfl

theorem bupd_wand_r {P Q : PROP} : (|==> P) ∗ (P -∗ Q) ⊢ |==> Q :=
  sep_symm.trans bupd_wand_l

theorem bupd_sep {P Q : PROP} : (|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q) :=
  bupd_frame_l.trans <| (mono <| frame_r).trans BIUpdate.trans

theorem bupd_idem {P : PROP} : (|==> |==> P) ⊣⊢ |==> P :=
  ⟨BIUpdate.trans, BIUpdate.intro⟩

theorem bupd_or {P Q: PROP} : (|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q) :=
  or_elim (mono or_intro_l) (mono or_intro_r)

theorem bupd_and {P Q : PROP} : (|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

theorem bupd_exist {Φ : A → PROP} : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x :=
  exists_elim (mono <| exists_intro ·)

theorem bupd_forall {Φ : A → PROP} :
    (|==> «forall» fun x : A => Φ x) ⊢ «forall» fun x : A => iprop(|==> Φ x) :=
  forall_intro (mono <| forall_elim ·)

theorem bupd_except0 {P : PROP} : ◇ (|==> P) ⊢ (|==> ◇ P) :=
  or_elim (or_intro_l.trans intro) (mono or_intro_r)

instance {P : PROP} [Absorbing P] : Absorbing iprop(|==> P) :=
  ⟨bupd_frame_l.trans <| mono sep_elim_r⟩

end BUpdLaws

section BUpdPlainlyLaws

variable [Sbi PROP] [BIUpdate PROP] [BIBUpdatePlainly PROP]

open BIUpdate

theorem bupd_elim {P : PROP} [Plain P] : |==> P ⊢ P :=
  (mono Plain.plain).trans BIBUpdatePlainly.bupd_plainly

theorem bupd_plain_forall (Φ : A → PROP) [∀ x, Plain (Φ x)] :
    (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x) := by
  refine ⟨bupd_forall, ?_⟩
  refine .trans ?_ intro
  exact (forall_intro fun a => (forall_elim a).trans  bupd_elim)

instance {P : PROP} [Plain P] : Plain iprop(|==> P) :=
  ⟨(mono Plain.plain).trans <| (bupd_elim).trans <| plainly_mono intro⟩

end BUpdPlainlyLaws

section FUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

theorem fupd_mask_intro_subseteq {E1 E2 : CoPset} {P : PROP} : E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P :=
  λ h => (emp_sep.2.trans <| sep_mono_l <| subset h).trans <|
    frame_r.trans <| mono <| frame_r.trans <| mono emp_sep.1

theorem fupd_intro {E : CoPset} {P : PROP} : P ⊢ |={E}=> P :=
  (fupd_mask_intro_subseteq λ _ => id).trans trans

-- Introduction lemma for a mask-chaging fupd
theorem fupd_mask_intro {E1 E2 : CoPset} {P : PROP} :
    E2 ⊆ E1 → ((|={E2,E1}=> emp) -∗ P) ⊢ |={E1,E2}=> P :=
  λ h => (wand_mono_r fupd_intro).trans <|
    (emp_sep.2.trans <| sep_mono_l <| subset h).trans <|
    frame_r.trans <| (mono wand_elim_r).trans trans

theorem fupd_mask_intro_discard {E1 E2 : CoPset} {P : PROP} [Absorbing P] : E2 ⊆ E1 → P ⊢ |={E1,E2}=> P :=
  λ h => (wand_intro' sep_elim_r).trans <| fupd_mask_intro h

theorem fupd_elim {E1 E2 E3 : CoPset} {P Q : PROP} : (Q ⊢ |={E2,E3}=> P) → (|={E1,E2}=> Q) ⊢ |={E1,E3}=> P :=
  λ h => (mono h).trans trans

theorem fupd_frame_l {E1 E2 : CoPset} {P Q : PROP} : P ∗ (|={E1,E2}=> Q) ⊢ |={E1,E2}=> P ∗ Q :=
  sep_symm.trans <| frame_r.trans <| mono sep_symm

theorem fupd_frame_r {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ Q ⊢ |={E1,E2}=> P ∗ Q :=
  frame_r

theorem fupd_wand_l {E1 E2 : CoPset} {P Q : PROP} : (P -∗ Q) ∗ (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q :=
  fupd_frame_l.trans <| mono <| wand_elim .rfl

theorem fupd_wand_r {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |={E1,E2}=> Q :=
  sep_symm.trans fupd_wand_l

theorem fupd_sep {E : CoPset} {P Q : PROP} : (|={E}=> P) ∗ (|={E}=> Q) ⊢ |={E}=> P ∗ Q :=
  fupd_frame_l.trans <| (mono frame_r).trans trans

theorem fupd_idem {E : CoPset} {P : PROP} : (|={E}=> |={E}=> P) ⊣⊢ |={E}=> P := ⟨trans, fupd_intro⟩

theorem fupd_or {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∨ (|={E1,E2}=> Q) ⊢ |={E1,E2}=> P ∨ Q :=
  or_elim (mono or_intro_l) (mono or_intro_r)

theorem fupd_and {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P ∧ Q) ⊢ (|={E1,E2}=> P) ∧ (|={E1,E2}=> Q) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

theorem fupd_exist {E1 E2 : CoPset} {Φ : A → PROP} : (∃ a : A, |={E1,E2}=> Φ a) ⊢ |={E1,E2}=> ∃ a : A, Φ a :=
  exists_elim (mono <| exists_intro ·)

theorem fupd_forall {E1 E2 : CoPset} {Φ : A → PROP} :
    (|={E1,E2}=> «forall» λ a : A => Φ a) ⊢ «forall» λ a : A => iprop(|={E1,E2}=> Φ a) :=
  forall_intro (mono <| forall_elim ·)

theorem fupd_except0 {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> ◇ P :=
  except0.trans (mono except0_intro)

instance {E1 E2 : CoPset} {P : PROP} [Absorbing P] : Absorbing iprop(|={E1,E2}=> P) :=
  ⟨fupd_frame_l.trans <| mono sep_elim_r⟩

theorem fupd_mask_frame_r {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P :=
  λ h => (mono <| imp_intro' and_elim_r).trans <| mask_frame_r' h

theorem fupd_mask_mono {E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E2 → (|={E1}=> P) ⊢ |={E2}=> P :=
  λ h => by simpa [subset_union_diff h] using
    (fupd_mask_frame_r (E2 := E1) (Ef := E2 \ E1) disjoint_diff_right)

theorem fupd_mask_frame {E E' E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E → (|={E1,E2}=> |={E2 ∪ (E \ E1),E'}=> P) ⊢ |={E,E'}=> P :=
  λ h => by simpa [subset_union_diff h] using
    ((fupd_mask_frame_r (P := iprop(|={E2 ∪ (E \ E1),E'}=> P)) disjoint_diff_right).trans trans)

/-- A variant of [fupd_mask_frame] that works well for accessors:
  Tailored to eliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to transform the
  closing view shift instead of letting you prove the same side-conditions twice. -/
theorem fupd_mask_frame_acc {E E' E1 E2 : CoPset} {P Q : PROP}:
    E1 ⊆ E → (|={E1,E1 \ E2}=> Q) ⊢
    (Q -∗ |={E \ E2,E'}=> (∀ R, (|={E1 \ E2,E1}=> R) -∗ |={E \ E2,E}=> R) -∗  P) -∗
    (|={E,E'}=> P) := λ hE => by
  have hmask : E \ E2 ⊆ (E1 \ E2) ∪ (E \ E1) := by
    intro x hx; rw [mem_diff] at hx
    by_cases hx1 : x ∈ E1
    · exact mem_union.2 <| .inl <| mem_diff.2 ⟨hx1, hx.2⟩
    · exact mem_union.2 <| .inr <| mem_diff.2 ⟨hx.1, hx1⟩
  have hdisj : (E1 \ E2) ## (E \ E1) := disjoint_subset_left diff_subset_left disjoint_diff_right
  refine wand_intro <| fupd_frame_r.trans <| (BIFUpdate.mono wand_elim_r).trans ?_
  refine (BIFUpdate.mono ?_).trans <| fupd_mask_frame hE
  refine sep_emp.2.trans <| (sep_mono_r <| fupd_mask_intro_subseteq hmask).trans ?_
  refine fupd_frame_l.trans <| (BIFUpdate.mono fupd_frame_r).trans <| fupd_elim ?_
  refine BIFUpdate.mono <| sep_symm.trans ?_
  refine (sep_mono ?_ .rfl).trans wand_elim_r
  refine forall_intro λ R => wand_intro <| fupd_frame_r.trans <| fupd_elim ?_
  exact emp_sep.1.trans <| (fupd_mask_frame_r hdisj).trans <| by simp [subset_union_diff hE]

theorem fupd_mask_subseteq_emptyset_difference {E1 E2 : CoPset} :
    E2 ⊆ E1 → ⊢ |={E1,E2}=> |={∅,E1\E2}=> (emp: PROP) :=
  λ h => by
    simpa [union_comm, subset_union_diff h] using (fupd_mask_intro_subseteq empty_subset).trans <|
      fupd_mask_frame_r (P := iprop(|={∅,E1 \ E2}=> (emp : PROP))) (disjoint_symm <| disjoint_diff_right)

theorem fupd_trans_frame {E1 E2 E3 : CoPset} {P Q : PROP} :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ⊢ |={E1,E3}=> P :=
  fupd_frame_l.trans <| fupd_elim <| ((sep_assoc.2.trans <| sep_mono_l sep_comm.1).trans <|
    sep_mono_l wand_elim_r).trans <| fupd_frame_r.trans <| BIFUpdate.mono emp_sep.1

end FUpdLaws
