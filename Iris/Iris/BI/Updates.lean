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
syntax:25 term:26 " ==∗ " term:25 : term

macro_rules
  | `(iprop(|==> $P))  => ``(BUpd.bupd iprop($P))
  | `(iprop($P ==∗ $Q))  => ``(BIBase.wand iprop($P) (BUpd.bupd iprop($Q)))
  | `($P ==∗ $Q)  => ``(⊢ $P ==∗ $Q)

delab_rule BUpd.bupd
  | `($_ $P) => do ``(iprop(|==> $(← Iris.BI.unpackIprop P)))
-- delab_rule WandUpdate ??
--   | `($_ $P $Q) => ``(iprop($P ==∗ $Q))

class FUpd (PROP : Type _) where
  fupd : CoPset → CoPset → PROP → PROP
export FUpd (fupd)

syntax "|={" term "," term "}=> " term : term
syntax:25 term:26 "={" term "," term "}=∗ " term:25 : term
syntax "|={" term "}=> " term : term
syntax:25 term:26 "={" term "}=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E1,$E2}=> $P))  => ``(FUpd.fupd $E1 $E2 iprop($P))
  | `(iprop($P ={$E1,$E2}=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E2 iprop($Q)))
  | `(iprop(|={$E1}=> $P))  => ``(FUpd.fupd $E1 $E1 iprop($P))
  | `(iprop($P ={$E1}=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E1 iprop($Q)))
  | `($P ={$E1,$E2}=∗ $Q)  => ``(⊢ $P ={$E1,$E2}=∗ $Q)
  | `($P ={$E1}=∗ $Q)  => ``(⊢ $P ={$E1}=∗ $Q)

delab_rule FUpd.fupd
  | `($_ $E1 $E2 $P) => do
      let P ← Iris.BI.unpackIprop P
      if E1 == E2 then ``(iprop(|={$E1}=> $P))
      else ``(iprop(|={$E1,$E2}=> $P))

syntax "|={" term "}[" term "]▷=> " term : term
syntax:25 term:26 "={" term "}[" term "]▷=∗ " term:25 : term
syntax "|={" term "}▷=> " term : term
syntax:25 term:26 "={" term "}▷=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷=> $P))  => ``(iprop(|={$E1,$E2}=> ▷ (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={$E1}▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={$E1}▷=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷=∗ iprop($Q)))

-- Delab rules

syntax "|={" term "}[" term "]▷^" term "=> " term : term
syntax:25 term:26 "={" term "}[" term "]▷^" term "=∗ " term:25 : term
syntax "|={" term "}▷^" term "=> " term : term
syntax:25 term:26 "={" term "}▷^" term "=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷^$n=> $P))  => ``(iprop(|={$E1,$E2}=> ▷^[$n] (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷^$n=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={$E1}▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={$E1}▷^$n=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷^$n=∗ iprop($Q)))

-- Delab rules

syntax "|={ " term " }[ " term " ]▷=>^[ " term " ]" term : term
syntax:25 term:26 "={ " term " }[ " term " ]▷=∗^[ " term " ]" term:25 : term
syntax "|={ " term " }▷=>^[ " term " ]" term : term
syntax:25 term:26 "={ " term " }▷=∗^[ " term " ]" term:25 : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷=>^[ $n ] $P))  => ``(Nat.repeat (fun Q => iprop(|={ $E1 }[ $E2 ]▷=> Q)) $n iprop($P))
  | `(iprop($P ={ $E1 }[ $E2 ]▷=∗^[ $n ] $Q))  => ``(BIBase.wand iprop($P) (Nat.repeat (fun Q => iprop(|={ $E1 }[ $E2 ]▷=> Q) $n) iprop($Q)))
  | `(iprop(|={ $E1 }▷=>^[ $n ] $P))  => ``(Nat.repeat (fun Q => iprop(|={ $E1 }[ $E1 ]▷=> Q)) $n iprop($P))
  | `(iprop($P ={ $E1 }▷=∗^[ $n ] $Q))  => ``(BIBase.wand iprop($P) (Nat.repeat (fun Q => iprop(|={ $E1 }[ $E1 ]▷=> Q)) $n iprop($Q)))

-- Delab rules

class BIUpdate (PROP : Type _) [BI PROP] extends BUpd PROP where
  [bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP))]
  intro {P : PROP} : P ⊢ |==> P
  mono {P Q : PROP} : (P ⊢ Q) → |==> P ⊢ |==> Q
  trans {P : PROP} : |==> |==> P ⊢ |==> P
  frame_r {P R : PROP} : (|==> P) ∗ R ⊢ |==> (P ∗ R)

class BIFUpdate (PROP : Type _) [BI PROP] extends FUpd PROP where
  [ne {E1 E2 : CoPset} : OFE.NonExpansive (iprop(|={E1,E2}=> · : PROP))]
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
    (|={E}=> ■ sForall Φ) ⊢ |={E}=> sForall Φ

class BIBUpdateSbi (PROP : Type _) [BI PROP] [BIUpdate PROP] [Sbi PROP] where
  bupd_si_pure (Pi : SiProp) : iprop(|==> <si_pure> Pi ⊢@{PROP} <si_pure> Pi)

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
    E2 ⊆ E1 → ⊢@{PROP} |={E1,E2}=> |={∅,E1\E2}=> emp :=
  λ h => by
    simpa [union_comm, subset_union_diff h] using (fupd_mask_intro_subseteq empty_subset).trans <|
      fupd_mask_frame_r (P := iprop(|={∅,E1 \ E2}=> (emp : PROP))) (disjoint_symm <| disjoint_diff_right)

theorem fupd_trans_frame {E1 E2 E3 : CoPset} {P Q : PROP} :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ⊢ |={E1,E3}=> P :=
  fupd_frame_l.trans <| fupd_elim <| ((sep_assoc.2.trans <| sep_mono_l sep_comm.1).trans <|
    sep_mono_l wand_elim_r).trans <| fupd_frame_r.trans <| BIFUpdate.mono emp_sep.1

end FUpdLaws

section StepFUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

theorem step_fupdN_contractive {E1 E2 : CoPset} {n : Nat} [ι : BILaterContractive PROP] :
    OFE.Contractive (iprop(|={E1}[E2]▷=>^[n + 1] · : PROP)) where
  distLater_dist := by
    intro i x y xy_i
    induction n with
    | zero =>
      dsimp only [Nat.repeat]
      apply BIFUpdate.ne.ne
      apply ι.distLater_dist
      intros j ji
      apply BIFUpdate.ne.ne
      apply xy_i j ji
    | succ n IH =>
      dsimp only [Nat.repeat]
      apply BIFUpdate.ne.ne
      apply later_ne.ne
      apply BIFUpdate.ne.ne
      assumption

theorem step_fupdN_ne {E1 E2 : CoPset} {n : Nat} :
    OFE.NonExpansive (iprop(|={E1}[E2]▷=>^[n] · : PROP)) where
  ne := by
    intro i x y xy_i
    induction n with
    | zero => simp only [Nat.repeat, xy_i]
    | succ n IH =>
      dsimp only [Nat.repeat]
      apply BIFUpdate.ne.ne
      apply later_ne.ne
      apply BIFUpdate.ne.ne
      assumption

theorem step_fupdN_wand {Eo Ei : CoPset} {n : Nat} {P Q : PROP} :
    (|={Eo}[Ei]▷=>^[n] P) ⊢ (P -∗ Q) -∗ (|={Eo}[Ei]▷=>^[n] Q) := by
  refine wand_intro' ?_
  induction n with
  | zero =>
    dsimp [Nat.repeat]
    exact wand_elim_l
  | succ n IH =>
    dsimp [Nat.repeat]
    calc iprop((P -∗ Q) ∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> _)
      _ ⊢ |={Eo,Ei}=> (P -∗ Q) ∗ ▷ |={Ei,Eo}=> _  := (fupd_frame_l ..)
      _ ⊢ |={Eo,Ei}=> (▷ (P -∗ Q)) ∗ ▷ |={Ei,Eo}=> _  := mono (sep_mono (later_intro) .rfl)
      _ ⊢ |={Eo,Ei}=> ▷ ((P -∗ Q) ∗ |={Ei,Eo}=> _) := mono (later_sep.2)
      _ ⊢ |={Eo,Ei}=> ▷ |={Ei,Eo}=> ((P -∗ Q) ∗ _) := mono (later_mono (fupd_frame_l ..))
      _ ⊢ |={Eo,Ei}=> ▷ |={Ei,Eo}=> _ := mono (later_mono (mono IH))

theorem step_fupd_wand {Eo Ei : CoPset} {P Q : PROP} :
    (|={Eo}[Ei]▷=> P) ⊢ (P -∗ Q) -∗ (|={Eo}[Ei]▷=> Q) := by
  exact step_fupdN_wand (n := 1)

theorem step_fupd_mask_mono {Eo₁ Eo₂ Ei₁ Ei₂ : CoPset} {P : PROP} :
    Ei₂ ⊆ Ei₁ →
    Eo₁ ⊆ Eo₂ →
    (|={Eo₁}[Ei₁]▷=> P) ⊢ |={Eo₂}[Ei₂]▷=> P := by
  intro Ei₂_Ei₁ Eo₁_Eo₂

  refine emp_sep.2.trans ?_
  refine (sep_mono (fupd_mask_intro_subseteq Eo₁_Eo₂) .rfl).trans ?_
  refine fupd_frame_r.trans ?_
  refine BI.Entails.trans (mono ?_) (BIFUpdate.trans (E2 := Eo₁))

  refine fupd_frame_l.trans ?_
  refine BI.Entails.trans (mono ?_) (BIFUpdate.trans (E2 := Ei₁))

  refine (sep_mono (fupd_mask_intro_subseteq Ei₂_Ei₁) .rfl).trans ?_
  refine fupd_frame_r.trans ?_
  apply mono

  refine (sep_mono later_intro .rfl).trans ?_
  refine later_sep.2.trans ?_
  apply later_mono

  refine  fupd_frame_r.trans ?_
  refine BI.Entails.trans (mono ?_) (BIFUpdate.trans (E2 := Ei₁))

  refine fupd_frame_l.trans ?_
  refine BI.Entails.trans (mono ?_) (BIFUpdate.trans (E2 := Eo₁))

  refine fupd_frame_r.trans ?_
  refine mono emp_sep.1

theorem step_fupd_intro {Ei Eo : CoPset} {P : PROP} :
    Ei ⊆ Eo →
    ▷ P ⊢ |={Eo}[Ei]▷=> P := by
  intro Ei_Eo
  calc iprop(▷ P)
    _ ⊢ |={Ei}=> ▷ P := fupd_intro
    _ ⊢ |={Ei}[Ei]▷=> P := mono <| later_mono fupd_intro
    _ ⊢ |={Eo}[Ei]▷=> P := step_fupd_mask_mono (subset_refl) Ei_Eo

theorem step_fupdN_le {n m : Nat}{Eo Ei : CoPset}{P : PROP} :
    n ≤ m →
    Ei ⊆ Eo →
    (|={Eo}[Ei]▷=>^[n] P) ⊢ |={Eo}[Ei]▷=>^[m] P
  | .refl, _ => .rfl
  | .step (m := m) n_m, Ei_Eo => by
    refine step_fupdN_le n_m Ei_Eo |>.trans ?_
    refine later_intro.trans ?_
    apply step_fupd_intro Ei_Eo

@[rocq_alias step_fupd_fupd]
theorem step_fupd_fupd {Eo Ei : CoPset} {P : PROP} : (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P) :=
  ⟨mono <| later_mono <| mono fupd_intro, mono <| later_mono BIFUpdate.trans⟩

end StepFUpdLaws

section StepFUpdPlainlyLaws

variable [Sbi PROP] [BIFUpdate PROP] [BIFUpdatePlainly PROP]

open BIFUpdate BIFUpdatePlainly

@[rocq_alias fupd_plainly_mask]
theorem fupd_plainly_mask E E' {P : PROP} : (|={E,E'}=> ■ P) ⊢ |={E}=> P :=
  (wand_intro' emp_sep.1).trans <|
  (sep_emp.2.trans <| (fupd_plainly_keep_l E E' P emp).trans <| mono sep_emp.1)

@[rocq_alias fupd_plain_mask]
theorem fupd_plain_mask {E E' : CoPset} {P : PROP} [Plain P] : (|={E,E'}=> P) ⊢ |={E}=> P :=
  (mono Plain.plain).trans <|
  (wand_intro' emp_sep.1).trans <|
  (sep_emp.2.trans <| (fupd_plainly_keep_l E E' P emp).trans <| mono sep_comm.1).trans <|
  mono emp_sep.mp

@[rocq_alias fupd_plain_later]
theorem fupd_plain_later {E : CoPset} {P : PROP} [Plain P] : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P :=
  (later_mono (mono Plain.plain)).trans (fupd_plainly_later E P)

@[rocq_alias step_fupd_plain]
theorem step_fupd_plain {E1 E2 : CoPset} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=> P) ⊢ |={E1}=> ▷ ◇ P :=
  (fupd_elim <| (later_mono fupd_plain_mask).trans fupd_plain_later).trans fupd_plain_mask

@[rocq_alias step_fupdN_plain]
theorem step_fupdN_plain {E1 E2 : CoPset} {n : Nat} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=>^[n] P) ⊢ |={E1}=> ▷^[n] ◇ P := by
  induction n with
  | zero => exact except0_intro.trans fupd_intro
  | succ n ih =>
    simp only [Nat.repeat]
    refine (mono <| later_mono <| mono ih).trans ?_
    refine step_fupd_fupd.2.trans ?_
    refine step_fupd_plain.trans ?_
    refine (mono <| later_mono <| except0_laterN n).trans ?_
    exact mono <| laterN_mono (n+1) except0_idemp.1

end StepFUpdPlainlyLaws
