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

@[rocq_alias BUpd]
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

delab_rule BIBase.wand
  | `($_ $P iprop(|==> $Q)) => do `(iprop($(←Iris.BI.unpackIprop P) ==∗ $Q))

@[rocq_alias FUpd]
class FUpd (PROP : Type _) where
  fupd : CoPset → CoPset → PROP → PROP
export FUpd (fupd)

syntax "|={" term ", " term "}=> " term : term
syntax:25 term:26 " ={" term ", " term "}=∗ " term:25 : term
syntax "|={" term "}=> " term : term
syntax:25 term:26 " ={" term "}=∗ " term:25 : term

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

delab_rule BIBase.wand
  | `($_ $P iprop(|={$E₁,$E₂}=> $Q)) => do `(iprop($(←Iris.BI.unpackIprop P) ={$E₁,$E₂}=∗ $Q))
  | `($_ $P iprop(|={$E₁}=> $Q)) => do `(iprop($(←Iris.BI.unpackIprop P) ={$E₁}=∗ $Q))

syntax "|={" term "}[" term "]▷=> " term : term
syntax:25 term:26 " ={" term "}[" term "]▷=∗ " term:25 : term
syntax "|={" term "}▷=> " term : term
syntax:25 term:26 " ={" term "}▷=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷=> $P))  => ``(iprop(|={$E1,$E2}=> ▷ (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={$E1}▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={$E1}▷=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷=∗ iprop($Q)))

delab_rule FUpd.fupd
  | `($_ $E₁ $E₂ iprop(▷ |={$E₂',$E₁'}=> $P)) => do
    unless E₁ == E₁' ∧ E₂ == E₂' do throw ()
    `(iprop(|={$E₁}[$E₂]▷=> $(←Iris.BI.unpackIprop P)))
  | `($_ $E₁ $E₁' iprop(▷ |={$E₁''}=> $P)) => do
    unless E₁ == E₁' ∧ E₁' == E₁'' do throw ()
    `(iprop(|={$E₁}▷=> $(←Iris.BI.unpackIprop P)))

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷=> $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}[$E₂]▷=∗ $P))
  | `($_ $Q iprop(|={$E₁}▷=> $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}▷=∗ $P))

syntax "|={" term "}[" term "]▷^" term "=> " term : term
syntax:25 term:26 " ={" term "}[" term "]▷^" term "=∗ " term:25 : term
syntax "|={" term "}▷^" term "=> " term : term
syntax:25 term:26 " ={" term "}▷^" term "=∗ " term:25 : term

macro_rules
  | `(iprop(|={$E1}[$E2]▷^$n=> $P))  => ``(iprop(|={$E1,$E2}=> ▷^[$n] (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={$E1}[$E2]▷^$n=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={$E1}▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={$E1}▷^$n=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷^$n=∗ iprop($Q)))

delab_rule FUpd.fupd
  | `($_ $E₁ $E₂ iprop(▷^[$n] |={$E₂',$E₁'}=> $P)) => do
    unless E₁ == E₁' ∧ E₂ == E₂' do throw ()
    `(iprop(|={$E₁}[$E₂]▷^$n=> $(←Iris.BI.unpackIprop P)))
  | `($_ $E₁ $E₁' iprop(▷^[$n] |={$E₁''}=> $P)) => do
    unless E₁ == E₁' ∧ E₁' == E₁'' do throw ()
    `(iprop(|={$E₁}▷^$n=> $(←Iris.BI.unpackIprop P)))

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷^$n=> $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}[$E₂]▷^$n=∗ $P))
  | `($_ $Q iprop(|={$E₁}▷^$n=> $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}▷^$n=∗ $P))

syntax "|={" term "}[" term "]▷=>^[" term "] " term : term
syntax:25 term:26 " ={" term "}[" term "]▷=∗^[" term "] " term:25 : term
syntax "|={" term "}▷=>^[" term "] " term : term
syntax:25 term:26 " ={" term "}▷=∗^[" term "] " term:25 : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷=>^[ $n ] $P))  => ``(Nat.repeat (fun Q => iprop(|={ $E1 }[ $E2 ]▷=> Q)) $n iprop($P))
  | `(iprop($P ={ $E1 }[ $E2 ]▷=∗^[ $n ] $Q))  => ``(BIBase.wand iprop($P) (Nat.repeat (fun Q => iprop(|={ $E1 }[ $E2 ]▷=> Q)) $n iprop($Q)))
  | `(iprop(|={ $E1 }▷=>^[ $n ] $P))  => ``(Nat.repeat (fun Q => iprop(|={ $E1 }[ $E1 ]▷=> Q)) $n iprop($P))
  | `(iprop($P ={ $E1 }▷=∗^[ $n ] $Q))  => ``(BIBase.wand iprop($P) (Nat.repeat (fun Q => iprop(|={ $E1 }[ $E1 ]▷=> Q)) $n iprop($Q)))

open Lean.PrettyPrinter.Delaborator SubExpr in
@[app_delab Nat.repeat]
meta def delabStepFUpdN : Delab :=  do
  let_expr Nat.repeat _ lam _ _ := ←getExpr | unreachable!
  let n ← withNaryArg 2 delab
  let P ← withNaryArg 3 delab
  guard <| lam.isLambda
  let lamBody ← withNaryArg 1 do
    withBindingBody' `_ Pure.pure fun arg => do
    guard <| (←getExpr).getAppFn.constName! == ``FUpd.fupd
    withNaryArg 4 do
      guard <| (←getExpr).getAppFn.constName! == ``BIBase.later
      withNaryArg 2 do
      guard <| (←getExpr).getAppFn.constName! == ``FUpd.fupd
      withNaryArg 4 do
      let body ← getExpr
      guard (←Lean.Meta.isDefEq arg body)
    delab
  match lamBody with
  | `(iprop(|={$E₁}▷=> $_)) => `(iprop(|={$E₁}▷=>^[$n] $P))
  | `(iprop(|={$E₁}[$E₂]▷=> $_)) => `(iprop(|={$E₁}[$E₂]▷=>^[$n] $P))
  | _ => failure

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷=>^[$n] $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}[$E₂]▷=∗^[$n] $P))
  | `($_ $Q iprop(|={$E₁}▷=>^[$n] $P)) => do
    `(iprop($(←Iris.BI.unpackIprop Q) ={$E₁}▷=∗^[$n] $P))

@[rocq_alias BiBUpd]
class BIUpdate (PROP : Type _) [BI PROP] extends BUpd PROP where
  [bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP))]
  intro {P : PROP} : P ⊢ |==> P
  mono {P Q : PROP} : (P ⊢ Q) → |==> P ⊢ |==> Q
  trans {P : PROP} : |==> |==> P ⊢ |==> P
  frame_right {P R : PROP} : (|==> P) ∗ R ⊢ |==> (P ∗ R)

#rocq_ignore BiBUpdMixin "Included in BIUpdate typeclass."

@[rocq_alias BiFUpd]
class BIFUpdate (PROP : Type _) [BI PROP] extends FUpd PROP where
  [ne {E1 E2 : CoPset} : OFE.NonExpansive (iprop(|={E1,E2}=> · : PROP))]
  subset {E1 E2 : CoPset} : E2 ⊆ E1 → ⊢ |={E1,E2}=> |={E2,E1}=> (emp : PROP)
  except0 {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> P
  mono {E1 E2 : CoPset} {P Q : PROP} : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q
  trans {E1 E2 E3 : CoPset} {P : PROP} : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P
  mask_frame_right_strong {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P
  frame_right {E1 E2 : CoPset} {P R : PROP} : (|={E1,E2}=> P) ∗ R ⊢ |={E1,E2}=> P ∗ R

#rocq_ignore BiFUpdMixin "Included in BIFUpdate typeclass."

@[rocq_alias BiBUpdFUpd]
class BIUpdateFUpdate (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] where
  fupd_of_bupd {P : PROP} {E : CoPset} : (|==> P) ⊢ |={E}=> P

class BIFUpdatePlainly (PROP : Type _) [BI PROP] [BIFUpdate PROP] [Sbi PROP] where
  fupd_keep_si_pure {E} E' Pi (R : PROP) :
    (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R
  fupd_plainly_later (E : CoPset) (P : PROP) : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P
  fupd_plainly_sForall_2 (E : CoPset) (Φ : PROP → Prop) :
    (|={E}=> ■ sForall Φ) ⊢ |={E}=> sForall Φ

@[rocq_alias BiBUpdSbi]
class BIBUpdateSbi (PROP : Type _) [BI PROP] [BIUpdate PROP] [Sbi PROP] where
  bupd_si_pure (Pi : SiProp) : iprop(|==> <si_pure> Pi ⊢@{PROP} <si_pure> Pi)

section BUpdLaws

variable [BI PROP] [BIUpdate PROP]

open BIUpdate

@[rocq_alias bupd_ne]
instance bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP)) := BIUpdate.bupd_ne
#rocq_ignore bupd_mono' "Use bupd_mono."
#rocq_ignore bupd_flip_mono' "Use bupd_mono."
#rocq_ignore bupd_proper "Derivable from bupd_ne with NonExpansive.eqv"

@[rocq_alias bupd_intro]
theorem bupd_intro {P : PROP} : P ⊢ |==> P := intro

@[rocq_alias bupd_mono]
theorem bupd_mono {P Q : PROP} (h : P ⊢ Q) : |==> P ⊢ |==> Q := mono h

@[rocq_alias bupd_trans]
theorem bupd_trans {P : PROP} : |==> |==> P ⊢ |==> P := trans

@[rocq_alias bupd_frame_r]
theorem bupd_frame_right {P Q : PROP} : (|==> P) ∗ Q ⊢ |==> (P ∗ Q) := frame_right

@[rocq_alias bupd_frame_l]
theorem bupd_frame_left {P Q : PROP} : P ∗ |==> Q ⊢ |==> (P ∗ Q) :=
  sep_symm.trans <| frame_right.trans <| mono sep_symm

@[rocq_alias bupd_wand_l]
theorem bupd_wand_left {P Q : PROP} : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q :=
  bupd_frame_left.trans <| mono <| wand_elim .rfl

@[rocq_alias bupd_wand_r]
theorem bupd_wand_right {P Q : PROP} : (|==> P) ∗ (P -∗ Q) ⊢ |==> Q :=
  sep_symm.trans bupd_wand_left

@[rocq_alias bupd_sep]
theorem bupd_sep {P Q : PROP} : (|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q) :=
  bupd_frame_left.trans <| (mono <| frame_right).trans BIUpdate.trans

@[rocq_alias bupd_idemp]
theorem bupd_idem {P : PROP} : (|==> |==> P) ⊣⊢ |==> P :=
  ⟨BIUpdate.trans, BIUpdate.intro⟩

@[rocq_alias bupd_or]
theorem bupd_or {P Q: PROP} : (|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q) :=
  or_elim (mono or_intro_l) (mono or_intro_r)

@[rocq_alias bupd_and]
theorem bupd_and {P Q : PROP} : (|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

@[rocq_alias bupd_exist]
theorem bupd_exist {Φ : A → PROP} : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x :=
  exists_elim (mono <| exists_intro ·)

@[rocq_alias bupd_forall]
theorem bupd_forall {Φ : A → PROP} :
    (|==> ∀ x, Φ x) ⊢ ∀ x, |==> Φ x :=
  forall_intro (mono <| forall_elim ·)

@[rocq_alias except_0_bupd]
theorem except0_bupd {P : PROP} : ◇ (|==> P) ⊢ (|==> ◇ P) :=
  or_elim (or_intro_l.trans intro) (mono or_intro_r)

@[rocq_alias bupd_absorbing]
instance {P : PROP} [Absorbing P] : Absorbing iprop(|==> P) :=
  ⟨bupd_frame_left.trans <| mono sep_elim_right⟩

@[rocq_alias bupd_sep_homomorphism]
instance bupd_sep_homomorphism :
  Algebra.MonoidHomomorphism (M₁ := PROP) sep sep emp emp (flip Entails) bupd where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := BIUpdate.bupd_ne
  map_op := bupd_sep
  map_unit := BIUpdate.intro

@[rocq_alias big_sepM_bupd]
theorem BigSepM.bigSepM_bupd [LawfulFiniteMap M' K] (Φ : K → V → PROP) {l : M' V} :
    ([∗map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗map] k↦x ∈ l, Φ k x :=
    Algebra.BigOpM.bigOpM_hom (R := flip Entails) Φ l

end BUpdLaws

section BUpdPlainlyLaws

variable [Sbi PROP] [BIUpdate PROP] [BIBUpdateSbi PROP]
open BIUpdate

@[rocq_alias bupd_plainly]
theorem bupd_plainly {P : PROP} : (|==> ■ P) ⊢ ■ P :=
  BIBUpdateSbi.bupd_si_pure (SiEmpValid.siEmpValid P)

@[rocq_alias bupd_plainly_elim]
theorem bupd_plainly_elim {P : PROP} [Absorbing P] : (|==> ■ P) ⊢ P :=
  bupd_plainly.trans plainly_elim

@[rocq_alias bupd_elim]
theorem bupd_elim {P : PROP} [Plain P] [Absorbing P] : |==> P ⊢ P :=
  (mono Plain.plain).trans bupd_plainly_elim

@[rocq_alias bupd_plain_forall]
theorem bupd_plain_forall (Φ : A → PROP) [∀ x, Plain (Φ x)] [∀ x, Absorbing (Φ x)] :
    (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x) := by
  refine ⟨bupd_forall, ?_⟩
  refine .trans ?_ intro
  exact (forall_intro fun a => (forall_elim a).trans bupd_elim)

@[rocq_alias bupd_plain]
instance bupd_plain {P : PROP} [Plain P] : Plain iprop(|==> P) :=
  ⟨(mono Plain.plain).trans <| (bupd_elim).trans <| plainly_mono intro⟩

end BUpdPlainlyLaws

section FUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

@[rocq_alias fupd_mask_intro_subseteq]
theorem fupd_mask_intro_subseteq {E1 E2 : CoPset} {P : PROP} (h : E2 ⊆ E1) :
    P ⊢ |={E1,E2}=> |={E2,E1}=> P :=
  (emp_sep.2.trans <| sep_mono_left <| subset h).trans <|
    frame_right.trans <| mono <| frame_right.trans <| mono emp_sep.1

@[rocq_alias fupd_mask_subseteq]
theorem fupd_mask_subseteq {E1 E2 : CoPset} (h : E2 ⊆ E1) : ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp :=
  fupd_mask_intro_subseteq h

@[rocq_alias fupd_mask_frame_r']
theorem fupd_mask_frame_right_strong {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P :=
  mask_frame_right_strong

theorem fupd_intro {E : CoPset} {P : PROP} : P ⊢ |={E}=> P :=
  (fupd_mask_intro_subseteq λ _ => id).trans trans

@[rocq_alias fupd_mask_intro]
theorem fupd_mask_intro {E1 E2 : CoPset} {P : PROP} (h : E2 ⊆ E1) :
  ((|={E2,E1}=> emp) -∗ P) ⊢ |={E1,E2}=> P :=
  (wand_mono_right fupd_intro).trans <|
    (emp_sep.2.trans <| sep_mono_left <| subset h).trans <|
    frame_right.trans <| (mono wand_elim_right).trans trans

@[rocq_alias fupd_mask_intro_discard]
theorem fupd_mask_intro_discard {E1 E2 : CoPset} {P : PROP} [Absorbing P] (h : E2 ⊆ E1) :
    P ⊢ |={E1,E2}=> P :=
  (wand_intro_left sep_elim_right).trans <| fupd_mask_intro h

@[rocq_alias fupd_elim]
theorem fupd_elim {E1 E2 E3 : CoPset} {P Q : PROP} (h : Q ⊢ |={E2,E3}=> P) :
    (|={E1,E2}=> Q) ⊢ |={E1,E3}=> P :=
  (mono h).trans trans

theorem fupd_frame_right {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ Q ⊢ |={E1,E2}=> P ∗ Q :=
  frame_right

@[rocq_alias fupd_frame_l]
theorem fupd_frame_left {E1 E2 : CoPset} {P Q : PROP} : P ∗ (|={E1,E2}=> Q) ⊢ |={E1,E2}=> P ∗ Q :=
  sep_symm.trans <| fupd_frame_right.trans <| mono sep_symm

@[rocq_alias fupd_wand_l]
theorem fupd_wand_left {E1 E2 : CoPset} {P Q : PROP} : (P -∗ Q) ∗ (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q :=
  fupd_frame_left.trans <| mono <| wand_elim .rfl

@[rocq_alias fupd_wand_r]
theorem fupd_wand_right {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |={E1,E2}=> Q :=
  sep_symm.trans fupd_wand_left

@[rocq_alias fupd_sep]
theorem fupd_sep {E : CoPset} {P Q : PROP} : (|={E}=> P) ∗ (|={E}=> Q) ⊢ |={E}=> P ∗ Q :=
  fupd_frame_left.trans <| (mono frame_right).trans trans

@[rocq_alias fupd_mask_weaken]
theorem fupd_mask_weaken {E1 E3 : CoPset} (E2 : CoPset) {P : PROP} (h : E2 ⊆ E1) :
    ((|={E2,E1}=> emp) ={E2,E3}=∗ P) ⊢ |={E1,E3}=> P := by
  refine (emp_sep (P := iprop((|={E2,E1}=> emp) -∗ |={E2,E3}=> P))).mpr.trans ?_
  refine (sep_mono_left (fupd_mask_subseteq h)).trans ?_
  exact frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans BIFUpdate.trans

@[rocq_alias fupd_idemp]
theorem fupd_idem {E : CoPset} {P : PROP} : (|={E}=> |={E}=> P) ⊣⊢ |={E}=> P := ⟨trans, fupd_intro⟩

@[rocq_alias fupd_or]
theorem fupd_or {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∨ (|={E1,E2}=> Q) ⊢ |={E1,E2}=> P ∨ Q :=
  or_elim (mono or_intro_l) (mono or_intro_r)

@[rocq_alias fupd_and]
theorem fupd_and {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P ∧ Q) ⊢ (|={E1,E2}=> P) ∧ (|={E1,E2}=> Q) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

@[rocq_alias fupd_exist]
theorem fupd_exist {E1 E2 : CoPset} {Φ : A → PROP} : (∃ a : A, |={E1,E2}=> Φ a) ⊢ |={E1,E2}=> ∃ a : A, Φ a :=
  exists_elim (mono <| exists_intro ·)

@[rocq_alias fupd_forall]
theorem fupd_forall {E1 E2 : CoPset} {Φ : A → PROP} :
    (|={E1,E2}=> «forall» λ a : A => Φ a) ⊢ «forall» λ a : A => iprop(|={E1,E2}=> Φ a) :=
  forall_intro (mono <| forall_elim ·)

@[rocq_alias except_0_fupd]
theorem except0_fupd {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> ◇ P :=
  except0.trans (mono except0_intro)

@[rocq_alias fupd_except_0]
theorem fupd_except0 {E1 E2 : CoPset} {P : PROP} : (|={E1,E2}=> ◇ P) ⊢ |={E1,E2}=> P :=
  (BIFUpdate.mono (except0_mono (fupd_intro (E := E2) (P := P)))).trans
    (BIFUpdate.mono BIFUpdate.except0 |>.trans BIFUpdate.trans)

@[rocq_alias fupd_absorbing]
instance {E1 E2 : CoPset} {P : PROP} [Absorbing P] : Absorbing iprop(|={E1,E2}=> P) :=
  ⟨fupd_frame_left.trans <| mono sep_elim_right⟩

theorem fupd_mask_frame_right {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P :=
  λ h => (mono <| imp_intro_swap and_elim_r).trans <| mask_frame_right_strong h

@[rocq_alias fupd_mask_mono]
theorem fupd_mask_mono {E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E2 → (|={E1}=> P) ⊢ |={E2}=> P :=
  λ h => by simpa [subset_union_diff h] using
    (fupd_mask_frame_right (E2 := E1) (Ef := E2 \ E1) disjoint_diff_right)

@[rocq_alias fupd_mask_frame]
theorem fupd_mask_frame {E E' E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E → (|={E1,E2}=> |={E2 ∪ (E \ E1),E'}=> P) ⊢ |={E,E'}=> P :=
  λ h => by simpa [subset_union_diff h] using
    ((fupd_mask_frame_right (P := iprop(|={E2 ∪ (E \ E1),E'}=> P)) disjoint_diff_right).trans trans)

/-- A variant of [fupd_mask_frame] that works well for accessors:
  Tailored to eliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to transform the
  closing view shift instead of letting you prove the same side-conditions twice. -/
@[rocq_alias fupd_mask_frame_acc]
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
  refine wand_intro <| frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans ?_
  refine (BIFUpdate.mono ?_).trans <| fupd_mask_frame hE
  refine sep_emp.2.trans <| (sep_mono_right <| fupd_mask_intro_subseteq hmask).trans ?_
  refine fupd_frame_left.trans <| (BIFUpdate.mono frame_right).trans <| fupd_elim ?_
  refine BIFUpdate.mono <| sep_symm.trans ?_
  refine (sep_mono ?_ .rfl).trans wand_elim_right
  refine forall_intro λ R => wand_intro <| frame_right.trans <| fupd_elim ?_
  exact emp_sep.1.trans <| (fupd_mask_frame_right hdisj).trans <| by simp [subset_union_diff hE]

@[rocq_alias fupd_mask_subseteq_emptyset_difference]
theorem fupd_mask_subseteq_emptyset_difference {E1 E2 : CoPset} (h : E2 ⊆ E1) :
    ⊢@{PROP} |={E1,E2}=> |={∅,E1\E2}=> emp := by
  have H : emp ⊢@{PROP} |={E1 \ E2 ∪ E2, ∅ ∪ E2}=> |={∅, E1 \ E2}=> emp :=
    (fupd_mask_intro_subseteq empty_subset).trans
    (fupd_mask_frame_right (disjoint_symm disjoint_diff_right))
  rw [union_comm, subset_union_diff h] at H
  exact H

@[rocq_alias fupd_trans_frame]
theorem fupd_trans_frame {E1 E2 E3 : CoPset} {P Q : PROP} :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ⊢ |={E1,E3}=> P :=
  fupd_frame_left.trans <| fupd_elim <| ((sep_assoc.2.trans <| sep_mono_left sep_comm.1).trans <|
    sep_mono_left wand_elim_right).trans <| frame_right.trans <| BIFUpdate.mono emp_sep.1

@[rocq_alias fupd_sep_homomorphism]
instance fupd_sep_homomorphism E :
  Algebra.MonoidHomomorphism (M₁ := PROP) sep sep emp emp (flip Entails) (fupd E E) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_ne := BIFUpdate.ne
  map_op := fupd_sep
  map_unit := fupd_intro

@[rocq_alias big_sepM_fupd]
theorem BigSepM.bigSepM_fupd [LawfulFiniteMap M' K] E (Φ : K → V → PROP) (l : M' V) :
    ([∗map] k↦x ∈ l, |={E}=> Φ k x) ⊢ |={E}=> [∗map] k↦x ∈ l, Φ k x :=
    Algebra.BigOpM.bigOpM_hom (R := flip Entails) Φ l

@[rocq_alias big_sepL_fupd]
theorem BigSepL2.bigSepL_fupd {A : Type _} E (Φ : Nat → A → PROP) l :
    ([∗list] k↦x ∈ l, |={E}=> Φ k x) ⊢ |={E}=> [∗list] k↦x ∈ l, Φ k x :=
    Algebra.BigOpL.bigOpL_hom (R := flip Entails) Φ l

@[rocq_alias big_sepL2_fupd]
theorem BigSepL2.bigSepL2_fupd {A B : Type _} E (Φ : Nat → A → B → PROP) l1 l2 :
    ([∗list] k↦x;y ∈ l1;l2, |={E}=> Φ k x y) ⊢ |={E}=> [∗list] k↦x;y ∈ l1;l2, Φ k x y := by
  refine BigSepL2.bigSepL2_alt.mp.trans ?_
  refine persistent_and_affinely_sep_left.mp.trans ?_
  refine .trans ?_ (mono BigSepL2.bigSepL2_alt.mpr)
  refine .trans ?_ (mono persistent_and_affinely_sep_left.mpr)
  exact .trans (sep_mono_right (BigSepL2.bigSepL_fupd E _ _ )) fupd_frame_left

#rocq_ignore fupd_mono' "Use BIFUpdate.mono."
#rocq_ignore fupd_flip_mono' "Use BIFUpdate.mono."
#rocq_ignore fupd_proper "Derivable from BIFUpdate.ne with NonExpansive.eqv"

end FUpdLaws

section StepFUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

theorem step_fupdN_contractive {E1 E2 : CoPset} {n : Nat} [ι : BILaterContractive PROP] :
    OFE.Contractive (iprop(|={E1}[E2]▷=>^[n + 1] · : PROP)) where
  distLater_dist {i x y} xy_i := by
    induction n with
    | zero => exact ne.ne (ι.distLater_dist (ne.ne <| xy_i · ·))
    | succ n IH => exact ne.ne (later_ne.ne (ne.ne IH))

theorem step_fupdN_ne {E1 E2 : CoPset} {n : Nat} :
    OFE.NonExpansive (iprop(|={E1}[E2]▷=>^[n] · : PROP)) where
  ne {i x y} xy_i := by
    induction n with
    | zero => simp [Nat.repeat, xy_i]
    | succ n IH => exact ne.ne (later_ne.ne (ne.ne IH))

theorem step_fupd_mono {Eo Ei : CoPset} {P Q : PROP} :
    (Q ⊢ P) → (|={Eo}[Ei]▷=> Q) ⊢ |={Eo}[Ei]▷=> P :=
  (mono <| later_mono <| mono ·)

@[rocq_alias step_fupdN_wand]
theorem step_fupdN_wand {Eo Ei : CoPset} {n : Nat} {P Q : PROP} :
    (|={Eo}[Ei]▷=>^[n] P) ⊢ (P -∗ Q) -∗ (|={Eo}[Ei]▷=>^[n] Q) := by
  refine wand_intro_left ?_
  induction n with
  | zero =>
    exact wand_elim_left
  | succ n IH =>
    calc iprop((P -∗ Q) ∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> _)
      _ ⊢ |={Eo,Ei}=> (P -∗ Q) ∗ ▷ |={Ei,Eo}=> _  := (fupd_frame_left ..)
      _ ⊢ |={Eo,Ei}=> (▷ (P -∗ Q)) ∗ ▷ |={Ei,Eo}=> _  := mono (sep_mono (later_intro) .rfl)
      _ ⊢ |={Eo,Ei}=> ▷ ((P -∗ Q) ∗ |={Ei,Eo}=> _) := mono (later_sep.2)
      _ ⊢ |={Eo,Ei}=> ▷ |={Ei,Eo}=> ((P -∗ Q) ∗ _) := mono (later_mono (fupd_frame_left ..))
      _ ⊢ |={Eo,Ei}=> ▷ |={Ei,Eo}=> _ := step_fupd_mono IH

@[rocq_alias step_fupd_wand]
theorem step_fupd_wand {Eo Ei : CoPset} {P Q : PROP} :
    (|={Eo}[Ei]▷=> P) ⊢ (P -∗ Q) -∗ (|={Eo}[Ei]▷=> Q) :=
  step_fupdN_wand (n := 1)

@[rocq_alias step_fupd_mask_mono]
theorem step_fupd_mask_mono {Eo₁ Eo₂ Ei₁ Ei₂ : CoPset} {P : PROP}
    (Ei₂_Ei₁ : Ei₂ ⊆ Ei₁) (Eo₁_Eo₂ : Eo₁ ⊆ Eo₂) :
    (|={Eo₁}[Ei₁]▷=> P) ⊢ |={Eo₂}[Ei₂]▷=> P := by
  refine emp_sep.2.trans ?_
  refine (sep_mono (fupd_mask_intro_subseteq Eo₁_Eo₂) .rfl).trans ?_
  refine frame_right.trans ?_
  refine .trans (mono ?_) (trans (E2 := Eo₁))
  refine fupd_frame_left.trans ?_
  refine .trans (mono ?_) (trans (E2 := Ei₁))
  refine (sep_mono (fupd_mask_intro_subseteq Ei₂_Ei₁) .rfl).trans ?_
  refine frame_right.trans ?_
  refine mono ?_
  refine (sep_mono later_intro .rfl).trans ?_
  refine later_sep.2.trans ?_
  refine later_mono ?_
  refine frame_right.trans ?_
  refine .trans (mono ?_) (trans (E2 := Ei₁))
  refine fupd_frame_left.trans ?_
  refine .trans (mono ?_) (trans (E2 := Eo₁))
  refine frame_right.trans ?_
  exact mono emp_sep.1

@[rocq_alias step_fupd_intro]
theorem step_fupd_intro {Ei Eo : CoPset} {P : PROP} (Ei_Eo : Ei ⊆ Eo) :
    ▷ P ⊢ |={Eo}[Ei]▷=> P := by
  calc iprop(▷ P)
    _ ⊢ |={Ei}=> ▷ P := fupd_intro
    _ ⊢ |={Ei}[Ei]▷=> P := mono <| later_mono fupd_intro
    _ ⊢ |={Eo}[Ei]▷=> P := step_fupd_mask_mono (subset_refl) Ei_Eo

@[rocq_alias step_fupdN_intro]
theorem step_fupdN_intro {Ei Eo : CoPset} {P : PROP} (Ei_Eo : Ei ⊆ Eo) :
    ▷^[n] P ⊢ |={Eo}[Ei]▷=>^[n] P :=
  match n with
  | 0 => .rfl
  | n+1 => by
    simp only [Nat.repeat]
    refine .trans (later_laterN n).1 ?_
    refine .trans (step_fupd_intro Ei_Eo) ?_
    exact step_fupd_mono <| step_fupdN_intro Ei_Eo

@[rocq_alias step_fupdN_le]
theorem step_fupdN_le {n m : Nat} {Eo Ei : CoPset} {P : PROP} :
    n ≤ m → Ei ⊆ Eo → (|={Eo}[Ei]▷=>^[n] P) ⊢ |={Eo}[Ei]▷=>^[m] P
  | .refl, _ => .rfl
  | .step (m := m) n_m, Ei_Eo =>
    step_fupdN_le n_m Ei_Eo |>.trans (later_intro.trans (step_fupd_intro Ei_Eo))

@[rocq_alias step_fupd_fupd]
theorem step_fupd_fupd {Eo Ei : CoPset} {P : PROP} : (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P) :=
  ⟨step_fupd_mono fupd_intro, mono <| later_mono BIFUpdate.trans⟩

@[rocq_alias step_fupdN_mono]
theorem step_fupdN_mono {n : Nat} {Eo Ei : CoPset} {P Q : PROP} (H : P ⊢ Q) :
    (|={Eo}[Ei]▷=>^[n] P) ⊢ (|={Eo}[Ei]▷=>^[n] Q) := by
  induction n with
  | zero => exact H
  | succ k IH => exact step_fupd_mono IH

@[rocq_alias step_fupdN_S_fupd]
theorem step_fupdN_S_fupd {n : Nat} {E : CoPset} {P : PROP} :
    (|={E}[∅]▷=>^[n + 1] P) ⊣⊢ (|={E}[∅]▷=>^[n + 1] |={E}=> P) := by
  refine ⟨step_fupd_mono <| step_fupdN_mono fupd_intro, ?_⟩
  simp only [Nat.repeat_add]
  exact step_fupdN_mono step_fupd_fupd.mpr

@[rocq_alias step_fupd_frame_l]
theorem step_fupd_frame_left {Eo Ei : CoPset} {R Q : PROP} :
    (R ∗ |={Eo}[Ei]▷=> Q) ⊢ |={Eo}[Ei]▷=> (R ∗ Q) :=
  fupd_frame_left.trans <| mono <|
    (sep_mono_left later_intro).trans <| later_sep.2.trans <| later_mono fupd_frame_left

@[rocq_alias step_fupdN_add]
theorem step_fupdN_add {n m : Nat} {Eo Ei : CoPset} {P : PROP} :
    (|={Eo}[Ei]▷=>^[n + m] P) ⊣⊢ (|={Eo}[Ei]▷=>^[n] |={Eo}[Ei]▷=>^[m] P) := by
  induction n with
  | zero => rw [Nat.zero_add]; exact .rfl
  | succ n IH =>
    rw [Nat.add_right_comm n 1 m]
    exact ⟨mono <| later_mono <| mono IH.1, mono <| later_mono <| mono IH.2⟩

@[rocq_alias step_fupdN_frame_l]
theorem step_fupdN_frame_left {Eo Ei : CoPset} {n : Nat} {R Q : PROP} :
    (R ∗ |={Eo}[Ei]▷=>^[n] Q) ⊢ |={Eo}[Ei]▷=>^[n] (R ∗ Q) := by
  induction n with
  | zero => exact .rfl
  | succ n IH => exact step_fupd_frame_left.trans (mono <| later_mono <| mono IH)

end StepFUpdLaws

section StepFUpdPlainlyLaws

variable [Sbi PROP] [BIFUpdate PROP] [BIFUpdatePlainly PROP]

open BIFUpdate BIFUpdatePlainly

@[rocq_alias fupd_keep_si_pure]
theorem fupd_keep_si_pure {E1 E2 : CoPset} E2' Pi {R : PROP} :
  (|={E1,E2'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R :=
  (and_mono_right (wand_mono_right fupd_intro)).trans <|
    (BIFUpdatePlainly.fupd_keep_si_pure E2' Pi iprop(|={E1,E2}=> R)).trans trans

@[rocq_alias fupd_keep_plainly]
theorem fupd_keep_plainly [BIAffine PROP] {E1 E2 : CoPset} E2' (P : PROP) {R : PROP} :
  (|={E1,E2'}=> ■ P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R :=
  (and_mono_right (wand_mono_left siPure_siEmpValid_elim)).trans <|
    fupd_keep_si_pure E2' (SiEmpValid.siEmpValid P)

@[rocq_alias fupd_plainly_later]
theorem fupd_plainly_later (E : CoPset) (P : PROP) : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P :=
  BIFUpdatePlainly.fupd_plainly_later E P

@[rocq_alias fupd_keep_plain]
theorem fupd_keep_plain [BIAffine PROP] {E1 E2 : CoPset} E2' (P R : PROP) [Plain P] :
  (|={E1,E2'}=> P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R :=
  (and_mono_left (mono Plain.plain)).trans (fupd_keep_plainly E2' P)

@[rocq_alias fupd_plainly_mask]
theorem fupd_plainly_mask [BIAffine PROP] E E' {P : PROP} : (|={E,E'}=> ■ P) ⊢ |={E}=> P :=
  (and_intro .rfl (wand_intro_left (sep_elim_left.trans fupd_intro))).trans <|
    fupd_keep_plainly E' P

@[rocq_alias fupd_plain_mask]
theorem fupd_plain_mask [BIAffine PROP] {E E' : CoPset} {P : PROP} [Plain P] :
    (|={E,E'}=> P) ⊢ |={E}=> P :=
  (mono Plain.plain).trans (fupd_plainly_mask E E')

@[rocq_alias fupd_plain_later]
theorem fupd_plain_later {E : CoPset} {P : PROP} [Plain P] : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P :=
  (later_mono (mono Plain.plain)).trans (fupd_plainly_later E P)

@[rocq_alias fupd_keep_plain_sep]
theorem fupd_keep_plain_sep [BIAffine PROP] {E E' : CoPset} {P R : PROP} [Plain P] :
    (R ={E,E'}=∗ P) -∗ R -∗ |={E}=> P ∗ R :=
  entails_wand <| wand_intro <|
    (and_intro wand_elim_left (sep_elim_right.trans (wand_intro_left fupd_intro))).trans
      (fupd_keep_plain (E1 := E) (E2 := E) E' P iprop(P ∗ R))

@[rocq_alias step_fupd_plain]
theorem step_fupd_plain [BIAffine PROP] {E1 E2 : CoPset} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=> P) ⊢ |={E1}=> ▷ ◇ P :=
  (fupd_elim <| (later_mono fupd_plain_mask).trans fupd_plain_later).trans fupd_plain_mask

@[rocq_alias step_fupdN_plain]
theorem step_fupdN_plain [BIAffine PROP] {E1 E2 : CoPset} {n : Nat} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=>^[n] P) ⊢ |={E1}=> ▷^[n] ◇ P := by
  induction n with
  | zero => exact except0_intro.trans fupd_intro
  | succ n ih =>
    simp only [Nat.repeat]
    refine (step_fupd_mono ih).trans ?_
    refine step_fupd_fupd.2.trans ?_
    refine step_fupd_plain.trans ?_
    refine (mono <| later_mono <| except0_laterN n).trans ?_
    exact mono <| laterN_mono (n+1) except0_idem.1

end StepFUpdPlainlyLaws
