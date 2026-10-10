/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Remy Seassau, Yunsong Yang
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.BI.Notation
public import Iris.Algebra
public import Iris.BI.Plainly
public import Iris.Std.CoPset

@[expose] public section


variable {SI : Iris.stepindex (Type _)} [Iris.SIdx SI]
local stepindex SI

namespace Iris
open Iris.Std BI

/--
Basic update modality.

- `|==> P` is the basic update modality.
- `P ==∗ Q` is shorthand for `|==> P -∗ Q`.
-/
@[rocq_alias BUpd]
class BUpd (PROP : Type _) where
  bupd : PROP → PROP
export BUpd (bupd)

attribute [inherit_doc BUpd] BUpd.bupd
syntax "|==> " term:40 : term
syntax:25 term:26 " ==∗ " term:25 : term

macro_rules
  | `(iprop(|==>%$tk $P))   => ``($(wrapIprop tk ``BUpd.bupd) iprop($P))
  | `(iprop($P ==∗%$tk $Q)) =>
    ``(BIBase.wand iprop($P) ($(wrapIprop tk ``BUpd.bupd) iprop($Q)))
  | `($P ==∗%$tk $Q)        => ``(⊢ $P ==∗%$tk $Q)

delab_rule BUpd.bupd
  | `($_ $P) => do ``(iprop(|==> $(← unpackIprop P)))

delab_rule BIBase.wand
  | `($_ $P iprop(|==> $Q)) => do `(iprop($(← unpackIprop P) ==∗ $Q))

/--
Fancy update modality.

- `|={E1,E2}=> P` changes the mask from `E1` to `E2`.
- `|={E}=> P` is shorthand for `|={E,E}=> P`.
- `P ={E1,E2}=∗ Q` is shorthand for `|={E1,E2}=> P -∗ Q`.
- `P ={E}=∗ Q` is shorthand for `|={E}=> P -∗ Q`.
- `|={E1}[E2]▷=> P` is a one-step fancy update.
- `|={E}▷=> P` is a one-step fancy update with a fixed mask.
- `|={E1}[E2]▷^n=> P` is a fancy update taking `n` steps.
- `|={E}▷^n=> P` is a fancy update taking `n` steps with a fixed mask.
- `|={E1}[E2]▷=>^[n] P` iterates the one-step fancy update `n` times.
- `|={E}▷=>^[n] P` iterates the one-step fancy update `n` times with a fixed mask.

The wand form `P ={E1,E2}=∗ Q` is a shorthand for `|={E1,E2}=> P -∗ Q`.
The wand forms of the other notations are analogous.
-/
@[rocq_alias FUpd]
class FUpd (PROP : Type _) where
  fupd : CoPset → CoPset → PROP → PROP
export FUpd (fupd)

attribute [inherit_doc FUpd] FUpd.fupd
syntax "|={" term "," term "}=> " term : term
syntax:25 term:26 " ={" term "," term "}=∗ " term:25 : term
syntax "|={" term "}=> " term : term
syntax:25 term:26 " ={" term "}=∗ " term:25 : term

macro_rules
  | `(iprop(|={%$tk1 $E1,$E2 }=>%$tk2 $P))   => do
      ``($(wrapIpropSpan tk1 tk2 ``FUpd.fupd) $E1 $E2 iprop($P))
  | `(iprop($P ={%$tk1 $E1,$E2 }=∗%$tk2 $Q)) => do
      ``(BIBase.wand iprop($P) ($(wrapIpropSpan tk1 tk2 ``FUpd.fupd) $E1 $E2 iprop($Q)))
  | `(iprop(|={%$tk1 $E1}=>%$tk2 $P))       => do
      ``($(wrapIpropSpan tk1 tk2 ``FUpd.fupd) $E1 $E1 iprop($P))
  | `(iprop($P ={%$tk1 $E1 }=∗%$tk2 $Q))     => do
      ``(BIBase.wand iprop($P) ($(wrapIpropSpan tk1 tk2 ``FUpd.fupd) $E1 $E1 iprop($Q)))
  | `($P ={%$tk $E1,$E2}=∗ $Q)        => ``(⊢ $P ={%$tk $E1,$E2}=∗ $Q)
  | `($P ={%$tk $E1}=∗ $Q)            => ``(⊢ $P ={%$tk $E1}=∗ $Q)

delab_rule FUpd.fupd
  | `($_ $E1 $E2 $P) => do
      let P ← unpackIprop P
      if E1 == E2 then ``(iprop(|={$E1}=> $P))
      else ``(iprop(|={$E1,$E2}=> $P))

delab_rule BIBase.wand
  | `($_ $P iprop(|={$E₁,$E₂}=> $Q)) => do `(iprop($(← unpackIprop P) ={$E₁,$E₂}=∗ $Q))
  | `($_ $P iprop(|={$E₁}=> $Q)) => do `(iprop($(← unpackIprop P) ={$E₁}=∗ $Q))

syntax "|={" term "}[" term "]▷=> " term : term
syntax:25 term:26 " ={" term "}[" term "]▷=∗ " term:25 : term
syntax "|={" term "}▷=> " term : term
syntax:25 term:26 " ={" term "}▷=∗ " term:25 : term

macro_rules
  | `(iprop(|={%$tk $E1}[$E2]▷=> $P))   =>
    ``(iprop(|={%$tk $E1,$E2}=> ▷ (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={%$tk $E1}[$E2]▷=∗ $Q)) =>
    ``(iprop(iprop($P) -∗ |={%$tk $E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={%$tk $E1}▷=> $P))        =>
    ``(iprop(|={%$tk $E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={%$tk $E1}▷=∗ $Q))      =>
    ``(iprop(iprop($P) ={%$tk $E1}[$E1]▷=∗ iprop($Q)))

delab_rule FUpd.fupd
  | `($_ $E₁ $E₂ iprop(▷ |={$E₂',$E₁'}=> $P)) => do
    unless E₁ == E₁' ∧ E₂ == E₂' do throw ()
    `(iprop(|={$E₁}[$E₂]▷=> $(← unpackIprop P)))
  | `($_ $E₁ $E₁' iprop(▷ |={$E₁''}=> $P)) => do
    unless E₁ == E₁' ∧ E₁' == E₁'' do throw ()
    `(iprop(|={$E₁}▷=> $(← unpackIprop P)))

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷=> $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}[$E₂]▷=∗ $P))
  | `($_ $Q iprop(|={$E₁}▷=> $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}▷=∗ $P))

syntax "|={" term "}[" term "]▷^" term "=> " term : term
syntax:25 term:26 " ={" term "}[" term "]▷^" term "=∗ " term:25 : term
syntax "|={" term "}▷^" term "=> " term : term
syntax:25 term:26 " ={" term "}▷^" term "=∗ " term:25 : term

macro_rules
  | `(iprop(|={%$tk $E1}[$E2]▷^$n=> $P))   =>
      ``(iprop(|={%$tk $E1,$E2}=> ▷^[$n] (|={$E2,$E1}=> iprop($P))))
  | `(iprop($P ={%$tk $E1}[$E2]▷^$n=∗ $Q)) =>
      ``(iprop(iprop($P) -∗ |={%$tk $E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={%$tk $E1}▷^$n=> $P))        =>
      ``(iprop(|={%$tk $E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={%$tk $E1}▷^$n=∗ $Q))      =>
      ``(iprop(iprop($P) ={%$tk $E1}[$E1]▷^$n=∗ iprop($Q)))

delab_rule FUpd.fupd
  | `($_ $E₁ $E₂ iprop(▷^[$n] |={$E₂',$E₁'}=> $P)) => do
    unless E₁ == E₁' ∧ E₂ == E₂' do throw ()
    `(iprop(|={$E₁}[$E₂]▷^$n=> $(← unpackIprop P)))
  | `($_ $E₁ $E₁' iprop(▷^[$n] |={$E₁''}=> $P)) => do
    unless E₁ == E₁' ∧ E₁' == E₁'' do throw ()
    `(iprop(|={$E₁}▷^$n=> $(← unpackIprop P)))

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷^$n=> $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}[$E₂]▷^$n=∗ $P))
  | `($_ $Q iprop(|={$E₁}▷^$n=> $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}▷^$n=∗ $P))

syntax "|={" term "}[" term "]▷=>^[" term "] " term : term
syntax:25 term:26 " ={" term "}[" term "]▷=∗^[" term "] " term:25 : term
syntax "|={" term "}▷=>^[" term "] " term : term
syntax:25 term:26 " ={" term "}▷=∗^[" term "] " term:25 : term

/-- Iterated step-taking fancy update `|={Eo}[Ei]▷=>^[n] P`. -/
@[rocq_alias step_fupdN]
def step_fupdN {PROP : Type _} [BIBase PROP] [FUpd PROP] (Eo Ei : CoPset) : Nat → PROP → PROP
  | 0, P => P
  | n + 1, P => iprop(|={Eo}[Ei]▷=> step_fupdN Eo Ei n P)

macro_rules
  | `(iprop(|={%$tk $E1 }[ $E2 ]▷=>^[ $n ] $P))   =>
      ``($(wrapIprop tk ``step_fupdN) $E1 $E2 $n iprop($P))
  | `(iprop($P ={%$tk $E1 }[ $E2 ]▷=∗^[ $n ] $Q)) =>
      ``(BIBase.wand iprop($P) ($(wrapIprop tk ``step_fupdN) $E1 $E2 $n iprop($Q)))
  | `(iprop(|={%$tk $E1 }▷=>^[ $n ] $P))          =>
      ``($(wrapIprop tk ``step_fupdN) $E1 $E1 $n iprop($P))
  | `(iprop($P ={%$tk $E1 }▷=∗^[ $n ] $Q))        =>
      ``(BIBase.wand iprop($P) ($(wrapIprop tk ``step_fupdN) $E1 $E1 $n iprop($Q)))

delab_rule step_fupdN
  | `($_ $E₁ $E₂ $n $P) => do
      let P ← unpackIprop P
      if E₁ == E₂ then ``(iprop(|={$E₁}▷=>^[$n] $P))
      else ``(iprop(|={$E₁}[$E₂]▷=>^[$n] $P))

delab_rule BIBase.wand
  | `($_ $Q iprop(|={$E₁}[$E₂]▷=>^[$n] $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}[$E₂]▷=∗^[$n] $P))
  | `($_ $Q iprop(|={$E₁}▷=>^[$n] $P)) => do
    `(iprop($(← unpackIprop Q) ={$E₁}▷=∗^[$n] $P))

@[rocq_alias BiBUpd]
class BIUpdate (PROP : Type _) [BI PROP] extends BUpd PROP where
  intro {P : PROP} : P ⊢ |==> P
  mono {P Q : PROP} : (P ⊢ Q) → |==> P ⊢ |==> Q
  trans {P : PROP} : |==> |==> P ⊢ |==> P
  frame_right {P R : PROP} : (|==> P) ∗ R ⊢ |==> (P ∗ R)

#rocq_ignore BiBUpdMixin "Included in BIUpdate typeclass."

@[rocq_alias BiFUpd]
class BIFUpdate (PROP : Type _) [BI PROP] extends FUpd PROP where
  subset {E1 E2 : CoPset} : E2 ⊆ E1 → ⊢ |={E1,E2}=> |={E2,E1}=> (emp : PROP)
  except0 {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> P
  mono {E1 E2 : CoPset} {P Q : PROP} : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q
  trans {E1 E2 E3 : CoPset} {P : PROP} : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P
  mask_frame_right_strong {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P
  frame_right {E1 E2 : CoPset} {P R : PROP} : (|={E1,E2}=> P) ∗ R ⊢ |={E1,E2}=> P ∗ R

#rocq_ignore BiFUpdMixin "Included in BIFUpdate typeclass."

/-- Non-expansiveness of the basic update (step-indexed mixin; the update laws are SI-free). -/
@[indexed]
class BUpdNE (SI : stepindex (Type _)) [SIdx SI] (PROP : Type _) [BI PROP] [BIStepIndexed PROP] [BUpd PROP] :
    Prop where
  bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP))
attribute [instance] BUpdNE.bupd_ne

/-- Non-expansiveness of the fancy update (step-indexed mixin; the update laws are SI-free). -/
@[indexed]
class FUpdNE (SI : stepindex (Type _)) [SIdx SI] (PROP : Type _) [BI PROP] [BIStepIndexed PROP] [FUpd PROP] :
    Prop where
  fupd_ne {E1 E2 : CoPset} : OFE.NonExpansive (iprop(|={E1,E2}=> · : PROP))
attribute [instance] FUpdNE.fupd_ne

@[rocq_alias BiBUpdFUpd]
class BIUpdateFUpdate (PROP : Type _) [BI.BIBase PROP] [BUpd PROP] [FUpd PROP] where
  fupd_of_bupd {P : PROP} {E : CoPset} : (|==> P) ⊢ |={E}=> P

@[indexed, rocq_alias BiFUpdSbi]
class BIFUpdateSbi (SI : stepindex (Type _)) [SIdx SI] (PROP : Type _) [BI PROP] [BIStepIndexed PROP]
    [Sbi PROP] [FUpd PROP] where
  fupd_keep_siPure {E} E' (Pi : SiProp) (R : PROP) :
    (|={E,E'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E}=∗ R) ⊢ |={E}=> R
  fupd_siPure_later (E : CoPset) (Pi : SiProp) :
    (▷ |={E}=> <si_pure> Pi) ⊢@{PROP} |={E}=> ▷ ◇ <si_pure> Pi
  fupd_siPure_sForall_2 (E : CoPset) (Ψi : SiProp → Prop) :
    (∀ q, ⌜Ψi q⌝ → |={E}=> <si_pure> q) ⊢@{PROP} |={E}=> <si_pure> (sForall Ψi)

@[indexed, rocq_alias BiBUpdSbi]
class BIBUpdateSbi (SI : stepindex (Type _)) [SIdx SI] (PROP : Type _) [BI PROP] [BIStepIndexed PROP]
    [Sbi PROP] [BUpd PROP] where
  bupd_siPure (Pi : SiProp) : iprop(|==> <si_pure> Pi ⊢@{PROP} <si_pure> Pi)

/-- SI-free plain-update law of the basic update (Iris ≤ 4.2 `BiBUpdPlainly`). For an `Sbi`, follows
from `BIBUpdateSbi` (`BIBUpdatePlainly.ofSbi`). -/
class BIBUpdatePlainly (PROP : Type _) [BI PROP] [BIPlainly PROP] [BUpd PROP] : Prop where
  bupd_plainly {P : PROP} : (|==> ■ P) ⊢ ■ P

/-- SI-free plain-update laws of the fancy update (Iris ≤ 4.2 `BiFUpdPlainly`). For an affine
`Sbi`, follows from `BIFUpdateSbi` (`BIFUpdatePlainly.ofSbi`). -/
class BIFUpdatePlainly (PROP : Type _) [BI PROP] [BIPlainly PROP] [FUpd PROP] : Prop where
  fupd_keep_plainly {E1 E2 : CoPset} (E2' : CoPset) (P R : PROP) :
    (|={E1,E2'}=> ■ P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R
  fupd_plainly_later (E : CoPset) (P : PROP) : (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P
  fupd_plainly_sForall_2 (E : CoPset) (Φ : PROP → Prop) :
    (∀ p, ⌜Φ p⌝ → |={E}=> ■ p) ⊢ |={E}=> BIBase.sForall Φ

section BUpdLaws

variable [BI PROP] [BIUpdate PROP]

open BIUpdate

@[rocq_alias bupd_ne]
theorem bupd_ne [BIStepIndexed PROP] [BUpdNE PROP] :
    OFE.NonExpansive (BUpd.bupd (PROP := PROP)) := BUpdNE.bupd_ne
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
theorem bupd_frame_left {P Q : PROP} : P ∗ |==> Q ⊢ |==> (P ∗ Q) := calc
  _ ⊢ |==> Q ∗ P   := sep_symm
  _ ⊢ |==> (Q ∗ P) := frame_right
  _ ⊢ |==> (P ∗ Q) := mono sep_symm

@[rocq_alias bupd_wand_l]
theorem bupd_wand_left {P Q : PROP} : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q :=
  bupd_frame_left.trans <| mono <| wand_elim .rfl

@[rocq_alias bupd_wand_r]
theorem bupd_wand_right {P Q : PROP} : (|==> P) ∗ (P -∗ Q) ⊢ |==> Q :=
  sep_symm.trans bupd_wand_left

@[rocq_alias bupd_sep]
theorem bupd_sep {P Q : PROP} : (|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q) := calc
  _ ⊢ |==> (|==> P ∗ Q) := bupd_frame_left
  _ ⊢ |==> |==> (P ∗ Q) := mono frame_right
  _ ⊢ |==> (P ∗ Q)      := trans

@[rocq_alias bupd_idemp]
theorem bupd_idem {P : PROP} : (|==> |==> P) ⊣⊢ |==> P :=
  ⟨BIUpdate.trans, BIUpdate.intro⟩

@[rocq_alias bupd_or]
theorem bupd_or {P Q : PROP} : (|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q) :=
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
  map_op := bupd_sep
  map_unit := BIUpdate.intro

@[rocq_alias bupd_or_homomorphism]
instance bupd_or_homomorphism :
  Algebra.MonoidHomomorphism (M₁ := PROP) (M₂ := PROP) or or iprop(False) iprop(False)
    (flip Entails) bupd where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := or_mono
  map_op := bupd_or
  map_unit := BIUpdate.intro

@[rocq_alias big_sepL_bupd]
theorem BigSepL.bigSepL_bupd (Φ : Nat → A → PROP) (l : List A) :
    ([∗list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗list] k↦x ∈ l, Φ k x :=
  Algebra.BigOpL.bigOpL_hom (R := flip Entails) Φ l

@[rocq_alias big_sepM_bupd]
theorem BigSepM.bigSepM_bupd [LawfulFiniteMap M' K] (Φ : K → V → PROP) {l : M' V} :
    ([∗map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗map] k↦x ∈ l, Φ k x :=
    Algebra.BigOpM.bigOpM_hom (R := flip Entails) Φ l

@[rocq_alias big_sepM2_bupd]
theorem BigSepM2.bigSepM2_bupd [LawfulFiniteMap M' K] (Φ : K → V → W → PROP)
    {m1 : M' V} {m2 : M' W} :
    ([∗map] k↦x;y ∈ m1;m2, |==> Φ k x y) ⊢ |==> [∗map] k↦x;y ∈ m1;m2, Φ k x y :=
  BigSepM2.bigSepM2_alt.mp.trans <| pure_elim_left fun hdom =>
    (BigSepM.bigSepM_bupd _).trans <| mono <|
      (and_intro (pure_intro hdom) .rfl).trans BigSepM2.bigSepM2_alt.mpr

@[rocq_alias big_sepS_bupd]
theorem BigSepS.bigSepS_bupd [LawfulFiniteSet S A] (Φ : A → PROP) (X : S) :
    ([∗set] x ∈ X, |==> Φ x) ⊢ |==> [∗set] x ∈ X, Φ x :=
  Algebra.BigOpS.hom (R := flip Entails) bupd_sep_homomorphism Φ X

@[rocq_alias big_sepMS_bupd]
theorem BigSepMS.bigSepMS_bupd [LawfulFiniteMultiSet MS A] (Φ : A → PROP) (X : MS) :
    ([∗mset] x ∈ X, |==> Φ x) ⊢ |==> [∗mset] x ∈ X, Φ x :=
  Algebra.BigOpMS.hom (R := flip Entails) bupd_sep_homomorphism Φ X

end BUpdLaws

theorem BIBUpdatePlainly.ofSbi (SI : stepindex (Type _)) [SIdx SI] [BI PROP] [BIStepIndexed PROP]
    [Sbi PROP] [BIPlainly PROP] [BIPlainlySbi PROP] [BUpd PROP] [BIBUpdateSbi PROP] :
    BIBUpdatePlainly PROP where
  bupd_plainly {P} := by
    rw [plainly_eq_siPure_siEmpValid (SI := SI)]
    exact BIBUpdateSbi.bupd_siPure (SiEmpValid.siEmpValid P)

section BUpdPlainlyLaws

variable [BI PROP] [BIPlainly PROP] [BIUpdate PROP] [BIBUpdatePlainly PROP]
open BIUpdate

@[rocq_alias bupd_plainly]
theorem bupd_plainly {P : PROP} : (|==> ■ P) ⊢ ■ P := BIBUpdatePlainly.bupd_plainly

@[rocq_alias bupd_plainly_elim]
theorem bupd_plainly_elim {P : PROP} [Absorbing P] : (|==> ■ P) ⊢ P :=
  bupd_plainly.trans plainly_elim

@[rocq_alias bupd_elim]
theorem bupd_elim {P : PROP} [Plain P] [Absorbing P] : |==> P ⊢ P :=
  (mono (plain_plainly_2 )).trans bupd_plainly_elim

@[rocq_alias bupd_plain_forall]
theorem bupd_plain_forall (Φ : A → PROP) [∀ x, Plain (Φ x)] [∀ x, Absorbing (Φ x)] :
    (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x) := by
  refine ⟨bupd_forall, ?_⟩
  refine .trans ?_ intro
  exact (forall_intro fun a => (forall_elim a).trans (bupd_elim ))

@[rocq_alias bupd_plain]
instance bupd_plain {P : PROP} [Plain P] : Plain iprop(|==> P) where
  plain := calc
    _ ⊢ |==> ■ P := mono (plain_plainly_2 )
    _ ⊢ ■ P      := bupd_elim 
    _ ⊢ ■ |==> P := plainly_mono intro

end BUpdPlainlyLaws

section FUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

@[rocq_alias updates.fupd_ne]
instance fupd_ne [BIStepIndexed PROP] [FUpdNE PROP] {E1 E2 : CoPset} :
    OFE.NonExpansive (iprop(|={E1,E2}=> · : PROP)) := FUpdNE.fupd_ne

@[rocq_alias updates.fupd_mono]
theorem fupd_mono {E1 E2 : CoPset} {P Q : PROP} (h : P ⊢ Q) : (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q :=
  mono h

@[rocq_alias updates.fupd_trans]
theorem fupd_trans {E1 E2 E3 : CoPset} {P : PROP} : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P :=
  trans

@[rocq_alias fupd_mask_intro_subseteq]
theorem fupd_mask_intro_subseteq {E1 E2 : CoPset} {P : PROP} (h : E2 ⊆ E1) :
    P ⊢ |={E1,E2}=> |={E2,E1}=> P := calc
  P ⊢ emp ∗ P                           := emp_sep.mpr
  _ ⊢ (|={E1,E2}=> |={E2,E1}=> emp) ∗ P := sep_mono_left <| subset h
  _ ⊢ |={E1,E2}=> (|={E2,E1}=> emp) ∗ P := frame_right
  _ ⊢ |={E1,E2}=> |={E2,E1}=> P         := mono <| frame_right.trans <| mono emp_sep.mp

@[rocq_alias fupd_mask_subseteq]
theorem fupd_mask_subseteq {E1 E2 : CoPset} (h : E2 ⊆ E1) : ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp :=
  fupd_mask_intro_subseteq h

@[rocq_alias fupd_mask_frame_r']
theorem fupd_mask_frame_right_strong {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P :=
  mask_frame_right_strong

@[rocq_alias updates.fupd_intro]
theorem fupd_intro {E : CoPset} {P : PROP} : P ⊢ |={E}=> P :=
  (fupd_mask_intro_subseteq fun _ => id).trans trans

@[rocq_alias fupd_mask_intro]
theorem fupd_mask_intro {E1 E2 : CoPset} {P : PROP} (h : E2 ⊆ E1) :
    ((|={E2,E1}=> emp) -∗ P) ⊢ |={E1,E2}=> P := calc
  _ ⊢ (|={E2,E1}=> emp) ={E2}=∗ P                                     := wand_mono_right fupd_intro
  _ ⊢ emp ∗ ((|={E2,E1}=> emp) ={E2}=∗ P)                             := emp_sep.mpr
  _ ⊢ (|={E1,E2}=> |={E2,E1}=> emp) ∗ ((|={E2,E1}=> emp) ={E2}=∗ P)   := sep_mono_left <| subset h
  _ ⊢ (|={E1,E2}=> (|={E2,E1}=> emp) ∗ ((|={E2,E1}=> emp) ={E2}=∗ P)) := frame_right
  _ ⊢ |={E1,E2}=> |={E2}=> P                                          := mono wand_elim_right
  _ ⊢ |={E1,E2}=> P                                                   := trans

@[rocq_alias fupd_mask_intro_discard]
theorem fupd_mask_intro_discard {E1 E2 : CoPset} {P : PROP} [Absorbing P] (h : E2 ⊆ E1) :
    P ⊢ |={E1,E2}=> P :=
  (wand_intro_left sep_elim_right).trans <| fupd_mask_intro h

@[rocq_alias fupd_elim]
theorem fupd_elim {E1 E2 E3 : CoPset} {P Q : PROP} (h : Q ⊢ |={E2,E3}=> P) :
    (|={E1,E2}=> Q) ⊢ |={E1,E3}=> P :=
  (mono h).trans trans

@[rocq_alias updates.fupd_frame_r]
theorem fupd_frame_right {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ Q ⊢ |={E1,E2}=> P ∗ Q :=
  frame_right

@[rocq_alias fupd_frame_l]
theorem fupd_frame_left {E1 E2 : CoPset} {P Q : PROP} :
    P ∗ (|={E1,E2}=> Q) ⊢ |={E1,E2}=> P ∗ Q := calc
  _ ⊢ (|={E1,E2}=> Q) ∗ P := sep_symm
  _ ⊢ |={E1,E2}=> Q ∗ P   := fupd_frame_right
  _ ⊢ |={E1,E2}=> P ∗ Q   := mono sep_symm

@[rocq_alias fupd_wand_l]
theorem fupd_wand_left {E1 E2 : CoPset} {P Q : PROP} : (P -∗ Q) ∗ (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q :=
  fupd_frame_left.trans <| mono <| wand_elim .rfl

@[rocq_alias fupd_wand_r]
theorem fupd_wand_right {E1 E2 : CoPset} {P Q : PROP} : (|={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |={E1,E2}=> Q :=
  sep_symm.trans fupd_wand_left

@[rocq_alias fupd_sep]
theorem fupd_sep {E : CoPset} {P Q : PROP} : (|={E}=> P) ∗ (|={E}=> Q) ⊢ |={E}=> P ∗ Q := calc
  _ ⊢ |={E}=> (|={E}=> P) ∗ Q := fupd_frame_left
  _ ⊢ |={E}=> |={E}=> P ∗ Q   := mono frame_right
  _ ⊢ |={E}=> P ∗ Q           := trans

@[rocq_alias fupd_mask_weaken]
theorem fupd_mask_weaken {E1 E3 : CoPset} (E2 : CoPset) {P : PROP} (h : E2 ⊆ E1) :
    ((|={E2,E1}=> emp) ={E2,E3}=∗ P) ⊢ |={E1,E3}=> P := by
  calc
    _ ⊢ emp ∗ ((|={E2,E1}=> emp) ={E2,E3}=∗ P)                             := emp_sep.mpr
    _ ⊢ (|={E1,E2}=> |={E2,E1}=> emp) ∗ ((|={E2,E1}=> emp) ={E2,E3}=∗ P)   := sep_mono_left <| fupd_mask_subseteq h
    _ ⊢ (|={E1,E2}=> (|={E2,E1}=> emp) ∗ ((|={E2,E1}=> emp) ={E2,E3}=∗ P)) := frame_right
    _ ⊢ |={E1,E2}=> |={E2,E3}=> P                                          := mono wand_elim_right
    _ ⊢ |={E1,E3}=> P                                                      := trans

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
    (|={E1,E2}=> «forall» fun a : A => Φ a) ⊢ «forall» fun a : A => iprop(|={E1,E2}=> Φ a) :=
  forall_intro (mono <| forall_elim ·)

@[rocq_alias except_0_fupd]
theorem except0_fupd {E1 E2 : CoPset} {P : PROP} : (◇ |={E1,E2}=> P) ⊢ |={E1,E2}=> ◇ P :=
  except0.trans (mono except0_intro)

@[rocq_alias fupd_except_0]
theorem fupd_except0 {E1 E2 : CoPset} {P : PROP} : (|={E1,E2}=> ◇ P) ⊢ |={E1,E2}=> P := calc
  _ ⊢ |={E1,E2}=> ◇ |={E2}=> P := mono <| except0_mono fupd_intro
  _ ⊢ |={E1,E2}=> |={E2}=> P    := mono except0
  _ ⊢ |={E1,E2}=> P             := trans

@[rocq_alias fupd_absorbing]
instance {E1 E2 : CoPset} {P : PROP} [Absorbing P] : Absorbing iprop(|={E1,E2}=> P) :=
  ⟨fupd_frame_left.trans <| mono sep_elim_right⟩

@[rocq_alias updates.fupd_mask_frame_r]
theorem fupd_mask_frame_right {E1 E2 Ef : CoPset} {P : PROP} :
    E1 ## Ef → (|={E1,E2}=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P :=
  fun h => (mono <| imp_intro_swap and_elim_r).trans <| mask_frame_right_strong h

@[rocq_alias fupd_mask_mono]
theorem fupd_mask_mono {E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E2 → (|={E1}=> P) ⊢ |={E2}=> P :=
  fun h => by simpa [subset_union_diff h] using
    (fupd_mask_frame_right (E2 := E1) (Ef := E2 \ E1) disjoint_diff_right)

@[rocq_alias fupd_mask_frame]
theorem fupd_mask_frame {E E' E1 E2 : CoPset} {P : PROP} :
    E1 ⊆ E → (|={E1,E2}=> |={E2 ∪ (E \ E1),E'}=> P) ⊢ |={E,E'}=> P :=
  fun h => by simpa [subset_union_diff h] using
    ((fupd_mask_frame_right (P := iprop(|={E2 ∪ (E \ E1),E'}=> P)) disjoint_diff_right).trans trans)

/-- A variant of [fupd_mask_frame] that works well for accessors:
  Tailored to eliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to transform the
  closing view shift instead of letting you prove the same side-conditions twice. -/
@[rocq_alias fupd_mask_frame_acc]
theorem fupd_mask_frame_acc {E E' E1 E2 : CoPset} {P Q : PROP} :
    E1 ⊆ E → (|={E1,E1 \ E2}=> Q) ⊢
    (Q -∗ |={E \ E2,E'}=> (∀ R, (|={E1 \ E2,E1}=> R) -∗ |={E \ E2,E}=> R) -∗ P) -∗
    (|={E,E'}=> P) := fun hE => by
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
  refine (sep_mono_left ?_).trans wand_elim_right
  refine forall_intro fun R => wand_intro <| frame_right.trans <| fupd_elim ?_
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
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ⊢ |={E1,E3}=> P := by
  refine fupd_frame_left.trans <| fupd_elim ?_
  calc
    _ ⊢ ((Q ={E2,E3}=∗ emp) ∗ Q) ∗ P := sep_assoc.mpr
    _ ⊢ (Q ∗ (Q ={E2,E3}=∗ emp)) ∗ P := sep_mono_left sep_comm.mp
    _ ⊢ (|={E2,E3}=> emp) ∗ P        := sep_mono_left wand_elim_right
    _ ⊢ |={E2,E3}=> emp ∗ P          := frame_right
    _ ⊢ |={E2,E3}=> P                := mono <| emp_sep.mp

@[rocq_alias fupd_sep_homomorphism]
instance fupd_sep_homomorphism E :
  Algebra.MonoidHomomorphism (M₁ := PROP) sep sep emp emp (flip Entails) (fupd E E) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := sep_mono
  map_op := fupd_sep
  map_unit := fupd_intro

@[rocq_alias fupd_or_homomorphism]
instance fupd_or_homomorphism E :
  Algebra.MonoidHomomorphism (M₁ := PROP) (M₂ := PROP) or or iprop(False) iprop(False)
    (flip Entails) (fupd E E) where
  rel_refl := .rfl
  rel_trans := flip .trans
  op_proper := or_mono
  map_op := fupd_or
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

@[rocq_alias big_sepM2_fupd]
theorem BigSepM2.bigSepM2_fupd [LawfulFiniteMap M' K] E (Φ : K → V → W → PROP)
    (m1 : M' V) (m2 : M' W) :
    ([∗map] k↦x;y ∈ m1;m2, |={E}=> Φ k x y) ⊢ |={E}=> [∗map] k↦x;y ∈ m1;m2, Φ k x y :=
  BigSepM2.bigSepM2_alt.mp.trans <| pure_elim_left fun hdom =>
    (BigSepM.bigSepM_fupd E _ _).trans <| mono <|
      (and_intro (pure_intro hdom) .rfl).trans BigSepM2.bigSepM2_alt.mpr

@[rocq_alias big_sepS_fupd]
theorem BigSepS.bigSepS_fupd [LawfulFiniteSet S A] E (Φ : A → PROP) (X : S) :
    ([∗set] x ∈ X, |={E}=> Φ x) ⊢ |={E}=> [∗set] x ∈ X, Φ x :=
  Algebra.BigOpS.hom (R := flip Entails) (fupd_sep_homomorphism E) Φ X

@[rocq_alias big_sepMS_fupd]
theorem BigSepMS.bigSepMS_fupd [LawfulFiniteMultiSet MS A] E (Φ : A → PROP) (X : MS) :
    ([∗mset] x ∈ X, |={E}=> Φ x) ⊢ |={E}=> [∗mset] x ∈ X, Φ x :=
  Algebra.BigOpMS.hom (R := flip Entails) (fupd_sep_homomorphism E) Φ X

#rocq_ignore fupd_mono' "Use fupd_mono."
#rocq_ignore fupd_flip_mono' "Use fupd_mono."
#rocq_ignore fupd_proper "Derivable from FUpdNE.fupd_ne with NonExpansive.eqv"

end FUpdLaws

section StepFUpdLaws

variable [BI PROP] [BIFUpdate PROP]

open BIFUpdate LawfulSet

theorem step_fupdN_contractive [BIStepIndexed PROP] [FUpdNE PROP] {E1 E2 : CoPset} {n : Nat}
    [ι : BILaterContractive PROP] :
    OFE.Contractive (iprop(|={E1}[E2]▷=>^[n + 1] · : PROP)) where
  distLater_dist {i x y} xy_i := by
    induction n with
    | zero => exact fupd_ne.ne (ι.distLater_dist (fupd_ne.ne <| xy_i · ·))
    | succ n IH => exact fupd_ne.ne (later_ne.ne (fupd_ne.ne IH))

@[rocq_alias step_fupdN_ne]
instance step_fupdN_ne [BIStepIndexed PROP] [FUpdNE PROP] {E1 E2 : CoPset} {n : Nat} :
    OFE.NonExpansive (iprop(|={E1}[E2]▷=>^[n] · : PROP)) where
  ne {i x y} xy_i := by
    induction n with
    | zero => exact xy_i
    | succ n IH => exact fupd_ne.ne (later_ne.ne (fupd_ne.ne IH))

#rocq_ignore step_fupdN_proper "Derivable from step_fupdN_ne with NonExpansive.eqv"

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
      _ ⊢ |={Eo,Ei}=> ▷ ((P -∗ Q) ∗ |={Ei,Eo}=> _) := mono (later_sep_2)
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
  refine (sep_mono_left (fupd_mask_intro_subseteq Eo₁_Eo₂)).trans ?_
  refine frame_right.trans ?_
  refine .trans (mono ?_) (trans (E2 := Eo₁))
  refine fupd_frame_left.trans ?_
  refine .trans (mono ?_) (trans (E2 := Ei₁))
  refine (sep_mono_left (fupd_mask_intro_subseteq Ei₂_Ei₁)).trans ?_
  refine frame_right.trans ?_
  refine mono ?_
  refine (sep_mono_left later_intro).trans ?_
  refine later_sep_2.trans ?_
  refine later_mono ?_
  refine frame_right.trans ?_
  refine .trans (mono ?_) (trans (E2 := Ei₁))
  refine fupd_frame_left.trans ?_
  refine .trans (mono ?_) (trans (E2 := Eo₁))
  refine frame_right.trans ?_
  exact mono emp_sep.1

@[rocq_alias step_fupd_mask_frame_r]
theorem step_fupd_mask_frame_right {Eo Ei Ef : CoPset} {P : PROP}
    (hEo : Eo ## Ef) (hEi : Ei ## Ef) :
    (|={Eo}[Ei]▷=> P) ⊢ |={Eo ∪ Ef}[Ei ∪ Ef]▷=> P :=
  (mono <| later_mono <| fupd_mask_frame_right hEi).trans (fupd_mask_frame_right hEo)

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
  | n+1 =>
    calc
      _ ⊢ ▷ ▷^[n] P                         := (laterN_succ_left n).mp
      _ ⊢ |={Eo}[Ei]▷=> ▷^[n] P             := step_fupd_intro Ei_Eo
      _ ⊢ |={Eo}[Ei]▷=> |={Eo}[Ei]▷=>^[n] P := step_fupd_mono <| step_fupdN_intro Ei_Eo

@[rocq_alias step_fupdN_le]
theorem step_fupdN_le {n m : Nat} {Eo Ei : CoPset} {P : PROP} :
    n ≤ m → Ei ⊆ Eo → (|={Eo}[Ei]▷=>^[n] P) ⊢ |={Eo}[Ei]▷=>^[m] P
  | .refl, _ => .rfl
  | .step (m := m) n_m, Ei_Eo =>
    calc
      _ ⊢ |={Eo}[Ei]▷=>^[m] P                := step_fupdN_le n_m Ei_Eo
      _ ⊢ (▷ |={Eo}[Ei]▷=>^[m] P)           := later_intro
      _ ⊢ |={Eo}[Ei]▷=> |={Eo}[Ei]▷=>^[m] P := step_fupd_intro Ei_Eo

@[rocq_alias step_fupd_fupd]
theorem step_fupd_fupd {Eo Ei : CoPset} {P : PROP} : (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P) :=
  ⟨step_fupd_mono fupd_intro, mono <| later_mono BIFUpdate.trans⟩

@[rocq_alias step_fupdN_mono]
theorem step_fupdN_mono {n : Nat} {Eo Ei : CoPset} {P Q : PROP} (H : P ⊢ Q) :
    (|={Eo}[Ei]▷=>^[n] P) ⊢ (|={Eo}[Ei]▷=>^[n] Q) := by
  induction n with
  | zero => exact H
  | succ k IH => exact step_fupd_mono IH

#rocq_ignore step_fupdN_mono' "Use step_fupdN_mono."
#rocq_ignore step_fupdN_flip_mono "Use step_fupdN_mono."

@[rocq_alias step_fupdN_0]
theorem step_fupdN_0 {Eo Ei : CoPset} {P : PROP} : (|={Eo}[Ei]▷=>^[0] P) ⊣⊢ P := .rfl

@[rocq_alias step_fupdN_1]
theorem step_fupdN_1 {Eo Ei : CoPset} {P : PROP} : (|={Eo}[Ei]▷=>^[1] P) ⊣⊢ |={Eo}[Ei]▷=> P := .rfl

@[rocq_alias step_fupdN_succ_l]
theorem step_fupdN_succ_l {n : Nat} {Eo Ei : CoPset} {P : PROP} :
    (|={Eo}[Ei]▷=>^[n + 1] P) ⊣⊢ |={Eo}[Ei]▷=> |={Eo}[Ei]▷=>^[n] P := .rfl

@[rocq_alias step_fupdN_succ_r]
theorem step_fupdN_succ_r {n : Nat} {Eo Ei : CoPset} {P : PROP} :
    (|={Eo}[Ei]▷=>^[n + 1] P) ⊣⊢ |={Eo}[Ei]▷=>^[n] |={Eo}[Ei]▷=> P := by
  induction n with
  | zero => exact .rfl
  | succ n IH => exact ⟨step_fupd_mono IH.1, step_fupd_mono IH.2⟩

@[rocq_alias step_fupdN_add]
theorem step_fupdN_add {n m : Nat} {Eo Ei : CoPset} {P : PROP} :
    (|={Eo}[Ei]▷=>^[n + m] P) ⊣⊢ (|={Eo}[Ei]▷=>^[n] |={Eo}[Ei]▷=>^[m] P) := by
  induction n with
  | zero => rw [Nat.zero_add]; exact .rfl
  | succ n IH =>
    rw [Nat.add_right_comm n 1 m]
    exact ⟨step_fupd_mono IH.1, step_fupd_mono IH.2⟩

@[rocq_alias step_fupdN_S_fupd]
theorem step_fupdN_S_fupd {n : Nat} {E : CoPset} {P : PROP} :
    (|={E}[∅]▷=>^[n + 1] P) ⊣⊢ (|={E}[∅]▷=>^[n + 1] |={E}=> P) :=
  calc
    _ ⊣⊢ |={E}[∅]▷=>^[n] |={E}[∅]▷=> P := step_fupdN_succ_r
    _ ⊣⊢ |={E}[∅]▷=>^[n] |={E}[∅]▷=> |={E}=> P :=
      ⟨step_fupdN_mono step_fupd_fupd.1, step_fupdN_mono step_fupd_fupd.2⟩
    _ ⊣⊢ _ := step_fupdN_succ_r.symm

@[rocq_alias step_fupd_frame_l]
theorem step_fupd_frame_left {Eo Ei : CoPset} {R Q : PROP} :
    (R ∗ |={Eo}[Ei]▷=> Q) ⊢ |={Eo}[Ei]▷=> (R ∗ Q) := by
  refine fupd_frame_left.trans <| mono ?_
  calc
    _ ⊢ ▷ R ∗ ▷ |={Ei,Eo}=> Q := sep_mono_left later_intro
    _ ⊢ ▷ (R ∗ |={Ei,Eo}=> Q)  := later_sep_2
    _ ⊢ ▷ |={Ei,Eo}=> R ∗ Q    := later_mono fupd_frame_left

@[rocq_alias step_fupdN_frame_l]
theorem step_fupdN_frame_left {Eo Ei : CoPset} {n : Nat} {R Q : PROP} :
    (R ∗ |={Eo}[Ei]▷=>^[n] Q) ⊢ |={Eo}[Ei]▷=>^[n] (R ∗ Q) := by
  induction n with
  | zero => exact .rfl
  | succ n IH => exact step_fupd_frame_left.trans (mono <| later_mono <| mono IH)

end StepFUpdLaws

section FUpdSbiLaws

variable [BI PROP] [BIStepIndexed PROP] [Sbi PROP] [BIFUpdate PROP] [BIFUpdateSbi PROP]

open BIFUpdate BIFUpdateSbi

@[rocq_alias fupd_keep_si_pure]
theorem fupd_keep_siPure {E1 E2 : CoPset} E2' (Pi : SiProp) {R : PROP} :
    (|={E1,E2'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R := calc
  _ ⊢ (|={E1, E2'}=> <si_pure> Pi) ∧ (<si_pure> Pi ={E1}=∗ |={E1, E2}=> R) :=
      and_mono_right <| wand_mono_right fupd_intro
  _ ⊢ |={E1}=> |={E1, E2}=> R :=
      BIFUpdateSbi.fupd_keep_siPure E2' Pi iprop(|={E1,E2}=> R)
  _ ⊢ |={E1, E2}=> R := trans

omit [BIFUpdate PROP] [BIFUpdateSbi PROP] in
theorem sForall_eq_forall {Φ : α → PROP} :
    sForall (fun p => ∃ a, p = Φ a) ⊣⊢ ∀ a, Φ a :=
  ⟨forall_intro fun a => sForall_elim ⟨a, rfl⟩,
   sForall_intro fun _ ⟨a, hp⟩ => hp ▸ forall_elim a⟩

/--
  Proves that the Rocq class field `fupd_si_pure_forall_2` for `BIFUpdSbi`
  follows from `BIFUpdateSbi.fupd_siPure_sForall_2`.
-/
theorem fupd_siPure_forall_2 {E : CoPset} {A : Sort _} {Φi : A → SiProp} :
    (∀ x, |={E}=> <si_pure> Φi x) ⊢@{PROP} |={E}=> ∀ x, <si_pure> Φi x := calc
  _ ⊢ ∀ q, ⌜∃ x, q = Φi x⌝ → |={E}=> <si_pure> q :=
      forall_intro fun _ => imp_intro_swap <| pure_elim_left fun ⟨x, hx⟩ => hx ▸ forall_elim x
  _ ⊢@{PROP} |={E}=> <si_pure> (sForall fun q => ∃ x, q = Φi x) :=
      BIFUpdateSbi.fupd_siPure_sForall_2 E _
  _ ⊢ |={E}=> ∀ x, <si_pure> Φi x :=
      mono <| forall_intro fun x => siPure_mono (sForall_elim ⟨x, rfl⟩)

end FUpdSbiLaws

/-- The plain fancy-update laws of an affine `Sbi` with `BIFUpdateSbi`. -/
theorem BIFUpdatePlainly.ofSbi (SI : stepindex (Type _)) [SIdx SI] [BI PROP] [BIAffine PROP]
    [BIStepIndexed SI PROP] [Sbi SI PROP] [BIPlainly PROP] [BIPlainlySbi SI PROP]
    [BIFUpdate PROP] [BIFUpdateSbi SI PROP] : BIFUpdatePlainly PROP where
  fupd_keep_plainly E2' P R := by
    rw [plainly_eq_siPure_siEmpValid (SI := SI)]
    exact (and_mono_right (wand_mono_left siPure_siEmpValid_elim)).trans <|
      fupd_keep_siPure E2' (SiEmpValid.siEmpValid P)
  fupd_plainly_later E P := by
    rw [plainly_eq_siPure_siEmpValid (SI := SI)]
    exact (BIFUpdateSbi.fupd_siPure_later E iprop(<si_emp_valid> P)).trans <|
      BIFUpdate.mono <| later_mono <| except0_mono siPure_siEmpValid_elim
  fupd_plainly_sForall_2 E Φ := by
    rw [plainly_eq_siPure_siEmpValid (SI := SI)]
    calc iprop(∀ p, ⌜Φ p⌝ → |={E}=> <si_pure> (<si_emp_valid> p : SiProp (SI := SI)))
      _ ⊢ ∀ x : {p : PROP // Φ p}, |={E}=> <si_pure> (<si_emp_valid> x.1 : SiProp (SI := SI)) :=
          forall_intro fun x => (forall_elim x.1).trans (pure_imp_elim x.2)
      _ ⊢ |={E}=> ∀ x : {p : PROP // Φ p}, <si_pure> (<si_emp_valid> x.1 : SiProp (SI := SI)) :=
          fupd_siPure_forall_2
      _ ⊢ |={E}=> sForall Φ := BIFUpdate.mono <| sForall_intro fun p hp =>
          (forall_elim (⟨p, hp⟩ : {p // Φ p})).trans siPure_siEmpValid_elim

section StepFUpdPlainlyLaws

variable [BI PROP] [BIPlainly PROP] [BIFUpdate PROP] [BIFUpdatePlainly PROP]

open BIFUpdate

@[rocq_alias fupd_keep_plainly]
theorem fupd_keep_plainly {E1 E2 : CoPset} E2' (P : PROP) {R : PROP} :
  (|={E1,E2'}=> ■ P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R :=
  BIFUpdatePlainly.fupd_keep_plainly E2' P R

@[rocq_alias fupd_plainly_later]
theorem fupd_plainly_later (E : CoPset) (P : PROP) :
    (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P :=
  BIFUpdatePlainly.fupd_plainly_later E P

@[rocq_alias fupd_keep_plain]
theorem fupd_keep_plain {E1 E2 : CoPset} E2' (P R : PROP) [Plain P] :
  (|={E1,E2'}=> P) ∧ (P ={E1,E2}=∗ R) ⊢ |={E1,E2}=> R :=
  (and_mono_left (mono (plain_plainly_2 ))).trans (fupd_keep_plainly E2' P)

@[rocq_alias fupd_plainly_mask]
theorem fupd_plainly_mask [BIAffine PROP] E E' {P : PROP} : (|={E,E'}=> ■ P) ⊢ |={E}=> P :=
  (and_intro .rfl (wand_intro_left (sep_elim_left.trans fupd_intro))).trans <|
    fupd_keep_plainly E' P

@[rocq_alias fupd_plain_mask]
theorem fupd_plain_mask [BIAffine PROP] {E E' : CoPset} {P : PROP} [Plain P] :
    (|={E,E'}=> P) ⊢ |={E}=> P :=
  (mono (plain_plainly_2 )).trans (fupd_plainly_mask E E')

@[rocq_alias fupd_plain_later]
theorem fupd_plain_later {E : CoPset} {P : PROP} [Plain P] : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P :=
  (later_mono (mono (plain_plainly_2 ))).trans (fupd_plainly_later E P)

@[rocq_alias fupd_plainly_laterN]
theorem fupd_plainly_laterN [BIAffine PROP] (E : CoPset) (n : Nat) (P : PROP) :
    (▷^[n] |={E}=> ■ P) ⊢ |={E}=> ▷^[n] ◇ P := by
  induction n generalizing P with
  | zero => exact mono <| plainly_elim.trans except0_intro
  | succ n ih => calc
    _ ⊢ ▷^[n] ▷ |={E}=> ■ P   := (laterN_succ_right n).mp
    _ ⊢ ▷^[n] ▷ |={E}=> ■ ■ P := laterN_mono n <| later_mono <| mono plainly_idem.mpr
    _ ⊢ ▷^[n] |={E}=> ▷ ◇ ■ P := laterN_mono n <| fupd_plainly_later E iprop(■ P)
    _ ⊢ ▷^[n] |={E}=> ▷ ■ ◇ P := laterN_mono n <| mono <| later_mono except0_plainly.mp
    _ ⊢ ▷^[n] |={E}=> ■ ▷ ◇ P := laterN_mono n <| mono later_plainly_mp
    _ ⊢ |={E}=> ▷^[n] ◇ ▷ ◇ P := ih iprop(▷ ◇ P)
    _ ⊢ |={E}=> ▷^[n] ▷ ◇ P   := mono <| laterN_mono n except0_later
    _ ⊢ |={E}=> ▷^[n + 1] ◇ P := mono (laterN_succ_right n).mpr

@[rocq_alias fupd_plain_laterN]
theorem fupd_plain_laterN [BIAffine PROP] {E : CoPset} {n : Nat} {P : PROP} [Plain P] :
    (▷^[n] |={E}=> P) ⊢ |={E}=> ▷^[n] ◇ P :=
  (laterN_mono n <| mono (plain_plainly_2 )).trans (fupd_plainly_laterN E n P)

@[rocq_alias fupd_keep_plain_sep]
theorem fupd_keep_plain_sep [BIAffine PROP] {E E' : CoPset} {P R : PROP} [Plain P] :
    (R ={E,E'}=∗ P) -∗ R -∗ |={E}=> P ∗ R :=
  entails_wand <| wand_intro <|
    (and_intro wand_elim_left (sep_elim_right.trans (wand_intro_left fupd_intro))).trans
      (fupd_keep_plain  (E1 := E) (E2 := E) E' P iprop(P ∗ R))

@[rocq_alias step_fupd_plain]
theorem step_fupd_plain [BIAffine PROP] {E1 E2 : CoPset} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=> P) ⊢ |={E1}=> ▷ ◇ P :=
  (fupd_elim <| (later_mono (fupd_plain_mask )).trans
    (fupd_plain_later )).trans (fupd_plain_mask )

@[rocq_alias step_fupdN_plain]
theorem step_fupdN_plain [BIAffine PROP] {E1 E2 : CoPset} {n : Nat} {P : PROP} [Plain P] :
    (|={E1}[E2]▷=>^[n] P) ⊢ |={E1}=> ▷^[n] ◇ P := by
  induction n with
  | zero => exact except0_intro.trans fupd_intro
  | succ n ih =>
    calc
      _ ⊢ |={E1}[E2]▷=> |={E1}=> ▷^[n] ◇ P := step_fupd_mono ih
      _ ⊢ |={E1}[E2]▷=> ▷^[n] ◇ P          := step_fupd_fupd.mpr
      _ ⊢ |={E1}=> ▷ ◇ ▷^[n] ◇ P          := step_fupd_plain 
      _ ⊢ |={E1}=> ▷ ▷^[n] ◇ ◇ P          := mono <| later_mono <| except0_laterN n
      _ ⊢ |={E1}=> ▷^[n + 1] ◇ P            := mono <| laterN_mono (n + 1) except0_idem.mp

@[rocq_alias fupd_plainly_forall_2]
theorem fupd_plainly_forall_2 {E : CoPset} {Φ : α → PROP} :
    (∀ a, |={E}=> ■ Φ a) ⊢ |={E}=> ∀ a, Φ a :=
  (forall_intro fun _ => imp_intro_swap <| pure_elim_left fun ⟨a, ha⟩ => ha ▸ forall_elim a).trans
    (BIFUpdatePlainly.fupd_plainly_sForall_2 E _)

@[rocq_alias fupd_plain_forall_2]
theorem fupd_plain_forall_2 {E : CoPset} {Φ : α → PROP} [∀ a, Plain (Φ a)] :
    (∀ a, |={E}=> Φ a) ⊢ |={E}=> ∀ a, Φ a :=
  (forall_mono fun _ => mono (plain_plainly_2 )).trans fupd_plainly_forall_2

@[rocq_alias fupd_plain_forall]
theorem fupd_plain_forall [BIAffine PROP] {E1 E2 : CoPset} {Φ : α → PROP}
    [inst : ∀ a, Plain (Φ a)] (h : E2 ⊆ E1) :
    (|={E1,E2}=> ∀ a, Φ a) ⊣⊢ ∀ a, |={E1,E2}=> Φ a := by
  constructor
  · exact fupd_forall
  · calc
      _ ⊢ ∀ a, |={E1}=> Φ a    := forall_mono fun _ => fupd_plain_mask 
      _ ⊢ |={E1}=> ∀ a, Φ a    := fupd_plain_forall_2 
      _ ⊢ |={E1,E2}=> ∀ a, Φ a := fupd_elim ?_
    calc
      _ ⊢ ■ (∀ a, Φ a)             := Plain.plain
      _ ⊢ |={E1,E2}=> ■ (∀ a, Φ a) := fupd_mask_intro_discard h
      _ ⊢ |={E1,E2}=> |={E2}=> _   := mono <| fupd_intro.trans <| fupd_plainly_mask E2 E2
      _ ⊢ |={E1,E2}=> ∀ a, Φ a     := trans

@[rocq_alias fupd_plain_forall']
theorem fupd_plain_forall' [BIAffine PROP] {E : CoPset} {Φ : α → PROP} [∀ a, Plain (Φ a)] :
    (|={E}=> ∀ a, Φ a) ⊣⊢ ∀ a, |={E}=> Φ a :=
  fupd_plain_forall  LawfulSet.subset_refl

@[rocq_alias step_fupd_plain_forall]
theorem step_fupd_plain_forall [BIAffine PROP] {Eo Ei : CoPset} {Φ : α → PROP}
    [∀ a, Plain (Φ a)] (h : Ei ⊆ Eo) :
    (|={Eo}[Ei]▷=> ∀ a, Φ a) ⊣⊢ ∀ a, |={Eo}[Ei]▷=> Φ a := by
  constructor
  · exact forall_intro fun a => step_fupd_mono (forall_elim a)
  · calc
      _ ⊢ ∀ a, |={Eo}=> ▷ ◇ Φ a := forall_mono fun _ => step_fupd_plain 
      _ ⊢ |={Eo}=> ∀ a, ▷ ◇ Φ a := (fupd_plain_forall  LawfulSet.subset_refl).mpr
      _ ⊢ |={Eo}[Ei]▷=> ∀ a, Φ a := fupd_elim ?_
    calc
      _ ⊢ ▷ ∀ a, ◇ Φ a              := later_forall.mpr
      _ ⊢ ▷ ◇ ∀ a, Φ a              := later_mono except0_forall.mpr
      _ ⊢ |={Eo}[Ei]▷=> ◇ ∀ a, Φ a  := step_fupd_intro h
      _ ⊢ |={Eo}[Ei]▷=> ∀ a, Φ a     := mono <| later_mono fupd_except0

end StepFUpdPlainlyLaws

end Iris
