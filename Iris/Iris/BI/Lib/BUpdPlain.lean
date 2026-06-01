module

public import Iris.Std
public import Iris.BI
public import Iris.Algebra.Updates
public import Iris.ProofMode.Classes
public import Iris.ProofMode.Tactics
public import Iris.ProofMode.Display
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

namespace Iris
open Iris.Std BI

/-! This file contains an alternative version of basic updates.

Namely, this definition is an expression in terms of the plain modality [■],
which can be used to instantiate BUpd for any Sbi BI.

cf. https://gitlab.mpi-sws.org/iris/iris/merge_requests/211
-/

namespace BUpdPlain

@[rocq_alias bupd_alt]
def BUpdPlain [BIBase PROP] [BIBase.Plainly PROP] (P : PROP) : PROP :=
  iprop(∀ R, (P -∗ ■ R) -∗ ■ R)

section BupdPlainDef

open OFE

variable [Sbi PROP]

@[rocq_alias bupd_alt_ne]
instance BUpdPlain_ne : NonExpansive (BUpdPlain (PROP := PROP)) where
  ne _ _ _ H := forall_ne fun _ => wand_ne.ne (wand_ne.ne H .rfl) .rfl

@[rocq_alias bupd_alt_intro]
theorem BUpdPlain_intro {P : PROP} : P ⊢ BUpdPlain P := by
  iintro Hp
  unfold BUpdPlain
  iintro %_ H
  iapply H $$ Hp

@[rocq_alias bupd_alt_mono]
theorem BUpdPlain_mono {P Q : PROP} : (P ⊢ Q) → (BUpdPlain P ⊢ BUpdPlain Q) := by
  intros H
  unfold BUpdPlain
  iintro R %HQR Hp
  iapply R
  iintro HP
  iapply Hp
  iapply H $$ HP

@[rocq_alias bupd_alt_trans]
theorem BUpdPlain_idem {P : PROP} : BUpdPlain (BUpdPlain P) ⊢ BUpdPlain P := by
  unfold BUpdPlain
  iintro Hp %R H
  iapply Hp
  iintro Hp
  iapply Hp $$ H

@[rocq_alias bupd_alt_frame_r]
theorem BUpdPlain_frame_right {P Q : PROP} : BUpdPlain P ∗ Q ⊢ (BUpdPlain iprop(P ∗ Q)) := by
  unfold BUpdPlain
  iintro ⟨Hp, Hq⟩ %R H
  iapply Hp
  iintro Hp
  iapply H
  isplitl [Hp]
  · iexact Hp
  · iexact Hq

@[rocq_alias bupd_alt_plainly]
theorem BUpdPlain_plainly {P : PROP} : BUpdPlain iprop(■ P) ⊢ (■ P) := by
  unfold BUpdPlain
  iintro H
  iapply H
  iapply wand_rfl

/- BiBUpdPlainly entails the alternative definition -/
@[rocq_alias bupd_bupd_alt]
theorem BUpd_BUpdPlain [BIUpdate PROP] [BIBUpdateSbi PROP] [BIAffine PROP] {P : PROP} : (|==> P) ⊢ BUpdPlain P := by
  unfold BUpdPlain
  iintro HP %_ Hx
  imod HP
  iapply Hx $$ HP

-- FIXME: @[rocq_alias own_updateP] duplicate alias
/-- We get the usual rule for frame preserving updates if we have an [own]
  connective satisfying the following rule w.r.t. interaction with plainly. -/
theorem own_updateP [UCMRA M] {own : M → PROP} {x : M} {Φ : M → Prop}
  (own_updateP_plainly : ∀ (x : M) (Φ : M → Prop) (R : PROP),
    (x ~~>: Φ) → own x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R)
  (Hup : x ~~>: Φ) :
    own x ⊢ BUpdPlain iprop(∃ y, ⌜Φ y⌝ ∧ own y) := by
  iintro Hx
  unfold BUpdPlain
  iintro %R H
  iapply own_updateP_plainly x Φ R Hup
  isplitl [Hx]
  · iexact Hx
  iintro %y %HΦ Hy
  iapply H
  iexists y
  isplit
  · ipure_intro
    exact HΦ
  · iexact Hy

end BupdPlainDef
end BUpdPlain
