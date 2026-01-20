import Iris.Std
import Iris.BI
import Iris.Algebra.Updates
import Iris.ProofMode.Classes
import Iris.ProofMode.Tactics
import Iris.ProofMode.Display

namespace Iris
open Iris.Std BI

/-! This file contains an alternative version of basic updates.

Namely, this definition is an expression in terms of the plain modality [■],
which can be used to instanstiate BUpd for any BIPlainly BI.

cf. https://gitlab.mpi-sws.org/iris/iris/merge_requests/211
-/

namespace BUpdPlain

def BUpdPlain [BIBase PROP] [Plainly PROP] (P : PROP) : PROP :=
  iprop(∀ R, (P -∗ ■ R) -∗ ■ R)

section BupdPlainDef

open OFE

variable [BI PROP] [BIPlainly PROP]

instance BUpdPlain_ne : NonExpansive (BUpdPlain (PROP := PROP)) where
  ne _ _ _ H := forall_ne fun _ => wand_ne.ne (wand_ne.ne H .rfl) .rfl

theorem BUpdPlain_intro {P : PROP} : P ⊢ BUpdPlain P := by
  iintro Hp
  unfold BUpdPlain
  iintro _ H
  iapply H $$ Hp

theorem BUpdPlain_mono {P Q : PROP} : (P ⊢ Q) → (BUpdPlain P ⊢ BUpdPlain Q) := by
  intros H
  unfold BUpdPlain
  iintro R HQR
  iintro Hp
  have H1 : ⊢ iprop(Q -∗ ■ HQR) -∗ iprop(P -∗ ■ HQR) := by
    iintro H Hp
    iapply H
    apply H
  iapply R
  iapply H1 $$ Hp

theorem BUpdPlain_idemp {P : PROP} : BUpdPlain (BUpdPlain P) ⊢ BUpdPlain P := by
  unfold BUpdPlain
  iintro Hp R H
  iapply Hp
  iintro Hp
  iapply Hp $$ H

theorem BUpdPlain_frame_r {P Q : PROP} : BUpdPlain P ∗ Q ⊢ (BUpdPlain iprop(P ∗ Q)) := by
  unfold BUpdPlain
  iintro ⟨Hp, Hq⟩ R H
  iapply Hp
  iintro Hp
  iapply H
  isplitl [Hp]
  · iexact Hp
  · iexact Hq

theorem BUpdPlain_plainly {P : PROP} : BUpdPlain iprop(■ P) ⊢ (■ P) := by
  unfold BUpdPlain
  iintro H
  iapply H
  exact wand_rfl

/- BiBUpdPlainly entails the alternative definition -/
theorem BUpd_BUpdPlain [BIUpdate PROP] [BIBUpdatePlainly PROP] {P : PROP} : (|==> P) ⊢ BUpdPlain P := by
  unfold BUpdPlain
  iintro _ _ _
  refine BIUpdate.frame_r.trans ?_
  refine (BIUpdate.mono sep_symm).trans ?_
  exact (BIUpdate.mono <| wand_elim .rfl).trans bupd_elim

-- We get the usual rule for frame preserving updates if we have an [own]
-- connective satisfying the following rule w.r.t. interaction with plainly.

theorem own_updateP [UCMRA M] {own : M → PROP} {x : M} {Φ : M → Prop}
  (own_updateP_plainly : ∀ (x : M) (Φ : M → Prop) (R : PROP),
    (x ~~>: Φ) → own x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R)
  (Hup : x ~~>: Φ) :
    own x ⊢ BUpdPlain iprop(∃ y, ⌜Φ y⌝ ∧ own y) := by
  iintro Hx
  unfold BUpdPlain
  iintro R H
  iapply own_updateP_plainly x Φ R Hup
  isplitl [Hx]
  · iexact Hx
  iintro y ⌜HΦ⌝
  iintro Hy
  iapply H
  iexists y
  isplit
  · ipure_intro
    exact HΦ
  · iexact Hy

end BupdPlainDef
end BUpdPlain
