import Iris.ProofMode
import Iris.Instances.UPred.Instance

-- set_option trace.Meta.synthInstance true

namespace Iris
open Iris.Std BI

-- This file contains an alternative version of basic updates, that is
-- expression in terms of just the plain modality [■]
def bupd_alt [BI PROP] [BIPlainly PROP] (P : PROP) : PROP :=
  iprop(∀ R, (P -∗ ■ R) -∗ ■ R)

section bupd_alt
variable [BI PROP] [BIPlainly PROP]

instance bupd_alt_ne : OFE.NonExpansive (bupd_alt (PROP := PROP)) where
  ne n x1 x2 Hx := by
    unfold bupd_alt
    apply forall_ne
    intro R
    apply wand_ne.ne;
    · apply wand_ne.ne
      · exact Hx
      · exact .rfl
    · exact .rfl

-- The Laws of the basic update modality hold
theorem bupd_alt_intro {P : PROP} : P ⊢ bupd_alt P := by
  iintro Hp
  unfold bupd_alt
  iintro R H
  ispecialize H Hp as H1
  iexact H1

theorem bupt_alt_mono {P Q : PROP} : (P ⊢ Q) → (bupd_alt P ⊢ bupd_alt Q) := by
  intros H
  unfold bupd_alt
  iintro R HQR
  iintro Hp
  have H1 : ⊢ iprop(Q -∗ ■ HQR) -∗ iprop(P -∗ ■ HQR) := by
    iintro H
    iintro Hp
    iapply H
    apply H
    done
  iintro ⟨Ha, H2⟩
  ispecialize Ha HQR
  iapply Ha
  iapply H1
  iassumption

theorem bupd_alt_trans {P : PROP} : bupd_alt (bupd_alt P) ⊢ bupd_alt P := by
  unfold bupd_alt
  iintro Hp R H
  ispecialize Hp R as HpR
  iapply HpR
  iintro Hp
  ispecialize Hp R as HpR2
  iapply HpR2
  iassumption

theorem bupd_alt_frame_r {P Q : PROP} : bupd_alt P ∗ Q ⊢ (bupd_alt iprop(P ∗ Q)) := by
  unfold bupd_alt
  iintro ⟨Hp, Hq⟩ R H
  ispecialize Hp R as HpR
  iapply HpR
  iintro Hp
  iapply H
  isplitl [Hp]
  · iexact Hp
  · iexact Hq

theorem bupd_alt_plainly {P : PROP} : bupd_alt iprop(■ P) ⊢ (■ P) := by
  unfold bupd_alt
  iintro H
  ispecialize H P as HP
  iapply HP
  iintro Hp
  iexact Hp

-- Any modality confirming with [BiBUpdPlainly] entails the alternative definition
theorem bupd_bupd_alt [BIUpdate PROP] [BIBUpdatePlainly PROP] {P : PROP} : (|==> P) ⊢  bupd_alt P := by
  unfold bupd_alt
  iintro HP (R) H
  -- Eliminate the bupds (by hand, until iMod is implemented)
  refine BIUpdate.frame_r.trans ?_
  refine (BIUpdate.mono sep_symm).trans ?_
  exact (BIUpdate.mono <| wand_elim .rfl).trans bupd_elim

-- We get the usual rule for frame preserving updates if we have an [own]
-- connective satisfying the following rule w.r.t. interaction with plainly.
variable [UCMRA M] (own : M → PROP)
variable (own_updateP_plainly :
  ∀ (x : M) (Φ : M → Prop) (R : PROP),
    (x ~~>: Φ) →
    own x ∗ (∀ y, iprop(<affine> ⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R)

theorem own_updateP {x : M} {Φ : M → Prop}
    (own_updateP_plainly :
      ∀ (x : M) (Φ : M → Prop) (R : PROP),
        (x ~~>: Φ) →
        own x ∗ (∀ y, <affine> iprop(⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R) :
    (x ~~>: Φ) →
    own x ⊢ bupd_alt iprop(∃ y, ⌜Φ y⌝ ∧ own y) := by
  intro Hup
  iintro Hx
  unfold bupd_alt
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
end bupd_alt

-- Helper predicate for bupd_alt_bupd proof
private def bupd_alt_pred [UCMRA M] (P : UPred M) (y : M) : UPred M where
  holds k _ := ∃ x'', ✓{k} (x'' • y) ∧ P k x''
  mono {_} := fun ⟨z, Hz1, Hz2⟩ _ Hn =>
    ⟨z, CMRA.validN_of_le Hn Hz1, P.mono Hz2 (CMRA.incN_refl z) Hn⟩

-- The alternative definition entails the ordinary basic update
theorem bupd_alt_bupd [UCMRA M] (P : UPred M) : bupd_alt P ⊢ |==> P := by
  unfold bupd_alt bupd
  intro n x Hx H
  -- Unfold bupd definition in `Instance.lean`
  intro k y Hkn Hxy
  let R := bupd_alt_pred P y
  have H_inst : iprop((P -∗ ■ R) -∗ ■ R).holds n x := H _ ⟨R, rfl⟩

  have wand_holds : iprop(P -∗ ■ R).holds k y := by
    intro k' z Hk' Hvyz HP
    refine ⟨z, ?_, HP⟩
    exact CMRA.validN_ne CMRA.op_commN Hvyz
  exact H_inst k y Hkn Hxy wand_holds


theorem bupd_alt_bupd_iff [UCMRA M] (P : UPred M) : bupd_alt P ⊣⊢ |==> P := by
  refine ⟨?_, ?_⟩
  · apply bupd_alt_bupd
  · apply bupd_bupd_alt

-- The law about the interaction between [uPred_ownM] and plainly holds.
theorem ownM_updateP [UCMRA M] (x : M) (Φ : M → Prop) (R : UPred M) :
    (x ~~>: Φ) →
    UPred.ownM x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ UPred.ownM y -∗ ■ R) ⊢ ■ R := by
  intro Hup
  intro n z
  intro Hv
  -- x1 z2 are introduced for separating conjunction
  -- (ownM x).holds n x1 := x ≼{n} x1, namely x · z1 = x1
  intro ⟨x1, z2, Hx, ⟨z1, Hz1⟩, HR⟩
  -- manually having ofe_subst, z ≡{n} (x • z1) • z2
  have Hz_subst : z ≡{n}≡ (x • z1) • z2 := by
    calc z ≡{n}≡ x1 • z2 := Hx
         _ ≡{n}≡ (x • z1) • z2 := Hz1.op_l

  have Hvalid : ✓{n} (x •? some (z1 • z2)) := by
    show ✓{n} (x • (z1 • z2))
    refine CMRA.validN_ne ?_ Hv
    calc z ≡{n}≡ (x • z1) • z2 := Hz_subst
         _ ≡{n}≡ x • (z1 • z2) := CMRA.assoc.symm.dist
  have ⟨y, HΦy, Hvalid_y⟩ := Hup n (some (z1 • z2)) Hvalid

  have Hp := HR (iprop(⌜Φ y⌝ -∗ (UPred.ownM y -∗ ■ R))) ⟨y, rfl⟩

  have Hv_z2z1 : ✓{n} (z2 • z1) := by
    exact CMRA.validN_ne CMRA.comm.dist (CMRA.validN_op_right Hvalid)

  have Hp1 : iprop(UPred.ownM y -∗ ■ R).holds n (z2 • z1) := Hp n z1 (Nat.le_refl _) Hv_z2z1 HΦy

  have Hv_z2z1y : ✓{n} ((z2 • z1) • y) := by
    apply CMRA.validN_ne ?_ Hvalid_y
    calc y • (z1 • z2) ≡{n}≡ y • (z2 • z1) := CMRA.comm.dist.op_r
         _ ≡{n}≡ (z2 • z1) • y := CMRA.comm.symm.dist

  have Hy_incl : y ≼{n} y := CMRA.incN_refl y
  exact Hp1 n y (Nat.le_refl _) Hv_z2z1y Hy_incl
