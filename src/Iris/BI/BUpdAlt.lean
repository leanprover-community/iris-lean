-- TODO: reduce import size?
import Iris.BI.BI
import Iris.BI.BIBase
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.Algebra
import Iris.Algebra.Updates
import Iris.Algebra.UPred
import Iris.BI.Plainly
import Iris.ProofMode
import Iris.BI.Updates

-- TODO: why in rocq I don't need to explicitly import this?
-- I need to import this for "bupd_alt_bupd"
import Iris.Instances.UPred.Instance

set_option trace.Meta.synthInstance true

namespace Iris
open Iris.Std BI

-- This file contains an alternative version of basic updates, that is
-- expression in terms of just the plain modality [■]
def bupd_alt [BI PROP] [BIPlainly PROP] (P : PROP) : PROP :=
  iprop(∀ R, (P -∗ ■ R) -∗ ■ R)



section bupd_alt
variable [BI PROP] [BIPlainly PROP]

-- TODO: the following 4 global instance

/- Implicit Types P Q R : PROP. -/

/-
Global Instance bupd_alt_ne : NonExpansive bupd_alt.
Proof. solve_proper. Qed.
Global Instance bupd_alt_proper : Proper ((≡) ==> (≡)) bupd_alt.
Proof. solve_proper. Qed.
Global Instance bupd_alt_mono' : Proper ((⊢) ==> (⊢)) bupd_alt.
Proof. solve_proper. Qed.
Global Instance bupd_alt_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) bupd_alt.
Proof. solve_proper. Qed.
-/
-- NonExpansive

-- Proper

-- mono'

-- flip mono

-- TODO: should I use `lemma`? and how?

-- The Laws of the basica update modality hold
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

-- TODO: why need to wrap `P ∗ Q` with an iprop
theorem bupd_alt_frame_r {P Q : PROP} : bupd_alt P ∗ Q ⊢ (bupd_alt iprop(P ∗ Q)) := by
  unfold bupd_alt
  iintro ⟨Hp, Hq⟩ R H
  ispecialize Hp R as HpR
  iapply HpR
  iintro Hp
  iapply H
  isplit l [Hp]
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
-- TODO: don't quite understand the typeclass mechanisms...
theorem bupd_bupd_alt [BIUpdate PROP] [BIBUpdatePlainly PROP] {P : PROP} : (|==> P) ⊢  bupd_alt P := by
  unfold bupd_alt
  iintro HP (R) H
  -- Eliminate the bupds (by hand, until iMod is implemented)
  refine BIUpdate.frame_r.trans ?_
  refine (BIUpdate.mono sep_symm).trans ?_
  -- TODO: what gets filled in in the `_` here, namely what is of type `BI PROP`?
  refine (BIUpdate.mono <| @wand_elim PROP _ iprop(P -∗ ■ R) P iprop(■R) .rfl).trans ?_
  exact bupd_elim

-- We get the usual rule for frame preserving updates if we have an [own]
-- connective satisfying the following rule w.r.t. interaction with plainly.

-- TODO: how to translate the following?
-- TODO: How is context different from variable
-- TODO: check if this is a faithful translation of
/-
  Context {M : ucmra} (own : M → PROP).
  Context (own_updateP_plainly : ∀ x Φ R,
    x ~~>: Φ →
    own x ∗ (∀ y, ⌜Φ y⌝ -∗ own y -∗ ■ R) ⊢ ■ R).
-/
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
  isplit l [Hx]
  · iexact Hx
  -- TODO: can't intro HΦ to pure context
  iintro y
  iintro HΦ
  icases HΦ with ⌜HQ⌝
  iintro Hy
  iapply H
  iexists y
  isplit
  · ipure_intro
    exact HQ
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
  have H_inst : (UPred.wand (UPred.wand P (UPred.plainly R)) (UPred.plainly R)).holds n x :=
    -- TODO: why do i need to pass this wand into H..., why I also need to pass in this proof
    H (UPred.wand (UPred.wand P (UPred.plainly R)) (UPred.plainly R)) ⟨R, rfl⟩

  have wand_holds : (UPred.wand P (UPred.plainly R)).holds k y := by
    intro k' z Hk' Hvyz HP
    -- Need to show: (■ R) k' (y • z), which is R k' UCMRA.unit
    -- R k' UCMRA.unit = ∃ x'', ✓{k'} (x'' • y) ∧ P k' x''
    refine ⟨z, ?_, HP⟩
    exact CMRA.validN_ne CMRA.op_commN Hvyz

  -- TODO: why do I need to pass in k, y, Hkn, Hxy, wand_holds again??
  have HR : (UPred.plainly R).holds k (x • y) := H_inst k y Hkn Hxy wand_holds
  -- HR : (■ R) k (x • y), which unfolds to R k UCMRA.unit
  -- R k UCMRA.unit = ∃ x', ✓{k} (x' • y) ∧ P k x'
  exact HR


theorem bupd_alt_bupd_iff [UCMRA M] (P : UPred M) : bupd_alt P ⊣⊢ |==> P := by
  refine ⟨?_, ?_⟩
  · apply bupd_alt_bupd
  · apply bupd_bupd_alt

-- The law about the interaction between [uPred_ownM] and plainly holds.
theorem ownM_updateP [UCMRA M] (x : M) (Φ : M → Prop) (R : UPred M) :
    (x ~~>: Φ) →
    UPred.ownM x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ UPred.ownM y -∗ ■ R) ⊢ ■ R := by
  intro Hup
  -- Unfold to work at the representation level
  intro n z Hv ⟨x1, z2, Hx, ⟨z1, Hz1⟩, HR⟩
  -- Hv : ✓{n} z
  -- Destructure the sep:
  -- x1, z2 are the two parts
  -- Hx : z ≡{n} x1 • z2
  -- ⟨z1, Hz1⟩ : (ownM x) n x1, which means x ≼{n} x1, i.e., ∃ z1, x1 ≡{n} x • z1
  -- HR : ForAll holds at z2

  -- After ofe_subst, we have z ≡{n} (x • z1) • z2
  have Hz_subst : z ≡{n}≡ (x • z1) • z2 := by
    calc z ≡{n}≡ x1 • z2 := Hx
         _ ≡{n}≡ (x • z1) • z2 := Hz1.op_l

  -- Apply the update with frame z1 • z2
  have Hvalid : ✓{n} (x •? some (z1 • z2)) := by
    show ✓{n} (x • (z1 • z2))
    refine CMRA.validN_ne ?_ Hv
    calc z ≡{n}≡ (x • z1) • z2 := Hz_subst
         _ ≡{n}≡ x • (z1 • z2) := CMRA.assoc.symm.dist

  obtain ⟨y, HΦy, Hvalid_y⟩ := Hup n (some (z1 • z2)) Hvalid

  -- HR : ∀ p, (∃ y', p = ...) → p n z2
  -- We need to instantiate with the wand
  let p := UPred.wand (UPred.pure (Φ y)) (UPred.wand (UPred.ownM y) (UPred.plainly R))
  have Hp : (UPred.wand (UPred.pure (Φ y)) (UPred.wand (UPred.ownM y) (UPred.plainly R))).holds n z2 :=
    HR p ⟨y, rfl⟩

  -- Apply Hp at step n with resource z1
  -- First wand: (⌜Φ y⌝ -∗ (ownM y -∗ ■ R)).holds n z2
  -- Means: ∀ n' x', n' ≤ n → ✓{n'} (z2 • x') → (⌜Φ y⌝) n' x' → (ownM y -∗ ■ R) n' (z2 • x')
  -- We need ✓{n} (z2 • z1)
  have Hv_z2z1 : ✓{n} (z2 • z1) := by
    -- From Coq line 250: rewrite comm. by eapply cmra_validN_op_r.
    -- We have Hvalid_y : ✓{n} (y •? some (z1 • z2)) = ✓{n} (y • (z1 • z2))
    -- Need ✓{n} (z2 • z1)
    have : ✓{n} (y • (z1 • z2)) := Hvalid_y
    exact CMRA.validN_ne CMRA.comm.dist (CMRA.validN_op_right this)

  have Hp1 : (UPred.wand (UPred.ownM y) (UPred.plainly R)).holds n (z2 • z1) := Hp n z1 (Nat.le_refl _) Hv_z2z1 HΦy

  -- Apply the second wand at step n with resource y
  -- (ownM y -∗ ■ R).holds n (z2 • z1)
  -- Means: ∀ n' x', n' ≤ n → ✓{n'} ((z2 • z1) • x') → (ownM y) n' x' → (■ R) n' ((z2 • z1) • x')
  -- We want to apply this with x' = y at step n
  -- Need: ✓{n} ((z2 • z1) • y)
  have Hv_z2z1y : ✓{n} ((z2 • z1) • y) := by
    -- From Coq line 251: by rewrite (comm _ _ y) (comm _ z2).
    -- We have Hvalid_y : ✓{n} (y • (z1 • z2))
    have : ✓{n} (y • (z1 • z2)) := Hvalid_y
    refine CMRA.validN_ne ?_ this
    calc y • (z1 • z2) ≡{n}≡ y • (z2 • z1) := CMRA.comm.dist.op_r
         _ ≡{n}≡ (z2 • z1) • y := CMRA.comm.symm.dist

  -- Need: (ownM y) n y, which is y ≼{n} y
  have Hy_incl : y ≼{n} y := CMRA.incN_refl y

  have HR_goal : (UPred.plainly R).holds n ((z2 • z1) • y) :=
    Hp1 n y (Nat.le_refl _) Hv_z2z1y Hy_incl

  -- HR_goal : R n UCMRA.unit
  -- We need to show: R n UCMRA.unit
  exact HR_goal
