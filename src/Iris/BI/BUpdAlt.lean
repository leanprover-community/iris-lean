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

namespace Iris
open Iris.Std BI


-- Note to self: all rocq code are in multiline comments
--               All questions start with TODO:

-- TODO: why in rocq this definition is not moved into the section?

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
  -- TODO: can i use iapply now?
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
    own x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R)

  -- Lemma own_updateP x (Φ : M → Prop) :
  --   x ~~>: Φ → own x ⊢ bupd_alt (∃ y, ⌜Φ y⌝ ∧ own y).
  -- Proof.
  --   iIntros (Hup) "Hx"; iIntros (R) "H".
  --   iApply (own_updateP_plainly with "[$Hx H]"); first done.
  --   iIntros (y ?) "Hy". iApply "H"; auto.
  -- Qed.
theorem own_updateP {x : M} {Φ : M → Prop}
    (own_updateP_plainly :
      ∀ (x : M) (Φ : M → Prop) (R : PROP),
        (x ~~>: Φ) →
        own x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ own y -∗ ■ R) ⊢ ■ R) :
    (x ~~>: Φ) →
    own x ⊢ bupd_alt iprop(∃ y, ⌜Φ y⌝ ∧ own y) := by
  intro Hup
  iintro Hx
  unfold bupd_alt
  iintro R H
  iapply own_updateP_plainly x Φ R Hup
  isplit l [Hx]
  · iexact Hx
  -- TODO: can't intro (HΦ) to pure context
  iintro y (HΦ) Hy
  iapply H
  iexists y
  sorry

end bupd_alt

-- The alternative definition entails the ordinary basic update
theorem bupd_alt_bupd [UCMRA M] (P : UPred M) : bupd_alt P ⊢ |==> P := by
  sorry


theorem bupd_alt_bupd_iff [UCMRA M] (P : UPred M) : bupd_alt P ⊣⊢ |==> P := by
  refine ⟨?_, ?_⟩
  · apply bupd_alt_bupd
  · apply bupd_bupd_alt

-- The law about the interaction between [uPred_ownM] and plainly holds.
theorem ownM_updateP [UCMRA M] (x : M) (Φ : M → Prop) (R : UPred M) :
    (x ~~>: Φ) →
    UPred.ownM x ∗ (∀ y, iprop(⌜Φ y⌝) -∗ UPred.ownM y -∗ ■ R) ⊢ ■ R := by
  sorry
