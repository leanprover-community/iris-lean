/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.Lib.Fixpoint

@[expose] public section

/-!  # Logical Relation Closures -/

namespace Iris
open Iris.Std BI OFE

@[rocq_alias bi_rtc_pre]
def biRtcPre [Sbi PROP] [OFE A] (R : A → A → PROP) (x₂ : A) (rec : A → PROP) (x₁ : A) : PROP :=
  iprop% <affine> (x₁ ≡ x₂) ∨ ∃ x', R x₁ x' ∗ rec x'

/-- The reflexive-transitive closure. -/
@[rocq_alias bi_rtc]
def biRtc [Sbi PROP] [OFE A] (R : A → A → PROP) (x₁ x₂ : A) : PROP :=
  bi_least_fixpoint (biRtcPre R x₂) x₁

@[rocq_alias bi_tc_pre]
def biTcPre [Sbi PROP] [OFE A] (R : A → A → PROP) (x₂ : A) (rec : A → PROP) (x₁ : A) : PROP :=
  iprop% R x₁ x₂ ∨ ∃ x', R x₁ x' ∗ rec x'

/-- The transitive closure. -/
@[rocq_alias bi_tc]
def biTc [Sbi PROP] [OFE A] (R : A → A → PROP) (x₁ x₂ : A) : PROP :=
  bi_least_fixpoint (biTcPre R x₂) x₁

/-- The assertion that two elements are related by exactly `n` steps. -/
@[rocq_alias bi_nsteps]
def biNsteps [Sbi PROP] [OFE A] (R : A → A → PROP) : Nat → A → A → PROP
  | 0, x₁, x₂ => iprop% <affine> (x₁ ≡ x₂)
  | n + 1, x₁, x₂ => iprop% ∃ x', R x₁ x' ∗ biNsteps R n x' x₂

@[rocq_alias bi_rtc_pre_mono]
local instance bi_rtc_pre_mono [Sbi PROP] [OFE A] (R : A → A → PROP) [NonExpansive₂ R]
    (x : A) : BIMonoPred (biRtcPre R x) where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #Hmono %x₁ H
    unfold biRtcPre
    icases H with ⟨H | ⟨%x', HR, Hrec⟩⟩
    · ileft; itrivial
    · iright
      iexists x'
      iframe HR
      iapply Hmono $$ Hrec
  mono_pred_ne := ⟨fun {_ _ _} h => or_ne.ne
    (affinely_ne.ne <| (internalEq.ne_l x).ne h)
    (exists_ne fun _ : A => sep_ne.ne (NonExpansive₂.ne h .rfl) .rfl)⟩

@[rocq_alias bi_rtc_ne]
instance bi_rtc_ne [Sbi PROP] [OFE A] (R : A → A → PROP) : NonExpansive₂ (biRtc R) where
  ne {_ _ _} hx {_ _} hy := by
    refine forall_ne fun Φ => wand_ne.ne
      (intuitionistically_ne.ne <| forall_ne (fun z => ?_)) (NonExpansive.ne hx)
    refine wand_ne.ne (or_ne.ne (affinely_ne.ne ?_) .rfl) .rfl
    exact (internalEq.ne_r z).ne hy

#rocq_ignore bi_rtc_proper "Subsumed by congruence"

@[rocq_alias bi_tc_pre_mono]
instance bi_tc_pre_mono [Sbi PROP] [OFE A] (R : A → A → PROP) [NonExpansive₂ R]
    (x : A) : BIMonoPred (biTcPre R x) where
  mono_pred := by
    intro Φ Ψ hΦ hΨ
    iintro #Hmono %x₁ H
    iunfold biTcPre in H
    iunfold biTcPre
    icases H with ⟨H | ⟨%x', HR, Hrec⟩⟩
    · ileft; itrivial
    · iright
      iexists x'
      iframe HR
      iapply Hmono $$ Hrec
  mono_pred_ne := ⟨fun {_ _ _} h => or_ne.ne (NonExpansive₂.ne h .rfl)
    (exists_ne fun _ : A => sep_ne.ne (NonExpansive₂.ne h .rfl) .rfl)⟩

@[rocq_alias bi_tc_ne]
instance bi_tc_ne [Sbi PROP] [OFE A] (R : A → A → PROP) [NonExpansive₂ R] :
    NonExpansive₂ (biTc R) where
  ne {_ _ _} hx {_ _} hy := by
    refine forall_ne fun _ => wand_ne.ne (intuitionistically_ne.ne ?_) (NonExpansive.ne hx)
    exact forall_ne fun _ => wand_ne.ne (or_ne.ne (NonExpansive₂.ne .rfl hy) .rfl) .rfl

#rocq_ignore bi_tc_proper "Subsumed by congruence"

@[rocq_alias bi_nsteps_ne]
instance bi_nsteps_ne [Sbi PROP] [OFE A] (R : A → A → PROP) [NonExpansive₂ R]
    (n : Nat) : NonExpansive₂ (biNsteps R n) := by
  induction n with
  | zero => exact ⟨fun {_ _ _} hx {_ _} hy =>
      affinely_ne.ne (NonExpansive₂.ne hx hy)⟩
  | succ n ih => exact ⟨fun {_ _ _} hx {_ _} hy => exists_ne fun _ : A =>
      sep_ne.ne (NonExpansive₂.ne hx .rfl) (ih.ne .rfl hy)⟩

#rocq_ignore bi_nsteps_proper "Subsumed by congruence"

section General

variable [Sbi PROP] [OFE A] (R : A → A → PROP)

@[rocq_alias bi_rtc_ind_l]
theorem bi_rtc_ind_left (x₂ : A) (Φ : A → PROP) [NonExpansive Φ] :
    ⊢ □ (∀ x₁, <affine> (x₁ ≡ x₂) ∨ (∃ x', R x₁ x' ∗ Φ x') -∗ Φ x₁) -∗
      ∀ x₁, biRtc R x₁ x₂ -∗ Φ x₁ :=
  least_fixpoint_iter (biRtcPre R x₂)

@[rocq_alias bi_tc_ind_l]
theorem bi_tc_ind_left (x₂ : A) (Φ : A → PROP) [NonExpansive Φ] :
    ⊢ □ (∀ x₁, R x₁ x₂ ∨ (∃ x', R x₁ x' ∗ Φ x') -∗ Φ x₁) -∗
      ∀ x₁, biTc R x₁ x₂ -∗ Φ x₁ :=
  least_fixpoint_iter (biTcPre R x₂)

@[rocq_alias bi_nsteps_l]
theorem bi_nsteps_left (n : Nat) (x y z : A) :
    R x y -∗ biNsteps R n y z -∗ biNsteps R (n + 1) x z := by
  iintro HR Hn
  iunfold biNsteps
  iexists y
  iframe

@[rocq_alias bi_nsteps_O]
theorem bi_nsteps_zero (x : A) : ⊢ biNsteps R 0 x x :=
  affinely_intro internalEq.refl

@[rocq_alias bi_nsteps_once]
theorem bi_nsteps_once (x y : A) : R x y -∗ biNsteps R 1 x y := by
  iintro H
  iapply bi_nsteps_left $$ H
  iapply bi_nsteps_zero

@[rocq_alias bi_nsteps_add_inv]
theorem bi_nsteps_add_inv (n m : Nat) (x z : A) :
    biNsteps R (n + m) x z ⊢ ∃ y, biNsteps R n x y ∗ biNsteps R m y z := by
  iinduction n generalizing %x with
  | zero =>
    simp only [Nat.zero_add]
    iintro H
    iexists x
    iframe H
    exact bi_nsteps_zero R x
  | succ n ih =>
    rw [Nat.succ_add]
    iintro H
    iunfold biNsteps in H
    icases H with ⟨%y, HR, Hrest⟩
    icases ih $$ Hrest with ⟨%y', Hn, Hm⟩
    iexists y'
    iframe Hm
    iapply bi_nsteps_left $$ HR Hn

variable [NonExpansive₂ R]

@[rocq_alias bi_rtc_unfold]
theorem bi_rtc_unfold (x₁ x₂ : A) :
    biRtc R x₁ x₂ = biRtcPre R x₂ (fun x₁ => biRtc R x₁ x₂) x₁ :=
  least_fixpoint_unfold (biRtcPre R x₂)

@[rocq_alias bi_rtc_strong_ind_l]
theorem bi_rtc_strong_ind_left (x₂ : A) (Φ : A → PROP) [NonExpansive Φ] :
    ⊢ □ (∀ x₁, <affine> (x₁ ≡ x₂) ∨ (∃ x', R x₁ x' ∗ (Φ x' ∧ biRtc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biRtc R x₁ x₂ -∗ Φ x₁ :=
  least_fixpoint_ind (biRtcPre R x₂) Φ

@[rocq_alias bi_rtc_refl]
theorem bi_rtc_refl (x : A) : ⊢ biRtc R x x :=
  (bi_rtc_unfold R x x).symm ▸ or_intro_left_trans (affinely_intro internalEq.refl)

@[rocq_alias bi_rtc_l]
theorem bi_rtc_left (x₁ x₂ x₃ : A) :
    R x₁ x₂ -∗ biRtc R x₂ x₃ -∗ biRtc R x₁ x₃ := by
  iintro H₁ H₂
  rw [bi_rtc_unfold R x₁ x₃, biRtcPre]
  iright
  iexists x₂
  iframe

@[rocq_alias bi_rtc_once]
theorem bi_rtc_once (x₁ x₂ : A) : R x₁ x₂ -∗ biRtc R x₁ x₂ := by
  iintro H
  iapply bi_rtc_left $$ H
  iapply bi_rtc_refl

local instance : NonExpansive (fun x => biRtc R x y) := NonExpansive₂.ne_left (biRtc R) y
local instance : NonExpansive (fun y => biTc R x y) := NonExpansive₂.ne_right (biTc R) x

@[rocq_alias bi_rtc_trans]
theorem bi_rtc_trans (x₁ x₂ x₃ : A) :
    biRtc R x₁ x₂ -∗ biRtc R x₂ x₃ -∗ biRtc R x₁ x₃ := by
  irevert %x₁
  letI : NonExpansive (fun x => iprop(biRtc R x₂ x₃ -∗ biRtc R x x₃)) :=
    ⟨fun _ _ _ h => wand_ne.ne .rfl (NonExpansive₂.ne h .rfl)⟩
  iapply bi_rtc_ind_left
  iintro !> %x₁ ⟨Heq|⟨%x', HR, IH⟩⟩ H₂
  · irewrite [Heq]; itrivial
  · iapply bi_rtc_left R x₁ x' x₃ $$ HR
    iapply IH; itrivial

@[rocq_alias bi_rtc_r]
theorem bi_rtc_right (x y z : A) : biRtc R x y -∗ R y z -∗ biRtc R x z := by
  iintro Hrtc HR
  iapply bi_rtc_trans $$ Hrtc
  iapply bi_rtc_once $$ HR

@[rocq_alias bi_rtc_inv]
theorem bi_rtc_inv (x z : A) :
    biRtc R x z -∗ <affine> (x ≡ z) ∨ ∃ y, R x y ∗ biRtc R y z :=
  (bi_rtc_unfold R x z) ▸ wand_rfl

@[rocq_alias bi_rtc_affine]
instance bi_rtc_affine [∀ x y, Affine (R x y)] (x y : A) :
    Affine (biRtc R x y) := by
  unfold biRtc
  unfold biRtcPre
  infer_instance

@[rocq_alias bi_rtc_persistent]
instance bi_rtc_persistent [∀ x y, Persistent (R x y)] (x y : A) :
    Persistent (biRtc R x y) where
  persistent := by
    letI : NonExpansive (fun x => iprop(<pers> biRtc R x y)) := by
      exact ⟨fun _ _ _ h => persistently_ne.ne (NonExpansive₂.ne h .rfl)⟩
    irevert %x
    iapply bi_rtc_ind_left
    iintro !> %x ⟨#Heq|⟨%x', #HR, #Hrtc⟩⟩
    · irewrite [Heq]
      iapply bi_rtc_refl
    · iapply bi_rtc_left $$ HR Hrtc

@[rocq_alias bi_tc_unfold]
theorem bi_tc_unfold (x₁ x₂ : A) :
    biTc R x₁ x₂ = biTcPre R x₂ (fun x₁ => biTc R x₁ x₂) x₁ :=
  least_fixpoint_unfold (biTcPre R x₂)

@[rocq_alias bi_tc_strong_ind_l]
theorem bi_tc_strong_ind_left (x₂ : A) (Φ : A → PROP) (hΦ : NonExpansive Φ) :
    ⊢ □ (∀ x₁, R x₁ x₂ ∨
        (∃ x', R x₁ x' ∗ (Φ x' ∧ biTc R x' x₂)) -∗ Φ x₁) -∗
      ∀ x₁, biTc R x₁ x₂ -∗ Φ x₁ :=
  least_fixpoint_ind (biTcPre R x₂) Φ

@[rocq_alias bi_tc_l]
theorem bi_tc_left (x₁ x₂ x₃ : A) :
    R x₁ x₂ -∗ biTc R x₂ x₃ -∗ biTc R x₁ x₃ := by
  iintro H₁ H₂
  rw [bi_tc_unfold R x₁ x₃, biTcPre]
  iright
  iexists x₂
  iframe

@[rocq_alias bi_tc_once]
theorem bi_tc_once (x₁ x₂ : A) : R x₁ x₂ -∗ biTc R x₁ x₂ := by
  iintro H
  rw [bi_tc_unfold R x₁ x₂, biTcPre]
  ileft
  iexact H

@[rocq_alias bi_tc_trans]
theorem bi_tc_trans (x₁ x₂ x₃ : A) :
    biTc R x₁ x₂ -∗ biTc R x₂ x₃ -∗ biTc R x₁ x₃ := by
  letI : NonExpansive (fun x => iprop(biTc R x₂ x₃ -∗ biTc R x x₃)) :=
    ⟨fun _ _ _ h => wand_ne.ne .rfl (NonExpansive.ne h)⟩
  irevert %x₁
  iapply bi_tc_ind_left
  iintro !> %x₁ ⟨H | ⟨%x', HR, IH⟩⟩ H₂
  · iapply bi_tc_left $$ H H₂
  · iapply bi_tc_left $$ HR
    iapply IH; itrivial

@[rocq_alias bi_tc_r]
theorem bi_tc_right (x y z : A) : biTc R x y -∗ R y z -∗ biTc R x z := by
  iintro Htc HR
  iapply bi_tc_trans $$ Htc
  iapply bi_tc_once; itrivial

@[rocq_alias bi_tc_rtc_l]
theorem bi_tc_rtc_left (x y z : A) : biRtc R x y -∗ biTc R y z -∗ biTc R x z := by
  letI : NonExpansive (fun x => iprop(biTc R y z -∗ biTc R x z)) :=
    ⟨fun _ _ _ h => wand_ne.ne .rfl (NonExpansive.ne h)⟩
  irevert %x
  iapply bi_rtc_ind_left
  iintro !> %x ⟨Heq | ⟨%x', HR, IH⟩⟩ Hyz
  · irewrite [Heq]
    · exact NonExpansive₂.ne_left (biTc R) z
    itrivial
  · iapply bi_tc_left $$ HR
    iapply IH; itrivial

@[rocq_alias bi_tc_rtc_r]
theorem bi_tc_rtc_right (x y z : A) : biTc R x y -∗ biRtc R y z -∗ biTc R x z := by
  letI : NonExpansive (fun y => iprop(∀ x, biTc R x y -∗ biTc R x z)) :=
    ⟨fun _ _ _ h => forall_ne fun x => wand_ne.ne (NonExpansive.ne h) .rfl⟩
  iintro Hxy Hyz
  irevert %x Hxy
  irevert %y Hyz
  iapply bi_rtc_ind_left
  iintro !> %y ⟨Heq | ⟨%y', HR, IH⟩⟩ %x Hxy
  · irewrite [←Heq]; itrivial
  · iapply IH
    iapply bi_tc_right $$ Hxy HR

@[rocq_alias bi_tc_rtc]
theorem bi_tc_rtc (x y : A) : biTc R x y -∗ biRtc R x y := by
  letI : NonExpansive (fun x => biRtc R x y) := NonExpansive₂.ne_left (biRtc R) y
  irevert %x
  iapply bi_tc_ind_left
  iintro !> %x ⟨H | ⟨%x', HR, IH⟩⟩
  · iapply bi_rtc_once; itrivial
  · iapply bi_rtc_left $$ HR IH

@[rocq_alias bi_tc_affine]
instance bi_tc_affine [∀ x y, Affine (R x y)] (x y : A) :
    Affine (biTc R x y) := by
  unfold biTc
  unfold biTcPre
  infer_instance

@[rocq_alias bi_tc_absorbing]
instance bi_tc_absorbing [∀ x y, Absorbing (R x y)] (x y : A) :
    Absorbing (biTc R x y) :=
    @least_fixpoint_absorbing PROP A _ _ (biTcPre R y) inferInstance
      (fun _ _ _ => by unfold biTcPre; infer_instance) x

@[rocq_alias bi_tc_persistent]
instance bi_tc_persistent [∀ x y, Persistent (R x y)] (x y : A) :
    Persistent (biTc R x y) where
  persistent := by
    letI : NonExpansive (fun x => iprop(<pers> biTc R x y)) :=
      ⟨fun _ _ _ h => persistently_ne.ne (NonExpansive₂.ne h .rfl)⟩
    irevert %x
    iapply bi_tc_ind_left
    iintro !> %x ⟨#H | ⟨%x', #_, #_⟩⟩ !>
    · iapply bi_tc_once ; itrivial
    · iapply bi_tc_left <;> itrivial

@[rocq_alias bi_nsteps_once_inv]
theorem bi_nsteps_once_inv (x y : A) : biNsteps R 1 x y -∗ R x y := by
  iintro Hn
  iunfold biNsteps in Hn
  icases Hn with ⟨%x', H, Heq⟩
  iunfold biNsteps in Heq
  irewrite [Heq] at H
  · exact NonExpansive₂.ne_right R x
  itrivial

@[rocq_alias bi_nsteps_trans]
theorem bi_nsteps_trans (n m : Nat) (x y z : A) :
    biNsteps R n x y -∗ biNsteps R m y z -∗ biNsteps R (n + m) x z := by
  iinduction n generalizing %x with
  | zero =>
      iintro Heq
      iunfold biNsteps in Heq
      simp only [Nat.zero_add]
      irewrite [Heq]
      · exact ⟨fun _ _ _ h => wand_ne.ne .rfl (NonExpansive₂.ne h .rfl)⟩
      iintro $
  | succ n ih =>
      rw (occs := [1]) [biNsteps]
      iintro ⟨%x', HR, Hrest⟩ Hyz
      isimp only [biNsteps, Nat.add_comm]
      iexists x'
      iframe HR
      simp only [Nat.add_comm]
      iapply ih $$ Hrest Hyz

@[rocq_alias bi_nsteps_r]
theorem bi_nsteps_right (n : Nat) (x y z : A) :
    biNsteps R n x y -∗ R y z -∗ biNsteps R (n + 1) x z := by
  iintro Hn HR
  iapply bi_nsteps_trans $$ Hn
  iapply bi_nsteps_once $$ HR

@[rocq_alias bi_nsteps_inv_r]
theorem bi_nsteps_inv_right (n : Nat) (x z : A) :
    biNsteps R (n + 1) x z ⊢ ∃ y, biNsteps R n x y ∗ R y z := by
  iintro H
  icases bi_nsteps_add_inv $$ H with ⟨%y, Hn, H1⟩
  iexists y
  iframe Hn
  iapply bi_nsteps_once_inv $$ H1

@[rocq_alias bi_rtc_tc]
theorem bi_rtc_tc (x y : A) : biRtc R x y ⊣⊢ <affine> (x ≡ y) ∨ biTc R x y := by
  isplit
  · irevert %x
    letI : NonExpansive (fun x => iprop(<affine> (x ≡ y) ∨ biTc R x y)) :=
      ⟨fun _ _ _ h => or_ne.ne (affinely_ne.ne ((internalEq.ne_l y).ne h)) (NonExpansive₂.ne h .rfl)⟩
    iapply bi_rtc_ind_left
    iintro !> %x ⟨Heq | ⟨%x', HR, IH⟩⟩
    · ileft; itrivial
    · iright
      icases IH with ⟨Heq|Htc⟩
      · irewrite [Heq] at HR
        · exact NonExpansive₂.ne_right R x
        iapply bi_tc_once; itrivial
      · iapply bi_tc_left $$ HR Htc
  · iintro ⟨Heq|Htc⟩
    · irewrite [Heq]
      iapply bi_rtc_refl
    · iapply bi_tc_rtc; itrivial

@[rocq_alias bi_tc_nsteps]
theorem bi_tc_nsteps (x y : A) :
    biTc R x y ⊣⊢ ∃ n, <affine> ⌜0 < n⌝ ∗ biNsteps R n x y := by
  isplit
  · irevert %x
    letI : NonExpansive (fun x => iprop(∃ n, <affine> ⌜0 < n⌝ ∗ biNsteps R n x y)) :=
      ⟨fun _ _ _ h => exists_ne fun _ => sep_ne.ne .rfl (NonExpansive₂.ne h .rfl)⟩
    iapply bi_tc_ind_left
    iintro !> %x ⟨Hxy | ⟨%x', HR, IH⟩⟩
    · iexists 1
      isplitr
      · itrivial
      · iapply bi_nsteps_once; itrivial
    icases IH with ⟨%n, %hpos, Hn⟩
    iexists n + 1
    isplitr
    · ipureintro;grind
    · iapply bi_nsteps_left $$ HR Hn
  · iintro ⟨%n, %_, Hn⟩
    iinduction n generalizing! %y with
    | zero => trivial
    | succ n ih =>
        icases bi_nsteps_inv_right R n x y $$ Hn with ⟨%x', Hprev, HR⟩
        cases n with
        | zero =>
            iunfold biNsteps in Hprev
            irewrite [←Hprev] at HR
            · exact NonExpansive₂.ne_left R y
            iapply bi_tc_once; itrivial
        | succ n =>
            iapply bi_tc_right $$ [Hprev] HR
            iapply ih $$ [//] Hprev

@[rocq_alias bi_rtc_nsteps]
theorem bi_rtc_nsteps (x y : A) : biRtc R x y ⊣⊢ ∃ n, biNsteps R n x y := by
  isplit
  · letI : NonExpansive (fun x => iprop(∃ n, biNsteps R n x y)) :=
      ⟨fun _ _ _ h => exists_ne fun n => NonExpansive₂.ne h .rfl⟩
    irevert %x
    iapply bi_rtc_ind_left
    iintro !> %x ⟨Heq | ⟨%x', HR, IH⟩⟩
    · iexists 0
      irewrite [Heq]
      · exact NonExpansive₂.ne_left (biNsteps R 0) y
      iapply bi_nsteps_zero
    · icases IH with ⟨%n, Hn⟩
      iexists n + 1
      iapply bi_nsteps_left $$ HR Hn
  · iintro ⟨%n, Hn⟩
    iinduction n generalizing! %y with
    | zero =>
        iunfold biNsteps in Hn
        irewrite [Hn]
        iapply bi_rtc_refl
    | succ n ih =>
        icases bi_nsteps_inv_right $$ Hn with ⟨%x', Hprev, HR⟩
        iapply bi_rtc_right R x x' y $$ [Hprev] HR
        iapply ih; itrivial

end General

section Timeless

variable [Sbi PROP]
variable [Timeless (emp : PROP)] [OFE A] [OFE.Discrete A]
  (R : A → A → PROP)
variable [NonExpansive₂ R]

@[rocq_alias bi_nsteps_timeless]
instance bi_nsteps_timeless (n : Nat) [∀ x y, Timeless (R x y)] (x y : A) :
    Timeless (biNsteps R n x y) := by
  induction n generalizing x y <;>
    unfold biNsteps <;> infer_instance

@[rocq_alias bi_rtc_timeless]
instance bi_rtc_timeless [∀ x y, Timeless (R x y)] (x y : A) :
    Timeless (biRtc R x y) :=
      (equiv_iff.mpr (bi_rtc_nsteps R x y)) ▸ inferInstance

@[rocq_alias bi_tc_timeless]
instance bi_tc_timeless [∀ x y, Timeless (R x y)] (x y : A) :
    Timeless (biTc R x y) :=
      (equiv_iff.mpr (bi_tc_nsteps R x y)) ▸ inferInstance

end Timeless

end Iris
