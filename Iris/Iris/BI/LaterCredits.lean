/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.BI
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Updates

@[expose] public section


variable {SI : Type _} [Iris.SIdx SI]

/-! # Later credits -/

namespace Iris
open BI

/-- Later credits: `£ n` denotes ownership of `n` later credits. -/
@[rocq_alias LaterCredits]
class LaterCredits (PROP : Type _) where
  lc : Nat → PROP
export LaterCredits (lc)

attribute [inherit_doc LaterCredits] LaterCredits.lc
notation:max "£ " i:40 => LaterCredits.lc i

@[rocq_alias BiLaterCredits]
class BILaterCredits (PROP : Type _) [BI.BIBase PROP] extends LaterCredits PROP where
  lc_split {n m : Nat} : £ (n + m) ⊣⊢@{PROP} £ n ∗ £ m
  lc_timeless (n : Nat) : Timeless (PROP := PROP) (£ n)
  lc_0_persistent : Persistent (PROP := PROP) (£ 0)
  lc_affine (n : Nat) : Affine (PROP := PROP) (£ n)
export BILaterCredits (lc_split lc_timeless lc_0_persistent lc_affine)
attribute [instance] lc_timeless lc_0_persistent lc_affine

#rocq_ignore BiLaterCreditsMixin "Included in BILaterCredits typeclass."

@[rocq_alias BiBUpdLaterCredits]
class BIBUpdLaterCredits (PROP : Type _) [BI.BIBase PROP] [LaterCredits PROP] [BUpd PROP] where
  lc_zero : ⊢@{PROP} |==> £ 0
export BIBUpdLaterCredits (lc_zero)

@[rocq_alias BiFUpdLaterCredits]
class BIFUpdLaterCredits (PROP : Type _) [BI.BIBase PROP] [LaterCredits PROP] [FUpd PROP] where
  lc_fupd_elim_later {E : CoPset} {P : PROP} : £ 1 -∗ (▷ P) -∗ |={E}=> P
export BIFUpdLaterCredits (lc_fupd_elim_later)

section LcLaws

variable {PROP : Type _} [BI SI PROP] [BILaterCredits PROP]

#rocq_ignore lc_split "Defined in the `BILaterCredits` class."
#rocq_ignore lc_timeless "Defined in the `BILaterCredits` class."
#rocq_ignore lc_0_persistent "Defined in the `BILaterCredits` class."
#rocq_ignore lc_0_affine "Defined in the `BILaterCredits` class."

@[rocq_alias lc_succ]
theorem lc_succ {n : Nat} : £ (.succ n) ⊣⊢@{PROP} £ 1 ∗ £ n := by
  rw [Nat.succ_eq_add_one, Nat.add_comm]
  exact lc_split

@[rocq_alias lc_weaken]
theorem lc_weaken {n : Nat} (m : Nat) (h : m ≤ n) : £ n ⊢@{PROP} £ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact lc_split.mp.trans sep_elim_left

end LcLaws

section LcFUpdDerived

variable {PROP : Type _} [BI SI PROP] [BILaterCredits PROP] [BIFUpdate SI PROP] [BIFUpdLaterCredits PROP]

@[rocq_alias lc_fupd_add_later]
theorem lc_fupd_add_later {E1 E2 : CoPset} {P : PROP} :
    £ 1 -∗ (▷ |={E1,E2}=> P) -∗ |={E1,E2}=> P :=
  entails_wand <| wand_intro <|
    (wand_elim (wand_entails lc_fupd_elim_later)).trans BIFUpdate.trans

@[rocq_alias lc_fupd_add_laterN]
theorem lc_fupd_add_laterN (n : Nat) {E1 E2 : CoPset} {P : PROP} :
    £ n -∗ (▷^[n] |={E1,E2}=> P) -∗ |={E1,E2}=> P := by
  refine entails_wand <| wand_intro ?_
  induction n with
  | zero => exact sep_elim_right
  | succ n IH =>
    calc
      _ ⊢ £ 1 ∗ £ n ∗ ▷ ▷^[n] |={E1,E2}=> P := (sep_mono_left lc_succ.mp).trans sep_assoc.mp
      _ ⊢ £ 1 ∗ ▷ (£ n ∗ ▷^[n] |={E1,E2}=> P) :=
        sep_mono_right <| (sep_mono_left later_intro).trans later_sep_2
      _ ⊢ £ 1 ∗ ▷ |={E1,E2}=> P := sep_mono_right <| later_mono IH
      _ ⊢ |={E1,E2}=> P := wand_elim (wand_entails lc_fupd_add_later)

@[rocq_alias lc_fupd_add_step_fupdN]
theorem lc_fupd_add_step_fupdN (E1 E2 E3 : CoPset) (P : PROP) (n : Nat) :
    £ n -∗ (|={E1}[E2]▷=>^[n] |={E1,E3}=> P) -∗ |={E1,E3}=> P := by
  refine entails_wand <| wand_intro ?_
  induction n with
  | zero => exact sep_elim_right
  | succ n IH =>
    calc
      _ ⊢ £ 1 ∗ £ n ∗ |={E1}[E2]▷=> |={E1}[E2]▷=>^[n] |={E1,E3}=> P :=
        (sep_mono_left lc_succ.mp).trans sep_assoc.mp
      _ ⊢ £ 1 ∗ |={E1}[E2]▷=> |={E1,E3}=> P :=
        sep_mono_right <| step_fupd_frame_left.trans <| step_fupd_mono IH
      _ ⊢ |={E1,E2}=> £ 1 ∗ ▷ |={E2,E1}=> |={E1,E3}=> P := fupd_frame_left
      _ ⊢ |={E1,E3}=> P := fupd_elim <| (sep_mono_right <| later_mono BIFUpdate.trans).trans
          (wand_elim (wand_entails lc_fupd_add_later))

end LcFUpdDerived

end Iris
