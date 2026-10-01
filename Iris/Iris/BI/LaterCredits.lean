/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.BI
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Updates

@[expose] public section

/-! # Later credits

A generic interface for an arbitrary implementation of later credits via the
`BILaterCredits`, `BIBUpdLaterCredits` and `BIFUpdLaterCredits` typeclasses. They state
the primitive laws for later credits and their interaction with `bupd` and `fupd`, which
let you split and allocate later credits, and use them to eliminate laters, respectively.
See `Iris.Instances.Lib.LaterCredits` and `Iris.BI.MonPred` for instances. -/

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
class BILaterCredits (PROP : Type _) [BI PROP] extends LaterCredits PROP where
  lc_split {n m : Nat} : £ (n + m) ⊣⊢@{PROP} £ n ∗ £ m
  lc_timeless (n : Nat) : Timeless (PROP := PROP) (£ n)
  lc_0_persistent : Persistent (PROP := PROP) (£ 0)
  lc_affine (n : Nat) : Affine (PROP := PROP) (£ n)

#rocq_ignore BiLaterCreditsMixin "Included in BILaterCredits typeclass."

@[rocq_alias BiBUpdLaterCredits]
class BIBUpdLaterCredits (PROP : Type _) [BI PROP] [BILaterCredits PROP] [BIUpdate PROP] where
  lc_zero : ⊢@{PROP} |==> £ 0
export BIBUpdLaterCredits (lc_zero)

/-- `lc_fupd_elim_later` allows to eliminate a later from a hypothesis at an update.
This is typically used as `imod lc_fupd_elim_later $$ Hcredit HP with HP`, where `Hcredit`
is a credit available in the context and `HP` is the assumption from which a later should
be stripped. -/
@[rocq_alias BiFUpdLaterCredits]
class BIFUpdLaterCredits (PROP : Type _) [BI PROP] [BILaterCredits PROP] [BIFUpdate PROP] where
  lc_fupd_elim_later {E : CoPset} {P : PROP} : ⊢ £ 1 -∗ (▷ P) -∗ |={E}=> P
export BIFUpdLaterCredits (lc_fupd_elim_later)

section LcLaws

variable {PROP : Type _} [BI PROP] [BILaterCredits PROP]

@[rocq_alias lc_split]
theorem lc_split {n m : Nat} : £ (n + m) ⊣⊢@{PROP} £ n ∗ £ m := BILaterCredits.lc_split

@[rocq_alias lc_timeless]
instance lc_timeless {n : Nat} : Timeless (PROP := PROP) (£ n) := BILaterCredits.lc_timeless n

@[rocq_alias lc_0_persistent]
instance lc_0_persistent : Persistent (PROP := PROP) (£ 0) := BILaterCredits.lc_0_persistent

@[rocq_alias lc_0_affine]
instance lc_0_affine {n : Nat} : Affine (PROP := PROP) (£ n) := BILaterCredits.lc_affine n

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

variable {PROP : Type _} [BI PROP] [BILaterCredits PROP] [BIFUpdate PROP] [BIFUpdLaterCredits PROP]

/-- If the goal is a fancy update, this lemma can be used to make a later appear in front
of it in exchange for a later credit. This is typically used as
`iapply lc_fupd_add_later $$ Hcredit`, where `Hcredit` is a credit available in the
context. -/
@[rocq_alias lc_fupd_add_later]
theorem lc_fupd_add_later {E1 E2 : CoPset} {P : PROP} :
    ⊢ £ 1 -∗ (▷ |={E1,E2}=> P) -∗ |={E1,E2}=> P :=
  entails_wand <| wand_intro <|
    (wand_elim (wand_entails lc_fupd_elim_later)).trans BIFUpdate.trans

/-- Similar to `lc_fupd_add_later`, but here we are adding `n` laters. -/
@[rocq_alias lc_fupd_add_laterN]
theorem lc_fupd_add_laterN (n : Nat) {E1 E2 : CoPset} {P : PROP} :
    ⊢ £ n -∗ (▷^[n] |={E1,E2}=> P) -∗ |={E1,E2}=> P := by
  refine entails_wand <| wand_intro ?_
  induction n with
  | zero => exact sep_elim_right
  | succ n IH =>
    calc
      _ ⊢ £ 1 ∗ £ n ∗ ▷ ▷^[n] |={E1,E2}=> P := (sep_mono_left lc_succ.mp).trans sep_assoc.mp
      _ ⊢ £ 1 ∗ ▷ (£ n ∗ ▷^[n] |={E1,E2}=> P) :=
        sep_mono_right <| (sep_mono_left later_intro).trans later_sep.mpr
      _ ⊢ £ 1 ∗ ▷ |={E1,E2}=> P := sep_mono_right <| later_mono IH
      _ ⊢ |={E1,E2}=> P := wand_elim (wand_entails lc_fupd_add_later)

@[rocq_alias lc_fupd_add_step_fupdN]
theorem lc_fupd_add_step_fupdN (E1 E2 E3 : CoPset) (P : PROP) (n : Nat) :
    ⊢ £ n -∗ (|={E1}[E2]▷=>^[n] |={E1,E3}=> P) -∗ |={E1,E3}=> P := by
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
      _ ⊢ |={E1,E3}=> P := fupd_elim <|
        (sep_mono_right <| later_mono BIFUpdate.trans).trans
          (wand_elim (wand_entails lc_fupd_add_later))

end LcFUpdDerived

end Iris
