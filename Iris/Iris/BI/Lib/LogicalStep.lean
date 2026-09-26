/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.BI.Updates
public import Iris.ProofMode

/-! # Logical steps (Transfinite Iris)

This file ports `theories/base_logic/lib/logical_step.v` of Transfinite Iris. The modalities
defined here are the "logical steps" of the transfinite program logics: instead of taking exactly
one later per program step, a proof may take an arbitrary (but finite) number of laters, interleaved
with fancy updates, before the next program step.

- `eventuallyN n E P` (Rocq: `<E>_n P`) takes `n` laters, each surrounded by fancy updates at mask
  `E`.
- `eventually E P` (Rocq: `<E> P`) takes some finite number of such steps.
- `gstepN n Ei E1 E2 P` and `gstep Ei E1 E2 P` (Rocq: `>={E1}={Ei}={E2}=>_n P` and
  `>={E1}={Ei}={E2}=> P`) open the mask from `E1` to `Ei`, take the steps, and close the mask to
  `E2`. The *logical step* of the Rocq development is the special case `Ei = ∅`.

Everything is generic over the step-index type; in particular, the number of laters in `eventually`
is existentially quantified, which is only meaningful as a *finite* number of steps with transfinite
step-indices (where `▷` does not commute with `∃`).
-/

@[expose] public section
variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.BI
open Iris.Std Iris.ProofMode BIFUpdate LawfulSet

variable [BI PROP] [BIFUpdate PROP]

/-! ## Helpers -/

/-- A mask-changing update can be introduced next to a later, keeping the closing update under the
later. -/
theorem later_fupd_mask_intro {E1 E2 : CoPset} (h : E2 ⊆ E1) {W : PROP} :
    ▷ W ⊢ |={E1,E2}=> ▷ (W ∗ |={E2,E1}=> emp) := calc
  _ ⊢ ▷ W ∗ emp                           := sep_emp.mpr
  _ ⊢ ▷ W ∗ |={E1,E2}=> |={E2,E1}=> emp   := sep_mono_right (fupd_mask_subseteq h)
  _ ⊢ |={E1,E2}=> ▷ W ∗ |={E2,E1}=> emp   := fupd_frame_left
  _ ⊢ |={E1,E2}=> ▷ (W ∗ |={E2,E1}=> emp) := fupd_mono <| (sep_mono_right later_intro).trans later_sep_2

/-- A mask-changing update can be introduced, keeping the closing update. -/
theorem fupd_mask_intro_frame {E1 E2 : CoPset} (h : E2 ⊆ E1) {W : PROP} :
    W ⊢ |={E1,E2}=> W ∗ |={E2,E1}=> emp := calc
  _ ⊢ W ∗ emp                           := sep_emp.mpr
  _ ⊢ W ∗ |={E1,E2}=> |={E2,E1}=> emp   := sep_mono_right (fupd_mask_subseteq h)
  _ ⊢ |={E1,E2}=> W ∗ |={E2,E1}=> emp   := fupd_frame_left

/-- Using a closing update. -/
theorem fupd_close {E1 E2 : CoPset} {W : PROP} : W ∗ (|={E1,E2}=> emp) ⊢ |={E1,E2}=> W :=
  fupd_frame_left.trans (fupd_mono sep_emp.mp)

/-- The step-taking fancy update (Rocq: `elim_fupd_step`). -/
@[rocq_alias elim_fupd_step]
instance elimModal_step_fupd p io E (P Q : PROP) :
    ElimModal True p io false iprop(|={E}▷=> P) P iprop(|={E}▷=> Q) Q where
  elim_modal _ := calc
    _ ⊢ (|={E}▷=> P) ∗ (P -∗ Q) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={E}▷=> (P -∗ Q) ∗ P   := sep_comm.mp.trans step_fupd_frame_left
    _ ⊢ |={E}▷=> Q              := step_fupd_mono wand_elim_left

/-! ## Eventually -/

/-- `eventuallyN n E P` (Rocq: `<E>_n P`): `P` holds after `n` laters, each surrounded by fancy
updates at mask `E`. -/
@[rocq_alias eventuallyN]
def eventuallyN : Nat → CoPset → PROP → PROP
  | 0, E, P => iprop(|={E}=> P)
  | n + 1, E, P => iprop(|={E}=> ▷ |={E}=> eventuallyN n E P)

/-- `eventually E P` (Rocq: `<E> P`): `P` holds after finitely many steps. -/
@[rocq_alias eventually]
def eventually (E : CoPset) (P : PROP) : PROP := iprop(|={E}=> ∃ n, eventuallyN n E P)

@[rocq_alias eventuallyN_ne]
instance eventuallyN_ne (n : Nat) (E : CoPset) : OFE.NonExpansive (eventuallyN (PROP := PROP) n E) where
  ne {k P Q} h := by
    induction n with
    | zero => exact fupd_ne.ne h
    | succ n ih => exact fupd_ne.ne (later_ne.ne (fupd_ne.ne ih))

@[rocq_alias eventually_ne]
instance eventually_ne (E : CoPset) : OFE.NonExpansive (eventually (PROP := PROP) E) where
  ne _ _ _ h := fupd_ne.ne (exists_ne fun n => (eventuallyN_ne n E).ne h)

#rocq_ignore eventuallyN_equiv "Follows from `eventuallyN_ne`."
#rocq_ignore eventually_equiv "Follows from `eventually_ne`."

variable {E E1 E2 : CoPset} {P Q R : PROP}

theorem eventuallyN_mono (n : Nat) (h : P ⊢ Q) : eventuallyN n E P ⊢ eventuallyN n E Q := by
  induction n with
  | zero => exact fupd_mono h
  | succ n ih => exact fupd_mono (later_mono (fupd_mono ih))

theorem eventually_mono (h : P ⊢ Q) : eventually E P ⊢ eventually E Q :=
  fupd_mono (exists_mono fun n => eventuallyN_mono n h)

@[rocq_alias eventuallyN_intro]
theorem eventuallyN_intro : P ⊢ eventuallyN 0 E P := fupd_intro

@[rocq_alias eventuallyN_eventually]
theorem eventuallyN_eventually (n : Nat) : eventuallyN n E P ⊢ eventually E P :=
  (exists_intro_trans (Ψ := fun n => eventuallyN n E P) n .rfl).trans fupd_intro

@[rocq_alias eventuallyN_fupd_left]
theorem eventuallyN_fupd_left (n : Nat) : (|={E}=> eventuallyN n E P) ⊢ eventuallyN n E P := by
  cases n <;> exact fupd_trans

@[rocq_alias eventuallyN_fupd_right]
theorem eventuallyN_fupd_right (n : Nat) : eventuallyN n E iprop(|={E}=> P) ⊢ eventuallyN n E P := by
  induction n with
  | zero => exact fupd_trans
  | succ n ih => exact fupd_mono (later_mono (fupd_mono ih))

@[rocq_alias eventuallyN_step_left]
theorem eventuallyN_step_left (n : Nat) : ▷ eventuallyN n E P ⊢ eventuallyN (n + 1) E P :=
  (later_mono fupd_intro).trans fupd_intro

@[rocq_alias eventuallyN_intro_n]
theorem eventuallyN_intro_n (n : Nat) : P ⊢ eventuallyN n E P := by
  induction n with
  | zero => exact eventuallyN_intro
  | succ n ih => exact later_intro.trans ((later_mono ih).trans (eventuallyN_step_left n))

@[rocq_alias eventuallyN_mono]
theorem eventuallyN_mono_le {n1 n2 : Nat} (h : n1 ≤ n2) : eventuallyN n1 E P ⊢ eventuallyN n2 E P := by
  induction n1 generalizing n2 with
  | zero =>
    cases n2 with
    | zero => exact .rfl
    | succ n2 => exact (fupd_mono (eventuallyN_intro_n _)).trans (eventuallyN_fupd_left _)
  | succ n1 ih =>
    cases n2 with
    | zero => omega
    | succ n2 => exact fupd_mono (later_mono (fupd_mono (ih (by omega))))

@[rocq_alias eventuallyN_step_right]
theorem eventuallyN_step_right (n : Nat) : eventuallyN n E iprop(▷ P) ⊢ eventuallyN (n + 1) E P := by
  induction n with
  | zero => exact fupd_mono (later_mono (fupd_intro.trans fupd_intro))
  | succ n ih => exact fupd_mono (later_mono (fupd_mono ih))

@[rocq_alias eventually_fupd_left]
theorem eventually_fupd_left : (|={E}=> eventually E P) ⊢ eventually E P := fupd_trans

@[rocq_alias eventually_fupd_right]
theorem eventually_fupd_right : eventually E iprop(|={E}=> P) ⊢ eventually E P :=
  fupd_mono (exists_mono fun n => eventuallyN_fupd_right n)

@[rocq_alias eventually_step_right]
theorem eventually_step_right : eventually E iprop(▷ P) ⊢ eventually E P :=
  fupd_mono <| exists_elim fun n => (eventuallyN_step_right n).trans (exists_intro_trans (n + 1) .rfl)

@[rocq_alias eventuallyN_mask_mono]
theorem eventuallyN_mask_mono (n : Nat) (h : E1 ⊆ E2) : eventuallyN n E1 P ⊢ eventuallyN n E2 P := by
  induction n with
  | zero => exact fupd_mask_mono h
  | succ n ih =>
    exact (fupd_mono (later_mono ((fupd_mono ih).trans (fupd_mask_mono h)))).trans (fupd_mask_mono h)

@[rocq_alias eventually_mask_mono]
theorem eventually_mask_mono (h : E1 ⊆ E2) : eventually E1 P ⊢ eventually E2 P :=
  (fupd_mono (exists_mono fun n => eventuallyN_mask_mono n h)).trans (fupd_mask_mono h)

@[rocq_alias eventuallyN_compose]
theorem eventuallyN_compose (n m : Nat) :
    eventuallyN n E (eventuallyN m E P) ⊢ eventuallyN (n + m) E P := by
  induction n with
  | zero => rw [Nat.zero_add]; exact eventuallyN_fupd_left m
  | succ n ih => rw [Nat.succ_add]; exact fupd_mono (later_mono (fupd_mono ih))

theorem eventuallyN_frame_right (n : Nat) : eventuallyN n E P ∗ R ⊢ eventuallyN n E iprop(P ∗ R) := by
  induction n with
  | zero => exact fupd_frame_right
  | succ n ih =>
    refine fupd_frame_right.trans (fupd_mono ?_)
    exact (sep_mono_right later_intro).trans <| later_sep_2.trans <| later_mono <|
      fupd_frame_right.trans (fupd_mono ih)

theorem eventuallyN_frame_left (n : Nat) : R ∗ eventuallyN n E P ⊢ eventuallyN n E iprop(R ∗ P) :=
  sep_comm.mp.trans <| (eventuallyN_frame_right n).trans (eventuallyN_mono n sep_comm.mp)

theorem eventuallyN_wand (n : Nat) : eventuallyN n E P ∗ (P -∗ Q) ⊢ eventuallyN n E Q :=
  (eventuallyN_frame_right n).trans (eventuallyN_mono n wand_elim_right)

@[rocq_alias elim_eventuallyN]
instance elimModal_eventuallyN p io E n (P Q : PROP) :
    ElimModal True p io false (eventuallyN n E P) P (eventuallyN n E Q) Q where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans (eventuallyN_wand n)

@[rocq_alias eventuallyN_compose']
theorem eventuallyN_compose' (n m : Nat) :
    eventuallyN n E P ∗ eventuallyN m E iprop(P -∗ Q) ⊢ eventuallyN (n + m) E Q :=
  (eventuallyN_frame_right n).trans <| (eventuallyN_mono n <|
    (eventuallyN_frame_left m).trans (eventuallyN_mono m wand_elim_right)).trans
      (eventuallyN_compose n m)

theorem eventually_frame_right : eventually E P ∗ R ⊢ eventually E iprop(P ∗ R) :=
  fupd_frame_right.trans <| fupd_mono <| sep_exists_right.mp.trans <|
    exists_mono fun n => eventuallyN_frame_right n

@[rocq_alias eventually_compose]
theorem eventually_compose : eventually E P ∗ eventually E iprop(P -∗ Q) ⊢ eventually E Q := by
  refine fupd_sep.trans (fupd_mono ?_)
  refine sep_exists_right.mp.trans (exists_elim fun n => ?_)
  refine sep_exists_left.mp.trans (exists_elim fun m => ?_)
  exact (eventuallyN_compose' n m).trans (exists_intro_trans (n + m) .rfl)

@[rocq_alias eventually_intro]
theorem eventually_intro : P ⊢ eventually E P := eventuallyN_intro.trans (eventuallyN_eventually 0)

#rocq_ignore elim_eventually "A local instance in Rocq; use `eventually_compose`."

/-! ## General steps -/

/-- `gstepN n Ei E1 E2 P` (Rocq: `>={E1}={Ei}={E2}=>_n P`): open the mask from `E1` to `Ei`, take
`n` steps at mask `Ei`, and close the mask to `E2`. -/
@[rocq_alias gstepN]
def gstepN (n : Nat) (Ei E1 E2 : CoPset) (P : PROP) : PROP :=
  iprop(|={E1,Ei}=> eventuallyN n Ei iprop(|={Ei,E2}=> P))

/-- `gstep Ei E1 E2 P` (Rocq: `>={E1}={Ei}={E2}=> P`): open the mask from `E1` to `Ei`, take
finitely many steps at mask `Ei`, and close the mask to `E2`. -/
@[rocq_alias gstep]
def gstep (Ei E1 E2 : CoPset) (P : PROP) : PROP :=
  iprop(|={E1,Ei}=> eventually Ei iprop(|={Ei,E2}=> P))

@[rocq_alias gstep_ne]
instance gstep_ne (Ei E1 E2 : CoPset) : OFE.NonExpansive (gstep (PROP := PROP) Ei E1 E2) where
  ne _ _ _ h := fupd_ne.ne ((eventually_ne _).ne (fupd_ne.ne h))

@[rocq_alias gstepN_ne]
instance gstepN_ne (n : Nat) (Ei E1 E2 : CoPset) : OFE.NonExpansive (gstepN (PROP := PROP) n Ei E1 E2) where
  ne _ _ _ h := fupd_ne.ne ((eventuallyN_ne _ _).ne (fupd_ne.ne h))

#rocq_ignore gstep_equiv "Follows from `gstep_ne`."
#rocq_ignore gstepN_equiv "Follows from `gstepN_ne`."

variable {Ei Ej E3 : CoPset}

theorem gstepN_mono' (n : Nat) (h : P ⊢ Q) : gstepN n Ei E1 E2 P ⊢ gstepN n Ei E1 E2 Q :=
  fupd_mono (eventuallyN_mono n (fupd_mono h))

theorem gstep_mono (h : P ⊢ Q) : gstep Ei E1 E2 P ⊢ gstep Ei E1 E2 Q :=
  fupd_mono (eventually_mono (fupd_mono h))

@[rocq_alias gstepN_fupd_left]
theorem gstepN_fupd_left (n : Nat) :
    (|={E1,E2}=> gstepN n Ei E2 E3 P) ⊢ gstepN n Ei E1 E3 P := fupd_trans

@[rocq_alias gstepN_fupd_right]
theorem gstepN_fupd_right (n : Nat) :
    gstepN n Ei E1 E2 iprop(|={E2,E3}=> P) ⊢ gstepN n Ei E1 E3 P :=
  fupd_mono (eventuallyN_mono n fupd_trans)

@[rocq_alias gstep_fupd_left]
theorem gstep_fupd_left : (|={E1,E2}=> gstep Ei E2 E3 P) ⊢ gstep Ei E1 E3 P := fupd_trans

@[rocq_alias gstep_fupd_right]
theorem gstep_fupd_right : gstep Ei E1 E2 iprop(|={E2,E3}=> P) ⊢ gstep Ei E1 E3 P :=
  fupd_mono (eventually_mono fupd_trans)

@[rocq_alias gstepN_gstep]
theorem gstepN_gstep (n : Nat) : gstepN n Ei E1 E2 P ⊢ gstep Ei E1 E2 P :=
  fupd_mono (eventuallyN_eventually n)

@[rocq_alias gstepN_later]
theorem gstepN_later (n : Nat) (h : Ei ⊆ E1) :
    ▷ gstepN n Ei E1 E2 P ⊢ gstepN (n + 1) Ei E1 E2 P := calc
  _ ⊢ |={E1,Ei}=> ▷ (gstepN n Ei E1 E2 P ∗ |={Ei,E1}=> emp) := later_fupd_mask_intro h
  _ ⊢ |={E1,Ei}=> ▷ |={Ei}=> eventuallyN n Ei iprop(|={Ei,E2}=> P) :=
    fupd_mono (later_mono (fupd_close.trans fupd_trans))
  _ ⊢ gstepN (n + 1) Ei E1 E2 P := fupd_mono fupd_intro

@[rocq_alias gstepN_intro]
theorem gstepN_intro (h : Ei ⊆ E2) : (|={E1,E2}=> P) ⊢ gstepN 0 Ei E1 E2 P :=
  (fupd_mono (fupd_mask_intro_subseteq h)).trans <| fupd_trans.trans (fupd_mono fupd_intro)

@[rocq_alias gstepN_intro']
theorem gstepN_intro' (h : Ei ⊆ E1) : (|={E1,E2}=> P) ⊢ gstepN 0 Ei E1 E2 P :=
  (fupd_mask_intro_subseteq h).trans (fupd_mono (fupd_trans.trans fupd_intro))

theorem fupd_later_squash (h : Ei ⊆ E2) :
    (|={Ei,E2}=> ▷ P) ⊢ eventuallyN 1 Ei iprop(|={Ei,E2}=> P) := by
  refine (fupd_mono (fupd_mask_intro_frame h)).trans (fupd_trans.trans (fupd_mono ?_))
  refine (sep_mono_right later_intro).trans (later_sep_2.trans (later_mono ?_))
  exact fupd_close.trans (fupd_intro.trans fupd_intro)

@[rocq_alias gstep_squash]
theorem gstep_squash (h : Ei ⊆ E2) : gstep Ei E1 E2 iprop(▷ P) ⊢ gstep Ei E1 E2 P :=
  fupd_mono <| fupd_mono <| exists_elim fun n =>
    ((eventuallyN_mono n (fupd_later_squash h)).trans (eventuallyN_compose n 1)).trans
      (exists_intro_trans (n + 1) .rfl)

theorem eventuallyN_change_iter (n : Nat) (h : Ej ⊆ Ei) :
    eventuallyN n Ei iprop(|={Ei,E2}=> P) ∗ (|={Ej,Ei}=> emp) ⊢
      eventuallyN n Ej iprop(|={Ej,E2}=> P) := by
  induction n with
  | zero => exact fupd_close.trans <|
      (fupd_mono fupd_trans).trans (fupd_trans.trans fupd_intro)
  | succ n ih => calc
    _ ⊢ |={Ej,Ei}=> eventuallyN (n + 1) Ei iprop(|={Ei,E2}=> P) := fupd_close
    _ ⊢ |={Ej,Ei}=> ▷ |={Ei}=> eventuallyN n Ei iprop(|={Ei,E2}=> P) := fupd_trans
    _ ⊢ |={Ej,Ei}=> |={Ei,Ej}=>
          ▷ ((|={Ei}=> eventuallyN n Ei iprop(|={Ei,E2}=> P)) ∗ |={Ej,Ei}=> emp) :=
      fupd_mono (later_fupd_mask_intro h)
    _ ⊢ |={Ej}=> ▷ ((|={Ei}=> eventuallyN n Ei iprop(|={Ei,E2}=> P)) ∗ |={Ej,Ei}=> emp) :=
      fupd_trans
    _ ⊢ eventuallyN (n + 1) Ej iprop(|={Ej,E2}=> P) :=
      fupd_mono (later_mono ((sep_mono_left (eventuallyN_fupd_left n)).trans (ih.trans fupd_intro)))

@[rocq_alias gstepN_change_iter]
theorem gstepN_change_iter (n : Nat) (h : Ej ⊆ Ei) :
    gstepN n Ei E1 E2 P ⊢ gstepN n Ej E1 E2 P :=
  (fupd_mono (fupd_mask_intro_frame h)).trans <| fupd_trans.trans <|
    fupd_mono (eventuallyN_change_iter n h)

@[rocq_alias gstep_change_iter]
theorem gstep_change_iter (h : Ej ⊆ Ei) : gstep Ei E1 E2 P ⊢ gstep Ej E1 E2 P := calc
  _ ⊢ |={E1,Ei}=> ∃ n, eventuallyN n Ei iprop(|={Ei,E2}=> P) := fupd_trans
  _ ⊢ |={E1,Ei}=> |={Ei,Ej}=>
        (∃ n, eventuallyN n Ei iprop(|={Ei,E2}=> P)) ∗ |={Ej,Ei}=> emp :=
    fupd_mono (fupd_mask_intro_frame h)
  _ ⊢ |={E1,Ej}=> (∃ n, eventuallyN n Ei iprop(|={Ei,E2}=> P)) ∗ |={Ej,Ei}=> emp := fupd_trans
  _ ⊢ |={E1,Ej}=> ∃ n, eventuallyN n Ej iprop(|={Ej,E2}=> P) :=
    fupd_mono (sep_exists_right.mp.trans (exists_mono fun n => eventuallyN_change_iter n h))
  _ ⊢ gstep Ej E1 E2 P := fupd_mono fupd_intro

theorem eventuallyN_compose_masks (n1 n2 : Nat) (h2i : E2 ⊆ Ei) (hij : Ei ⊆ Ej) :
    eventuallyN n1 Ei iprop(|={Ei,E2}=> P) ∗ (|={E2,Ei}=> emp) ∗
        eventuallyN n2 Ej iprop(|={Ej,E3}=> Q) ⊢
      eventuallyN (n1 + n2) Ej iprop(|={Ej,E3}=> P ∗ Q) := by
  induction n1 with
  | zero =>
    have hP : eventuallyN 0 Ei iprop(|={Ei,E2}=> P) ∗ (|={E2,Ei}=> emp) ⊢ |={Ej}=> P :=
      sep_comm.mp.trans <| fupd_frame_right.trans <|
        (fupd_mono (emp_sep.mp.trans fupd_trans)).trans <| fupd_trans.trans <|
          fupd_mask_mono (subset_trans h2i hij)
    rw [Nat.zero_add]
    refine sep_assoc.mpr.trans <| (sep_mono_left hP).trans <| fupd_frame_right.trans <|
      (fupd_mono ?_).trans (eventuallyN_fupd_left n2)
    exact (eventuallyN_frame_left n2).trans (eventuallyN_mono n2 fupd_frame_left)
  | succ n1 ih =>
    rw [Nat.succ_add]
    refine (sep_mono_left (fupd_mask_mono hij)).trans <| fupd_frame_right.trans <| fupd_mono ?_
    refine (sep_mono_right later_intro).trans <| later_sep_2.trans <| later_mono ?_
    exact (sep_mono_left (eventuallyN_fupd_left n1)).trans (ih.trans fupd_intro)

theorem gstep_compose_aux (h2i : E2 ⊆ Ei) (hij : Ei ⊆ Ej) :
    (∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗ (|={E2,Ei}=> emp) ∗ gstep Ej E2 E3 Q ⊢
      |={E2,Ej}=> |={Ej}=> ∃ k, eventuallyN k Ej iprop(|={Ej,E3}=> P ∗ Q) := calc
  _ ⊢ |={E2,Ej}=> ((∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗ (|={E2,Ei}=> emp)) ∗
        |={Ej}=> ∃ n2, eventuallyN n2 Ej iprop(|={Ej,E3}=> Q) := sep_assoc.mpr.trans fupd_frame_left
  _ ⊢ |={E2,Ej}=> |={Ej}=> ((∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗
        (|={E2,Ei}=> emp)) ∗ ∃ n2, eventuallyN n2 Ej iprop(|={Ej,E3}=> Q) :=
    fupd_mono fupd_frame_left
  _ ⊢ |={E2,Ej}=> |={Ej}=> ∃ k, eventuallyN k Ej iprop(|={Ej,E3}=> P ∗ Q) := by
    refine fupd_mono (fupd_mono ?_)
    refine sep_exists_left.mp.trans <| exists_elim fun n2 => ?_
    refine (sep_mono_left sep_exists_right.mp).trans <| sep_exists_right.mp.trans <|
      exists_elim fun n1 => ?_
    exact sep_assoc.mp.trans <| (eventuallyN_compose_masks n1 n2 h2i hij).trans
      (exists_intro_trans (Ψ := fun k => eventuallyN k Ej iprop(|={Ej,E3}=> P ∗ Q)) (n1 + n2) .rfl)

@[rocq_alias gstep_compose]
theorem gstep_compose (h2i : E2 ⊆ Ei) (hij : Ei ⊆ Ej) :
    gstep Ei E1 E2 P ⊢ gstep Ej E2 E3 Q -∗ gstep Ej E1 E3 iprop(P ∗ Q) := by
  refine wand_intro ?_
  calc
    _ ⊢ |={E1,Ei}=> (|={Ei}=> ∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗
          gstep Ej E2 E3 Q := fupd_frame_right
    _ ⊢ |={E1,Ei}=> |={Ei}=> (∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗
          gstep Ej E2 E3 Q := fupd_mono fupd_frame_right
    _ ⊢ |={E1,Ei}=> (∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗
          gstep Ej E2 E3 Q := fupd_trans
    _ ⊢ |={E1,Ei}=> |={Ei,E2}=> ((∃ n1, eventuallyN n1 Ei iprop(|={Ei,E2}=> P)) ∗
          gstep Ej E2 E3 Q) ∗ |={E2,Ei}=> emp := fupd_mono (fupd_mask_intro_frame h2i)
    _ ⊢ |={E1,Ei}=> |={Ei,E2}=> |={E2,Ej}=> |={Ej}=>
          ∃ k, eventuallyN k Ej iprop(|={Ej,E3}=> P ∗ Q) :=
      fupd_mono (fupd_mono (sep_right_comm.mp.trans (sep_assoc.mp.trans (gstep_compose_aux h2i hij))))
    _ ⊢ gstep Ej E1 E3 iprop(P ∗ Q) := (fupd_mono fupd_trans).trans fupd_trans

@[rocq_alias gstepN_mono]
theorem gstepN_mono {k1 k2 : Nat} (h : k1 ≤ k2) : gstepN k1 Ei E1 E2 P ⊢ gstepN k2 Ei E1 E2 P :=
  fupd_mono (eventuallyN_mono_le h)

theorem gstepN_frame_right (n : Nat) : gstepN n Ei E1 E2 P ∗ R ⊢ gstepN n Ei E1 E2 iprop(P ∗ R) :=
  fupd_frame_right.trans <| fupd_mono <|
    (eventuallyN_frame_right n).trans (eventuallyN_mono n fupd_frame_right)

theorem gstep_frame_right : gstep Ei E1 E2 P ∗ R ⊢ gstep Ei E1 E2 iprop(P ∗ R) :=
  fupd_frame_right.trans <| fupd_mono <| eventually_frame_right.trans (eventually_mono fupd_frame_right)

@[rocq_alias elim_gstep]
instance elimModal_gstep p io Ei E1 E2 (P Q : PROP) :
    ElimModal True p io false (gstep Ei E1 E2 P) P (gstep Ei E1 E2 Q) Q where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    gstep_frame_right.trans (gstep_mono wand_elim_right)

@[rocq_alias elim_gstepN]
instance elimModal_gstepN p io Ei E1 E2 n (P Q : PROP) :
    ElimModal True p io false (gstepN n Ei E1 E2 P) P (gstepN n Ei E1 E2 Q) Q where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (gstepN_frame_right n).trans (gstepN_mono' n wand_elim_right)

theorem gstep_iter_frame_right (n : Nat) :
    Nat.repeat (gstep ∅ E1 E2) n P ∗ R ⊢ Nat.repeat (gstep ∅ E1 E2) n iprop(P ∗ R) := by
  induction n with
  | zero => exact .rfl
  | succ n ih => exact gstep_frame_right.trans (gstep_mono ih)

theorem gstep_iter_mono (n : Nat) (h : P ⊢ Q) :
    Nat.repeat (gstep ∅ E1 E2) n P ⊢ Nat.repeat (gstep ∅ E1 E2) n Q := by
  induction n with
  | zero => exact h
  | succ n ih => exact gstep_mono ih

@[rocq_alias elim_gstep_N]
instance elimModal_gstep_iter p io E1 E2 n (P Q : PROP) :
    ElimModal True p io false (Nat.repeat (gstep ∅ E1 E2) n P) P
      (Nat.repeat (gstep ∅ E1 E2) n Q) Q where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (gstep_iter_frame_right n).trans (gstep_iter_mono n wand_elim_right)

/-! ## Logical steps

A *logical step* is a general step whose iteration mask is empty (Rocq notations
`>={E1}=={E2}=>_n P` and `>={E1}=={E2}=> P`). -/

@[rocq_alias lstep_fupd_left]
theorem lstep_fupd_left : (|={E1,E2}=> gstep ∅ E2 E3 P) ⊢ gstep ∅ E1 E3 P := gstep_fupd_left

@[rocq_alias lstep_fupd_right]
theorem lstep_fupd_right : gstep ∅ E1 E2 iprop(|={E2,E3}=> P) ⊢ gstep ∅ E1 E3 P := gstep_fupd_right

@[rocq_alias lstepN_fupd_left]
theorem lstepN_fupd_left (n : Nat) : (|={E1,E2}=> gstepN n ∅ E2 E3 P) ⊢ gstepN n ∅ E1 E3 P :=
  gstepN_fupd_left n

@[rocq_alias lstepN_fupd_right]
theorem lstepN_fupd_right (n : Nat) : gstepN n ∅ E1 E2 iprop(|={E2,E3}=> P) ⊢ gstepN n ∅ E1 E3 P :=
  gstepN_fupd_right n

@[rocq_alias lstepN_lstep]
theorem lstepN_lstep (n : Nat) : gstepN n ∅ E1 E2 P ⊢ gstep ∅ E1 E2 P := gstepN_gstep n

@[rocq_alias lstepN_later]
theorem lstepN_later (n : Nat) : ▷ gstepN n ∅ E1 E2 P ⊢ gstepN (n + 1) ∅ E1 E2 P :=
  gstepN_later n empty_subset

@[rocq_alias lstepN_intro']
theorem lstepN_intro' : (|={E1,E2}=> P) ⊢ gstepN 0 ∅ E1 E2 P :=
  gstepN_intro empty_subset

@[rocq_alias lstepN_intro]
theorem lstepN_intro (n : Nat) : (|={E1,E2}=> P) ⊢ gstepN n ∅ E1 E2 P :=
  lstepN_intro'.trans (gstepN_mono (Nat.zero_le n))

@[rocq_alias lstep_squash]
theorem lstep_squash : gstep ∅ E1 E2 iprop(▷ P) ⊢ gstep ∅ E1 E2 P :=
  gstep_squash empty_subset

@[rocq_alias lstep_intro]
theorem lstep_intro : (|={E1,E2}=> P) ⊢ gstep ∅ E1 E2 P :=
  lstepN_intro'.trans (lstepN_lstep 0)

end Iris.BI
