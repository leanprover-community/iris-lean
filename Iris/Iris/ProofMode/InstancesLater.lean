/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ClassesMake
public import Iris.ProofMode.ModalityInstances
public import Iris.Std.TC

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

/-- FromAssumption -/

@[rocq_alias from_assumption_later]
instance fromAssumption_later [BI PROP] (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷ Q) where
  from_assumption := h.1.trans later_intro

@[rocq_alias from_assumption_laterN]
instance fromAssumption_laterN [BI PROP] n (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(▷^[n] Q) where
  from_assumption := h.1.trans (laterN_intro n)

@[rocq_alias from_assumption_except_0]
instance fromAssumption_except0 [BI PROP] (p : Bool) (P Q : PROP)
    [h : FromAssumption p ioP P Q] : FromAssumption p ioP P iprop(◇ Q) where
  from_assumption := h.1.trans except0_intro


/-- FromPure -/

@[rocq_alias from_pure_later]
instance fromPure_later [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(▷ P) io φ where
  from_pure := h.1.trans later_intro

@[rocq_alias from_pure_laterN]
instance fromPure_laterN [BI PROP] (a : Bool) (n : Nat) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(▷^[n] P) io φ where
  from_pure := h.1.trans (laterN_intro n)

@[rocq_alias from_pure_except_0]
instance fromPure_except0 [BI PROP] (a : Bool) (P : PROP) (φ : Prop)
    [h : FromPure a P io φ] : FromPure a iprop(◇ P) io φ where
  from_pure := h.1.trans except0_intro

/-- IntoWand -/

@[rocq_alias into_wand_later]
instance intoWand_later [BI PROP] (p q : Bool) (R P Q : PROP)
    [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q iprop(▷ R) ioP iprop(▷ P) ioQ iprop(▷ Q) where
  into_wand := later_intuitionisticallyIf_2.trans <|
    (later_mono h.1).trans <| later_wand.trans <| wand_mono later_intuitionisticallyIf_2 .rfl

#rocq_ignore into_wand_later_args "IntoWand' is not used in Lean"
-- TODO: see if this is necessary. It is an instance for IntoWand' in Rocq
-- instance intoWand_later_args [BI PROP] (p q : Bool) (R P Q : PROP)
--     [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q R ioP iprop(▷ P) ioQ iprop(▷ Q) where
--   into_wand := (intuitionisticallyIf_mono later_intro).trans <| later_intuitionisticallyIf_2.trans <|
--     (later_mono h.1).trans <| later_wand.trans <| wand_mono later_intuitionisticallyIf_2 .rfl

@[rocq_alias into_wand_laterN]
instance intoWand_laterN [BI PROP] (n : Nat) (p q : Bool) (R P Q : PROP)
    [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q iprop(▷^[n] R) ioP iprop(▷^[n] P) ioQ iprop(▷^[n] Q) where
  into_wand := (laterN_intuitionisticallyIf n).trans <|
    (laterN_mono n h.1).trans <| (laterN_wand n).trans <| wand_mono (laterN_intuitionisticallyIf n) .rfl

#rocq_ignore into_wand_laterN_args "IntoWand' is not used in Lean"
-- TODO: see if this is necessary. It is an instance for IntoWand' in Rocq
-- instance intoWand_laterN_args [BI PROP] (n : Nat) (p q : Bool) (R P Q : PROP)
--     [h : IntoWand p q R ioP P ioQ Q] : IntoWand p q R ioP iprop(▷^[n] P) ioQ iprop(▷^[n] Q) where
--   into_wand := (intuitionisticallyIf_mono (laterN_intro n)).trans <| (laterN_intuitionisticallyIf n).trans <|
--     (laterN_mono n h.1).trans <| (laterN_wand n).trans <| wand_mono (laterN_intuitionisticallyIf n) .rfl

/-- FromAnd -/

@[rocq_alias from_and_later]
instance fromAnd_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_and := later_and.2.trans (later_mono h.1)

@[rocq_alias from_and_laterN]
instance fromAnd_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_and := (laterN_and n).2.trans (laterN_mono n h.1)

@[rocq_alias from_and_except_0]
instance fromAnd_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromAnd P Q1 Q2] : FromAnd iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_and := except0_and.2.trans (except0_mono h.1)

/-- FromSep -/

@[rocq_alias from_sep_later]
instance fromSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_sep := later_sep.2.trans (later_mono h.1)

@[rocq_alias from_sep_laterN]
instance fromSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_sep := (laterN_sep n).2.trans (laterN_mono n h.1)

@[rocq_alias from_sep_except_0]
instance fromSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromSep P Q1 Q2] : FromSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_sep := except0_sep.2.trans (except0_mono h.1)

/-- IntoAnd -/

@[rocq_alias into_and_later]
instance intoAnd_later [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <|
    later_intuitionisticallyIf_2.trans <| (later_mono <| h.1.trans intuitionisticallyIf_elim).trans later_and.1

@[rocq_alias into_and_laterN]
instance intoAnd_laterN [BI PROP] (n : Nat) (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <|
    (laterN_intuitionisticallyIf n).trans <|
    (laterN_mono n <| h.1.trans intuitionisticallyIf_elim).trans (laterN_and n).1

@[rocq_alias into_and_except_0]
instance intoAnd_except0 [BI PROP] (p : Bool) (P Q1 Q2 : PROP)
    [h : IntoAnd p P Q1 Q2] : IntoAnd p iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_and := intuitionisticallyIf_intro_intuitionisticallyIf <|
    except0_intuitionisticallyIf.trans <|
    (except0_mono <| h.1.trans intuitionisticallyIf_elim).trans except0_and.1

/-- IntoSep -/

@[rocq_alias into_sep_later]
instance intoSep_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans later_sep.1

@[rocq_alias into_sep_laterN]
instance intoSep_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_sep := (laterN_mono n h.1).trans (laterN_sep n).1

@[rocq_alias into_sep_except_0]
instance intoSep_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoSep P Q1 Q2] : IntoSep iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_sep := (except0_mono h.1).trans except0_sep.1

/-- FromOr -/

@[rocq_alias from_or_later]
instance fromOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  from_or := later_or.2.trans (later_mono h.1)

@[rocq_alias from_or_laterN]
instance fromOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  from_or := (laterN_or n).2.trans (laterN_mono n h.1)

@[rocq_alias from_or_except_0]
instance fromOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : FromOr P Q1 Q2] : FromOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  from_or := except0_or.2.trans (except0_mono h.1)

/-- IntoOr -/

@[rocq_alias into_or_later]
instance intoOr_later [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_or := (later_mono h.1).trans later_or.1

@[rocq_alias into_or_laterN]
instance intoOr_laterN [BI PROP] (n : Nat) (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(▷^[n] P) iprop(▷^[n] Q1) iprop(▷^[n] Q2) where
  into_or := (laterN_mono n h.1).trans (laterN_or n).1

@[rocq_alias into_or_except_0]
instance intoOr_except0 [BI PROP] (P Q1 Q2 : PROP)
    [h : IntoOr P Q1 Q2] : IntoOr iprop(◇ P) iprop(◇ Q1) iprop(◇ Q2) where
  into_or := (except0_mono h.1).trans except0_or.1

/-- FromExists -/

@[rocq_alias from_exist_later]
instance fromExists_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_exists := (exists_elim fun x => (later_mono (exists_intro x))).trans (later_mono h.1)

@[rocq_alias from_exist_laterN]
instance fromExists_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_exists := (exists_elim fun x => (laterN_mono n (exists_intro x))).trans (laterN_mono n h.1)

@[rocq_alias from_exist_except_0]
instance fromExists_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromExists P Φ] : FromExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_exists := except0_exists_mpr.trans (except0_mono h.1)

/-- IntoExists -/
@[rocq_alias into_exist_later]
instance intoExists_later [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_exists := (later_mono h.1).trans later_exists.2

@[rocq_alias into_exist_laterN]
instance intoExists_laterN [BI PROP] [Inhabited α] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_exists := (laterN_mono n h.1).trans (laterN_exists n).1

@[rocq_alias into_exist_except_0]
instance intoExists_except0 [BI PROP] [Inhabited α] (P : PROP) (Φ : α → PROP)
    [h : IntoExists P Φ] : IntoExists iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_exists := (except0_mono h.1).trans (except0_exists.1)

/-- IntoForall -/

@[rocq_alias into_forall_later]
instance intoForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_forall := (later_mono h.1).trans later_forall.1

@[rocq_alias into_forall_laterN]
instance intoForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  into_forall := (laterN_mono n h.1).trans (laterN_forall n).1

@[rocq_alias into_forall_except_0]
instance intoForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : IntoForall P Φ] : IntoForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  into_forall := (except0_mono h.1).trans except0_forall.1

/-- FromForall -/
@[rocq_alias from_forall_later]
instance fromForall_later [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  from_forall := later_forall.2.trans (later_mono h.1)

@[rocq_alias from_forall_laterN]
instance fromForall_laterN [BI PROP] (n : Nat) (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(▷^[n] P) (fun a => iprop(▷^[n] Φ a)) where
  from_forall := (laterN_forall n).2.trans (laterN_mono n h.1)

@[rocq_alias from_forall_except_0]
instance fromForall_except0 [BI PROP] (P : PROP) (Φ : α → PROP)
    [h : FromForall P Φ] : FromForall iprop(◇ P) (fun a => iprop(◇ Φ a)) where
  from_forall := except0_forall.2.trans (except0_mono h.1)

/-- IsExcept0 -/
@[rocq_alias is_except_0_except_0]
instance isExcept0_except0 [BI PROP] (P : PROP) : IsExcept0 iprop(◇ P) where
  is_except0 := (except0_idem.1)

@[rocq_alias is_except_0_later]
instance isExcept0_later [BI PROP] (P : PROP) : IsExcept0 iprop(▷ P) where
  is_except0 := except0_later

/-- FromModal -/
@[rocq_alias from_modal_later]
instance fromModal_later [BI PROP] (P : PROP) :
  FromModal True (modality_laterN 1) iprop(▷^[1] P) iprop(▷ P) P where
  from_modal _ := .rfl

@[rocq_alias from_modal_laterN]
instance fromModal_laterN [BI PROP] (P : PROP) n :
  FromModal True (modality_laterN n) iprop(▷^[n] P) iprop(▷^[n] P) P where
  from_modal _ := .rfl

@[rocq_alias from_modal_except_0]
instance fromModal_except0 [BI PROP] (P : PROP) :
  FromModal True modality_id iprop(◇ P) iprop(◇ P) P where
  from_modal _ := except0_intro

/-- IntoExcept0 -/
@[rocq_alias into_except_0_except_0]
instance intoExcept0_except0 [BI PROP] (P : PROP) : IntoExcept0 iprop(◇ P) P where
  into_except0 := .rfl

@[rocq_alias into_except_0_later]
instance intoExcept0_later [BI PROP] (P : PROP) [Timeless P] : IntoExcept0 iprop(▷ P) P where
  into_except0 := Timeless.timeless

@[rocq_alias into_except_0_later_if]
instance intoExcept0_laterIf [BI PROP] p (P : PROP) [Timeless P] : IntoExcept0 iprop(▷?p P) P where
  into_except0 := match p with
                  | true => Timeless.timeless (P := P)
                  | false => except0_intro

@[rocq_alias into_except_0_affinely]
instance intoExcept0_affinely [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<affine> P) iprop(<affine> Q) where
  into_except0 := (affinely_mono h.1).trans except0_affinely

@[rocq_alias into_except_0_intuitionistically]
instance intoExcept0_intuitionistically [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(□ P) iprop(□ Q) where
  into_except0 := (intuitionistically_mono h.1).trans except0_intuitionistically

@[rocq_alias into_except_0_absorbingly]
instance intoExcept0_absorbingly [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<absorb> P) iprop(<absorb> Q) where
  into_except0 := (absorbingly_mono h.1).trans except0_absorbingly.2

@[rocq_alias into_except_0_persistently]
instance intoExcept0_persistently [BI PROP] (P Q : PROP)
    [h : IntoExcept0 P Q] : IntoExcept0 iprop(<pers> P) iprop(<pers> Q) where
  into_except0 := (persistently_mono h.1).trans except0_persistently.2

/-- ElimModal -/
@[ipm_backtrack, rocq_alias elim_modal_timeless]
instance (priority := default - 10) elimModal_timeless [BI PROP] p io (P P' Q : PROP) [IntoExcept0 P P'] [IsExcept0 Q] :
  ElimModal True p io p P P' Q Q where
  elim_modal _ := ((sep_mono ((intuitionisticallyIf_mono into_except0).trans except0_intuitionisticallyIf) except0_intro).trans $ except0_sep.2.trans (except0_mono wand_elim_right)).trans is_except0

/-- IntoLaterN -/
@[ipm_backtrack, rocq_alias maybe_into_laterN_default]
instance (priority := low) intoLaterN_default [BI PROP] only_head n (P : PROP) :
    IntoLaterN false only_head n P P where
  into_laterN := laterN_intro n

@[ipm_backtrack, rocq_alias into_laterN_0, rocq_alias maybe_into_laterN_default_0]
instance (priority := high) intoLaterN_default_0 [BI PROP] strict only_head (P : PROP) :
    IntoLaterN strict only_head 0 P P where
  into_laterN := laterN_intro 0

@[rocq_alias into_laterN_later]
theorem intoLaterN_later [BI PROP] strict {strict'} only_head n n' m' (P Q lQ : PROP)
    (h1 : NatCancel n 1 n' m')
    (h2 : IntoLaterN strict' only_head n' P Q)
    (h3 : MakeLaterN m' Q lQ) : IntoLaterN strict only_head n iprop(▷ P) lQ where
  into_laterN := calc
      _ ⊢ ▷▷^[n']Q      := later_mono h2.into_laterN
      _ ⊢ ▷^[n' + 1]Q    := (later_laterN _).mpr
      _ ⊢ ▷^[n] ▷^[m']Q := by rw [h1.1]; exact (laterN_add _ _).mp
      _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

@[rocq_alias into_laterN_laterN]
theorem intoLaterN_laterN [BI PROP] strict {strict'} only_head n m n' m' (P Q lQ : PROP)
    (h1 : NatCancel n m n' m')
    (h2 : IntoLaterN strict' only_head n' P Q)
    (h3 : MakeLaterN m' Q lQ) : IntoLaterN strict only_head n iprop(▷^[m] P) lQ where
  into_laterN := calc
      _ ⊢ ▷^[m] ▷^[n']Q := laterN_mono _ h2.into_laterN
      _ ⊢ ▷^[m + n']Q    := (laterN_add _ _).mpr
      _ ⊢ ▷^[n] ▷^[m']Q := by rw [Nat.add_comm, h1.nat_cancel]; exact (laterN_add _ _).mp
      _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

@[ipm_backtrack, rocq_alias into_laterN_laterN_bool]
theorem intoLaterN_laterN_bool [BI PROP] strict {strict'} only_head n (p : Bool) n' m' (P Q lQ : PROP)
    (h1 : NatCancel n 1 n' m')
    (h2 : IntoLaterN strict' only_head n' P Q)
    (h3 : MakeLaterN m' Q lQ) : IntoLaterN strict only_head n iprop(▷?p P) lQ where
  into_laterN := by
    calc
      _ ⊢ ▷ P            := by cases p; exact later_intro; exact BIBase.Entails.rfl
      _ ⊢ ▷ ▷^[n']Q     := later_mono h2.into_laterN
      _ ⊢ ▷^[n' + 1]Q    := (later_laterN _).mpr
      _ ⊢ ▷^[n] ▷^[m']Q := h1.nat_cancel.symm ▸ (laterN_add _ _).mp
      _ ⊢ ▷^[n]lQ        := laterN_mono _ h3.make_laterN.mp

meta section
open Lean Elab Meta Std Qq ProofMode

def maybeIntoLaterN {prop : Q(Type u)} {bi : Q(BI $prop)}
    (oh : Q(Bool)) (n : Q(Nat)) (P Q : Q($prop)) :
    MetaM <| Option Q(IntoLaterN false $oh $n $P $Q) := do
  if let some inst ← synthInstanceRecursiveQ q(IntoLaterN true $oh $n $P $Q) then
    let inst : Q(IntoLaterN false $oh $n $P $Q) := q(⟨$(inst).into_laterN⟩)
    return some inst
  -- Fallback to the reflexive default
  Q.mvarId!.assign P
  have : $Q =Q $P := ⟨⟩
  return some q(intoLaterN_default $oh $n $P)

inductive LaterKind where
  | later
  | laterN
  | laterIf (p : Expr)

@[ipm_tactic_instance IntoLaterN _ _ _ iprop(▷ _) _,
  IntoLaterN _ _ _ iprop(▷^[_] _) _, IntoLaterN _ _ _ iprop(▷?_ _) _]
def intoLaterNLater : SynthTactic := λ e => do
  let mctx0 ← getMCtx
  let_expr IntoLaterN prop bi strict oh n P _ := e | return .continue
  have u := e.getAppFn.constLevels![0]!
  have prop : Q(Type u) := prop
  have _bi : Q(BI $prop) := bi
  have strict : Q(Bool) := strict
  have oh : Q(Bool) := oh
  have n : Q(Nat) := n

  -- Syntactic match with `▷ P'`, `▷^[m] P'` and `▷?p P'`.
  let candidates : List (Q(Nat) × Q($prop) × LaterKind) :=
    match_expr P with
    | BIBase.later _ _ P'     => [(q(1), P', .later)]
    | BIBase.laterN _ _ m P'  => [(m, P', .laterN)]
    -- Try `intoLaterN_laterN` and then `intoLaterN_laterN_bool`
    | BIBase.laterIf _ _ p P' =>
      have p : Q(Bool) := p
      [(q($(p).toNat), P', .laterN), (q(1), P', .laterIf p)]
    | _ => []

  for ⟨m, Pin, laterKind⟩ in candidates do
    setMCtx mctx0
    if let some inst ← intoLaterNLaterAux bi strict n oh m Pin laterKind then
      return .success inst
  setMCtx mctx0
  return .continue
where
  intoLaterNLaterAux {u : Level} {prop : Q(Type u)} (_bi : Q(BI $prop))
      (strict : Q(Bool)) (n : Q(Nat)) (oh : Q(Bool))
      (m : Q(Nat)) (Pin : Q($prop)) (kind : LaterKind) : MetaM (Option Expr) := do
    let n' : Q(Nat) ← mkFreshExprMVarQ q(Nat)
    let m' : Q(Nat) ← mkFreshExprMVarQ q(Nat)
    let some h1 ← synthInstanceRecursiveQ q(NatCancel $n $m $n' $m')
      | return none

    -- Check that progress is made in the recursive search
    let progress ← withTransparency .instances <|
      withConfig ({ · with isDefEqStuckEx := false }) do
        return !(← isDefEq m m')

    let Q : Q($prop) ← mkFreshExprMVarQ q($prop)
    let some h2 ←
      if progress then
        maybeIntoLaterN oh n' Pin Q
      else do
        let some inst ← synthInstanceRecursiveQ q(IntoLaterN true $oh $n' $Pin $Q)
          | pure none
        let inst : Q(IntoLaterN false «$oh» «$n'» «$Pin» «$Q») := q(⟨$(inst).into_laterN⟩)
        pure <| some inst
      | return none

    let lQ : Q($prop) ← mkFreshExprMVarQ q($prop)
    let some h3 ← synthInstanceRecursiveQ q(MakeLaterN $m' $Q $lQ)
      | throwError "MakeLaterN type class synthesis fails with {m'} and {Q}"

    match kind with
    | .later =>
      have : $m =Q 1 := ⟨⟩
      return some q(intoLaterN_later $strict $oh $n $n' $m' $Pin $Q $lQ $h1 $h2 $h3)
    | .laterN =>
      return some q(intoLaterN_laterN $strict $oh $n $m $n' $m' $Pin $Q $lQ $h1 $h2 $h3)
    | .laterIf p =>
      have p : Q(Bool) := p
      have : $m =Q 1 := ⟨⟩
      return some q(intoLaterN_laterN_bool $strict $oh $n $p $n' $m' $Pin $Q $lQ $h1 $h2 $h3)

end

-- There is no MaybeIntoLaterN in Lean, so we only need one instance
@[rocq_alias into_laterN_and_l, rocq_alias into_laterN_and_r]
instance intoLaterN_and [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN strict false n P1 Q1] [h2 : IntoLaterN strict false n P2 Q2] :
    IntoLaterN strict false n iprop(P1 ∧ P2) iprop(Q1 ∧ Q2) where
  into_laterN := (and_mono h1.1 h2.1).trans (laterN_and n).2

@[rocq_alias into_laterN_forall]
instance intoLaterN_forall [BI PROP] n (Φ Ψ : α → PROP)
    [h : ∀ x, IntoLaterN strict false n (Φ x) (Ψ x)] : IntoLaterN strict false n iprop(∀ x, Φ x) iprop(∀ x, Ψ x) where
  into_laterN := (forall_mono fun x => (h x).1).trans (laterN_forall n).2

@[rocq_alias into_laterN_exist]
instance intoLaterN_exists [BI PROP] n (Φ Ψ : α → PROP)
    [h : ∀ x, IntoLaterN strict false n (Φ x) (Ψ x)] : IntoLaterN strict false n iprop(∃ x, Φ x) iprop(∃ x, Ψ x) where
  into_laterN := (exists_mono fun x => (h x).1).trans (laterN_exists_mpr n)

@[rocq_alias into_laterN_or_l, rocq_alias into_laterN_or_r]
instance intoLaterN_or [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN strict false n P1 Q1] [h2 : IntoLaterN strict false n P2 Q2] :
    IntoLaterN strict false n iprop(P1 ∨ P2) iprop(Q1 ∨ Q2) where
  into_laterN := (or_mono h1.1 h2.1).trans (laterN_or n).2

@[rocq_alias into_later_affinely]
instance intoLaterN_affinely [BI PROP] n (P Q : PROP)
    [h : IntoLaterN strict false n P Q] : IntoLaterN strict false n iprop(<affine> P) iprop(<affine> Q) where
  into_laterN := (affinely_mono h.1).trans (laterN_affinely n)

@[rocq_alias into_later_intuitionistically]
instance intoLaterN_intuitionistically [BI PROP] n (P Q : PROP)
    [h : IntoLaterN strict false n P Q] : IntoLaterN strict false n iprop(□ P) iprop(□ Q) where
  into_laterN := (intuitionistically_mono h.1).trans (laterN_intuitionistically n)

@[rocq_alias into_later_absorbingly]
instance intoLaterN_absorbingly [BI PROP] n (P Q : PROP)
    [h : IntoLaterN strict false n P Q] : IntoLaterN strict false n iprop(<absorb> P) iprop(<absorb> Q) where
  into_laterN := (absorbingly_mono h.1).trans (laterN_absorbingly n).2

@[rocq_alias into_later_persistently]
instance intoLaterN_persistently [BI PROP] n (P Q : PROP)
    [h : IntoLaterN strict false n P Q] : IntoLaterN strict false n iprop(<pers> P) iprop(<pers> Q) where
  into_laterN := (persistently_mono h.1).trans (laterN_persistently n).2

@[rocq_alias into_laterN_sep_l, rocq_alias into_laterN_sep_r]
instance intoLaterN_sep [BI PROP] n (P1 P2 Q1 Q2 : PROP)
    [h1 : IntoLaterN strict false n P1 Q1] [h2 : IntoLaterN strict false n P2 Q2] :
    IntoLaterN strict false n iprop(P1 ∗ P2) iprop(Q1 ∗ Q2) where
  into_laterN := (sep_mono h1.1 h2.1).trans (laterN_sep n).2

@[rocq_alias maybe_combine_sep_as_later]
instance combineSepAs_later [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepAs Q1 Q2 P] :
  CombineSepAs iprop(▷ Q1) iprop(▷ Q2) iprop(▷ P) where
  combine_sep_as := later_sep.mpr.trans (later_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_laterN]
instance combineSepAs_laterN [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepAs Q1 Q2 P] :
  CombineSepAs iprop(▷^[n] Q1) iprop(▷^[n] Q2) iprop(▷^[n] P) where
  combine_sep_as := (laterN_sep n).mpr.trans (laterN_mono n h.combine_sep_as)

@[rocq_alias maybe_combine_sep_as_except_0]
instance combineSepAs_except0 [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepAs Q1 Q2 P] :
  CombineSepAs iprop(◇ Q1) iprop(◇ Q2) iprop(◇ P) where
  combine_sep_as := except0_sep.mpr.trans (except0_mono h.combine_sep_as)

@[rocq_alias maybe_combine_sep_gives_later]
instance combineSepGives_later [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepGives Q1 Q2 P] :
  CombineSepGives iprop(▷ Q1) iprop(▷ Q2) iprop(▷ P) where
  combine_sep_gives := by calc
    ▷ Q1 ∗ ▷ Q2 ⊢ ▷ (Q1 ∗ Q2) := later_sep.mpr
    _             ⊢ ▷ <pers> P  := later_mono h.combine_sep_gives
    _             ⊢ <pers> ▷ P  := later_persistently.mp

@[rocq_alias maybe_combine_sep_gives_laterN]
instance combineSepGives_laterN [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepGives Q1 Q2 P] :
  CombineSepGives iprop(▷^[n] Q1) iprop(▷^[n] Q2) iprop(▷^[n] P) where
  combine_sep_gives := by calc
    ▷^[n] Q1 ∗ ▷^[n] Q2 ⊢ ▷^[n] (Q1 ∗ Q2) := (laterN_sep n).mpr
    _                     ⊢ ▷^[n] <pers> P  := laterN_mono n h.combine_sep_gives
    _                     ⊢ <pers> ▷^[n] P  := (laterN_persistently n).mp

@[rocq_alias maybe_combine_sep_gives_except_0]
instance combineSepGives_except0 [BI PROP] (Q1 Q2 P : PROP)
  [h : CombineSepGives Q1 Q2 P] :
  CombineSepGives iprop(◇ Q1) iprop(◇ Q2) iprop(◇ P) where
  combine_sep_gives := by calc
    ◇ Q1 ∗ ◇ Q2 ⊢ ◇ (Q1 ∗ Q2) := except0_sep.mpr
    _             ⊢ ◇ <pers> P  := except0_mono h.combine_sep_gives
    _             ⊢ <pers> ◇ P  := except0_persistently.mp

end Iris.ProofMode
