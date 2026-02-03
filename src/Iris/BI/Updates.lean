/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI.BI
import Iris.BI.BIBase
import Iris.BI.Classes
import Iris.BI.DerivedLaws
import Iris.BI.DerivedLawsLater
import Iris.Algebra
import Iris.BI.Plainly

namespace Iris
open Iris.Std BI

--TODO: Which type should we use for sets of masks?
def Set (α : Type _) := α → Prop
def Set.univ {α : Type _} : Set α := fun _ => True
def Subset (x y : Set α) : Prop := ∀ a, x a → y a
def Disjoint (x y : Set α) : Prop := ∀ a, ¬(x a ∧ y a)
def union (x y : Set α) : Set α := fun a => x a ∨ y a

class BUpd (PROP : Type _) where
  bupd : PROP → PROP
export BUpd (bupd)

syntax "|==> " term:40 : term
syntax term:26 " ==∗ " term:25 : term

macro_rules
  | `(iprop(|==> $P))  => ``(BUpd.bupd iprop($P))
  | `(iprop($P ==∗ $Q))  => ``(BIBase.wand iprop($P) (BUpd.bupd iprop($Q)))

delab_rule BUpd.bupd
  | `($_ $P) => do ``(iprop(|==> $(← Iris.BI.unpackIprop P)))
-- delab_rule WandUpdate ??
--   | `($_ $P $Q) => ``(iprop($P ==∗ $Q))

class FUpd (PROP : Type _) (MASK : Type _) where
  fupd : Set MASK → Set MASK → PROP → PROP
export FUpd (fupd)

syntax "|={ " term " , " term " }=> " term : term
syntax term "={ " term " , " term " }=∗ " term : term
syntax "|={ " term " }=> " term : term
syntax term "={ " term " }=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 , $E2 }=> $P))  => ``(FUpd.fupd $E1 $E2 iprop($P))
  | `(iprop($P ={ $E1 , $E2 }=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E2 iprop($Q)))
  | `(iprop(|={ $E1 }=> $P))  => ``(FUpd.fupd $E1 $E1 iprop($P))
  | `(iprop($P ={ $E1 }=∗ $Q))  => ``(BIBase.wand iprop($P) (FUpd.fupd $E1 $E1 iprop($Q)))

-- Delab rules

syntax "|={ " term " }[ " term " ]▷=> " term : term
syntax term "={ " term " }[ " term " ]▷=∗ " term : term
syntax "|={ " term " }▷=> " term : term
syntax term "={ " term " }▷=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷=> $P))  => ``(iprop(|={$E1, $E2}=> ▷ (|={ $E2, $E1 }=> iprop($P))))
  | `(iprop($P ={ $E1 }[ $E2 ]▷=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷=> iprop($Q)))
  | `(iprop(|={ $E1 }▷=> $P))  => ``(iprop(|={$E1}[$E1]▷=> iprop($P)))
  | `(iprop($P ={ $E1 }▷=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷=∗ iprop($Q)))

-- Delab rules

/-- Iterated step-fancy update. -/
def step_fupdN {PROP MASK : Type _} [BIBase PROP] [FUpd PROP MASK]
    (Eo Ei : Set MASK) (n : Nat) (P : PROP) : PROP :=
  -- unfold to a chain of step-fupd updates
  Nat.rec P (fun _ Q => iprop(|={Eo}[Ei]▷=> Q)) n

syntax "|={ " term " }[ " term " ]▷^" term "=> " term : term
syntax term "={ " term " }[ " term " ]▷^" term "=∗ " term : term
syntax "|={ " term " }▷^" term "=> " term : term
syntax term "={ " term " }▷^" term "=∗ " term : term

macro_rules
  | `(iprop(|={ $E1 }[ $E2 ]▷^$n=> $P))  => ``(step_fupdN (Eo := $E1) (Ei := $E2) $n iprop($P))
  | `(iprop($P ={ $E1 }[ $E2 ]▷^$n=∗ $Q))  => ``(iprop(iprop($P) -∗ |={$E1}[$E2]▷^$n=> iprop($Q)))
  | `(iprop(|={ $E1 }▷^$n=> $P))  => ``(iprop(|={$E1}[$E1]▷^$n=> iprop($P)))
  | `(iprop($P ={ $E1 }▷^$n=∗ $Q))  => ``(iprop(iprop($P) ={$E1}[$E1]▷^$n=∗ iprop($Q)))

-- Delab rules

class BIUpdate (PROP : Type _) [BI PROP] extends BUpd PROP where
  [bupd_ne : OFE.NonExpansive (BUpd.bupd (PROP := PROP))]
  intro {P : PROP} : iprop(P ⊢ |==> P)
  mono {P Q : PROP} : iprop(P ⊢ Q) → iprop(|==> P ⊢ |==> Q)
  trans {P : PROP} : iprop(|==> |==> P ⊢ |==> P)
  frame_r {P R : PROP} : iprop((|==> P) ∗ R ⊢ |==> (P ∗ R))

class BIFUpdate (PROP MASK : Type _) [BI PROP] extends FUpd PROP MASK where
  [ne {E1 E2 : Set MASK} : OFE.NonExpansive (FUpd.fupd E1 E2 (PROP := PROP))]
  subset {E1 E2 : Set MASK} : Subset E2 E1 → ⊢ |={E1, E2}=> |={E2, E1}=> (emp : PROP)
  except0 {E1 E2 : Set MASK} (P : PROP) : (◇ |={E1, E2}=> P) ⊢ |={E1, E2}=> P
  mono {E1 E2 : Set MASK} {P Q : PROP} :
    (P ⊢ Q) → (FUpd.fupd (PROP := PROP) E1 E2 P ⊢ FUpd.fupd (PROP := PROP) E1 E2 Q)
  trans {E1 E2 E3 : Set MASK} (P : PROP) : (|={E1, E2}=> |={E2, E3}=> P) ⊢ |={E1, E3}=> P
  mask_frame_r' {E1 E2 Ef : Set MASK} (P : PROP) :
    Disjoint E1 Ef → (|={E1,E2}=> ⌜Disjoint E2 Ef⌝ → P) ⊢ |={union E1 Ef, union E2 Ef}=> P
  frame_r {E1 E2 : Set MASK} (P R : PROP) :
    iprop((|={E1, E2}=> P) ∗ R ⊢ |={E1, E2}=> P ∗ R)

class BIUpdateFUpdate (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIFUpdate PROP MASK] where
  fupd_of_bupd {P : PROP} {E : Set MASK} : iprop(⊢ |==> P) → iprop(⊢ |={E}=> P)

class BIBUpdatePlainly (PROP : Type _) [BI PROP] [BIUpdate PROP] [BIPlainly PROP] where
  bupd_plainly {P : PROP} : iprop((|==> ■ P)) ⊢ P

class BIFUpdatePlainly (PROP MASK : Type _) [BI PROP] [BIFUpdate PROP MASK] [BIPlainly PROP] where
  fupd_plainly_keep_l (E E' : Set MASK) (P R : PROP) :
    iprop((R ={E,E'}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R)
  fupd_plainly_later (E : Set MASK) (P : PROP) :
    iprop((▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P)
  fupd_plainly_sForall_2 (E : Set MASK) (Φ : PROP → Prop) :
    (∀ p, ⌜Φ p⌝ → |={E}=> ■ p) ⊢ |={E}=> sForall Φ

section BUpdLaws

variable [BI PROP] [BIUpdate PROP]

open BIUpdate

theorem bupd_frame_l {P Q : PROP} : iprop(P ∗ |==> Q ⊢ |==> (P ∗ Q)) :=
  sep_symm.trans <| frame_r.trans <| mono sep_symm

theorem bupd_frame_r {P Q : PROP} : iprop(|==> P ∗ Q ⊢ |==> (P ∗ Q)) :=
  frame_r

theorem bupd_wand_l {P Q : PROP} : iprop((P -∗ Q) ∗ (|==> P) ⊢ |==> Q) :=
  bupd_frame_l.trans <| mono <| wand_elim .rfl

theorem bupd_wand_r {P Q : PROP} : iprop((|==> P) ∗ (P -∗ Q) ⊢ |==> Q) :=
  sep_symm.trans bupd_wand_l

theorem bupd_sep {P Q : PROP} : iprop((|==> P) ∗ (|==> Q) ⊢ |==> (P ∗ Q)) :=
  bupd_frame_l.trans <| (mono <| frame_r).trans BIUpdate.trans

theorem bupd_idem {P : PROP} : iprop((|==> |==> P) ⊣⊢ |==> P) :=
  ⟨BIUpdate.trans, BIUpdate.intro⟩

theorem bupd_or {P Q: PROP} : iprop((|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q)) :=
  or_elim (mono or_intro_l) (mono or_intro_r)

theorem bupd_and {P Q : PROP} : iprop((|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q)) :=
  and_intro (mono and_elim_l) (mono and_elim_r)

theorem bupd_exist {Φ : A → PROP} : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x :=
  exists_elim (mono <| exists_intro ·)

theorem bupd_forall {Φ : A → PROP} :
    iprop(|==> «forall» fun x : A => Φ x) ⊢ «forall» fun x : A => iprop(|==> Φ x) :=
  forall_intro (mono <| forall_elim ·)

theorem bupd_except0 {P : PROP} : iprop(◇ (|==> P) ⊢ (|==> ◇ P)) :=
  or_elim (or_intro_l.trans intro) (mono or_intro_r)

instance {P : PROP} [Absorbing P] : Absorbing iprop(|==> P) :=
  ⟨bupd_frame_l.trans <| mono sep_elim_r⟩

section BUpdPlainlyLaws

variable [BIPlainly PROP] [BIBUpdatePlainly PROP]

theorem bupd_elim {P : PROP} [Plain P] : |==> P ⊢ P :=
  (mono Plain.plain).trans BIBUpdatePlainly.bupd_plainly

theorem bupd_plain_forall (Φ : A → PROP) [∀ x, Plain (Φ x)] :
    (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x) := by
  refine ⟨bupd_forall, ?_⟩
  refine .trans ?_ intro
  exact (forall_intro fun a => (forall_elim a).trans  bupd_elim)

instance {P : PROP} [Plain P] : Plain iprop(|==> P) :=
  ⟨(mono Plain.plain).trans <| (bupd_elim).trans <| BIPlainly.mono intro⟩

end BUpdPlainlyLaws
end BUpdLaws

/-! ## FUpd Laws -/

section FUpdLaws

variable [BI PROP] [BIFUpdate PROP MASK]

open BIFUpdate

/-- Mask subset introduction for fancy updates.

Coq: `fupd_mask_subseteq` in `updates.v`. -/
theorem fupd_mask_subseteq {E1 E2 : Set MASK} (h : Subset E2 E1) :
    ⊢ |={E1, E2}=> |={E2, E1}=> (emp : PROP) :=
  -- just expose the mixin field
  subset (E1 := E1) (E2 := E2) h

/-- Monotonicity of fancy updates.

Coq: `fupd_mono` in `updates.v`. -/
theorem fupd_mono {E1 E2 : Set MASK} {P Q : PROP} (h : P ⊢ Q) :
    (|={E1, E2}=> P) ⊢ |={E1, E2}=> Q :=
  -- delegate to the mixin field
  mono (E1 := E1) (E2 := E2) (P := P) (Q := Q) h

/-- Transitivity of fancy updates.

Coq: `fupd_trans` in `updates.v`. -/
theorem fupd_trans {E1 E2 E3 : Set MASK} (P : PROP) :
    (|={E1, E2}=> |={E2, E3}=> P) ⊢ |={E1, E3}=> P :=
  -- use the mixin field
  trans (E1 := E1) (E2 := E2) (E3 := E3) (P := P)

/-- Frame rule for fancy updates (right).

Coq: `fupd_frame_r` in `updates.v`. -/
theorem fupd_frame_r {E1 E2 : Set MASK} (P R : PROP) :
    iprop((|={E1, E2}=> P) ∗ R ⊢ |={E1, E2}=> P ∗ R) :=
  -- use the mixin field
  frame_r (E1 := E1) (E2 := E2) (P := P) (R := R)

/-- Mask introduction using a subset.

Coq: `fupd_mask_intro_subseteq` in `updates.v`. -/
theorem fupd_mask_intro_subseteq {E1 E2 : Set MASK} (P : PROP) (h : Subset E2 E1) :
    P ⊢ |={E1, E2}=> |={E2, E1}=> P := by
  -- insert the mask update and frame `P` through both updates
  have hmask : ⊢ |={E1, E2}=> |={E2, E1}=> (emp : PROP) :=
    fupd_mask_subseteq (E1 := E1) (E2 := E2) h
  have hframe : P ⊢ (|={E1, E2}=> |={E2, E1}=> emp) ∗ P := by
    -- add `emp` on the left and use monotonicity of `∗`
    refine (emp_sep.2).trans ?_
    exact sep_mono hmask .rfl
  have hinner : (|={E2, E1}=> emp) ∗ P ⊢ |={E2, E1}=> P := by
    -- frame inside the inner update and drop the `emp`
    refine (fupd_frame_r (E1 := E2) (E2 := E1) (P := emp) (R := P)).trans ?_
    exact fupd_mono (E1 := E2) (E2 := E1) (by simpa using (emp_sep.1 : emp ∗ P ⊢ P))
  have houter :
      (|={E1, E2}=> |={E2, E1}=> emp) ∗ P ⊢ |={E1, E2}=> |={E2, E1}=> P := by
    -- move `P` under the outer update, then apply the inner step
    refine (fupd_frame_r (E1 := E1) (E2 := E2) (P := iprop(|={E2, E1}=> emp)) (R := P)).trans ?_
    exact fupd_mono (E1 := E1) (E2 := E2) hinner
  exact hframe.trans houter

/-- Basic fupd introduction.

Coq: `fupd_intro` in `updates.v`. -/
theorem fupd_intro (E : Set MASK) (P : PROP) : P ⊢ |={E}=> P := by
  -- specialize mask intro and collapse nested updates
  have h := fupd_mask_intro_subseteq (E1 := E) (E2 := E) (P := P) (fun _ hE => hE)
  exact h.trans (fupd_trans (E1 := E) (E2 := E) (E3 := E) (P := P))

/-- Eliminate a fupd into another fupd.

Coq: `fupd_elim` in `updates.v`. -/
theorem fupd_elim {E1 E2 E3 : Set MASK} {P Q : PROP}
    (h : Q ⊢ |={E2, E3}=> P) : (|={E1, E2}=> Q) ⊢ |={E1, E3}=> P := by
  -- rewrite and compose the updates
  exact (fupd_mono (E1 := E1) (E2 := E2) h).trans
    (fupd_trans (E1 := E1) (E2 := E2) (E3 := E3) (P := P))

/-- Frame rule for fancy updates (left).

Coq: `fupd_frame_l` in `updates.v`. -/
theorem fupd_frame_l {E1 E2 : Set MASK} (R Q : PROP) :
    (R ∗ |={E1, E2}=> Q) ⊢ |={E1, E2}=> R ∗ Q := by
  -- commute the frame, apply the right rule, then commute inside
  refine (sep_comm.1).trans ?_
  refine (fupd_frame_r (E1 := E1) (E2 := E2) (P := Q) (R := R)).trans ?_
  exact fupd_mono (E1 := E1) (E2 := E2) (sep_comm.1)

/-- Wand rule for fancy updates (left).

Coq: `fupd_wand_l` in `updates.v`. -/
theorem fupd_wand_l {E1 E2 : Set MASK} (P Q : PROP) :
    iprop((P -∗ Q) ∗ (|={E1, E2}=> P) ⊢ |={E1, E2}=> Q) := by
  -- frame and eliminate the wand
  exact (fupd_frame_l (E1 := E1) (E2 := E2) (R := iprop(P -∗ Q)) (Q := P)).trans
    (fupd_mono (E1 := E1) (E2 := E2) (wand_elim_l (PROP := PROP)))

/-- Wand rule for fancy updates (right).

Coq: `fupd_wand_r` in `updates.v`. -/
theorem fupd_wand_r {E1 E2 : Set MASK} (P Q : PROP) :
    iprop((|={E1, E2}=> P) ∗ (P -∗ Q) ⊢ |={E1, E2}=> Q) := by
  -- swap and use the left wand rule
  exact (sep_comm.1).trans (fupd_wand_l (E1 := E1) (E2 := E2) (P := P) (Q := Q))

end FUpdLaws

/-! ## Plain Laws -/

section PlainLaws

variable [BI PROP] [BIPlainly PROP]

/-- Plainness is preserved by the later modality.

Coq: `later_plain` in `bi/plainly.v`. -/
theorem plain_later (P : PROP) [Plain P] : ▷ P ⊢ ■ ▷ P := by
  -- push plainness under `▷` and commute `■` outward
  have hplain : P ⊢ ■ P := Plain.plain (P := P)
  have hlater : ▷ P ⊢ ▷ ■ P := later_mono (PROP := PROP) hplain
  exact hlater.trans (later_plainly (P := P)).1

/-- Plainness is preserved by iterated later.

Coq: `laterN_plain` in `bi/plainly.v`. -/
theorem plain_laterN (P : PROP) (n : Nat) [Plain P] :
    BIBase.laterN (PROP := PROP) n P ⊢ ■ BIBase.laterN (PROP := PROP) n P := by
  -- follow the `laterN` recursion
  induction n with
  | zero =>
      -- base: `laterN 0 P` is `P`
      simpa [BIBase.laterN] using (Plain.plain (P := P))
  | succ n ih =>
      -- step: build a plain instance for `▷^n P`, then apply `plain_later`
      haveI : Plain (BIBase.laterN (PROP := PROP) n P) := ⟨ih⟩
      simpa [BIBase.laterN] using (plain_later (P := BIBase.laterN (PROP := PROP) n P))

/-- Plainness is preserved by except-0.

Coq: `except_0_plain` in `bi/plainly.v`. -/
theorem plain_except0 (P : PROP) [Plain P] : ◇ P ⊢ ■ ◇ P := by
  -- move plainness under `◇`, then distribute `■` over the disjunction
  have hplain : P ⊢ ■ P := Plain.plain (P := P)
  have hmono : ◇ P ⊢ ◇ ■ P := except0_mono (PROP := PROP) hplain
  have hfalse :
      ▷ (BIBase.pure (PROP := PROP) False) ⊢ ■ ▷ (BIBase.pure (PROP := PROP) False) := by
    -- `False` is pure, so `■` commutes with `▷` after `later_mono`
    have hpure : BIBase.pure (PROP := PROP) False ⊢ ■ BIBase.pure (PROP := PROP) False := by
      simpa using (plainly_pure (PROP := PROP) (φ := False)).2
    have hlater :
        ▷ BIBase.pure (PROP := PROP) False ⊢ ▷ ■ BIBase.pure (PROP := PROP) False :=
      later_mono (PROP := PROP) hpure
    exact hlater.trans (later_plainly (P := BIBase.pure (PROP := PROP) False)).1
  have hdisj : ◇ ■ P ⊢ ■ ◇ P := by
    -- rewrite `◇` and apply `plainly_or_2`
    have hor :
        ▷ BIBase.pure (PROP := PROP) False ∨ ■ P ⊢ ■ ▷ BIBase.pure (PROP := PROP) False ∨ ■ P := by
      refine or_elim ?hleft ?hright
      · exact hfalse.trans or_intro_l
      · exact or_intro_r
    have hplain_or : ■ ▷ False ∨ ■ P ⊢ ■ (▷ False ∨ P) :=
      plainly_or_2
        (P := BIBase.later (PROP := PROP) (BIBase.pure (PROP := PROP) False))
        (Q := P)
    simpa [BIBase.except0] using hor.trans hplain_or
  exact hmono.trans hdisj

end PlainLaws

/-! ## Step FUpd Laws -/

section StepFUpdLaws

variable [BI PROP] [BIFUpdate PROP MASK]

/-- Monotonicity of the step-fupd modality.

Coq: derived from `fupd_mono` in `updates.v`. -/
theorem step_fupd_mono {Eo Ei : Set MASK} {P Q : PROP} (h : P ⊢ Q) :
    (|={Eo}[Ei]▷=> P) ⊢ |={Eo}[Ei]▷=> Q := by
  -- push the entailment through the inner and outer fancy updates
  have hinner : (|={Ei, Eo}=> P) ⊢ |={Ei, Eo}=> Q :=
    fupd_mono (E1 := Ei) (E2 := Eo) h
  have hlater :
      BIBase.later (PROP := PROP) (fupd Ei Eo P) ⊢
        BIBase.later (PROP := PROP) (fupd Ei Eo Q) :=
    later_mono (PROP := PROP) hinner
  exact fupd_mono (E1 := Eo) (E2 := Ei) hlater

/-- Step-fupd commutes with an outer fupd.

Coq: `step_fupd_fupd` in `updates.v`. -/
theorem step_fupd_fupd (Eo Ei : Set MASK) (P : PROP) :
    (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P) := by
  refine ⟨?_, ?_⟩
  · -- introduce the outer fupd and lift it through step-fupd
    exact step_fupd_mono (Eo := Eo) (Ei := Ei) (fupd_intro (E := Eo) (P := P))
  · -- eliminate the nested fupd via transitivity
    have hinner : (|={Ei, Eo}=> |={Eo}=> P) ⊢ |={Ei, Eo}=> P :=
      fupd_trans (E1 := Ei) (E2 := Eo) (E3 := Eo) (P := P)
    have hlater :
        BIBase.later (PROP := PROP) (fupd Ei Eo (fupd Eo Eo P)) ⊢
          BIBase.later (PROP := PROP) (fupd Ei Eo P) :=
      later_mono (PROP := PROP) hinner
    exact fupd_mono (E1 := Eo) (E2 := Ei) hlater

end StepFUpdLaws

/-! ## Plain FUpd Laws -/

section FUpdPlainlyLaws

variable [BI PROP] [BIFUpdate PROP MASK] [BIPlainly PROP] [BIFUpdatePlainly PROP MASK]

/-- Plainly keep-left rule for fancy updates.

Coq: `fupd_plainly_keep_l` in `updates.v`. -/
theorem fupd_plainly_keep_l (E E' : Set MASK) (P R : PROP) :
    iprop((R ={E, E'}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R) :=
  -- delegate to the mixin
  BIFUpdatePlainly.fupd_plainly_keep_l (E := E) (E' := E') (P := P) (R := R)

/-- Plainly later rule for fancy updates.

Coq: `fupd_plainly_later` in `updates.v`. -/
theorem fupd_plainly_later (E : Set MASK) (P : PROP) :
    iprop((▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P) :=
  -- delegate to the mixin
  BIFUpdatePlainly.fupd_plainly_later (E := E) (P := P)

/-- Plainly mask elimination for fancy updates.

Coq: `fupd_plainly_mask` in `updates.v`. -/
theorem fupd_plainly_mask (E E' : Set MASK) (P : PROP) :
    (|={E, E'}=> ■ P) ⊢ |={E}=> P := by
  -- use the keep-left rule with the empty frame, then drop `emp`
  have hkeep :
      (emp ={E, E'}=∗ ■ P) ∗ emp ⊢ |={E}=> P ∗ emp :=
    fupd_plainly_keep_l (E := E) (E' := E') (P := P) (R := emp)
  have hwand : (emp -∗ |={E, E'}=> ■ P) ⊣⊢ |={E, E'}=> ■ P := by
    -- `emp` is the unit for the separating implication
    refine ⟨?_, ?_⟩
    · exact (emp_sep.2).trans (wand_elim_r (P := emp) (Q := iprop(|={E, E'}=> ■ P)))
    · exact wand_intro (sep_emp.1 :
        (|={E, E'}=> ■ P) ∗ emp ⊢ |={E, E'}=> ■ P)
  have hpre : (|={E, E'}=> ■ P) ⊢ (emp -∗ |={E, E'}=> ■ P) ∗ emp := by
    -- introduce the wand and frame `emp`
    refine (sep_emp.2).trans ?_
    exact sep_mono hwand.2 .rfl
  have hpost : (|={E}=> P ∗ emp) ⊢ |={E}=> P :=
    fupd_mono (E1 := E) (E2 := E) (sep_emp.1)
  exact hpre.trans (hkeep.trans hpost)

end FUpdPlainlyLaws

section FUpdPlainLaws

variable [BI PROP] [BIFUpdate PROP MASK] [BIPlainly PROP]
variable [BIFUpdatePlainly PROP MASK]

/-- Plain mask elimination for fancy updates.

Coq: `fupd_plain_mask` in `updates.v`. -/
theorem fupd_plain_mask (E E' : Set MASK) (P : PROP) [Plain P] :
    (|={E, E'}=> P) ⊢ |={E}=> P := by
  -- convert to a plainly statement and use the plainly mask lemma
  have hplain : P ⊢ ■ P := Plain.plain (P := P)
  exact (fupd_mono (E1 := E) (E2 := E') hplain).trans
    (fupd_plainly_mask (E := E) (E' := E') (P := P))

/-- Plain later rule for fancy updates.

Coq: `fupd_plain_later` in `updates.v`. -/
theorem fupd_plain_later (E : Set MASK) (P : PROP) [Plain P] :
    iprop((▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P) := by
  -- reduce to the plainly version
  have hplain : P ⊢ ■ P := Plain.plain (P := P)
  have hmono :
      (▷ |={E}=> P) ⊢ ▷ |={E}=> ■ P :=
    later_mono (PROP := PROP) (fupd_mono (E1 := E) (E2 := E) hplain)
  exact hmono.trans (fupd_plainly_later (E := E) (P := P))

/-- One-step plain step-fupd.

Coq: `step_fupd_plain` in `updates.v`. -/
theorem step_fupd_plain (Eo Ei : Set MASK) (P : PROP) [Plain P] :
    (|={Eo}[Ei]▷=> P) ⊢ |={Eo}=> ▷ ◇ P := by
  -- build plainness for `▷ ◇ P` to remove the mask
  haveI : Plain (BIBase.except0 (PROP := PROP) P) := ⟨plain_except0 (P := P)⟩
  haveI :
      Plain (BIBase.later (PROP := PROP) (BIBase.except0 (PROP := PROP) P)) :=
    ⟨plain_later (P := BIBase.except0 (PROP := PROP) P)⟩
  -- shrink the inner mask and apply the plainly-later rule
  have hmask : (|={Ei, Eo}=> P) ⊢ |={Ei}=> P :=
    fupd_plain_mask (E := Ei) (E' := Eo) (P := P)
  have hlater :
      BIBase.later (PROP := PROP) (fupd Ei Eo P) ⊢
        BIBase.later (PROP := PROP) (fupd Ei Ei P) :=
    later_mono (PROP := PROP) hmask
  have hinner :
      BIBase.later (PROP := PROP) (fupd Ei Eo P) ⊢
        fupd Ei Ei (BIBase.later (PROP := PROP) (BIBase.except0 (PROP := PROP) P)) :=
    hlater.trans (fupd_plain_later (E := Ei) (P := P))
  have hstep :
      (|={Eo, Ei}=> BIBase.later (PROP := PROP) (fupd Ei Eo P)) ⊢
        |={Eo, Ei}=> BIBase.later (PROP := PROP) (BIBase.except0 (PROP := PROP) P) :=
    fupd_elim (E1 := Eo) (E2 := Ei) (E3 := Ei)
      (Q := BIBase.later (PROP := PROP) (fupd Ei Eo P)) hinner
  exact hstep.trans <|
    fupd_plain_mask (E := Eo) (E' := Ei)
      (P := BIBase.later (PROP := PROP) (BIBase.except0 (PROP := PROP) P))

/-- Iterated plain step-fupd.

Coq: `step_fupdN_plain` in `updates.v`. -/
theorem step_fupdN_plain (Eo Ei : Set MASK) (n : Nat) (P : PROP) [Plain P] :
    (|={Eo}[Ei]▷^n=> P) ⊢ |={Eo}=> ▷^[n] ◇ P := by
  -- follow the iterated step-fupd recursion
  induction n with
  | zero =>
      -- base: `step_fupdN` is the identity
      exact (fupd_intro (E := Eo) (P := P)).trans
        (fupd_mono (E1 := Eo) (E2 := Eo) except0_intro)
  | succ n ih =>
      -- step: insert and remove `|={Eo}=>`, then use `step_fupd_plain`
      haveI : Plain (BIBase.except0 (PROP := PROP) P) := ⟨plain_except0 (P := P)⟩
      haveI :
          Plain (BIBase.laterN (PROP := PROP) n (BIBase.except0 (PROP := PROP) P)) :=
        ⟨plain_laterN (P := BIBase.except0 (PROP := PROP) P) n⟩
      have hmono :
          (|={Eo}=> |={Eo}=> ▷^[n] ◇ P) ⊢ |={Eo}=> ▷^[n] ◇ P :=
        fupd_trans (E1 := Eo) (E2 := Eo) (E3 := Eo)
          (P := BIBase.laterN (PROP := PROP) n (BIBase.except0 (PROP := PROP) P))
      have hstep_mono :
          (|={Eo}=> step_fupdN (Eo := Eo) (Ei := Ei) n P) ⊢ |={Eo}=> ▷^[n] ◇ P :=
        (fupd_mono (E1 := Eo) (E2 := Eo) ih).trans hmono
      have hstep :
          (|={Eo}[Ei]▷=> step_fupdN (Eo := Eo) (Ei := Ei) n P) ⊢ |={Eo}[Ei]▷=> ▷^[n] ◇ P :=
        (step_fupd_fupd (Eo := Eo) (Ei := Ei) (P := step_fupdN (Eo := Eo) (Ei := Ei) n P)).1.trans
          ((step_fupd_mono (Eo := Eo) (Ei := Ei) hstep_mono).trans
            (step_fupd_fupd (Eo := Eo) (Ei := Ei)
              (P := BIBase.laterN (PROP := PROP) n (BIBase.except0 (PROP := PROP) P))).2)
      have hdrop : ▷ ◇ ▷^[n] ◇ P ⊢ ▷^[n.succ] ◇ P := by
        -- simplify the nested `◇` under a `▷`
        have hcore : ◇ ▷^[n] ◇ P ⊢ ▷^[n] ◇ P := by
          refine (except0_laterN (n := n) (P := BIBase.except0 (PROP := PROP) P)).trans ?_
          exact laterN_mono (PROP := PROP) n (except0_idemp.1)
        simpa [BIBase.laterN] using (later_mono (PROP := PROP) hcore)
      exact hstep.trans
        ((step_fupd_plain (Eo := Eo) (Ei := Ei)
          (P := BIBase.laterN (PROP := PROP) n (BIBase.except0 (PROP := PROP) P))).trans
          (fupd_mono (E1 := Eo) (E2 := Eo) hdrop))

end FUpdPlainLaws
