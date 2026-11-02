/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.ProofMode

/-! # Monotone predicate transformers

`BIMono F` says that the predicate transformer `F : (A → PROP) → (A → PROP)` preserves pointwise
wands, inside the BI: `□ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x`.

The `IMono` rules prove `BIMono` one connective at a time. Each rule has the form
`⊢ □ R -∗ P -∗ P'`: under the persistent assumption `R`, the body `P` turns into `P'`. -/

@[expose] public section

namespace Iris
open BI Iris.Std

local bi PROP

variable {PROP : Type _} [BI PROP] {A : Sort _}

/-- `F` is monotone inside the BI: it preserves pointwise wands. -/
def BIMono (F : (A → PROP) → A → PROP) : Prop :=
  ∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

theorem BIMono.const (c : A → PROP) : BIMono fun _ => c := fun _ _ => by
  iintro #_ %x H
  iexact H

/-! ## Rules for `imono` -/

namespace IMono
variable {R P P' Q Q' : PROP}

/-- Introduce an argument of the predicates. -/
theorem arg {P : A → PROP} (h : ∀ x, ⊢ □ R -∗ P x) : ⊢ □ R -∗ ∀ x, P x :=
  wand_intro <| emp_sep.1.trans <| forall_intro fun x => emp_sep.2.trans (wand_elim (h x))

/-- A body that does not mention the recursive function. -/
theorem refl : ⊢ □ R -∗ P -∗ P :=
  wand_intro <| emp_sep.1.trans <| wand_intro sep_elim_right

theorem sep (h₁ : ⊢ □ R -∗ P -∗ P') (h₂ : ⊢ □ R -∗ Q -∗ Q') : ⊢ □ R -∗ P ∗ Q -∗ P' ∗ Q' := by
  iintro #H ⟨HP, HQ⟩
  isplitl [HP]
  · iapply h₁ $$ H HP
  · iapply h₂ $$ H HQ

theorem and (h₁ : ⊢ □ R -∗ P -∗ P') (h₂ : ⊢ □ R -∗ Q -∗ Q') :
    ⊢ □ R -∗ (P ∧ Q) -∗ (P' ∧ Q') := by
  iintro #H HPQ
  isplit
  · icases HPQ with ⟨HP, -⟩; iapply h₁ $$ H HP
  · icases HPQ with ⟨-, HQ⟩; iapply h₂ $$ H HQ

theorem or (h₁ : ⊢ □ R -∗ P -∗ P') (h₂ : ⊢ □ R -∗ Q -∗ Q') :
    ⊢ □ R -∗ (P ∨ Q) -∗ (P' ∨ Q') := by
  iintro #H (HP | HQ)
  · ileft; iapply h₁ $$ H HP
  · iright; iapply h₂ $$ H HQ

/-- The premise of a wand flips direction. -/
theorem wand (h₁ : ⊢ □ R -∗ P' -∗ P) (h₂ : ⊢ □ R -∗ Q -∗ Q') :
    ⊢ □ R -∗ (P -∗ Q) -∗ (P' -∗ Q') := by
  iintro #H HPQ HP'
  ihave HP := h₁ $$ H HP'
  iapply h₂ $$ H (HPQ $$ HP)

/-- The premise of a persistent implication flips direction. -/
theorem pers_imp (h₁ : ⊢ □ R -∗ P' -∗ P) (h₂ : ⊢ □ R -∗ Q -∗ Q') :
    ⊢ □ R -∗ (<pers> P → Q) -∗ (<pers> P' → Q') := by
  iintro #H HPQ #HP'
  ihave #HP := h₁ $$ H HP'
  iapply h₂ $$ H (HPQ $$ HP)

theorem «forall» {B : Sort _} {P P' : B → PROP} (h : ∀ b, ⊢ □ R -∗ P b -∗ P' b) :
    ⊢ □ R -∗ (∀ b, P b) -∗ (∀ b, P' b) := by
  iintro #H HP %b
  iapply h b $$ H HP

theorem «exists» {B : Sort _} {P P' : B → PROP} (h : ∀ b, ⊢ □ R -∗ P b -∗ P' b) :
    ⊢ □ R -∗ (∃ b, P b) -∗ (∃ b, P' b) := by
  iintro #H ⟨%b, HP⟩
  iexists b
  iapply h b $$ H HP

theorem persistently (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ <pers> P -∗ <pers> P' := by
  iintro #H #HP !>
  iapply h $$ H HP

theorem affinely (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ <affine> P -∗ <affine> P' := by
  iintro #H HP !>
  iapply h $$ H HP

theorem absorbingly (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ <absorb> P -∗ <absorb> P' := by
  iintro #H >HP !>
  iapply h $$ H HP

theorem intuitionistically (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ □ P -∗ □ P' := by
  iintro #H #HP !>
  iapply h $$ H HP

theorem later (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ ▷ P -∗ ▷ P' := by
  iintro #H HP !>
  iapply h $$ H HP

theorem laterN {n : Nat} (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ ▷^[n] P -∗ ▷^[n] P' := by
  iintro #H HP !>
  iapply h $$ H HP

theorem except0 (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ ◇ P -∗ ◇ P' := by
  iintro #H >HP !>
  iapply h $$ H HP

theorem bupd [BIUpdate PROP] (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ (|==> P) -∗ |==> P' := by
  iintro #H >HP !>
  iapply h $$ H HP

theorem fupd [BIFUpdate PROP] {E1 E2 : CoPset} (h : ⊢ □ R -∗ P -∗ P') :
    ⊢ □ R -∗ (|={E1,E2}=> P) -∗ |={E1,E2}=> P' := by
  iintro #H >HP !>
  iapply h $$ H HP

theorem step_fupdN [BIFUpdate PROP] {Eo Ei : CoPset} {n : Nat} (h : ⊢ □ R -∗ P -∗ P') :
    ⊢ □ R -∗ (|={Eo}[Ei]▷=>^[n] P) -∗ |={Eo}[Ei]▷=>^[n] P' := by
  induction n with
  | zero => exact h
  | succ n ih => exact fupd (later (fupd ih))

theorem bigSepL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, ⊢ □ R -∗ P k x -∗ P' k x) :
    ⊢ □ R -∗ ([∗list] k ↦ x ∈ l, P k x) -∗ [∗list] k ↦ x ∈ l, P' k x := by
  iintro #H HP
  iapply BigSepL.bigSepL_impl $$ HP
  iintro !> %k %x _ HPk
  iapply h k x $$ H HPk

theorem bigAndL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, ⊢ □ R -∗ P k x -∗ P' k x) :
    ⊢ □ R -∗ ([∧list] k ↦ x ∈ l, P k x) -∗ [∧list] k ↦ x ∈ l, P' k x :=
  wand_intro <| emp_sep.1.trans <| wand_intro <| BigAndL.bigAndL_intro fun k x hk =>
    (sep_mono_right (BigAndL.bigAndL_lookup hk)).trans <|
      wand_elim (emp_sep.2.trans (wand_elim (h k x)))

theorem bigOrL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, ⊢ □ R -∗ P k x -∗ P' k x) :
    ⊢ □ R -∗ ([∨list] k ↦ x ∈ l, P k x) -∗ [∨list] k ↦ x ∈ l, P' k x := by
  iintro #H HP
  ihave ⟨%k, %x, %hk, HPk⟩ := BigOrL.bigOrL_exist.1 $$ HP
  iapply BigOrL.bigOrL_intro hk
  iapply h k x $$ H HPk

theorem bigSepL2 {B C : Type _} {l1 : List B} {l2 : List C} {P P' : Nat → B → C → PROP}
    (h : ∀ k x y, ⊢ □ R -∗ P k x y -∗ P' k x y) :
    ⊢ □ R -∗ ([∗list] k ↦ x;y ∈ l1;l2, P k x y) -∗ [∗list] k ↦ x;y ∈ l1;l2, P' k x y := by
  iintro #H HP
  iapply BigSepL2.bigSepL2_impl $$ HP
  iintro !> %k %x %y _ _ HPk
  iapply h k x y $$ H HPk

theorem bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] {m : M V}
    {P P' : K → V → PROP} (h : ∀ k v, ⊢ □ R -∗ P k v -∗ P' k v) :
    ⊢ □ R -∗ ([∗map] k ↦ v ∈ m, P k v) -∗ [∗map] k ↦ v ∈ m, P' k v := by
  iintro #H HP
  iapply BigSepM.bigSepM_impl $$ HP
  iintro !> %k %v _ HPk
  iapply h k v $$ H HPk

theorem bigSepS {S B : Type _} [LawfulFiniteSet S B] {X : S} {P P' : B → PROP}
    (h : ∀ x, ⊢ □ R -∗ P x -∗ P' x) :
    ⊢ □ R -∗ ([∗set] x ∈ X, P x) -∗ [∗set] x ∈ X, P' x := by
  iintro #H HP
  iapply BigSepS.bigSepS_impl $$ HP
  iintro !> %x _ HPx
  iapply h x $$ H HPx

theorem bigSepMS {MS B : Type _} [LawfulFiniteMultiSet MS B] {X : MS} {P P' : B → PROP}
    (h : ∀ x, ⊢ □ R -∗ P x -∗ P' x) :
    ⊢ □ R -∗ ([∗mset] x ∈ X, P x) -∗ [∗mset] x ∈ X, P' x := by
  iintro #H HP
  iapply BigSepMS.bigSepMS_impl $$ HP
  iintro !> %x _ HPx
  iapply h x $$ H HPx

end IMono

end Iris
