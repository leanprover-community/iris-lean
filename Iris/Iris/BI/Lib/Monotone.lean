/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.ProofMode

/-! # Monotone predicate transformers

A *curried predicate* is a `PROP`, or a function into curried predicates. `wandAll Φ Ψ` is the
pointwise wand `∀ x, Φ x -∗ Ψ x`, and `BIMono F` says that `F` preserves it.

The `IMono` rules prove `BIMono` one connective at a time. Each rule has the form
`⊢ □ R -∗ P -∗ P'`: under the persistent assumption `R`, the body `P` turns into `P'`. -/

@[expose] public section

namespace Iris
open BI Iris.Std

local bi PROP

universe w in
/-- A curried predicate: a `PROP`, or a function into curried predicates. -/
class Curried (τ : Type _) (PROP : Type _) [BI PROP] where
  /-- The arguments of a curried predicate, as a tuple. -/
  Args : Type w
  /-- Apply a curried predicate to all of its arguments. -/
  app : τ → Args → PROP
  /-- `∀ x, P x`, with one `∀` per argument. -/
  all : (Args → PROP) → PROP
  all_intro {Q : PROP} {P : Args → PROP} : (∀ a, Q ⊢ P a) → Q ⊢ all P
  all_elim {P : Args → PROP} (a : Args) : all P ⊢ P a

namespace Curried
variable {PROP : Type _} [BI PROP]

instance : Curried PROP PROP where
  Args := Unit
  app P _ := P
  all P := P ()
  all_intro h := h ()
  all_elim _ := .rfl

instance {α : Type _} {β : α → Type _} [∀ a, Curried (β a) PROP] :
    Curried ((a : α) → β a) PROP where
  Args := (a : α) × Args (β a) PROP
  app f a := app (f a.1) a.2
  all P := iprop(∀ a, all fun r => P ⟨a, r⟩)
  all_intro h := forall_intro fun a => all_intro fun r => h ⟨a, r⟩
  all_elim a := (forall_elim a.1).trans (all_elim a.2)

variable {τ : Type _} [Curried τ PROP]

/-- The pointwise wand `∀ x, Φ x -∗ Ψ x`. -/
def wandAll (Φ Ψ : τ) : PROP := all fun a => iprop(app Φ a -∗ app Ψ a)

theorem wandAll_intro {Q : PROP} {Φ Ψ : τ} (h : ∀ a, Q ∗ app Φ a ⊢ app Ψ a) :
    Q ⊢ wandAll Φ Ψ :=
  all_intro fun a => wand_intro (h a)

theorem wandAll_elim {Φ Ψ : τ} (a : Args τ PROP) : wandAll Φ Ψ ∗ app Φ a ⊢ app Ψ a :=
  (sep_mono_left (all_elim a)).trans wand_elim_left

theorem wandAll_trans {Φ Ψ Ξ : τ} : wandAll Φ Ψ ∗ □ wandAll Ψ Ξ ⊢ wandAll Φ Ξ :=
  wandAll_intro fun a => sep_right_comm.1.trans <| (sep_mono_left (wandAll_elim a)).trans <|
    sep_symm.trans <| (sep_mono_left intuitionistically_elim).trans (wandAll_elim a)

theorem wandAll_prop {P Q : PROP} : wandAll P Q = iprop(P -∗ Q) := rfl

theorem wandAll_pi {α : Type _} {β : α → Type _} [∀ a, Curried (β a) PROP]
    {Φ Ψ : (a : α) → β a} : wandAll (PROP := PROP) Φ Ψ = iprop(∀ a, wandAll (Φ a) (Ψ a)) := rfl

end Curried

open Curried

/-- `F` is monotone inside the BI: it preserves pointwise wands. -/
def BIMono {PROP : Type _} [BI PROP] {τ : Type _} [Curried τ PROP] (F : τ → τ) : Prop :=
  ∀ Φ Ψ, ⊢ □ wandAll Φ Ψ -∗ wandAll (F Φ) (F Ψ)

theorem BIMono.const {PROP : Type _} [BI PROP] {τ : Type _} [Curried τ PROP] (c : τ) :
    BIMono (PROP := PROP) fun _ : τ => c :=
  fun _ _ => wand_intro <| sep_elim_right.trans <| wandAll_intro fun _ => sep_elim_right

/-! ## Rules for `imono` -/

namespace IMono
variable {PROP : Type _} [BI PROP] {R P P' Q Q' : PROP}

/-- Introduce the first argument of a curried predicate. -/
theorem pi {α : Type _} {β : α → Type _} [∀ a, Curried (β a) PROP] {Φ Ψ : (a : α) → β a}
    (h : ∀ a, ⊢ □ R -∗ wandAll (Φ a) (Ψ a)) : ⊢ □ R -∗ wandAll Φ Ψ :=
  wand_intro <| emp_sep.1.trans <| forall_intro fun a => emp_sep.2.trans (wand_elim (h a))

/-- A predicate with no arguments left. -/
theorem prop (h : ⊢ □ R -∗ P -∗ P') : ⊢ □ R -∗ wandAll P P' := h

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
