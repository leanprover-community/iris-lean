/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Iris.BI.Lib.MonotoneAttr
public import Iris.BI.Telescopes
public import Iris.ProofMode

/-! # Monotone predicate transformers

`BIMono F` says that `F` preserves pointwise wands. The `IMonoPred` rules here are what the
`imono` tactic (`ProofMode/Lib/Monotone.lean`) applies. -/

@[expose] public section

namespace Iris
open BI Iris.Std

local bi PROP

variable {PROP : Type _} [BI PROP] {A : Sort _}

/-- `F` is monotone inside the BI: it preserves pointwise wands. -/
def BIMono (F : (A → PROP) → A → PROP) : Prop :=
  ∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x

/-! ## Rules for `imono` -/

/-- A monotonicity goal. -/
def IMonoPred (R P Q : PROP) : Prop := ⊢ □ R -∗ P -∗ Q

namespace IMonoPred
variable {R P P' Q Q' : PROP}

/-- Introduce an argument of the predicates. -/
theorem arg {P : A → PROP} (h : ∀ x, ⊢ □ R -∗ P x) : ⊢ □ R -∗ ∀ x, P x :=
  wand_intro <| emp_sep.1.trans <| forall_intro fun x => emp_sep.2.trans (wand_elim (h x))

/-- A recursive call, by the assumption. -/
theorem call : IMonoPred iprop(P -∗ P') P P' := by
  unfold IMonoPred
  iintro #H HP
  iapply H $$ HP

/-- Specialize the assumption to the arguments of a recursive call. -/
theorem spec {B : Sort _} {S : B → PROP} (b : B) (h : IMonoPred (S b) P P') :
    IMonoPred iprop(∀ b, S b) P P' := by
  unfold IMonoPred at *
  iintro #H HP
  iapply h $$ [] HP
  iintro !>
  iapply H

/-- A body that does not mention the recursive function. -/
theorem refl : IMonoPred R P P :=
  wand_intro <| emp_sep.1.trans <| wand_intro sep_elim_right

@[imono] theorem sep (h₁ : IMonoPred R P P') (h₂ : IMonoPred R Q Q') :
    IMonoPred R iprop(P ∗ Q) iprop(P' ∗ Q') := by
  unfold IMonoPred at *
  iintro #H ⟨HP, HQ⟩
  isplitl [HP]
  · iapply h₁ $$ H HP
  · iapply h₂ $$ H HQ

@[imono] theorem and (h₁ : IMonoPred R P P') (h₂ : IMonoPred R Q Q') :
    IMonoPred R iprop(P ∧ Q) iprop(P' ∧ Q') := by
  unfold IMonoPred at *
  iintro #H HPQ
  isplit
  · icases HPQ with ⟨HP, -⟩; iapply h₁ $$ H HP
  · icases HPQ with ⟨-, HQ⟩; iapply h₂ $$ H HQ

@[imono] theorem or (h₁ : IMonoPred R P P') (h₂ : IMonoPred R Q Q') :
    IMonoPred R iprop(P ∨ Q) iprop(P' ∨ Q') := by
  unfold IMonoPred at *
  iintro #H (HP | HQ)
  · ileft; iapply h₁ $$ H HP
  · iright; iapply h₂ $$ H HQ

/-- The premise of a wand flips direction. -/
@[imono] theorem wand (h₁ : IMonoPred R P' P) (h₂ : IMonoPred R Q Q') :
    IMonoPred R iprop(P -∗ Q) iprop(P' -∗ Q') := by
  unfold IMonoPred at *
  iintro #H HPQ HP'
  ihave HP := h₁ $$ H HP'
  iapply h₂ $$ H (HPQ $$ HP)

/-- The premise of a persistent implication flips direction. -/
@[imono] theorem pers_imp (h₁ : IMonoPred R P' P) (h₂ : IMonoPred R Q Q') :
    IMonoPred R iprop(<pers> P → Q) iprop(<pers> P' → Q') := by
  unfold IMonoPred at *
  iintro #H HPQ #HP'
  ihave #HP := h₁ $$ H HP'
  iapply h₂ $$ H (HPQ $$ HP)

@[imono] theorem «forall» {B : Sort _} {P P' : B → PROP} (h : ∀ b, IMonoPred R (P b) (P' b)) :
    IMonoPred R iprop(∀ b, P b) iprop(∀ b, P' b) := by
  unfold IMonoPred at *
  iintro #H HP %b
  iapply h b $$ H HP

@[imono] theorem «exists» {B : Sort _} {P P' : B → PROP} (h : ∀ b, IMonoPred R (P b) (P' b)) :
    IMonoPred R iprop(∃ b, P b) iprop(∃ b, P' b) := by
  unfold IMonoPred at *
  iintro #H ⟨%b, HP⟩
  iexists b
  iapply h b $$ H HP

@[imono] theorem tforall {TT : Tele} {P P' : TT.Arg → PROP} (h : ∀ x, IMonoPred R (P x) (P' x)) :
    IMonoPred R (BI.tforall P) (BI.tforall P') := by
  rw [(tforall_forall P).to_eq, (tforall_forall P').to_eq]
  exact «forall» h

@[imono] theorem texist {TT : Tele} {P P' : TT.Arg → PROP} (h : ∀ x, IMonoPred R (P x) (P' x)) :
    IMonoPred R (BI.texist P) (BI.texist P') := by
  rw [(texist_exist P).to_eq, (texist_exist P').to_eq]
  exact «exists» h

@[imono] theorem persistently (h : IMonoPred R P P') :
    IMonoPred R iprop(<pers> P) iprop(<pers> P') := by
  unfold IMonoPred at *
  iintro #H #HP !>
  iapply h $$ H HP

@[imono] theorem affinely (h : IMonoPred R P P') :
    IMonoPred R iprop(<affine> P) iprop(<affine> P') := by
  unfold IMonoPred at *
  iintro #H HP !>
  iapply h $$ H HP

@[imono] theorem absorbingly (h : IMonoPred R P P') :
    IMonoPred R iprop(<absorb> P) iprop(<absorb> P') := by
  unfold IMonoPred at *
  iintro #H >HP !>
  iapply h $$ H HP

@[imono] theorem intuitionistically (h : IMonoPred R P P') :
    IMonoPred R iprop(□ P) iprop(□ P') := by
  unfold IMonoPred at *
  iintro #H #HP !>
  iapply h $$ H HP

@[imono] theorem later (h : IMonoPred R P P') : IMonoPred R iprop(▷ P) iprop(▷ P') := by
  unfold IMonoPred at *
  iintro #H HP !>
  iapply h $$ H HP

@[imono] theorem laterN {n : Nat} (h : IMonoPred R P P') :
    IMonoPred R iprop(▷^[n] P) iprop(▷^[n] P') := by
  unfold IMonoPred at *
  iintro #H HP !>
  iapply h $$ H HP

@[imono] theorem except0 (h : IMonoPred R P P') : IMonoPred R iprop(◇ P) iprop(◇ P') := by
  unfold IMonoPred at *
  iintro #H >HP !>
  iapply h $$ H HP

@[imono] theorem bupd [BIUpdate PROP] (h : IMonoPred R P P') :
    IMonoPred R iprop(|==> P) iprop(|==> P') := by
  unfold IMonoPred at *
  iintro #H >HP !>
  iapply h $$ H HP

@[imono] theorem fupd [BIFUpdate PROP] {E1 E2 : CoPset} (h : IMonoPred R P P') :
    IMonoPred R iprop(|={E1,E2}=> P) iprop(|={E1,E2}=> P') := by
  unfold IMonoPred at *
  iintro #H >HP !>
  iapply h $$ H HP

@[imono] theorem step_fupdN [BIFUpdate PROP] {Eo Ei : CoPset} {n : Nat} (h : IMonoPred R P P') :
    IMonoPred R iprop(|={Eo}[Ei]▷=>^[n] P) iprop(|={Eo}[Ei]▷=>^[n] P') := by
  induction n with
  | zero => exact h
  | succ n ih => exact fupd (later (fupd ih))

@[imono] theorem bigSepL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, IMonoPred R (P k x) (P' k x)) :
    IMonoPred R iprop([∗list] k ↦ x ∈ l, P k x) iprop([∗list] k ↦ x ∈ l, P' k x) := by
  unfold IMonoPred at *
  iintro #H HP
  iapply BigSepL.bigSepL_impl $$ HP
  iintro !> %k %x _ HPk
  iapply h k x $$ H HPk

@[imono] theorem bigAndL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, IMonoPred R (P k x) (P' k x)) :
    IMonoPred R iprop([∧list] k ↦ x ∈ l, P k x) iprop([∧list] k ↦ x ∈ l, P' k x) :=
  wand_intro <| emp_sep.1.trans <| wand_intro <| BigAndL.bigAndL_intro fun k x hk =>
    (sep_mono_right (BigAndL.bigAndL_lookup hk)).trans <|
      wand_elim (emp_sep.2.trans (wand_elim (h k x)))

@[imono] theorem bigOrL {B : Type _} {l : List B} {P P' : Nat → B → PROP}
    (h : ∀ k x, IMonoPred R (P k x) (P' k x)) :
    IMonoPred R iprop([∨list] k ↦ x ∈ l, P k x) iprop([∨list] k ↦ x ∈ l, P' k x) := by
  unfold IMonoPred at *
  iintro #H HP
  ihave ⟨%k, %x, %hk, HPk⟩ := BigOrL.bigOrL_exist.1 $$ HP
  iapply BigOrL.bigOrL_intro hk
  iapply h k x $$ H HPk

@[imono] theorem bigSepL2 {B C : Type _} {l1 : List B} {l2 : List C} {P P' : Nat → B → C → PROP}
    (h : ∀ k x y, IMonoPred R (P k x y) (P' k x y)) :
    IMonoPred R iprop([∗list] k ↦ x;y ∈ l1;l2, P k x y)
      iprop([∗list] k ↦ x;y ∈ l1;l2, P' k x y) := by
  unfold IMonoPred at *
  iintro #H HP
  iapply BigSepL2.bigSepL2_impl $$ HP
  iintro !> %k %x %y _ _ HPk
  iapply h k x y $$ H HPk

@[imono] theorem bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] {m : M V}
    {P P' : K → V → PROP} (h : ∀ k v, IMonoPred R (P k v) (P' k v)) :
    IMonoPred R iprop([∗map] k ↦ v ∈ m, P k v) iprop([∗map] k ↦ v ∈ m, P' k v) := by
  unfold IMonoPred at *
  iintro #H HP
  iapply BigSepM.bigSepM_impl $$ HP
  iintro !> %k %v _ HPk
  iapply h k v $$ H HPk

@[imono] theorem bigSepS {S B : Type _} [LawfulFiniteSet S B] {X : S} {P P' : B → PROP}
    (h : ∀ x, IMonoPred R (P x) (P' x)) :
    IMonoPred R iprop([∗set] x ∈ X, P x) iprop([∗set] x ∈ X, P' x) := by
  unfold IMonoPred at *
  iintro #H HP
  iapply BigSepS.bigSepS_impl $$ HP
  iintro !> %x _ HPx
  iapply h x $$ H HPx

@[imono] theorem bigSepMS {MS B : Type _} [LawfulFiniteMultiSet MS B] {X : MS} {P P' : B → PROP}
    (h : ∀ x, IMonoPred R (P x) (P' x)) :
    IMonoPred R iprop([∗mset] x ∈ X, P x) iprop([∗mset] x ∈ X, P' x) := by
  unfold IMonoPred at *
  iintro #H HP
  iapply BigSepMS.bigSepMS_impl $$ HP
  iintro !> %x _ HPx
  iapply h x $$ H HPx

end IMonoPred

end Iris
