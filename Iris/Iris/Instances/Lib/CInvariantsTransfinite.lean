/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProofMode
public import Iris.Instances.IProp.Instance
public import Iris.Instances.Lib.FUpdTransfinite
public import Iris.Instances.Lib.InvariantsTransfinite
public import Iris.BI.Lib.Fractional
public import Iris.Algebra.Frac
public import Iris.Std.Namespaces
public import Iris.Std.CoPset
public import Iris.Std.List

/-! # Cancelable invariants over arbitrary step-indices (Transfinite Iris)

This file ports `theories/base_logic/lib/cancelable_invariants.v` of Transfinite Iris for the
credit-free fancy update of `Iris.Instances.Lib.FUpdTransfinite`. Following Transfinite Iris, the
ghost state consists of plain fractions (no exclusive token), and a cancelable invariant closes
over an equivalent proposition under a later:
`cinv N γ P := ∃ P', □ ▷ (P ↔ P') ∗ inv N (P' ∨ own γ 1)`.
This avoids splitting `▷ (P ∗ Q)`, which is unsound for transfinite step-indices. The ghost state
is lifted to the universe of the resources (`constOFU`).

The Rocq fork assumes `FiniteBoundedExistential SI` for the accessors, to distribute `▷` over `∨`;
in Lean `later_or` holds for every step-index type, so no assumption is needed.
-/

@[expose] public noncomputable section

universe u v

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open BI CMRA OFE Iris Iris.Std LawfulSet COFE ProofMode

/-- The camera of cancelable invariant tokens (Rocq: `fracR`). -/
abbrev CInvR := Qp

/-- Rocq: `cinvG`. -/
class CInvG (GF : BundledGFunctors.{u}) where
  inv : ElemG GF (constOFU.{max u v} CInvR)

attribute [reducible, instance] CInvG.inv

namespace CancelableInvariant

variable {GF : BundledGFunctors} [WsatGS GF] [W : CInvG GF]

/-- Rocq: `cinv_own`. -/
def own (γ : GName) (p : Qp) : IProp GF :=
  iOwn (E := W.inv) γ (ULift.up (p : CInvR))

/-- Rocq: `cinv`. -/
def cinv (N : Namespace) (γ : GName) (P : IProp GF) : IProp GF :=
  iprop(∃ P' : IProp GF, □ ▷ (P ↔ P') ∗ inv N iprop(P' ∨ own γ (1 : Qp)))

/-! ## Instances -/

/-- Rocq: `cinv_own_timeless`. -/
instance instTimelessOwn (γ : GName) (p : Qp) : Timeless (own (GF := GF) γ p) :=
  iOwn_timeless

/-- Rocq: `cinv_contractive`. -/
instance instContractiveCinv (N : Namespace) (γ : GName) :
    Contractive (cinv (GF := GF) N γ) where
  distLater_dist {n x y} H := by
    unfold cinv
    refine exists_ne fun P' => sep_ne.ne (intuitionistically_ne.ne ?_) .rfl
    exact Contractive.distLater_dist fun m hm => iff_ne.ne (H m hm) .rfl

/-- Rocq: `cinv_ne`. -/
instance instNonExpansiveCinv (N : Namespace) (γ : GName) :
    NonExpansive (cinv (GF := GF) N γ) :=
  ne_of_contractive _

/-- Rocq: `cinv_persistent`. -/
instance instPersistentCinv (N : Namespace) (γ : GName) (P : IProp GF) :
    Persistent (cinv N γ P) := by
  unfold cinv; infer_instance

/-- Rocq: `cinv_own_fractional`. -/
instance instFractionalOwn (γ : GName) :
    Fractional (fun p : Qp => own (GF := GF) γ p) where
  fractional p q := by
    change iOwn (E := W.inv) γ (ULift.up ((p + q : Qp) : CInvR)) ⊣⊢ _
    refine .trans ?_ iOwn_op
    exact equiv_iff.mp rfl

/-- Rocq: `cinv_own_as_fractional`. -/
instance instAsFractionalOwn (γ : GName) (q : Qp) :
    AsFractional (own (GF := GF) γ q) ioΦ (fun p : Qp => own γ p) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := instFractionalOwn γ

omit [WsatGS GF] in
/-- Rocq: `cinv_own_valid`. -/
theorem own_valid {γ : GName} {q1 q2 : Qp} :
    ⊢@{IProp GF} own γ q1 -∗ own γ q2 -∗ ⌜(q1 + q2).val ≤ 1⌝ := by
  unfold own
  iintro H1 H2
  icombine H1 H2 as H
  ihave %H := iOwn_cmraValid $$ H
  ipureintro
  exact H

omit [WsatGS GF] in
/-- Rocq: `cinv_own_1_l`. -/
theorem own_one_l {γ : GName} {q : Qp} :
    ⊢ own (GF := GF) γ (1 : Qp) -∗ own γ q -∗ False := by
  iintro H1 H2
  icases own_valid $$ H1 H2 with %H
  exact absurd H (by have := q.2; have : (1 : Qp).val = 1 := rfl; grind)

/-- Rocq: `cinv_iff`. -/
theorem cinv_iff {N : Namespace} {γ : GName} {P Q : IProp GF} :
    ⊢ cinv (GF := GF) N γ P -∗ ▷ □ (P ↔ Q) -∗ cinv N γ Q := by
  unfold cinv
  iintro ⟨%P'', #HP'', #Hinv⟩ #HPQ
  iexists P''
  isplit
  · imodintro
    inext
    isplit
    · iintro HQ
      icases HP'' with ⟨H1, -⟩
      iapply H1
      icases HPQ with ⟨-, H2⟩
      iapply H2 $$ HQ
    · iintro HP
      icases HPQ with ⟨H1, -⟩
      iapply H1
      icases HP'' with ⟨-, H2⟩
      iapply H2 $$ HP
  · iexact Hinv

/-- Rocq: `cinv_alloc_strong`. -/
theorem alloc_strong (P : GName → Prop) (HP : PredInfinite P) (E : CoPset) (N : Namespace) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own γ (1 : Qp) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv N γ Q := by
  imod iOwn_alloc_strong (E := W.inv) (ULift.up ((1 : Qp) : CInvR)) P ?_
    (by exact Qp.valid_one) with ⟨%γ, %HPγ, Hown⟩
  · exact HP.exists_ge
  · imodintro
    iexists γ
    isplitr [Hown]
    · ipureintro; exact HPγ
    isplitl [Hown]
    · unfold own; iexact Hown
    iintro %Q HQ
    imod inv_alloc N E iprop(Q ∨ own γ (1 : Qp)) $$ [HQ] with #HI
    · inext; ileft; iexact HQ
    imodintro
    unfold cinv
    iexists Q
    isplit
    · imodintro; inext
      isplit <;> iintro H <;> iexact H
    · iexact HI

/-- Rocq: `cinv_alloc_cofinite`. -/
theorem alloc_cofinite (G : List GName) (E : CoPset) (N : Namespace) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (1 : Qp) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv N γ Q :=
  alloc_strong (· ∉ G) (PredInfinite.not_mem G) E N

/-- Extra (upstream Rocq: `cinv_alloc_strong_open`). -/
theorem alloc_strong_open (P : GName → Prop) (HP : PredInfinite P) (E : CoPset) (N : Namespace)
    (Hsub : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own γ (1 : Qp) ∗
      ∀ (Q : IProp GF), |={E, E \ ↑N}=> cinv N γ Q ∗ (▷ Q ={E \ ↑N, E}=∗ True) := by
  imod iOwn_alloc_strong (E := W.inv) (ULift.up ((1 : Qp) : CInvR)) P ?_
    (by exact Qp.valid_one) with ⟨%γ, %HPγ, Hown⟩
  · exact HP.exists_ge
  · imodintro
    iexists γ
    isplitr [Hown]
    · ipureintro; exact HPγ
    isplitl [Hown]
    · unfold own; iexact Hown
    iintro %Q
    imod inv_alloc_open N E iprop(Q ∨ own γ (1 : Qp)) Hsub with ⟨#HI, Hclose⟩
    imodintro
    isplitr [Hclose]
    · unfold cinv
      iexists Q
      isplit
      · imodintro; inext
        isplit <;> iintro H <;> iexact H
      · iexact HI
    · iintro HQ
      iapply Hclose
      inext
      ileft
      iexact HQ

/-- Rocq: `cinv_alloc`. -/
theorem alloc (E : CoPset) (N : Namespace) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ own γ (1 : Qp) := by
  iintro HP
  imod alloc_cofinite [] E N with ⟨%γ, %Hγ, Hown, Halloc⟩
  imod Halloc $$ HP with HI
  imodintro
  iexists γ
  iframe

/-- Extra (upstream Rocq: `cinv_alloc_open`). -/
theorem alloc_open (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E, E \ ↑N}=> ∃ γ, cinv N γ P ∗ own γ (1 : Qp) ∗
      (▷ P ={E \ ↑N, E}=∗ True) := by
  imod alloc_strong_open (fun _ => True) PredInfinite.true E N Hsub
    with ⟨%γ, _, Hown, Hmake⟩
  imod Hmake $$ %P with ⟨HI, Hclose⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `cinv_open_strong`. -/
theorem acc_strong (E : CoPset) (N : Namespace) (γ : GName) (p : Qp) (P : IProp GF)
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ p ={E, E \ ↑N}=∗
      ▷ P ∗ own γ p ∗ (▷ P ∨ own γ (1 : Qp) ={E \ ↑N, E}=∗ True) := by
  unfold cinv
  iintro ⟨%P', #HP', #Hinv⟩ Hγ
  imod inv_acc Hsub $$ Hinv with ⟨Hc, Hclose⟩
  icases later_or.mp $$ Hc with (HP | >Hγ')
  · imodintro
    isplitl [HP]
    · inext
      icases HP' with ⟨-, H2⟩
      iapply H2 $$ HP
    isplitl [Hγ]
    · iexact Hγ
    iintro (HP | Hγ1)
    · iapply Hclose
      inext
      ileft
      icases HP' with ⟨H1, -⟩
      iapply H1 $$ HP
    · iapply Hclose
      inext
      iright
      iexact Hγ1
  · iexfalso
    iapply own_one_l $$ Hγ' Hγ

/-- Rocq: `cinv_open`. -/
theorem acc {E : CoPset} {N : Namespace} {γ : GName} {p : Qp} {P : IProp GF}
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ p ={E, E \ ↑N}=∗ ▷ P ∗ own γ p ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hγ
  imod acc_strong _ _ _ _ _ Hsub $$ Hinv Hγ with ⟨HP, Hγ, Hcl⟩
  imodintro
  isplitl [HP]
  · iexact HP
  isplitl [Hγ]
  · iexact Hγ
  iintro HP
  iapply Hcl
  ileft
  iexact HP

/-- Extra (upstream Iris-Lean `CancelableInvariant.inv_open_fupd`). -/
theorem inv_open_fupd {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ (▷ P ∗ Q ∗ own γ q ={E \ N}=∗ P ∗ R) -∗
      (Q ∗ own γ q) ={E}=∗ R := by
  iintro #Hinv H ⟨HQ, Hown⟩
  imod acc Hsub $$ Hinv Hown with ⟨HP, Hown, Hclose⟩
  imod H $$ [$] with ⟨HP, HR⟩; iframe
  imod Hclose $$ [$HP] with -
  itrivial

/-- Rocq: `cinv_cancel`. -/
theorem cancel (E : CoPset) {N : Namespace} {γ : GName} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ (1 : Qp) ={E}=∗ ▷ P := by
  iintro #Hinv Hγ
  imod acc_strong _ _ _ _ _ Hsub $$ Hinv Hγ with ⟨HP, Hγ, Hcl⟩
  imod Hcl $$ [Hγ] with -
  · iright; iexact Hγ
  imodintro
  iexact HP

/-- Rocq: `into_inv_cinv`. -/
instance intoInv_cinv (N : Namespace) (γ : GName) (P : IProp GF) :
    IntoInv (cinv N γ P) N := {}

set_option synthInstance.checkSynthOrder false in
/-- Rocq: `into_acc_cinv`. -/
instance intoAcc_cinv (E : CoPset) (N : Namespace) (γ : GName) (P : IProp GF) (p : Qp) :
    IntoAcc (X := Unit) (cinv N γ P) (↑N ⊆ E) (own γ p) (fupd E (E \ ↑N)) (fupd (E \ ↑N) E)
      (fun _ => iprop(▷ P ∗ own γ p)) (fun _ => iprop(▷ P)) (fun _ => none) where
  into_acc := by
    dsimp only [accessor, Option.getD]
    iintro %x #Hinv Hown
    imod acc x $$ Hinv Hown with ⟨HP, Hγ, Hcl⟩
    imodintro
    iexists ()
    isplitl [HP Hγ]
    · iframe
    · iintro HP
      iapply (BIFUpdate.mono true_emp.mp)
      iapply Hcl $$ HP

end CancelableInvariant
end Iris.Transfinite
