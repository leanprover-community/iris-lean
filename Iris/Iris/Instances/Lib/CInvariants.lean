/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProofMode
public import Iris.Instances.IProp.Instance
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.Invariants
public import Iris.BI.Lib.Fractional
public import Iris.Algebra.Frac
public import Iris.Algebra.Excl
public import Iris.Std.Namespaces
public import Iris.Std.CoPset
public import Iris.Std.List

@[expose] public section

namespace Iris

open BI CMRA OFE Iris Std LawfulSet Excl COFE ProofMode

/-! # Cancelable Invariants -/

abbrev CInvF : OFunctorPre :=
  ProdOF (constOF (Option (Excl Unit))) (constOF (Option Qp))

@[rocq_alias cinvG]
class CInvG (GF : BundledGFunctors) where
  inv : ElemG GF CInvF

attribute [reducible, instance] CInvG.inv

namespace CancelableInvariant

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : CInvG GF]

@[rocq_alias cinv_own]
def own (γ : GName) (p : Qp) : IProp GF := iOwn (E := W.inv) γ (none, some p)

@[rocq_alias cinv_excl]
def excl (γ : GName) : IProp GF := iOwn (E := W.inv) γ (some (Excl.excl ()), none)

@[rocq_alias cinv]
def cinv (N : Namespace) (γ : GName) (P : IProp GF) : IProp GF :=
  inv N iprop(P ∗ excl γ ∨ own γ (1 : Qp))

/-! ## Instances -/

@[rocq_alias cinv_own_timeless]
instance instTimelessOwn (γ : GName) (p : Qp) : Timeless (own (GF := GF) γ p) :=
  iOwn_timeless

instance instTimelessExcl (γ : GName) : Timeless (excl (GF := GF) γ) :=
  iOwn_timeless

@[rocq_alias cinv_contractive]
instance instContractiveCinv (N : Namespace) (γ : GName) :
    Contractive (cinv (GF := GF) N γ) where
  distLater_dist {n x y} H := by
    unfold cinv
    refine Contractive.distLater_dist fun m hm => or_ne.ne (sep_ne.ne (H _ hm) .rfl) .rfl

@[rocq_alias cinv_ne]
instance instNonExpansiveCinv (N : Namespace) (γ : GName) :
    NonExpansive (cinv (GF := GF) N γ) :=
  ne_of_contractive _

#rocq_ignore cinv_proper "Subsumed by instNonExpansiveCinv"

@[rocq_alias cinv_persistent]
instance instPersistentCinv (N : Namespace) (γ : GName) (P : IProp GF) :
    Persistent (cinv N γ P) := by
  unfold cinv; infer_instance

@[rocq_alias cinv_own_valid]
theorem own_valid {γ : GName} {q1 q2 : Qp} :
    ⊢@{IProp GF} own γ q1 -∗ own γ q2 -∗ ⌜(q1 + q2).val ≤ 1⌝ := by
  unfold own
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]; iframe
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  ipureintro
  exact H.2

@[rocq_alias cinv_own_fractional]
instance instFractionalOwn (γ : GName) :
    Fractional (fun p : Qp => own (GF := GF) γ p) where
  fractional p q := by
    show iOwn (E := W.inv) γ ((none, some (p + q))) ⊣⊢ _
    refine .trans ?_ iOwn_op
    exact equiv_iff.mp (NonExpansive.eqv (.of_eq rfl))

@[rocq_alias cinv_own_as_fractional]
instance instAsFractionalOwn (γ : GName) (q : Qp) :
    AsFractional (own (GF := GF) γ q) (fun p : Qp => own γ p) q where
  as_fractional := .rfl
  as_fractional_fractional := instFractionalOwn γ

@[rocq_alias cinv_own_excl_alloc]
theorem own_excl_alloc (P : GName → Prop) (HP : PredInfinite P) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ excl γ ∗ own γ (1 : Qp) := by
  imod iOwn_alloc_strong (E := W.inv)
    ((some (Excl.excl ()), none) • (none, some (1 : Qp)) :
      CInvF (IProp GF) (IProp GF)) P ?_
    ⟨trivial, Qp.valid_one⟩ with ⟨%γ, %HPγ, Hown⟩
  · intro N
    obtain ⟨γ, HPγ, Hγ⟩ := HP (List.range (N + 1))
    exact ⟨γ, by grind, HPγ⟩
  · imodintro
    iexists γ
    -- NOTE: Ideally, iframe would discharge this pure goal
    iframe %HPγ
    unfold excl own
    icases iOwn_op.mp $$ Hown with ⟨Hexcl, Hown⟩
    iframe

@[rocq_alias cinv_own_1_l]
theorem own_one_l {γ : GName} {q : Qp} :
    ⊢ own (GF := GF) γ (1 : Qp) -∗ own γ q -∗ False := by
  iintro H1 H2
  icases own_valid $$ H1 H2 with %H
  exact absurd H (by have := q.2; have : (1 : Qp).val = 1 := rfl; grind)

@[rocq_alias cinv_excl_excl]
theorem excl_excl (γ : GName) :
    ⊢ excl (GF := GF) γ -∗ excl γ -∗ False := by
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]
  · unfold excl; iframe
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  exact H.1.elim

@[rocq_alias cinv_iff]
nonrec theorem cinv_iff {N : Namespace} {γ : GName} {P Q : IProp GF} :
    ⊢ cinv (GF := GF) N γ P -∗ ▷ □ (P ↔ Q) -∗ cinv N γ Q := by
  unfold cinv
  iintro HI #⟨HPQ₁, HPQ₂⟩
  iapply inv_iff $$ HI
  iintro !> !>
  isplit
  · iintro (⟨HP, Hexcl⟩ | Htok)
    · ileft
      iframe
      iapply HPQ₁ $$ HP
    · iright; iframe
  · iintro (⟨HQ, Hexcl⟩ | Htok)
    · ileft
      iframe
      iapply HPQ₂ $$ HQ
    · iframe

@[rocq_alias cinv_alloc_strong]
theorem alloc_strong (P : GName → Prop) (HP : PredInfinite P) (E : CoPset) (N : Namespace) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own γ (1 : Qp) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv N γ Q := by
  imod own_excl_alloc P HP with ⟨%γ, %HPγ, Hexcl, Hown⟩
  imodintro
  iexists γ
  iframe %HPγ Hown
  iintro %Q HQ
  unfold cinv
  iapply inv_alloc
  inext
  ileft
  iframe

@[rocq_alias cinv_alloc_strong_open]
theorem alloc_strong_open (P : GName → Prop) (HP : PredInfinite P) (E : CoPset) (N : Namespace)
  (Hsub : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own γ (1 : Qp) ∗
      ∀ (Q : IProp GF), |={E, E \ ↑N}=> cinv N γ Q ∗ (▷ Q ={E \ ↑N, E}=∗ True) := by
  imod own_excl_alloc P HP with ⟨%γ, %HPγ, Hexcl, Hown⟩
  imodintro
  iexists γ
  iframe %HPγ Hown
  iframe
  iintro %Q
  imod inv_alloc_open N E iprop(Q ∗ excl γ ∨ own γ (1 : Qp)) Hsub with ⟨HI, Hclose⟩
  imodintro
  unfold cinv
  iframe
  iintro HQ
  iapply Hclose
  inext
  ileft
  iframe

@[rocq_alias cinv_alloc_cofinite]
theorem alloc_cofinite (G : List GName) (E : CoPset) (N : Namespace) :
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (1 : Qp) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv N γ Q :=
  alloc_strong (· ∉ G) (PredInfinite.not_mem G) E N

@[rocq_alias cinv_alloc]
theorem alloc (E : CoPset) (N : Namespace) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ own γ (1 : Qp) := by
  iintro HP
  imod alloc_cofinite [] E N with ⟨%γ, %Hγ, Hown, Halloc⟩
  imod Halloc $$ HP with HI
  imodintro
  iexists γ
  iframe

@[rocq_alias cinv_alloc_open]
theorem alloc_open (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E, E \ ↑N}=> ∃ γ, cinv N γ P ∗ own γ (1 : Qp) ∗
      (▷ P ={E \ ↑N, E}=∗ True) := by
  imod alloc_strong_open (fun _ => True) PredInfinite.true E N Hsub
    with ⟨%γ, _, Hown, Hmake⟩
  imod Hmake $$ %P with ⟨HI, Hclose⟩
  imodintro
  iexists γ
  iframe

@[rocq_alias cinv_acc_strong]
theorem acc_strong (E : CoPset) (N : Namespace) (γ : GName) (p : Qp) (P : IProp GF)
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ p ={E, E \ ↑N}=∗
      ▷ P ∗ own γ p ∗ ∀ (E' : CoPset), ▷ P ∨ own γ (1 : Qp) ={E', ↑N ∪ E'}=∗ True := by
  unfold cinv
  iintro #Hinv Hown
  imod inv_acc_strong _ _ _ Hsub $$ Hinv with ⟨(⟨HP, >Hexcl⟩ | >Hown'), Hclose⟩
  · imodintro
    iframe
    iintro %E' HPor
    iapply Hclose
    icases HPor with (HP | Hown1)
    · ileft; iframe
    · iright; iframe
  · iexfalso
    iapply own_one_l $$ Hown' Hown

@[rocq_alias cinv_acc]
theorem acc (E : CoPset) (N : Namespace) (γ : GName) (p : Qp) (P : IProp GF)
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ p ={E, E \ ↑N}=∗ ▷ P ∗ own γ p ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hγ
  imod acc_strong _ _ _ _ _ Hsub $$ Hinv Hγ with ⟨HP, Hγ, Hcl⟩
  imodintro
  iframe
  iintro HP
  imod Hcl $$ [HP] with _
  · ileft; iframe
  rw [subset_union_diff Hsub]
  imodintro
  itrivial

@[rocq_alias cinv_acc_1]
theorem acc_one (E : CoPset) (N : Namespace) (γ : GName) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ (1 : Qp) ={E}=∗
      ▷ P ∗ (▷ P ={E}=∗ own γ (1 : Qp)) := by
  iintro #Hinv Hγ
  unfold cinv
  imod inv_acc _ _ _ Hsub $$ Hinv with ⟨(⟨HP, >Hexcl⟩ | >Hγ'), Hclose⟩
  · imod Hclose $$ [Hγ] with -
    · inext; iright; iassumption
    imodintro
    iframe
    iintro HP
    imod inv_acc _ _ _ Hsub $$ Hinv with ⟨(⟨_HPbad, >Hexcl2⟩ | >Hγ1), Hclose2⟩
    · iexfalso
      iapply excl_excl $$ Hexcl Hexcl2
    · imod Hclose2 $$ [HP Hexcl] with -
      · inext; ileft; iframe
      imodintro
      iexact Hγ1
  · iexfalso
    iapply own_one_l $$ Hγ Hγ'

@[rocq_alias cinv_cancel]
theorem cancel (E : CoPset) (N : Namespace) (γ : GName) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢ cinv N γ P -∗ own γ (1 : Qp) ={E}=∗ ▷ P := by
  iintro #Hinv Hγ
  imod acc_one _ _ _ _ Hsub $$ Hinv Hγ with ⟨HP, -⟩
  imodintro
  iexact HP

@[rocq_alias into_inv_cinv]
instance intoInv_cinv (N : Namespace) (γ : GName) (P : IProp GF) :
    IntoInv (cinv N γ P) N := {}

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_acc_cinv]
instance intoAcc_cinv (E : CoPset) (N : Namespace) (γ : GName) (P : IProp GF) (p : Qp) :
    IntoAcc (X := Unit) (cinv N γ P) (↑N ⊆ E) (own γ p) (fupd E (E \ ↑N)) (fupd (E \ ↑N) E)
      (fun _ => iprop(▷ P ∗ own γ p)) (fun _ => iprop(▷ P)) (λ _ => none) where
  into_acc := by
    simp only [accessor]
    iintro %x #Hinv Hown
    imod acc _ _ _ _ _ x $$ Hinv Hown with ⟨HP, Hγ, Hcl⟩
    imodintro
    iexists ()
    isplitl [HP Hγ]
    · iframe
    · iintro HP
      iapply (BIFUpdate.mono true_emp.mp)
      iapply Hcl $$ HP

end CancelableInvariant
end Iris
end
