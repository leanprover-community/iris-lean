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

open BI CMRA OFE Iris Std LawfulSet Excl Fraction COFE

/-! # Cancelable Invariants -/

abbrev CInvF (F : Type _) : OFunctorPre :=
  ProdOF (constOF (Option (Excl Unit))) (constOF (Option (Frac F)))

@[rocq_alias cinvG]
class CInvG (F : Type _) [UFraction F] (GF : BundledGFunctors) where
  inv : ElemG GF (CInvF F)

attribute [reducible, instance] CInvG.inv

namespace CancelableInvariant

variable {F : Type _} [UFraction F]
variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [W : CInvG F GF]

@[rocq_alias cinv_own]
def own (γ : GName) (p : Frac F) : IProp GF := iOwn (E := W.inv) γ (none, some p)

@[rocq_alias cinv_excl]
def excl (γ : GName) : IProp GF := iOwn (E := W.inv) γ (some (Excl.excl ()), none)

@[rocq_alias cinv]
def cinv (N : Namespace) (γ : GName) (P : IProp GF) : IProp GF :=
  inv N iprop(P ∗ excl (F := F) γ ∨ own γ (⟨One.one⟩ : Frac F))

/-! ## Instances -/

@[rocq_alias cinv_own_timeless]
instance instTimelessOwn (γ : GName) (p : Frac F) : Timeless (own (GF := GF) γ p) :=
  iOwn_timeless

instance instTimelessExcl (γ : GName) : Timeless (excl (F := F) (GF := GF) γ) :=
  iOwn_timeless

@[rocq_alias cinv_contractive]
instance instContractiveCinv (N : Namespace) (γ : GName) :
    Contractive (cinv (GF := GF) (F := F) N γ) where
  distLater_dist {n x y} H := by
    unfold cinv
    refine Contractive.distLater_dist fun m hm => or_ne.ne (sep_ne.ne (H _ hm) .rfl) .rfl

@[rocq_alias cinv_ne]
instance instNonExpansiveCinv (N : Namespace) (γ : GName) :
    NonExpansive (cinv (F := F) (GF := GF) N γ) :=
  ne_of_contractive _

#rocq_ignore cinv_proper "Subsumed by instNonExpansiveCinv"

@[rocq_alias cinv_persistent]
instance instPersistentCinv (N : Namespace) (γ : GName) (P : IProp GF) :
    Persistent (cinv (F := F) N γ P) := by
  unfold cinv; infer_instance

@[rocq_alias cinv_own_valid]
theorem own_valid {γ : GName} {q1 q2 : Frac F} :
    ⊢@{IProp GF} own γ q1 -∗ own γ q2 -∗ ⌜Proper (q1.car + q2.car)⌝ := by
  unfold own
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]; iframe
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  ipureintro
  exact H.2

@[rocq_alias cinv_own_fractional]
instance instFractionalOwn (γ : GName) :
    Fractional (fun p : F => own (GF := GF) γ ⟨p⟩) where
  fractional p q := by
    show iOwn (E := W.inv) γ ((none, some ⟨p + q⟩)) ⊣⊢ _
    refine .trans ?_ iOwn_op
    exact equiv_iff.mp (NonExpansive.eqv (.of_eq rfl))

@[rocq_alias cinv_own_as_fractional]
instance instAsFractionalOwn (γ : GName) (q : F) :
    AsFractional (own (GF := GF) γ ⟨q⟩) (fun p : F => own γ ⟨p⟩) q where
  as_fractional := .rfl
  as_fractional_fractional := instFractionalOwn γ

@[rocq_alias cinv_own_excl_alloc]
theorem own_excl_alloc (P : GName → Prop) (HP : PredInfinite P) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ excl (F := F) γ ∗ own γ (⟨One.one⟩ : Frac F) := by
  imod iOwn_alloc_strong (E := W.inv)
    ((some (Excl.excl ()), none) • (none, some (⟨One.one⟩ : Frac F)) :
      CInvF F (IProp GF) (IProp GF)) P ?_
    ⟨trivial, UFraction.one_whole.1⟩ with ⟨%γ, %HPγ, Hown⟩
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
theorem own_one_l {γ : GName} {q : Frac F} :
    ⊢ own (GF := GF) γ (⟨One.one⟩ : Frac F) -∗ own γ q -∗ False := by
  iintro H1 H2
  icases own_valid $$ H1 H2 with %H
  exact (UFraction.one_whole.2 ⟨q.car, H⟩).elim

@[rocq_alias cinv_excl_excl]
theorem excl_excl (γ : GName) :
    ⊢ excl (GF := GF) (F := F) γ -∗ excl (F := F) γ -∗ False := by
  iintro H1 H2
  ihave H := iOwn_op $$ [H1 H2]
  · unfold excl; iframe
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete $$ H with %H
  exact H.1.elim

@[rocq_alias cinv_iff]
nonrec theorem cinv_iff {N : Namespace} {γ : GName} {P Q : IProp GF} :
    ⊢ cinv (GF := GF) (F := F) N γ P -∗ ▷ □ (P ↔ Q) -∗ cinv (F := F) N γ Q := by
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
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own γ (⟨One.one⟩ : Frac F) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv (F := F) N γ Q := by
  imod own_excl_alloc (F := F) P HP with ⟨%γ, %HPγ, Hexcl, Hown⟩
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
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜P γ⌝ ∗ own (F := F) γ (⟨One.one⟩ : Frac F) ∗
      ∀ (Q : IProp GF), |={E, E \ ↑N}=> cinv (F := F) N γ Q ∗ (▷ Q ={E \ ↑N, E}=∗ True) := by
  imod own_excl_alloc (F := F) P HP with ⟨%γ, %HPγ, Hexcl, Hown⟩
  imodintro
  iexists γ
  iframe %HPγ Hown
  iframe
  iintro %Q
  imod inv_alloc_open N E iprop(Q ∗ excl (F := F) γ ∨ own γ (⟨One.one⟩ : Frac F)) Hsub with ⟨HI, Hclose⟩
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
    ⊢@{IProp GF} |={E}=> ∃ γ, ⌜γ ∉ G⌝ ∗ own (F := F) γ (⟨One.one⟩ : Frac F) ∗
      ∀ Q, ▷ Q ={E}=∗ cinv (F := F) N γ Q :=
  alloc_strong (· ∉ G) (PredInfinite.not_mem G) E N

@[rocq_alias cinv_alloc]
theorem alloc (E : CoPset) (N : Namespace) (P : IProp GF) :
    ⊢ ▷ P ={E}=∗ ∃ γ, cinv (F := F) N γ P ∗ own γ (⟨One.one⟩ : Frac F) := by
  iintro HP
  imod alloc_cofinite (F := F) [] E N with ⟨%γ, %Hγ, Hown, Halloc⟩
  imod Halloc $$ HP with HI
  imodintro
  iexists γ
  iframe

@[rocq_alias cinv_alloc_open]
theorem alloc_open (E : CoPset) (N : Namespace) (P : IProp GF) (Hsub : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E, E \ ↑N}=> ∃ γ, cinv (F := F) N γ P ∗ own γ (⟨One.one⟩ : Frac F) ∗
      (▷ P ={E \ ↑N, E}=∗ True) := by
  imod alloc_strong_open (F := F) (fun _ => True) PredInfinite.true E N Hsub
    with ⟨%γ, _, Hown, Hmake⟩
  imod Hmake $$ %P with ⟨HI, Hclose⟩
  imodintro
  iexists γ
  iframe

@[rocq_alias cinv_acc_strong]
theorem acc_strong (E : CoPset) (N : Namespace) (γ : GName) (p : Frac F) (P : IProp GF)
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv (F := F) N γ P -∗ own γ p ={E, E \ ↑N}=∗
      ▷ P ∗ own γ p ∗ ∀ (E' : CoPset), ▷ P ∨ own γ (⟨One.one⟩ : Frac F) ={E', ↑N ∪ E'}=∗ True := by
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
theorem acc (E : CoPset) (N : Namespace) (γ : GName) (p : Frac F) (P : IProp GF)
    (Hsub : ↑N ⊆ E) :
    ⊢ cinv (F := F) N γ P -∗ own γ p ={E, E \ ↑N}=∗ ▷ P ∗ own γ p ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
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
    ⊢ cinv (F := F) N γ P -∗ own (F := F) γ (⟨One.one⟩ : Frac F) ={E}=∗
      ▷ P ∗ (▷ P ={E}=∗ own γ (⟨One.one⟩ : Frac F)) := by
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
    ⊢ cinv (F := F) N γ P -∗ own (F := F) γ (⟨One.one⟩ : Frac F) ={E}=∗ ▷ P := by
  iintro #Hinv Hγ
  imod acc_one _ _ _ _ Hsub $$ Hinv Hγ with ⟨HP, -⟩
  imodintro
  iexact HP

end CancelableInvariant
end Iris
end
