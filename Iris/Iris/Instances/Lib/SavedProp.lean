/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Instances.IProp
public import Iris.Algebra.Lib.DFracAgree
public import Iris.BI.Lib.Fractional
public import Iris.BI.Algebra
public import Iris.BI.InternalEq
public import Iris.ProofMode

@[expose] public section

namespace Iris

open BI CMRA Agree OFE UPred IProp Std ProofMode COFE

/-! ## Saved anything -/

@[rocq_alias savedAnythingG]
class SavedAnythingG (GF : BundledGFunctors) (F : OFunctorPre) [OFunctorContractive F] where
  [elemG : ElemG GF (DFracAgree.DFracAgreeRF F)]

attribute [reducible, instance] SavedAnythingG.elemG

#rocq_ignore «savedAnythingΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_savedAnythingΣ» "Subsumed by BundledGFunctors typeclass synthesis"

@[rocq_alias saved_anything_own]
def saved_anything_own {GF : BundledGFunctors} {F : OFunctorPre} [OFunctorContractive F]
    [SavedAnythingG GF F] (γ : GName) (dq : DFrac) (x : F.ap (IProp GF)) : IProp GF :=
  iOwn (F := DFracAgree.DFracAgreeRF F) γ (DFracAgree.mk dq x)

section saved_anything

variable {GF : BundledGFunctors} {F : OFunctorPre} [OFunctorContractive F] [SavedAnythingG GF F]

@[rocq_alias saved_anything_discarded_persistent]
instance saved_anything_discarded_persistent (γ : GName) (x : F.ap (IProp GF)) :
    Persistent (saved_anything_own γ .discard x) := by
  unfold saved_anything_own
  infer_instance

@[rocq_alias saved_anything_ne]
instance saved_anything_ne (γ : GName) (dq : DFrac) :
    NonExpansive (saved_anything_own (GF := GF) (F := F) γ dq) where
  ne _ _ _ H := iOwn_ne.ne (DFracAgree.mk_ne.ne H)

#rocq_ignore «saved_anything_proper» "Not needed in the setoid-free setting."

@[rocq_alias saved_anything_fractional]
instance saved_anything_fractional (γ : GName) (x : F.ap (IProp GF)) :
    Fractional (fun q : Qp => saved_anything_own γ (.own q) x) where
  fractional p q := by
    unfold saved_anything_own
    refine .trans ?_ iOwn_op
    refine equiv_iff.mp ?_
    exact iOwn_ne.eqv (DFracAgree.Frac.mk_op (q₁ := p) (q₂ := q))

@[rocq_alias saved_anything_as_fractional]
instance saved_anything_as_fractional (γ : GName) (x : F.ap (IProp GF)) (q : Qp) :
    AsFractional (saved_anything_own γ (.own q) x)
      (fun q => saved_anything_own γ (.own q) x) q where
  as_fractional := .rfl
  as_fractional_fractional := saved_anything_fractional γ x

/-! ### Allocation -/

@[rocq_alias saved_anything_alloc_strong]
theorem saved_anything_alloc_strong (x : F.ap (IProp GF)) (I : GName → Prop) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜I γ⌝ ∗ saved_anything_own γ dq x := by
  unfold saved_anything_own
  refine iOwn_alloc_strong _ I ?_ ⟨Hdq, toAgree_valid⟩
  intro N
  obtain ⟨k, hk, hnk⟩ := HI (List.range N)
  exact ⟨k, Nat.not_lt.mp (fun h => hnk (List.mem_range.mpr h)), hk⟩

@[rocq_alias saved_anything_alloc_cofinite]
theorem saved_anything_alloc_cofinite (x : F.ap (IProp GF)) (G : List GName) (dq : DFrac)
    (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_anything_own γ dq x :=
  saved_anything_alloc_strong x (· ∉ G) dq Hdq (PredInfinite.not_mem G)

@[rocq_alias saved_anything_alloc]
theorem saved_anything_alloc (x : F.ap (IProp GF)) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, saved_anything_own γ dq x := by
  unfold saved_anything_own
  exact iOwn_alloc _ ⟨Hdq, toAgree_valid⟩

/-! ### Validity -/

@[rocq_alias saved_anything_valid]
theorem saved_anything_valid (γ : GName) (dq : DFrac) (x : F.ap (IProp GF)) :
    saved_anything_own γ dq x ⊢@{IProp GF} ⌜✓ dq⌝ :=
  iOwn_cmraValid.trans (dfrac_agree_validI dq x).mp

@[rocq_alias saved_anything_valid_2]
theorem saved_anything_valid_2 (γ : GName) (dq1 dq2 : DFrac) (x y : F.ap (IProp GF)) :
    saved_anything_own γ dq1 x ∗ saved_anything_own γ dq2 y ⊢@{IProp GF}
      ⌜✓ (dq1 • dq2)⌝ ∧ internalEq x y :=
  iOwn_cmraValid_op.trans (dfrac_agree_validI_2 dq1 dq2 x y).mp

@[rocq_alias saved_anything_agree]
theorem saved_anything_agree (γ : GName) (dq1 dq2 : DFrac) (x y : F.ap (IProp GF)) :
    saved_anything_own γ dq1 x ∗ saved_anything_own γ dq2 y ⊢@{IProp GF} internalEq x y :=
  (saved_anything_valid_2 γ dq1 dq2 x y).trans and_elim_r

@[rocq_alias saved_anything_combine_gives]
instance saved_anything_combine_gives (γ : GName) (dq1 dq2 : DFrac) (x y : F.ap (IProp GF)) :
    CombineSepGives (saved_anything_own γ dq1 x) (saved_anything_own γ dq2 y)
      iprop(⌜✓ (dq1 • dq2)⌝ ∧ internalEq x y) where
  combine_sep_gives :=
    (saved_anything_valid_2 γ dq1 dq2 x y).trans Persistent.persistent

@[rocq_alias saved_anything_combine_as]
instance saved_anything_combine_as (γ : GName) (dq1 dq2 : DFrac) (x y : F.ap (IProp GF)) :
    CombineSepAs (saved_anything_own γ dq1 x) (saved_anything_own γ dq2 y)
      (saved_anything_own γ (dq1 • dq2) x) where
  combine_sep_as := by
    iintro ⟨Hx, Hy⟩
    icombine Hx Hy gives ⟨-, #H⟩
    irewrite [← H] at Hy
    unfold saved_anything_own
    iapply (equiv_iff.mp (iOwn_ne.eqv (DFracAgree.mk_op (d₁ := dq1) (d₂ := dq2) (a := x)))).mpr
    iapply iOwn_op.mpr
    isplitl [Hx] <;> iassumption

/-! ### Make an element read-only -/

@[rocq_alias saved_anything_persist]
theorem saved_anything_persist (γ : GName) (dq : DFrac) (x : F.ap (IProp GF)) :
    saved_anything_own γ dq x ⊢@{IProp GF} |==> saved_anything_own γ .discard x := by
  unfold saved_anything_own
  exact iOwn_update DFracAgree.persist

@[rocq_alias saved_anything_unpersist]
theorem saved_anything_unpersist (γ : GName) (x : F.ap (IProp GF)) :
    saved_anything_own γ .discard x ⊢@{IProp GF} |==> ∃ q, saved_anything_own γ (.own q) x := by
  unfold saved_anything_own
  refine (iOwn_updateP DFracAgree.unpersist).trans (BIUpdate.mono ?_)
  iintro ⟨%a', %hq, Ha⟩
  obtain ⟨q, rfl⟩ := hq
  iexists q
  iexact Ha

/-! ### Updates -/

@[rocq_alias saved_anything_update]
theorem saved_anything_update (y : F.ap (IProp GF)) (γ : GName) (x : F.ap (IProp GF)) :
    saved_anything_own γ (.own 1) x ⊢@{IProp GF} |==> saved_anything_own γ (.own 1) y := by
  unfold saved_anything_own
  exact iOwn_update (Update.exclusive ⟨DFrac.valid_own_one, toAgree_valid⟩)

@[rocq_alias saved_anything_update_2]
theorem saved_anything_update_2 (y : F.ap (IProp GF)) (γ : GName) (q1 q2 : Qp)
    (x1 x2 : F.ap (IProp GF)) (Hq : q1 + q2 = 1) :
    saved_anything_own γ (.own q1) x1 ∗ saved_anything_own γ (.own q2) x2 ⊢@{IProp GF} |==>
      (saved_anything_own γ (.own q1) y ∗ saved_anything_own γ (.own q2) y) := by
  unfold saved_anything_own
  have hupd : DFracAgree.mk (.own q1) x1 • DFracAgree.mk (.own q2) x2 ~~>
      DFracAgree.mk (.own q1) y • DFracAgree.mk (.own q2) y :=
    DFracAgree.update₂ (show DFrac.own q1 • DFrac.own q2 = DFrac.own 1 from congrArg DFrac.own Hq)
  refine (iOwn_update_op hupd).trans (BIUpdate.mono ?_)
  exact iOwn_op.mp

@[rocq_alias saved_anything_update_halves]
theorem saved_anything_update_halves (y : F.ap (IProp GF)) (γ : GName)
    (x1 x2 : F.ap (IProp GF)) :
    saved_anything_own γ (.own (Qp.half 1)) x1 ∗ saved_anything_own γ (.own (Qp.half 1)) x2
      ⊢@{IProp GF} |==>
        (saved_anything_own γ (.own (Qp.half 1)) y ∗ saved_anything_own γ (.own (Qp.half 1)) y) :=
  saved_anything_update_2 y γ (Qp.half 1) (Qp.half 1) x1 x2 (Qp.half_add_half 1)

end saved_anything

/-! ## Saved propositions -/

abbrev SavedPropG (GF : BundledGFunctors) := SavedAnythingG GF (LaterOF IdOF)

@[rocq_alias saved_prop_own]
def saved_prop_own {GF : BundledGFunctors} [SavedPropG GF] (γ : GName) (dq : DFrac) (P : IProp GF) :
    IProp GF :=
  saved_anything_own (F := LaterOF IdOF) γ dq (Later.next P)

section saved_prop

variable {GF : BundledGFunctors} [SavedPropG GF]

@[rocq_alias saved_prop_own_contractive]
instance saved_prop_own_contractive (γ : GName) (dq : DFrac) :
    Contractive (saved_prop_own (GF := GF) γ dq) :=
  ⟨fun {_ _ _} h => saved_anything_ne γ dq |>.ne (NextContractive.distLater_dist h)⟩

@[rocq_alias saved_prop_discarded_persistent]
instance saved_prop_discarded_persistent (γ : GName) (P : IProp GF) :
    Persistent (saved_prop_own γ .discard P) := by
  unfold saved_prop_own
  infer_instance

@[rocq_alias saved_prop_fractional]
instance saved_prop_fractional (γ : GName) (P : IProp GF) :
    Fractional (fun q : Qp => saved_prop_own γ (.own q) P) := by
  unfold saved_prop_own
  infer_instance

@[rocq_alias saved_prop_as_fractional]
instance saved_prop_as_fractional (γ : GName) (P : IProp GF) (q : Qp) :
    AsFractional (saved_prop_own γ (.own q) P) (fun q => saved_prop_own γ (.own q) P) q where
  as_fractional := .rfl
  as_fractional_fractional := saved_prop_fractional γ P

@[rocq_alias saved_prop_alloc_strong]
theorem saved_prop_alloc_strong (I : GName → Prop) (P : IProp GF) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜I γ⌝ ∗ saved_prop_own γ dq P :=
  saved_anything_alloc_strong _ I dq Hdq HI

@[rocq_alias saved_prop_alloc_cofinite]
theorem saved_prop_alloc_cofinite (G : List GName) (P : IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prop_own γ dq P :=
  saved_anything_alloc_cofinite _ G dq Hdq

@[rocq_alias saved_prop_alloc]
theorem saved_prop_alloc (P : IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, saved_prop_own γ dq P :=
  saved_anything_alloc _ dq Hdq

@[rocq_alias saved_prop_valid]
theorem saved_prop_valid (γ : GName) (dq : DFrac) (P : IProp GF) :
    saved_prop_own γ dq P ⊢@{IProp GF} ⌜✓ dq⌝ :=
  saved_anything_valid γ dq _

@[rocq_alias saved_prop_valid_2]
theorem saved_prop_valid_2 (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    saved_prop_own γ dq1 P ∗ saved_prop_own γ dq2 Q ⊢@{IProp GF}
      ⌜✓ (dq1 • dq2)⌝ ∧ ▷ internalEq P Q :=
  (saved_anything_valid_2 (F := LaterOF IdOF) γ dq1 dq2 (Later.next P) (Later.next Q)).trans
    (and_mono_right (later_equivI P Q).mp)

@[rocq_alias saved_prop_agree]
theorem saved_prop_agree (γ : GName) (dq1 dq2 : DFrac) (P Q : IProp GF) :
    saved_prop_own γ dq1 P ∗ saved_prop_own γ dq2 Q ⊢@{IProp GF} ▷ internalEq P Q :=
  (saved_prop_valid_2 γ dq1 dq2 P Q).trans and_elim_r

@[rocq_alias saved_prop_persist]
theorem saved_prop_persist (γ : GName) (dq : DFrac) (P : IProp GF) :
    saved_prop_own γ dq P ⊢@{IProp GF} |==> saved_prop_own γ .discard P :=
  saved_anything_persist γ dq _

@[rocq_alias saved_prop_unpersist]
theorem saved_prop_unpersist (γ : GName) (P : IProp GF) :
    saved_prop_own γ .discard P ⊢@{IProp GF} |==> ∃ q, saved_prop_own γ (.own q) P :=
  saved_anything_unpersist γ _

@[rocq_alias saved_prop_update]
theorem saved_prop_update (Q : IProp GF) (γ : GName) (P : IProp GF) :
    saved_prop_own γ (.own 1) P ⊢@{IProp GF} |==> saved_prop_own γ (.own 1) Q :=
  saved_anything_update _ γ _

@[rocq_alias saved_prop_update_2]
theorem saved_prop_update_2 (Q : IProp GF) (γ : GName) (q1 q2 : Qp) (P1 P2 : IProp GF)
    (Hq : q1 + q2 = 1) :
    saved_prop_own γ (.own q1) P1 ∗ saved_prop_own γ (.own q2) P2 ⊢@{IProp GF} |==>
      (saved_prop_own γ (.own q1) Q ∗ saved_prop_own γ (.own q2) Q) :=
  saved_anything_update_2 _ γ q1 q2 _ _ Hq

@[rocq_alias saved_prop_update_halves]
theorem saved_prop_update_halves (Q : IProp GF) (γ : GName) (P1 P2 : IProp GF) :
    saved_prop_own γ (.own (Qp.half 1)) P1 ∗ saved_prop_own γ (.own (Qp.half 1)) P2
      ⊢@{IProp GF} |==>
        (saved_prop_own γ (.own (Qp.half 1)) Q ∗ saved_prop_own γ (.own (Qp.half 1)) Q) :=
  saved_anything_update_halves _ γ _ _

end saved_prop

/-! ## Saved predicates -/

abbrev SavedPredG (GF : BundledGFunctors) (A : Type _) :=
  SavedAnythingG GF (DiscreteFunOF (fun _ : A => LaterOF IdOF))

@[rocq_alias saved_pred_own]
def saved_pred_own {GF : BundledGFunctors} {A : Type _} [SavedPredG GF A]
    (γ : GName) (dq : DFrac) (Φ : A → IProp GF) : IProp GF :=
  saved_anything_own (F := DiscreteFunOF (fun _ : A => LaterOF IdOF)) γ dq
    (fun a => Later.next (Φ a))

section saved_pred

variable {GF : BundledGFunctors} {A : Type _} [SavedPredG GF A]

@[rocq_alias saved_pred_own_contractive]
instance saved_pred_own_contractive (γ : GName) (dq : DFrac) :
    Contractive (saved_pred_own (GF := GF) (A := A) γ dq) :=
  ⟨fun {_ _ _} h => saved_anything_ne γ dq |>.ne
    (fun a => NextContractive.distLater_dist (fun m hm => h m hm a))⟩

@[rocq_alias saved_pred_discarded_persistent]
instance saved_pred_discarded_persistent (γ : GName) (Φ : A → IProp GF) :
    Persistent (saved_pred_own γ .discard Φ) := by
  unfold saved_pred_own
  infer_instance

@[rocq_alias saved_pred_fractional]
instance saved_pred_fractional (γ : GName) (Φ : A → IProp GF) :
    Fractional (fun q : Qp => saved_pred_own γ (.own q) Φ) := by
  unfold saved_pred_own
  infer_instance

@[rocq_alias saved_pred_as_fractional]
instance saved_pred_as_fractional (γ : GName) (Φ : A → IProp GF) (q : Qp) :
    AsFractional (saved_pred_own γ (.own q) Φ) (fun q => saved_pred_own γ (.own q) Φ) q where
  as_fractional := .rfl
  as_fractional_fractional := saved_pred_fractional γ Φ

@[rocq_alias saved_pred_alloc_strong]
theorem saved_pred_alloc_strong (I : GName → Prop) (Φ : A → IProp GF) (dq : DFrac)
    (Hdq : ✓ dq) (HI : PredInfinite I) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ dq Φ :=
  saved_anything_alloc_strong _ I dq Hdq HI

@[rocq_alias saved_pred_alloc_cofinite]
theorem saved_pred_alloc_cofinite (G : List GName) (Φ : A → IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ dq Φ :=
  saved_anything_alloc_cofinite _ G dq Hdq

@[rocq_alias saved_pred_alloc]
theorem saved_pred_alloc (Φ : A → IProp GF) (dq : DFrac) (Hdq : ✓ dq) :
    ⊢@{IProp GF} |==> ∃ γ, saved_pred_own γ dq Φ :=
  saved_anything_alloc _ dq Hdq

@[rocq_alias saved_pred_valid]
theorem saved_pred_valid (γ : GName) (dq : DFrac) (Φ : A → IProp GF) :
    saved_pred_own γ dq Φ ⊢@{IProp GF} ⌜✓ dq⌝ :=
  saved_anything_valid γ dq _

@[rocq_alias saved_pred_valid_2]
theorem saved_pred_valid_2 (γ : GName) (dq1 dq2 : DFrac) (Φ Ψ : A → IProp GF) (x : A) :
    saved_pred_own γ dq1 Φ ∗ saved_pred_own γ dq2 Ψ ⊢@{IProp GF}
      ⌜✓ (dq1 • dq2)⌝ ∧ ▷ internalEq (Φ x) (Ψ x) := by
  unfold saved_pred_own
  refine (saved_anything_valid_2 (F := DiscreteFunOF (fun _ : A => LaterOF IdOF))
    γ dq1 dq2 _ _).trans (and_mono_right ?_)
  exact ((discreteFun_equivI _ _).mp.trans (forall_elim x)).trans (later_equivI (Φ x) (Ψ x)).mp

@[rocq_alias saved_pred_agree]
theorem saved_pred_agree (γ : GName) (dq1 dq2 : DFrac) (Φ Ψ : A → IProp GF) (x : A) :
    saved_pred_own γ dq1 Φ ∗ saved_pred_own γ dq2 Ψ ⊢@{IProp GF} ▷ internalEq (Φ x) (Ψ x) :=
  (saved_pred_valid_2 γ dq1 dq2 Φ Ψ x).trans and_elim_r

@[rocq_alias saved_pred_persist]
theorem saved_pred_persist (γ : GName) (dq : DFrac) (Φ : A → IProp GF) :
    saved_pred_own γ dq Φ ⊢@{IProp GF} |==> saved_pred_own γ .discard Φ :=
  saved_anything_persist γ dq _

@[rocq_alias saved_pred_unpersist]
theorem saved_pred_unpersist (γ : GName) (Φ : A → IProp GF) :
    saved_pred_own γ .discard Φ ⊢@{IProp GF} |==> ∃ q, saved_pred_own γ (.own q) Φ :=
  saved_anything_unpersist γ _

@[rocq_alias saved_pred_update]
theorem saved_pred_update (Ψ : A → IProp GF) (γ : GName) (Φ : A → IProp GF) :
    saved_pred_own γ (.own 1) Φ ⊢@{IProp GF} |==> saved_pred_own γ (.own 1) Ψ :=
  saved_anything_update _ γ _

@[rocq_alias saved_pred_update_2]
theorem saved_pred_update_2 (Ψ : A → IProp GF) (γ : GName) (q1 q2 : Qp) (Φ1 Φ2 : A → IProp GF)
    (Hq : q1 + q2 = 1) :
    saved_pred_own γ (.own q1) Φ1 ∗ saved_pred_own γ (.own q2) Φ2 ⊢@{IProp GF} |==>
      (saved_pred_own γ (.own q1) Ψ ∗ saved_pred_own γ (.own q2) Ψ) :=
  saved_anything_update_2 _ γ q1 q2 _ _ Hq

@[rocq_alias saved_pred_update_halves]
theorem saved_pred_update_halves (Ψ : A → IProp GF) (γ : GName) (Φ1 Φ2 : A → IProp GF) :
    saved_pred_own γ (.own (Qp.half 1)) Φ1 ∗ saved_pred_own γ (.own (Qp.half 1)) Φ2
      ⊢@{IProp GF} |==>
        (saved_pred_own γ (.own (Qp.half 1)) Ψ ∗ saved_pred_own γ (.own (Qp.half 1)) Ψ) :=
  saved_anything_update_halves _ γ _ _

end saved_pred

end Iris
