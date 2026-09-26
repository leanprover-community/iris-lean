/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.Lib.WSat
public import Iris.Instances.UPred.Transfinite
public import Iris.BI.Transfinite
public import Iris.ProofMode
public import Iris.BI.Lib.LogicalStep

/-! # Fancy updates over arbitrary step-indices (Transfinite Iris)

This file ports `theories/base_logic/lib/fancy_updates.v` of Transfinite Iris: the fancy update
modality `|={E1,E2}=> P := wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P)`, defined over any type of
step-indices, and the satisfiability of propositions relative to world satisfaction
(`satisfiable_at`).

Unlike `Iris.Instances.Lib.FUpd`, which follows current Iris and uses later credits (and is at
`SI = Nat`), these fancy updates do not use later credits, as in Transfinite Iris. The `BIFUpdate`
instance is scoped to the namespace `Iris.Transfinite`.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris OFE COFE BI Std.LawfulSet

variable {GF : BundledGFunctors} [W : WsatGS GF]

/-- The fancy update of Transfinite Iris (Rocq: `uPred_fupd_def`). -/
def uPred_fupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P))

instance {E1 E2 : CoPset} : NonExpansive (uPred_fupd (GF := GF) E1 E2) where
  ne {_ _ _} h := by
    simp only [uPred_fupd]
    refine wand_ne.ne .rfl ?_
    refine bupd_ne.ne ?_
    refine except0_ne.ne ?_
    exact sep_ne.ne .rfl (sep_ne.ne .rfl h)

/-- Rocq: `uPred_bi_fupd`. -/
scoped instance uPred_bi_fupd : BIFUpdate (IProp GF) where
  fupd := uPred_fupd
  subset Hsub := by
    simp only [uPred_fupd]
    iintro ⟨$, HE⟩
    rw [diff_subset_decomp Hsub]
    ihave ⟨HE1, $⟩ := (ownE_op (disjoint_symm disjoint_diff_right)).mp $$ HE
    imodintro
    imodintro
    iintro ⟨$, HE⟩
    imodintro
    imodintro
    ihave $ := (ownE_op (disjoint_symm disjoint_diff_right)).mpr $$ [$]
  except0 {E1 E2 P} := by
    simp only [uPred_fupd]
    iintro H Hwe
    imod H
    iapply H $$ Hwe
  mono H := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    iapply bupd_mono (except0_mono (sep_mono_right (sep_mono_right H)))
    iapply Hupd $$ HwE
  trans {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro Hupd HwE
    imod Hupd $$ HwE with H
    imod H with ⟨Hw, HE, Hupd⟩
    iapply Hupd $$ [$Hw $HE]
  mask_frame_right_strong {E1 E2 Ef P} Hdisj := by
    simp only [uPred_fupd]
    iintro Hupd ⟨Hwsat, HE⟩
    ihave ⟨HE1, HEf⟩ := ownE_op Hdisj $$ HE
    imod Hupd $$ [Hwsat HE1] with H
    · iframe
    imod H with ⟨Hw, HE2, HP⟩
    ihave ⟨%Hdisj', HE⟩ := (ownE_op_iff (E1 := E2) (E2 := Ef)).mpr $$ [HE2 HEf]
    · iframe
    imodintro
    imodintro
    isplitl [Hw]
    · iassumption
    isplitl [HE]
    · iassumption
    iapply HP
    ipureintro
    exact Hdisj'
  frame_right {_ _ _ _} := by
    simp only [uPred_fupd]
    iintro ⟨Hupd, HR⟩ HwE
    imod Hupd $$ HwE with H
    imod H with ⟨Hw, HE, HP⟩
    imodintro
    imodintro
    iframe

/-- Rocq: `uPred_bi_bupd_fupd`. -/
scoped instance : BIUpdateFUpdate (IProp GF) where
  fupd_of_bupd {_ _} := by
    iintro H
    simp only [FUpd.fupd, uPred_fupd]
    iintro ⟨$, $⟩
    imod H
    imodintro
    imodintro
    iassumption

/-- Rocq: `uPred_bi_fupd_plainly`. -/
scoped instance uPred_bi_fupd_sbi : BIFUpdateSbi (IProp GF) where
  fupd_keep_siPure E' Pi R := by
    simp only [FUpd.fupd, uPred_fupd]
    iintro H ⟨Hw, HE⟩
    ihave #HP : ◇ <si_pure> Pi $$ [H Hw HE]
    · icases H with ⟨H, -⟩
      iapply bupd_elim
      imod H $$ [$Hw $HE] with H
      imod H with ⟨-, -, HP⟩
      imodintro
      imodintro
      iexact HP
    imod HP
    icases H with ⟨-, H⟩
    iapply H $$ HP [$Hw $HE]
  fupd_siPure_later E Pi := by
    simp only [FUpd.fupd, uPred_fupd]
    iintro H ⟨Hw, HE⟩
    ihave #HP : ▷ ◇ <si_pure> Pi $$ [H Hw HE]
    · inext
      iapply bupd_elim
      imod H $$ [$Hw $HE] with H
      imod H with ⟨-, -, HP⟩
      imodintro
      imodintro
      iexact HP
    imodintro
    imodintro
    iframe
    iexact HP
  fupd_siPure_sForall_2 E Ψi := by
    simp only [FUpd.fupd, uPred_fupd]
    iintro H ⟨Hw, HE⟩
    ihave #HP : ◇ <si_pure> (sForall Ψi) $$ [H Hw HE]
    · iapply except0_mono (siPure_sForall_mpr (Ψi := Ψi))
      iapply except0_forall.2
      iintro %q
      iapply except0_mono pure_imp_forall.mpr
      iapply except0_forall.2
      iintro %hq
      iapply bupd_elim
      imod H $$ %q %hq [$Hw $HE] with H
      imod H with ⟨-, -, HP⟩
      imodintro
      imodintro
      iexact HP
    imod HP
    imodintro
    imodintro
    iframe
    iexact HP

theorem fupd_eq (E1 E2 : CoPset) (P : IProp GF) :
    iprop(|={E1,E2}=> P) = iprop(wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P)) := rfl

/-! ## Satisfiability relative to world satisfaction -/

/-- `P` is satisfiable together with world satisfaction and the enabled invariants `E`
(Rocq: `satisfiable_at`). -/
@[rocq_alias satisfiable_at]
def satisfiableAt (E : CoPset) (P : IProp GF) : Prop :=
  UPred.satisfiable iprop(wsat ∗ ownE E ∗ P)

/-- Rocq: `satisfiable_at_fupd`. -/
@[rocq_alias satisfiable_at_fupd]
theorem satisfiableAt_fupd {E1 E2 : CoPset} {P : IProp GF}
    (h : satisfiableAt E1 iprop(|={E1,E2}=> P)) : satisfiableAt E2 P := by
  refine UPred.satisfiable_later (UPred.satisfiable_bupd (UPred.satisfiable_mono h ?_))
  rw [fupd_eq]
  iintro ⟨W, O, H⟩
  imod H $$ [W O] with H
  · iframe
  imodintro
  iapply except0_into_later
  iexact H

/-- Rocq: `satisfiable_at_mono`. -/
@[rocq_alias satisfiable_at_mono]
theorem satisfiableAt_mono {E : CoPset} {P Q : IProp GF} (h : satisfiableAt E P) (hPQ : P ⊢ Q) :
    satisfiableAt E Q :=
  UPred.satisfiable_mono h (sep_mono_right (sep_mono_right hPQ))

/-- Rocq: `satisfiable_at_elim`. -/
@[rocq_alias satisfiable_at_elim]
theorem satisfiableAt_elim {E : CoPset} {P : IProp GF} [Plain P] (h : satisfiableAt E P) :
    iprop(True ⊢ P) :=
  UPred.satisfiable_elim (UPred.satisfiable_mono h (sep_elim_right.trans sep_elim_right))

/-- Rocq: `satisfiable_at_later`. -/
@[rocq_alias satisfiable_at_later]
theorem satisfiableAt_later {E : CoPset} {P : IProp GF} (h : satisfiableAt E iprop(▷ P)) :
    satisfiableAt E P := by
  refine UPred.satisfiable_later (UPred.satisfiable_mono h ?_)
  iintro ⟨W, O, P⟩
  inext
  iframe

/-- Rocq: `satisfiable_at_exists` (the existential property, for large step-indices). -/
@[rocq_alias satisfiable_at_exists]
theorem satisfiableAt_exists [SIdxLarge.{v} SI] {E : CoPset} {X : Type v} {P : X → IProp GF}
    (h : satisfiableAt E iprop(∃ x, P x)) : ∃ x, satisfiableAt E (P x) := by
  refine UPred.satisfiable_exists (UPred.satisfiable_mono h ?_)
  iintro ⟨W, O, %x, P⟩
  iexists x
  iframe

/-- Rocq: `satisfiable_at_pure`. -/
@[rocq_alias satisfiable_at_pure]
theorem satisfiableAt_pure {E : CoPset} {φ : Prop} (h : satisfiableAt (GF := GF) E iprop(⌜φ⌝)) :
    φ :=
  UPred.pure_soundness (satisfiableAt_elim h)

end Iris.Transfinite

namespace Iris.Transfinite

open Iris OFE COFE BI Std.LawfulSet

variable {GF : BundledGFunctors}

/-- Rocq: `fupd_plain_soundness`. -/
@[rocq_alias fupd_plain_soundness]
theorem fupd_plain_soundness [WsatGpreS GF] (E1 E2 : CoPset) {P : IProp GF} [Plain P]
    (h : ∀ (_ : WsatGS GF), ⊢ |={E1,E2}=> P) : ⊢ P := by
  refine true_emp.mpr.trans (UPred.later_soundness (true_emp.mp.trans ?_))
  iapply bupd_elim
  imod wsat_alloc (GF := GF) with ⟨%W, Hw, HE⟩
  have hW : ⊢ iprop(wsat (W := W) ∗ ownE (W := W) E1 ==∗
      ◇ (wsat (W := W) ∗ ownE (W := W) E2 ∗ P)) := h W
  rw [← subset_union_diff (s₁ := E1) (s₂ := ⊤) (fun _ _ => CoPset.mem_full)]
  icases ownE_op (W := W) disjoint_diff_right $$ HE with ⟨HE, -⟩
  imod hW $$ [$Hw $HE] with H
  imodintro
  imod H with ⟨-, -, HP⟩
  iintro -
  inext
  iexact HP

/-- Soundness of iterated logical steps for pure propositions (Rocq: `lstep_fupd_soundness`). -/
@[rocq_alias lstep_fupd_soundness]
theorem lstep_fupd_soundness [SIdxTransfinite SI] [WsatGpreS GF] (φ : Prop) (n : Nat)
    (h : ∀ (_ : WsatGS GF), ⊢ Nat.repeat (gstep ∅ ⊤ ⊤) n iprop(⌜φ⌝ : IProp GF)) : φ :=
  UPred.pure_soundness (M := IResUR GF) <| UPred.big_laterN_soundness n _ <|
    true_emp.mp.trans <| fupd_plain_soundness ⊤ ⊤ fun W => (h W).trans (lstep_fupdN_plain n)

end Iris.Transfinite
