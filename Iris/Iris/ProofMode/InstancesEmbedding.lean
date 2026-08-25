/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances

@[expose] public section

namespace Iris.ProofMode
open BI

section BiEmbed

variable [bi1 : BI PROP1] [bi2 : BI PROP2] [BiEmbed PROP1 PROP2]

/-! ### AsEmpValid -/

set_option synthInstance.checkSynthOrder false in
@[rocq_alias as_emp_valid_embed]
instance (priority := low) asEmpValid_embed d φ (P : PROP1)
    [inst : AsEmpValid0 d φ .in PROP1 bi1 .out P] :
    AsEmpValid d φ .in PROP2 bi2 (embed P) where
  as_emp_valid := by
    constructor
    · exact fun hd hφ => (embed_emp_valid P).mpr <| inst.as_emp_valid_0.as_emp_valid.left hd hφ
    · exact fun hd hP => inst.as_emp_valid_0.as_emp_valid.right hd <| (embed_emp_valid P).mp hP

/-! ### FromModal -/

@[rocq_alias from_modal_embed]
instance fromModal_embed io (P : PROP1) :
    FromModal (PROP1 := PROP1) io (modality_embed : Modality PROP1 PROP2) True
      iprop(⎡P⎤ : PROP2) iprop(⎡P⎤) P where
  from_modal _ := .rfl

@[ipm_backtrack, rocq_alias from_modal_id_embed]
instance (priority := low) fromModal_id_embed {α} φ io (sel : α)
    (P Q : PROP1) [inst : FromModal .in modality_id φ sel P Q] :
    FromModal (PROP1 := PROP2) io modality_id φ sel iprop(⎡P⎤) iprop(⎡Q⎤) where
  from_modal h := embed_mono <| inst.from_modal h

@[ipm_backtrack, rocq_alias from_modal_affinely_embed]
instance (priority := low) fromModal_affinely_embed {α} φ io (sel : α)
    (P Q : PROP1) [inst : FromModal .in modality_affinely φ sel P Q] :
    FromModal (PROP1 := PROP2) io modality_affinely φ sel iprop(⎡P⎤) iprop(⎡Q⎤) where
  from_modal h := (embed_affinely_2 Q).trans (embed_mono <| inst.from_modal h)

@[ipm_backtrack, rocq_alias from_modal_persistently_embed]
instance (priority := low) fromModal_persistently_embed {α} φ io (sel : α)
    (P Q : PROP1) [inst : FromModal .in modality_persistently φ sel P Q] :
    FromModal (PROP1 := PROP2) io modality_persistently φ sel iprop(⎡P⎤) iprop(⎡Q⎤) where
  from_modal h := (embed_persistently Q).mpr.trans (embed_mono <| inst.from_modal h)

@[ipm_backtrack, rocq_alias from_modal_intuitionistically_embed]
instance (priority := low) fromModal_intuitionistically_embed {α} φ io (sel : α)
    (P Q : PROP1) [inst : FromModal .in modality_intuitionistically φ sel P Q] :
    FromModal (PROP1 := PROP2) io modality_intuitionistically φ sel iprop(⎡P⎤) iprop(⎡Q⎤) where
  from_modal h := (embed_intuitionistically_2 Q).trans (embed_mono <| inst.from_modal h)

/-! ### IntoEmbed -/

@[rocq_alias into_embed_embed]
instance intoEmbed_embed (P : PROP1) : IntoEmbed (PROP1 := PROP1) (PROP2 := PROP2) iprop(⎡P⎤) P where
  into_embed := .rfl

@[rocq_alias into_embed_affinely]
instance intoEmbed_affinely [BIUpdate PROP1] [BIUpdate PROP2]
    [BiEmbedBUpd PROP1 PROP2] (P : PROP2) (Q : PROP1) [inst : IntoEmbed P Q] :
    IntoEmbed iprop(<affine> P) iprop(<affine> Q) where
  into_embed := (affinely_mono inst.into_embed).trans <| embed_affinely_2 Q

/-! ### IntoPure -/

@[rocq_alias into_pure_embed]
instance intoPure_embed (P : PROP1) φ [inst : IntoPure P φ] :
    IntoPure (PROP := PROP2) iprop(⎡P⎤) φ where
  into_pure := (embed_mono inst.into_pure).trans (embed_pure φ).mp

/-! ### FromPure -/

@[rocq_alias from_pure_embed]
instance fromPure_embed a (P : PROP1) ioφ φ [inst : FromPure a P ioφ φ] :
    FromPure (PROP := PROP2) a iprop(⎡P⎤) ioφ φ where
  from_pure := calc
    _ ⊢ <affine>?a ⎡(⌜φ⌝ : PROP1)⎤ := affinelyIf_mono (embed_pure φ).mpr
    _ ⊢ ⎡<affine>?a ⌜φ⌝⎤           := embed_affinely_if_2 _ a
    _ ⊢ ⎡P⎤                        := embed_mono inst.from_pure

/-! ### IntoPersistently -/

@[rocq_alias into_persistent_embed]
instance intoPersistently_embed p (P Q : PROP1) [inst : IntoPersistently p P Q] :
    IntoPersistently (PROP := PROP2) p iprop(⎡P⎤) iprop(⎡Q⎤) where
  into_persistently := calc
    _ ⊢ ⎡<pers>?p P⎤ := (embed_persistently_if P p).mpr
    _ ⊢ ⎡<pers> Q⎤   := embed_mono inst.into_persistently
    _ ⊢ <pers> ⎡Q⎤   := (BiEmbed.persistently Q).mp

/-! ### IntoWand -/

@[rocq_alias into_wand_embed]
instance intoWand_embed p q m (R P Q : PROP1) [inst : IntoWand p q R m P Q] :
    IntoWand (PROP := PROP2) p q iprop(⎡R⎤) m iprop(⎡P⎤) iprop(⎡Q⎤) where
  into_wand := calc
    _ ⊢ ⎡□?p R⎤        := embed_intuitionistically_if_2 R p
    _ ⊢ ⎡□?q P -∗ Q⎤   := embed_mono inst.into_wand
    _ ⊢ ⎡□?q P⎤ -∗ ⎡Q⎤ := (embed_wand iprop(□?q P) Q).mp
    _ ⊢ □?q ⎡P⎤ -∗ ⎡Q⎤ := wand_mono_left <| embed_intuitionistically_if_2 P q

/--
  When the wand `⎡R⎤` sits in the intuitionistic context, the result of wand
  elimination keeps the affine modality.
-/
@[rocq_alias into_wand_affine_embed_true]
instance (priority := low) intoWand_affine_embed_true q
    (P Q R : PROP1) [inst : IntoWand true q R (.matching s) P Q] :
    IntoWand (PROP := PROP2) true q iprop(⎡R⎤)
      (.matching s) iprop(<affine> ⎡P⎤) iprop(<affine> ⎡Q⎤) where
  into_wand := by
    refine (intuitionistically_intro_intuitionistically <|
      (embed_intuitionistically_2 R).trans (embed_mono inst.into_wand)).trans (wand_intro_left ?_)
    cases q
    · calc
        _ ⊢ <affine> ⎡P⎤ ∗ <affine> ⎡P -∗ Q⎤ := sep_mono_right affinely_of_intuitionistically
        _ ⊢ <affine> (⎡P⎤ ∗ ⎡P -∗ Q⎤)        := affinely_sep_mpr
        _ ⊢ <affine> ⎡P ∗ (P -∗ Q)⎤          := affinely_mono (embed_sep P iprop(P -∗ Q)).mpr
        _ ⊢ <affine> ⎡Q⎤                     := affinely_mono <| embed_mono wand_elim_right
    · calc
        _ ⊢ □ ⎡P⎤ ∗ □ ⎡□ P -∗ Q⎤ := sep_mono_left (intuitionistically_mono affinely_elim)
        _ ⊢ □ ⎡□ P⎤ ∗ □ ⎡□ P -∗ Q⎤ :=
              sep_mono_left (intuitionistically_intro_intuitionistically
                (embed_intuitionistically_2 P))
        _ ⊢ □ (⎡□ P⎤ ∗ ⎡□ P -∗ Q⎤) := intuitionistically_sep_mpr
        _ ⊢ □ ⎡□ P ∗ (□ P -∗ Q)⎤   :=
              intuitionistically_mono (embed_sep iprop(□ P) iprop(□ P -∗ Q)).mpr
        _ ⊢ □ ⎡Q⎤                  := intuitionistically_mono <| embed_mono wand_elim_right
        _ ⊢ <affine> ⎡Q⎤           := affinely_of_intuitionistically

@[rocq_alias into_wand_affine_embed_false]
instance (priority := low) intoWand_affine_embed_false q (P Q R : PROP1)
    [inst : IntoWand false q R (.matching .argument) iprop(<affine> P) Q] :
    IntoWand (PROP := PROP2) false q iprop(⎡R⎤) (.matching .argument)
      iprop(<affine> ⎡P⎤) iprop(⎡Q⎤) where
  into_wand := by
    calc
      _ ⊢ ⎡□?q (<affine> P) -∗ Q⎤   := embed_mono inst.into_wand
      _ ⊢ ⎡□?q (<affine> P)⎤ -∗ ⎡Q⎤ := (embed_wand iprop(□?q (<affine> P)) Q).mp
      _ ⊢ □?q (<affine> ⎡P⎤) -∗ ⎡Q⎤ := wand_mono_left ?_
    exact (intuitionisticallyIf_mono (embed_affinely_2 P)).trans
          (embed_intuitionistically_if_2 iprop(<affine> P) q)

/-! ### FromWand -/

@[rocq_alias from_wand_embed]
instance fromWand_embed io (P Q1 Q2 : PROP1) [inst : FromWand P io Q1 Q2] :
    FromWand (PROP := PROP2) iprop(⎡P⎤) io iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_wand := (embed_wand Q1 Q2).mpr.trans (embed_mono inst.from_wand)

/-! ### FromImp -/

@[rocq_alias from_impl_embed]
instance fromImp_embed (P Q1 Q2 : PROP1) [inst : FromImp P Q1 Q2] :
    FromImp (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_imp := (embed_impl Q1 Q2).mpr.trans (embed_mono inst.from_imp)

@[rocq_alias from_and_embed]
instance fromAnd_embed (P Q1 Q2 : PROP1) [inst : FromAnd P Q1 Q2] :
    FromAnd (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_and := (embed_and Q1 Q2).mpr.trans (embed_mono inst.from_and)

@[rocq_alias from_sep_embed]
instance fromSep_embed (P Q1 Q2 : PROP1) [inst : FromSep P Q1 Q2] :
    FromSep (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_sep := (embed_sep Q1 Q2).mpr.trans (embed_mono inst.from_sep)

/-! ### CombineSepAs -/

@[rocq_alias maybe_combine_sep_as_embed]
instance combineSepAs_embed (Q1 Q2 P : PROP1) [inst : CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(⎡Q1⎤ : PROP2) iprop(⎡Q2⎤) iprop(⎡P⎤) where
  combine_sep_as := (embed_sep Q1 Q2).mpr.trans (embed_mono inst.combine_sep_as)

/-! ### CombineSepGives -/

@[rocq_alias combine_sep_gives_embed]
instance combineSepGives_embed (Q1 Q2 P : PROP1) [inst : CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(⎡Q1⎤ : PROP2) iprop(⎡Q2⎤) iprop(⎡P⎤) where
  combine_sep_gives := calc
    _ ⊢ ⎡Q1 ∗ Q2⎤  := (embed_sep Q1 Q2).mpr
    _ ⊢ ⎡<pers> P⎤ := embed_mono inst.combine_sep_gives
    _ ⊢ <pers> ⎡P⎤ := (embed_persistently P).mp

/-! ### IntoAnd -/

@[rocq_alias into_and_embed]
instance intoAnd_embed p (P Q1 Q2 : PROP1) [inst : IntoAnd p P Q1 Q2] :
    IntoAnd (PROP := PROP2) p iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_and := by
    refine intuitionisticallyIf_intro_intuitionisticallyIf ?_
    calc
      _ ⊢ ⎡□?p P⎤         := embed_intuitionistically_if_2 P p
      _ ⊢ ⎡□?p (Q1 ∧ Q2)⎤ := embed_mono inst.into_and
      _ ⊢ ⎡Q1 ∧ Q2⎤       := embed_mono intuitionisticallyIf_elim
      _ ⊢ ⎡Q1⎤ ∧ ⎡Q2⎤     := (embed_and Q1 Q2).mp

/-! ### IntoSep -/

@[rocq_alias into_sep_embed]
instance intoSep_embed (P Q1 Q2 : PROP1) [inst : IntoSep P Q1 Q2] :
    IntoSep (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_sep := (embed_mono inst.into_sep).trans (embed_sep Q1 Q2).mp

/-! ### FromOr -/

@[rocq_alias from_or_embed]
instance fromOr_embed (P Q1 Q2 : PROP1) [inst : FromOr P Q1 Q2] :
    FromOr (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_or := (embed_or Q1 Q2).mpr.trans (embed_mono inst.from_or)

/-! ### IntoOr -/

@[rocq_alias into_or_embed]
instance intoOr_embed (P Q1 Q2 : PROP1) [inst : IntoOr P Q1 Q2] :
    IntoOr (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_or := (embed_mono inst.into_or).trans (embed_or Q1 Q2).mp

/-! ### FromExists -/

@[rocq_alias from_exist_embed]
instance fromExists_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [inst : FromExists P Φ] :
    FromExists (PROP := PROP2) iprop(⎡P⎤) (fun a => iprop(⎡Φ a⎤)) where
  from_exists := (embed_exist Φ).mpr.trans (embed_mono inst.from_exists)

/-! ### IntoExists -/

@[rocq_alias into_exist_embed]
instance intoExists_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [inst : IntoExists P Φ] :
    IntoExists (PROP := PROP2) iprop(⎡P⎤) (fun a => iprop(⎡Φ a⎤)) where
  into_exists := (embed_mono inst.into_exists).trans (embed_exist Φ).mp

/-! ### IntoForall -/

@[rocq_alias into_forall_embed]
instance intoForall_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [inst : IntoForall P Φ] :
    IntoForall (PROP := PROP2) iprop(⎡P⎤) (fun a => iprop(⎡Φ a⎤)) where
  into_forall := (embed_mono inst.into_forall).trans (embed_forall Φ).mp

/-! ### FromForall -/

@[rocq_alias from_forall_embed]
instance fromForall_embed {α : Sort _} (P : PROP1) (Ψ : α → PROP1) [inst : FromForall P Ψ] :
    FromForall (PROP := PROP2) iprop(⎡P⎤) (fun a => iprop(⎡Ψ a⎤)) where
  from_forall := (embed_forall Ψ).mpr.trans (embed_mono inst.from_forall)

/-! ### IntoInv -/

@[rocq_alias into_inv_embed]
instance intoInv_embed (P : PROP1) (N : Namespace) [IntoInv P N] :
    IntoInv (PROP := PROP2) iprop(⎡P⎤) N := {}

/-! ### IsExcept0 -/

@[rocq_alias is_except_0_embed]
instance isExcept0_embed [BiEmbedLater PROP1 PROP2] (P : PROP1)
    [inst : IsExcept0 P] : IsExcept0 (PROP := PROP2) iprop(⎡P⎤) where
  is_except0 := (embed_except_0 P).mpr.trans (embed_mono inst.is_except0)

/-! ### FromModal -/

@[ipm_backtrack, rocq_alias from_modal_later_embed]
instance fromModal_later_embed [BiEmbedLater PROP1 PROP2] {α} φ io (sel : α) n (P Q : PROP1)
    [inst : FromModal .in (modality_laterN n) φ sel P Q] :
    FromModal (PROP1 := PROP2) io (modality_laterN n) φ sel iprop(⎡P⎤) iprop(⎡Q⎤) where
  from_modal h := (embed_laterN n Q).mpr.trans (embed_mono <| inst.from_modal h)

/-! ### IntoExcept0 -/

@[rocq_alias into_except_0_embed]
instance intoExcept0_embed [BiEmbedLater PROP1 PROP2] (P Q : PROP1)
    [inst : IntoExcept0 P Q] :
    IntoExcept0 (PROP := PROP2) iprop(⎡P⎤) iprop(⎡Q⎤) where
  into_except0 := (embed_mono inst.into_except0).trans (embed_except_0 Q).mp

/-! ### IntoLater -/

@[rocq_alias into_later_embed]
instance intoLater_embed [BiEmbedLater PROP1 PROP2] (n : Nat) (P Q : PROP1) progress
    [inst : IntoLaterN (progress := true) (only_head := false) n P Q] :
    IntoLaterN (PROP := PROP2) progress (only_head := false) n iprop(⎡P⎤) iprop(⎡Q⎤) where
  into_laterN := (embed_mono inst.into_laterN).trans (embed_laterN n Q).mp

end BiEmbed

section SbiEmbed

variable [Sbi P1] [Sbi P2] [BiEmbed P1 P2] [BiEmbedSbi P1 P2]

@[ipm_backtrack, rocq_alias from_modal_plainly_embed]
instance (priority := low) fromModal_plainly_embed {α} φ io (sel : α)
    (P Q : P1) [inst : FromModal .in modality_plainly φ sel P Q] :
    FromModal io modality_plainly φ sel iprop(⎡P⎤ : P2) iprop(⎡Q⎤) where
  from_modal h := (embed_plainly Q).mpr.trans (embed_mono <| inst.from_modal h)

@[rocq_alias into_internal_eq_embed]
instance intoInternalEq_embed {A} [OFE A] (x y : A) (P : P1)
    [inst : IntoInternalEq P x y] : IntoInternalEq iprop(⎡P⎤ : P2) x y where
  into_internal_eq := (embed_mono inst.into_internal_eq).trans (embed_internal_eq x y).mp

end SbiEmbed

section BiEmbedBUpd
open BiEmbedBUpd

variable [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
  [BIUpdate PROP1] [BIUpdate PROP2] [BiEmbedBUpd PROP1 PROP2]

@[rocq_alias elim_modal_embed_bupd_goal]
instance elimModal_embed_bupd_goal φ p io p' (P P' : PROP2) (Q Q' : PROP1)
    [ElimModal φ p io p' P P' iprop(|==> ⎡Q⎤) iprop(|==> ⎡Q'⎤)] :
    ElimModal φ p io p' P P' iprop(⎡|==> Q⎤) iprop(⎡|==> Q'⎤) where
  elim_modal h := calc
    _ ⊢ □?p P ∗ (□?p' P' ==∗ ⎡Q'⎤) := sep_mono_right <| wand_mono_right (embed_bupd Q').mp
    _ ⊢ |==> ⎡Q⎤                   := elim_modal h
    _ ⊢ ⎡|==> Q⎤                   := (embed_bupd Q).mpr

@[rocq_alias elim_modal_embed_bupd_hyp]
instance elimModal_embed_bupd_hyp φ p io p' (P : PROP1) (P' Q Q' : PROP2)
    [ElimModal φ p io p' iprop(|==> ⎡P⎤) P' Q Q'] :
    ElimModal φ p io p' iprop(⎡|==> P⎤) P' Q Q' where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_congr <| embed_bupd P).mp).trans (elim_modal h)

@[rocq_alias add_modal_embed_bupd_goal]
instance addModal_embed_bupd_goal (P P' : PROP2) (Q : PROP1)
    [AddModal P P' iprop(|==> ⎡Q⎤)] : AddModal P P' iprop(⎡|==> Q⎤) where
  add_modal := calc
    _ ⊢ P ∗ (P' ==∗ ⎡Q⎤) := sep_mono_right <| wand_mono_right (embed_bupd Q).mp
    _ ⊢ |==> ⎡Q⎤         := add_modal
    _ ⊢ ⎡|==> Q⎤         := (embed_bupd Q).mpr

end BiEmbedBUpd

section BiEmbedFUpd
open BiEmbedFUpd

variable [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2] [BIFUpdate PROP1] [BIFUpdate PROP2] [BiEmbedFUpd PROP1 PROP2]

@[rocq_alias elim_modal_embed_fupd_goal]
instance elimModal_embed_fupd_goal φ p io p'
    (E1 E2 E3 : CoPset) (P P' : PROP2) (Q Q' : PROP1)
    [ElimModal φ p io p' P P' iprop(|={E1,E3}=> ⎡Q⎤) iprop(|={E2,E3}=> ⎡Q'⎤)] :
    ElimModal φ p io p' P P' iprop(⎡|={E1,E3}=> Q⎤) iprop(⎡|={E2,E3}=> Q'⎤) where
  elim_modal h := calc
    _ ⊢ □?p P ∗ (□?p' P' ={E2,E3}=∗ ⎡Q'⎤) := sep_mono_right <| wand_mono_right (embed_fupd ..).mp
    _ ⊢ |={E1, E3}=> ⎡Q⎤                  := elim_modal h
    _ ⊢ ⎡|={E1, E3}=> Q⎤                  := (embed_fupd E1 E3 Q).mpr

@[rocq_alias elim_modal_embed_fupd_hyp]
instance elimModal_embed_fupd_hyp φ p io p'
    (E1 E2 : CoPset) (P : PROP1) (P' Q Q' : PROP2)
    [ElimModal φ p io p' iprop(|={E1,E2}=> ⎡P⎤) P' Q Q'] :
    ElimModal φ p io p' iprop(⎡|={E1,E2}=> P⎤) P' Q Q' where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_congr <| embed_fupd E1 E2 P).mp).trans (elim_modal h)

@[rocq_alias add_modal_embed_fupd_goal]
instance addModal_embed_fupd_goal (E1 E2 : CoPset) (P P' : PROP2) (Q : PROP1)
    [AddModal P P' iprop(|={E1,E2}=> ⎡Q⎤)] : AddModal P P' iprop(⎡|={E1,E2}=> Q⎤) where
  add_modal := calc
    _ ⊢ P ∗ (P' ={E1,E2}=∗ ⎡Q⎤) := sep_mono_right <| wand_mono_right (embed_fupd E1 E2 Q).mp
    _ ⊢ |={E1, E2}=> ⎡Q⎤        := add_modal
    _ ⊢ ⎡|={E1, E2}=> Q⎤        := (embed_fupd E1 E2 Q).mpr

end BiEmbedFUpd
