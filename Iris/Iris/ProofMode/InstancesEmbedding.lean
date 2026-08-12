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

section

variable {PROP1 PROP2 : Type u} [bi1 : BI PROP1] [bi2 : BI PROP2] [biEmbed : BiEmbed PROP1 PROP2]

/-! ### AsEmpValid -/

set_option synthInstance.checkSynthOrder false in
@[rocq_alias as_emp_valid_embed]
instance (priority := low) asEmpValid_embed d φ io (P : PROP1)
    [inst : AsEmpValid0 d φ io PROP1 bi1 P] :
    AsEmpValid d φ io PROP2 bi2 (embed P) where
  as_emp_valid := by
    constructor
    · exact fun hd hφ => (embed_emp_valid P).mpr <| inst.as_emp_valid_0.as_emp_valid.left hd hφ
    · exact fun hd hP => inst.as_emp_valid_0.as_emp_valid.right hd <| (embed_emp_valid P).mp hP

/-! ### FromModal -/

@[rocq_alias from_modal_embed]
instance fromModal_embed (P : PROP1) :
    FromModal True (modality_embed (PROP2 := PROP2)) iprop(⎡P⎤ : PROP2) iprop(⎡P⎤) P where
  from_modal _ := .rfl

/-! ### IntoEmbed -/

@[rocq_alias into_embed_embed]
instance intoEmbed_embed (P : PROP1) : IntoEmbed iprop(⎡P⎤ : PROP2) P where
  into_embed := .rfl

@[rocq_alias into_embed_affinely]
instance intoEmbed_affinely [BIUpdate PROP1] [BIUpdate PROP2]
    [BiEmbedBUpd PROP1 PROP2] (P : PROP2) (Q : PROP1) [inst : IntoEmbed P Q] :
    IntoEmbed iprop(<affine> P) iprop(<affine> Q) where
  into_embed := (affinely_mono inst.into_embed).trans <| embed_affinely_2 Q

/-! ### IntoPure -/

@[rocq_alias into_pure_embed]
instance intoPure_embed (P : PROP1) (φ : Prop) [IntoPure P φ] :
    IntoPure iprop(⎡P⎤ : PROP2) φ where
  into_pure := sorry

/-! ### FromPure -/

@[rocq_alias from_pure_embed]
instance fromPure_embed (a : Bool) (P : PROP1) (ioφ : InOut) (φ : Prop)
    [FromPure a P ioφ φ] : FromPure a iprop(⎡P⎤ : PROP2) ioφ φ where
  from_pure := sorry

/-! ### IntoPersistently -/

@[rocq_alias into_persistent_embed]
instance intoPersistently_embed (p : Bool) (P Q : PROP1) [IntoPersistently p P Q] :
    IntoPersistently p iprop(⎡P⎤ : PROP2) iprop(⎡Q⎤) where
  into_persistently := sorry

/-! ### FromModal -/

@[rocq_alias from_modal_id_embed]
instance (priority := low) fromModal_id_embed {α : Type _} (φ : Prop) (sel : α)
    (P Q : PROP1) [FromModal φ modality_id sel P Q] :
    FromModal φ modality_id sel iprop(⎡P⎤ : PROP2) iprop(⎡Q⎤) where
  from_modal := sorry

@[rocq_alias from_modal_affinely_embed]
instance (priority := low) fromModal_affinely_embed {α : Type _} (φ : Prop) (sel : α)
    (P Q : PROP1) [FromModal φ modality_affinely sel P Q] :
    FromModal φ modality_affinely sel iprop(⎡P⎤ : PROP2) iprop(⎡Q⎤) where
  from_modal := sorry

@[rocq_alias from_modal_persistently_embed]
instance (priority := low) fromModal_persistently_embed {α : Type _} (φ : Prop) (sel : α)
    (P Q : PROP1) [FromModal φ modality_persistently sel P Q] :
    FromModal φ modality_persistently sel iprop(⎡P⎤ : PROP2) iprop(⎡Q⎤) where
  from_modal := sorry

@[rocq_alias from_modal_intuitionistically_embed]
instance (priority := low) fromModal_intuitionistically_embed {α : Type _} (φ : Prop) (sel : α)
    (P Q : PROP1) [FromModal φ modality_intuitionistically sel P Q] :
    FromModal φ modality_intuitionistically sel iprop(⎡P⎤ : PROP2) iprop(⎡Q⎤) where
  from_modal := sorry

/-! ### IntoWand -/

@[rocq_alias into_wand_embed]
instance intoWand_embed (p q : Bool) (m : WandMode) (R P Q : PROP1)
    [IntoWand p q R m P Q] :
    IntoWand p q iprop(⎡R⎤ : PROP2) m iprop(⎡P⎤) iprop(⎡Q⎤) where
  into_wand := sorry

/-- When the wand `⎡R⎤` sits in the intuitionistic context, the result of wand
elimination keeps the affine modality. -/
@[rocq_alias into_wand_affine_embed_true]
instance (priority := low) intoWand_affine_embed_true (q : Bool) (m : WandMode)
    (P Q R : PROP1) [IntoWand true q R .unknown P Q] :
    IntoWand true q iprop(⎡R⎤ : PROP2) m iprop(<affine> ⎡P⎤) iprop(<affine> ⎡Q⎤) where
  into_wand := sorry

@[rocq_alias into_wand_affine_embed_false]
instance (priority := low) intoWand_affine_embed_false (q : Bool) (m : WandMode)
    (P Q R : PROP1) [IntoWand false q R (.matching .argument) iprop(<affine> P) Q] :
    IntoWand false q iprop(⎡R⎤ : PROP2) m iprop(<affine> ⎡P⎤) iprop(⎡Q⎤) where
  into_wand := sorry

/-! ### FromWand -/

@[rocq_alias from_wand_embed]
instance fromWand_embed (io : InOut) (P Q1 Q2 : PROP1) [FromWand P io Q1 Q2] :
    FromWand iprop(⎡P⎤ : PROP2) io iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_wand := sorry

/-! ### FromImp -/

@[rocq_alias from_impl_embed]
instance fromImp_embed (P Q1 Q2 : PROP1) [FromImp P Q1 Q2] :
    FromImp iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_imp := sorry
@[rocq_alias from_and_embed]
instance fromAnd_embed (P Q1 Q2 : PROP1) [FromAnd P Q1 Q2] :
    FromAnd iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_and := sorry

@[rocq_alias from_sep_embed]
instance fromSep_embed (P Q1 Q2 : PROP1) [FromSep P Q1 Q2] :
    FromSep iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_sep := sorry

/-! ### CombineSepAs -/

@[rocq_alias maybe_combine_sep_as_embed]
instance combineSepAs_embed (Q1 Q2 P : PROP1) [CombineSepAs Q1 Q2 P] :
    CombineSepAs iprop(⎡Q1⎤ : PROP2) iprop(⎡Q2⎤) iprop(⎡P⎤) where
  combine_sep_as := sorry

/-! ### CombineSepGives -/

@[rocq_alias combine_sep_gives_embed]
instance combineSepGives_embed (Q1 Q2 P : PROP1) [CombineSepGives Q1 Q2 P] :
    CombineSepGives iprop(⎡Q1⎤ : PROP2) iprop(⎡Q2⎤) iprop(⎡P⎤) where
  combine_sep_gives := sorry

/-! ### IntoAnd -/

@[rocq_alias into_and_embed]
instance intoAnd_embed (p : Bool) (P Q1 Q2 : PROP1) [IntoAnd p P Q1 Q2] :
    IntoAnd p iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_and := sorry

/-! ### IntoSep -/

@[rocq_alias into_sep_embed]
instance intoSep_embed (P Q1 Q2 : PROP1) [IntoSep P Q1 Q2] :
    IntoSep iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_sep := sorry

/-! ### FromOr -/

@[rocq_alias from_or_embed]
instance fromOr_embed (P Q1 Q2 : PROP1) [FromOr P Q1 Q2] :
    FromOr iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  from_or := sorry

/-! ### IntoOr -/

@[rocq_alias into_or_embed]
instance intoOr_embed (P Q1 Q2 : PROP1) [IntoOr P Q1 Q2] :
    IntoOr iprop(⎡P⎤ : PROP2) iprop(⎡Q1⎤) iprop(⎡Q2⎤) where
  into_or := sorry

/-! ### FromExists -/

@[rocq_alias from_exist_embed]
instance fromExists_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [FromExists P Φ] :
    FromExists iprop(⎡P⎤ : PROP2) (fun a => iprop(⎡Φ a⎤)) where
  from_exists := sorry

/-! ### IntoExists -/

@[rocq_alias into_exist_embed]
instance intoExists_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [IntoExists P Φ] :
    IntoExists iprop(⎡P⎤ : PROP2) (fun a => iprop(⎡Φ a⎤)) where
  into_exists := sorry

/-! ### IntoForall -/

@[rocq_alias into_forall_embed]
instance intoForall_embed {α : Sort _} (P : PROP1) (Φ : α → PROP1) [IntoForall P Φ] :
    IntoForall iprop(⎡P⎤ : PROP2) (fun a => iprop(⎡Φ a⎤)) where
  into_forall := sorry

/-! ### FromForall -/

@[rocq_alias from_forall_embed]
instance fromForall_embed {α : Sort _} (P : PROP1) (Ψ : α → PROP1) [FromForall P Ψ] :
    FromForall iprop(⎡P⎤ : PROP2) (fun a => iprop(⎡Ψ a⎤)) where
  from_forall := sorry

/-! ### IntoInv -/

@[rocq_alias into_inv_embed]
instance intoInv_embed (P : PROP1) (N : Namespace) [IntoInv P N] :
    IntoInv iprop(⎡P⎤ : PROP2) N := {}

end
