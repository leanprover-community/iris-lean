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

/-! ### AsEmpValid -/

set_option synthInstance.checkSynthOrder false in
@[rocq_alias as_emp_valid_embed]
instance (priority := low) asEmpValid_embed
    {PROP1 PROP2} [bi1 : BI PROP1] [bi2 : BI PROP2] [BiEmbed PROP1 PROP2]
    (d : AsEmpValid.Direction) (φ : Prop) (P : PROP1)
    [inst : AsEmpValid0 d φ io PROP1 bi1 P] :
    AsEmpValid d φ io PROP2 bi2 (embed P) where
  as_emp_valid := by
    constructor
    · intro hd hφ
      apply (embed_emp_valid P).mpr <| inst.as_emp_valid_0.as_emp_valid.left hd hφ
    · intro hd hP
      apply inst.as_emp_valid_0.as_emp_valid.right hd <| (embed_emp_valid P).mp hP

/-! ### FromModal -/

@[rocq_alias from_modal_embed]
instance fromModal_embed [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2] (P : PROP1) :
    FromModal True (modality_embed (PROP2 := PROP2)) iprop(⎡P⎤ : PROP2) iprop(⎡P⎤) P where
  from_modal _ := .rfl

/-! ### IntoEmbed -/

@[rocq_alias into_embed_embed]
instance intoEmbed_embed [BI PROP1] [BI PROP2] [BiEmbed PROP1 PROP2]
    (P : PROP1) : IntoEmbed iprop(⎡P⎤ : PROP2) P where
  into_embed := .rfl

@[rocq_alias into_embed_affinely]
instance intoEmbed_affinely [BI PROP1] [BI PROP2] [BIUpdate PROP1] [BIUpdate PROP2]
    [BiEmbed PROP1 PROP2] [BiEmbedBUpd PROP1 PROP2] (P : PROP2) (Q : PROP1) [inst : IntoEmbed P Q] :
    IntoEmbed iprop(<affine> P) iprop(<affine> Q) where
  into_embed := (affinely_mono inst.into_embed).trans <| embed_affinely_2 Q
