/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes

@[expose] public section

namespace Iris.ProofMode
open BI

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
