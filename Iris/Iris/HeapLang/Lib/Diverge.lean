/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Diverge

@[rocq_alias diverge]
def diverge : Val := hl_val%
  rec diverge v := diverge v

section Spec

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

@[rocq_alias wp_diverge]
theorem wp_diverge (s : Stuckness) (E : CoPset) (Φ : Val → IProp GF) (v : Val) :
    ⊢ WP hl(&diverge &v) @ s; E {{ Φ }} := by
  iloeb as IH
  wp_lam
  iapply IH

end Spec

end Diverge
end
