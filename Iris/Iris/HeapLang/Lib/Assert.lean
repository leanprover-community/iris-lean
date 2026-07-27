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

namespace Assert

section Spec

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

@[rocq_alias wp_assert]
theorem wp_assert (E : CoPset) (Φ : Val → IProp GF) (e : Exp) :
    WP e @ E {{ v, ⌜v = hl_val(#true)⌝ ∧ ▷ Φ hl_val(#()) }} -∗
    WP hl(assert(&e)) @ E {{ Φ }} := by
  iintro HΦ
  unfold Exp.assert
  wp_bind &e
  iapply wp_wand $$ HΦ
  iintro %v ⟨%Heq, HΦ'⟩
  subst Heq
  wp_if
  iapply fupd_intro
  iexact HΦ'

end Spec

end Assert
end
