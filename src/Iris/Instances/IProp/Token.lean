/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Iris.Instances.IProp.Instance

namespace Iris

open BI CMRA Excl OFE UPred IProp

/-! ## Token

This library provides assertions that represent "unique tokens".
The `token γ` assertion provides ownership of the token named `γ`,
and the key lemma `token_exclusive` proves only one token exists. -/

abbrev TokenF : COFE.OFunctorPre := COFE.constOF (Excl Unit)

class TokenG (GF : BundledGFunctors) where
  [elemG : ElemG GF TokenF]

attribute [instance] TokenG.elemG

variable {GF : BundledGFunctors} [TokenG GF]

def token (γ : GName) : IProp GF := iOwn (F := TokenF) γ (excl ())

private theorem iSingleton_discreteE (γ : GName) (v : TokenF.ap (IProp GF)) [DiscreteE v] :
    DiscreteE (iSingleton TokenF γ v) where
  discrete {y} H τ' := by
    specialize H τ'
    simp only [iSingleton] at H ⊢
    split
    · next heq =>
      subst heq
      simp only [dite_true] at H ⊢
      letI := IProp.unfoldi_discreteE (ElemG.bundle_discreteE TokenG.elemG (v := v))
      exact GenMap.singleton_discreteE.discrete H
    · next hne =>
      simp only [hne, dite_false] at H ⊢
      exact GenMap.empty_discreteE.discrete H

instance token_timeless (γ : GName) : Timeless (token (GF := GF) γ) :=
  @UPred.ownM_timeless _ _ _ (iSingleton_discreteE γ (excl ()))

-- HP encodes `pred_infinite P` from Rocq
theorem token_alloc_strong (P : GName → Prop) (HP : ∀ xs : List GName, ∃ x, P x ∧ x ∉ xs) :
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token (GF := GF) γ := by
  sorry

theorem token_alloc : ⊢ |==> ∃ γ, token (GF := GF) γ :=
  iOwn_alloc (F := TokenF) (excl ()) trivial

theorem token_exclusive (γ : GName) : token (GF := GF) γ ∗ token γ ⊢ False :=
  iOwn_cmraValid_op.trans <|
  (UPred.cmraValid_elim _).trans <|
  pure_elim' fun h => (not_valid_exclN_op_left h).elim

end Iris
