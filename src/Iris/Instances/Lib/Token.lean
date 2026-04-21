/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.ProofMode
public import Iris.Instances.IProp.Instance

@[expose] public section

namespace Iris

open BI CMRA Excl OFE UPred IProp Std

/-! ## Token

This library provides assertions that represent "unique tokens".
The `token γ` assertion provides ownership of the token named `γ`,
and the key lemma `token_exclusive` proves only one token exists. -/

abbrev TokenF : COFE.OFunctorPre := COFE.constOF (Excl Unit)

class TokenG (GF : BundledGFunctors) where
  [elemG : ElemG GF TokenF]

attribute [reducible] TokenG.elemG
attribute [instance] TokenG.elemG

variable {GF : BundledGFunctors} [TokenG GF]

def token (γ : GName) : IProp GF := iOwn (F := TokenF) γ (excl ())

private theorem Token.iSingleton_discreteE (γ : GName) (v : TokenF.ap (IProp GF)) [DiscreteE v] :
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

instance token_timeless (γ : GName) : Timeless (token (GF := GF) γ) := by
  unfold token
  infer_instance

-- HP encodes `pred_infinite P` from Rocq
theorem token_alloc_strong (P : GName → Prop) (HP : ∀ xs : List GName, ∃ x, P x ∧ x ∉ xs) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ token γ := by
  unfold token
  iapply iOwn_alloc_strong _ P _ trivial
  intro N
  let choice := HP (List.range N)
  exists choice.choose
  refine ⟨?_, choice.choose_spec.left⟩
  have hle := choice.choose_spec.right
  rw [List.mem_range] at hle
  exact Nat.not_lt.mp hle

theorem token_alloc : ⊢@{IProp GF} |==> ∃ γ, token γ := by
  unfold token
  iapply iOwn_alloc (excl ()) trivial

theorem token_exclusive (γ : GName) : token γ ∗ token γ ⊢@{IProp GF} False := by
  unfold token
  iintro ⟨H1, H2⟩
  ihave H := iOwn_op $$ [H1 H2]; (isplitl [H1] <;> iassumption)
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete (A := Excl Unit) $$ H with %H
  exact H.elim

end Iris
