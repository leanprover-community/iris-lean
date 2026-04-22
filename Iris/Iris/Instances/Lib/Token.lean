/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Sergei Stepanenko
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
and the key lemma `token_exclusive` proves only one token exists.

FIXME: missing token_combine_gives
-/

abbrev TokenF : COFE.OFunctorPre := COFE.constOF (Excl Unit)

@[rocq_alias tokenG]
class TokenG (GF : BundledGFunctors) where
  [elemG : ElemG GF TokenF]

attribute [reducible] TokenG.elemG
attribute [instance] TokenG.elemG

variable {GF : BundledGFunctors} [TokenG GF]

@[rocq_alias token]
def token (γ : GName) : IProp GF := iOwn (F := TokenF) γ (excl ())

@[rocq_alias token_timeless]
instance token_timeless (γ : GName) : Timeless (token (GF := GF) γ) := by
  unfold token
  infer_instance

-- HP encodes `pred_infinite P` from Rocq
@[rocq_alias token_alloc_strong]
theorem token_alloc_strong (P : GName → Prop) (HP : ∀ xs : List GName, ∃ x, P x ∧ x ∉ xs) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ token γ := by
  unfold token
  iapply iOwn_alloc_strong _ P _ trivial
  intro N
  have choice := HP (List.range N)
  exists choice.choose
  refine ⟨?_, choice.choose_spec.left⟩
  have hle := choice.choose_spec.right
  rw [List.mem_range] at hle
  exact Nat.not_lt.mp hle

@[rocq_alias token_alloc]
theorem token_alloc : ⊢@{IProp GF} |==> ∃ γ, token γ := by
  unfold token
  iapply iOwn_alloc (excl ()) trivial

@[rocq_alias token_exclusive]
theorem token_exclusive (γ : GName) : token γ ∗ token γ ⊢@{IProp GF} False := by
  unfold token
  iintro ⟨H1, H2⟩
  ihave H := iOwn_op $$ [H1 H2]; (isplitl [H1] <;> iassumption)
  ihave H := iOwn_cmraValid $$ H
  icases internalCmraValid_discrete (A := Excl Unit) $$ H with %H
  exact H.elim

end Iris
