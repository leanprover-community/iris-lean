/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris

section Laterable
open BI

/-- Require that the proposition `P` is laterable. -/
@[rocq_alias Laterable]
class Laterable [BI PROP] (P : PROP) where
  laterable : P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q -∗ ◇ P)

@[rocq_alias IntoLaterable]
class IntoLaterable [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_laterable := P ⊢ Q
  into_laterable_result_laterable : Laterable Q

@[rocq_alias later_laterable]
instance later_laterable [BI PROP] (P : PROP) : Laterable iprop(▷ P) where
  laterable := by
    iintro HP
    iexists P
    iframe HP
    iintro !> HP !>
    iassumption

@[rocq_alias timeless_laterable]
instance timeless_laterable [BI PROP] (P : PROP) [Timeless P] : Laterable P where
  laterable := by
    iintro HP
    iexists P  /- TODO: test `iframe` for existential quantifiers here -/
    iframe HP
    isplitr
    · itrivial
    · iintro !> >HP !> //

@[rocq_alias intuitionistic_laterable]
theorem intuitionistic_laterable [BI PROP] (P : PROP)
    [instTimeless : Timeless (emp : PROP)]
    [instAffine : Affine P] [instPers : Persistent P] :
    Laterable P where
  laterable := by
    iintro #HP
    iexists emp
    isplitl
    · itrivial
    · iintro !> >- //

@[rocq_alias persistent_laterable]
instance persistent_laterable [BI PROP] [BIAffine PROP] (P : PROP) [Persistent P] :
    Laterable P := by
  apply intuitionistic_laterable <;> infer_instance

@[rocq_alias sep_laterable]
instance sep_laterable [BI PROP] (P Q : PROP) [instP : Laterable P] [instQ : Laterable Q] :
    Laterable iprop(P ∗ Q) where
  laterable := by
    iintro ⟨HP, HQ⟩
    icases instP.laterable $$ HP with ⟨%P', HP', #HP⟩
    icases instQ.laterable $$ HQ with ⟨%Q', HQ', #HQ⟩
    iexists iprop(P' ∗ Q')
    isplitl
    · iframe
    · iintro !> ⟨HP', HQ'⟩
      isplitl [HP']
      · iapply HP; iassumption
      · iapply HQ; iassumption

instance exist_laterable [BI PROP] {A} (Φ : A → PROP)
    [inst : ∀ x, Laterable (Φ x)] : Laterable (∃ x, Φ x) where
  laterable := by
    iintro ⟨%x, H⟩
    icases (inst x).laterable $$ H with ⟨%Q, HQ, #HΦ⟩
    iexists Q
    /- TODO: use the introduction pattern for framing here -/
    iframe HQ
    iintro !> HQ
    iexists x
    iapply HΦ
    iassumption

end Laterable
