/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import Iris.ProofMode
public section

namespace IrisITree

open Iris BI Std OFE

/-- linear monotone closure of a predicate transformer. -/
def bi_mono0 {PROP : Type _} [BI PROP] {α : Type _} (P : (α → PROP) → PROP) : (α → PROP) → PROP :=
  fun Q => iprop% ∃ Q' : α → PROP, P Q' ∗ ∀ x, Q' x -∗ Q x

section bi_mono0

variable {PROP : Type _} [BI PROP] {α : Type _}

theorem bi_mono0_ne {n} {P P' : (α → PROP) → PROP} {Q Q' : α → PROP} :
    P ≡{n}≡ P' →
    Q ≡{n}≡ Q' →
    bi_mono0 P Q ≡{n}≡ bi_mono0 P' Q' := by
  intro hp hq
  unfold bi_mono0
  refine exists_ne fun _ => sep_ne.ne (hp _) <| forall_ne fun _ => ?_
  refine wand_ne.ne .rfl (hq _)

theorem bi_mono0_intro0 (P : (α → PROP) → PROP) (Q : α → PROP) :
    P Q ⊢ bi_mono0 P Q := by
  iintro HP; simp only [bi_mono0]
  iexists Q; isplitl [HP]
  · iexact HP
  · iintro %x HQ; iexact HQ

theorem bi_mono0_mono (P : (α → PROP) → PROP) (Q1 Q2 : α → PROP) :
    bi_mono0 P Q1 ⊢ (∀ x, Q1 x -∗ Q2 x) -∗ bi_mono0 P Q2 := by
  iintro Hm HQ; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP, HQ1⟩
  iexists Q'; isplitl [HP]
  · iexact HP
  · iintro %x HQ'; iapply HQ; iapply HQ1; iapply HQ'

theorem bi_mono0_mono_l (P1 P2 : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P1 Q ⊢ (∀ Q, P1 Q -∗ P2 Q) -∗ bi_mono0 P2 Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HP1, HQ1⟩
  iexists Q'; isplitl [HP HP1]
  · iapply HP $$ %Q' HP1
  · iexact HQ1

theorem bi_mono0_elim (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P Q ⊢ (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗ P Q := by
  iintro Hm HP; simp only [bi_mono0]
  icases Hm with ⟨%Q', HPQ', HQ1⟩
  iapply HP $$ %Q %Q' HQ1 HPQ'

theorem bi_mono0_dup (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 (bi_mono0 P) Q ⊢ bi_mono0 P Q := by
  iintro H; simp only [bi_mono0]
  icases H with ⟨%Q', Houter, HQw⟩
  icases Houter with ⟨%Q'', HP, HQw'⟩
  iexists Q''; isplitl [HP]
  · iexact HP
  · iintro %x HQ''; iapply HQw; iapply HQw' $$ HQ''

theorem bi_mono0_intro (P : (α → PROP) → PROP) (Q Q' : α → PROP) :
    P Q' ⊢ (∀ x, Q' x -∗ Q x) -∗ bi_mono0 P Q := by
  iintro HP HQ; simp only [bi_mono0]
  iexists Q'; isplitl [HP]
  · iexact HP
  · iexact HQ

end bi_mono0

end IrisITree
