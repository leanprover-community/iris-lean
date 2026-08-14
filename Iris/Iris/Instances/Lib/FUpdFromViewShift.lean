/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.Algebra.UPred
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.BI.Plainly

@[expose] public section

namespace Iris

open Iris OFE BI

section fupd

variable {M : Type u} [UCMRA M] (vs : CoPset → CoPset → UPred M → UPred M → UPred M)

@[rocq_alias fupd]
abbrev fupd_vs (E1 E2 : CoPset) (P : UPred M) : UPred M :=
  iprop(∃ R, R ∗ vs E1 E2 R P)

@[rocq_alias fupd_ne]
instance fupd_vs_ne (E1 E2 : CoPset) [vs_ne : ∀ E1 E2, NonExpansive₂ (vs E1 E2)] :
    NonExpansive (fupd_vs vs E1 E2) where
  ne {_ _ _} h := exists_ne fun _ => sep_ne.ne .rfl ((vs_ne E1 E2).ne .rfl h)

@[rocq_alias fupd_intro]
theorem fupd_vs_intro (E : CoPset) (P : UPred M)
    (vs_impl : ∀ E P Q, iprop(□ (P → Q)) ⊢ vs E E P Q) :
    P ⊢ fupd_vs vs E E P := by
  iintro HP
  simp only [fupd_vs]
  iexists P
  iframe HP
  iapply vs_impl
  iintro !> $

@[rocq_alias fupd_mono]
theorem fupd_vs_mono {E1 E2 : CoPset} {P Q : UPred M} (HPQ : P ⊢ Q)
    (vs_trans : ∀ E1 E2 E3 P Q R, iprop(vs E1 E2 P Q ∧ vs E2 E3 Q R) ⊢ vs E1 E3 P R)
    (vs_impl : ∀ E P Q, iprop(□ (P → Q)) ⊢ vs E E P Q) :
    fupd_vs vs E1 E2 P ⊢ fupd_vs vs E1 E2 Q := by
  simp only [fupd_vs]
  iintro ⟨%R, HR, Hvs⟩
  iexists _
  iframe HR
  iapply vs_trans $$ [$Hvs]
  iapply vs_impl
  iintro !> HP
  iapply HPQ $$ HP

@[rocq_alias fupd_trans]
theorem fupd_vs_trans {E1 E2 E3 : CoPset} {P : UPred M} [∀ {E1 E2 P Q}, Persistent (vs E1 E2 P Q)]
    (vs_trans : ∀ E1 E2 E3 P Q R, iprop(vs E1 E2 P Q ∧ vs E2 E3 Q R) ⊢ vs E1 E3 P R)
    (vs_exists : ∀ {A: Type u} E1 E2 (Φ : A → UPred M) Q, (∀ x, vs E1 E2 (Φ x) Q) ⊢ vs E1 E2 iprop(∃ x, Φ x) Q)
    (vs_persistent_intro_r : ∀ E1 E2 P Q R, [Persistent R] → iprop(R -∗ vs E1 E2 P Q) ⊢ vs E1 E2 iprop(P ∗ R) Q)
    (vs_impl : ∀ E P Q, iprop(□ (P → Q)) ⊢ vs E E P Q) :
    fupd_vs vs E1 E2 (fupd_vs vs E2 E3 P) ⊢ fupd_vs vs E1 E3 P := by
  simp only [fupd_vs]
  iintro ⟨%R, HR, Hvs⟩
  iexists R
  iframe HR
  iapply vs_trans $$ [$Hvs]
  clear R
  iapply vs_exists
  iintro %R
  iapply vs_persistent_intro_r
  iintro Hvs
  iapply vs_trans $$ [$Hvs]
  iapply vs_impl
  iintro !> $

@[rocq_alias fupd_mask_frame_r]
theorem fupd_vs_mask_frame_r {E1 E2 Ef : CoPset} {P : UPred M} (HE : E1 ## Ef)
    (vs_mask_frame_r : ∀ E1 E2 Ef P Q, E1 ## Ef → vs E1 E2 P Q ⊢ vs (E1 ∪ Ef) (E2 ∪ Ef) P Q) :
    fupd_vs vs E1 E2 P ⊢ fupd_vs vs (E1 ∪ Ef) (E2 ∪ Ef) P := by
  simp only [fupd_vs]
  iintro ⟨%R, HR, Hvs⟩
  iexists R
  iframe HR
  iapply vs_mask_frame_r $$ Hvs
  trivial

@[rocq_alias fupd_frame_r]
theorem fupd_vs_frame_r {E1 E2 : CoPset} {P Q : UPred M}
    (vs_frame_r : ∀ E1 E2 P Q R, vs E1 E2 P Q ⊢ vs E1 E2 iprop(P ∗ R) iprop(Q ∗ R)) :
    iprop(fupd_vs vs E1 E2 P ∗ Q) ⊢ fupd_vs vs E1 E2 iprop(P ∗ Q) := by
  simp only [fupd_vs]
  iintro ⟨⟨%R, HR, Hvs⟩, HQ⟩
  iexists iprop(R ∗ Q)
  iframe HR HQ
  iapply vs_frame_r $$ Hvs

end fupd

end Iris

end
