/-
Copyright (c) 2026 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.BI
import Iris.ProofMode

namespace Iris
open Iris.Std BI OFE


class BIMonoPred [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) where
  mono_pred {Φ Ψ : A → PROP} [NonExpansive Φ] [NonExpansive Ψ] :
    ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x
  mono_pred_ne {Φ : A → PROP} [NonExpansive Φ] : NonExpansive (F Φ)
export BIMonoPred (mono_pred mono_pred_ne)
attribute [instance] mono_pred_ne

-- PORTING NOTE: This is an `abbrev` because of typeclass inference
abbrev bi_least_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∀ (Φ : A -n> PROP), □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)

def bi_greatest_fixpoint [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  iprop(∃ (Φ : A -n> PROP), □ (∀ x, Φ x -∗ F Φ x) ∗ Φ x)

/-- Porting note: The Rocq version of this theorem has an additional
  `∀ Φ, NonExpansive Φ → NonExpansive (F Φ)` hypothesis. Not sure why! -/
instance [BI PROP] [OFE A] {F : (A → PROP) → (A → PROP)} : NonExpansive (bi_least_fixpoint F) where
  ne {_ _ _} Hx := by
    refine forall_ne fun _ => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    exact NonExpansive.ne Hx

section LeastFixpoint

variable [BI PROP] [OFE A] (F : (A → PROP) → (A → PROP))

theorem least_fixpoint_unfold_2 [BIMonoPred F] {x} :
    F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x := by
  iintro Hf %Φ #Hincl
  iapply Hincl
  iapply mono_pred (Φ := bi_least_fixpoint F) $$ [], [Hf]
  · iintro !> %_ H
    iapply H
    iexact Hincl
  · iexact Hf

theorem least_fixpoint_unfold_1 {x} [BIMonoPred F] :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x := by
  iintro Hf
  ispecialize Hf $$ %(Hom.mk (F (bi_least_fixpoint F)) mono_pred_ne)
  iapply Hf
  iintro !> %y Hy
  iapply mono_pred (Φ := F (bi_least_fixpoint F)) $$ [], [Hy]
  · iintro !> %z Hz
    apply least_fixpoint_unfold_2
  · iexact Hy

theorem least_fixpoint_unfold {x} [BIMonoPred F] :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x :=
  equiv_iff.mpr ⟨least_fixpoint_unfold_1 _, least_fixpoint_unfold_2 _⟩

theorem least_fixpoint_iter {Φ : A → PROP} [I : NonExpansive Φ] :
    ⊢ □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HΦ %x HF
  iapply HF $$ %(Hom.mk Φ I)
  iexact HΦ

instance least_fixpoint_affine [Ia : ∀ x, Affine (F (fun _ => emp) x)] {x : A} :
    Affine (bi_least_fixpoint F x) where
  affine := by
    revert x
    iapply least_fixpoint_iter (Φ := fun _ => emp)
    iintro !> %y H
    iapply (Ia y).affine $$ H

instance least_fixpoint_absorbing [BIMonoPred F]
    [∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))] {x : A} :
    Absorbing (bi_least_fixpoint F x) where
  absorbing := by
    iapply wand_elim'
    revert x
    letI _ : NonExpansive fun x => iprop(True -∗ bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => wand_ne.ne .rfl (NonExpansive.ne H)⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y HF HT
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := (fun x : A => iprop(True -∗ bi_least_fixpoint F x))) $$ [], [HF, HT]
    · iintro !> %x HF
      iapply HF
      exact true_intro
    · iclear HT
      iexact HF

instance least_fixpoint_persistent_affine [BIMonoPred F]
    [∀ Φ, [∀ x, Affine (Φ x)] → (∀ x, Affine (F Φ x))]
    [∀ Φ, [∀ x, Persistent (Φ x)] → (∀ x, Persistent (F Φ x))]
    {x : A} : Persistent (bi_least_fixpoint F x) where
  persistent := by
    refine .trans ?_ persistently_of_intuitionistically
    revert x
    letI _ : NonExpansive fun x => iprop(□ bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => intuitionistically_ne.ne (NonExpansive.ne H)⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y #HY !>
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := fun x => iprop(□ bi_least_fixpoint F x))
    · iintro !> %_ #Hx
      iexact Hx
    · exact intuitionistically_elim

instance least_fixpoint_persistent_absorbing [BIMonoPred F]
    [Habsorb : ∀ Φ, [∀ x, Absorbing (Φ x)] → (∀ x, Absorbing (F Φ x))]
    [∀ Φ, [∀ x, Persistent (Φ x)] → (∀ x, Persistent (F Φ x))]
    {x : A} : Persistent (bi_least_fixpoint F x) where
  persistent := by
    revert x
    letI _ : NonExpansive fun x => iprop(<pers> bi_least_fixpoint F x) :=
      ⟨fun _ _ _ H => persistently_ne.ne <| NonExpansive.ne H⟩
    iapply least_fixpoint_iter
    · infer_instance -- FIXME: Issue #156
    iintro !> %y #HF !>
    iapply least_fixpoint_unfold
    · infer_instance -- FIXME: Issue #156
    iapply mono_pred (Φ := fun x => iprop(<pers> bi_least_fixpoint F x)) $$ [], HF
    letI _ := @least_fixpoint_absorbing _ _ _ _ _ _ Habsorb
    iintro !> %x #H
    iexact H

theorem least_fixpoint_strong_mono (G : (A → PROP) → (A → PROP)) [BIMonoPred G] :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, bi_least_fixpoint F x -∗ bi_least_fixpoint G x := by
  iintro #Hmon
  iapply least_fixpoint_iter
  · infer_instance -- FIXME: Issue #156
  iintro !> %y IH
  iapply least_fixpoint_unfold
  · infer_instance -- FIXME: Issue #156
  iapply Hmon $$ IH

section Strong

variable [IF : BIMonoPred F] (Φ : A → PROP) [IN : NonExpansive Φ]

local instance wf_pred_mono :
    BIMonoPred (fun (Ψ : A → PROP) (a : A) => iprop(Φ a ∧ F Ψ a)) where
  mono_pred := by
    intro Ψ Ψ' Hne Hne'
    iintro #HM %x Ha
    isplit
    · icases Ha with ⟨H, -⟩
      iexact H
    · icases Ha with ⟨-, H⟩
      iapply (mono_pred (F := F) (Φ := Ψ)) $$ [], H
      iexact HM
  mono_pred_ne.ne _ _ _ H := and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)

theorem least_fixpoint_ind_wf :
    ⊢ □ (∀ y, F (bi_least_fixpoint (fun Ψ a => iprop(Φ a ∧ F Ψ a))) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM %x
  -- Porting note: Generalized rewriting in the left-hand side of the wand in the goal.
  ihave Hthis : (F (bi_least_fixpoint F) x -∗ Φ x) -∗ (bi_least_fixpoint F x -∗ Φ x) $$ []
  · iintro H1 H2
    iapply H1
    iapply least_fixpoint_unfold
    · infer_instance
    iexact H2
  iapply Hthis
  iintro HF
  iapply HM
  iapply mono_pred (Φ := (bi_least_fixpoint F)) $$ [], HF
  imodintro
  iapply least_fixpoint_iter
  · infer_instance -- FIXME: Issue #156
  iintro !> %y Hy
  iapply least_fixpoint_unfold
  · exact wf_pred_mono (F := F) (Φ := Φ)
  isplit
  · iapply HM $$ Hy
  · iexact Hy

theorem least_fixpoint_ind :
    ⊢ □ (∀ y, F (fun x => iprop(Φ x ∧ bi_least_fixpoint F x)) y -∗ Φ y) -∗
      ∀ x, bi_least_fixpoint F x -∗ Φ x := by
  iintro #HM
  iapply least_fixpoint_ind_wf
  · infer_instance
  · infer_instance
  iintro !> %y Hy
  iapply HM
  letI _ : NonExpansive fun x => iprop(Φ x ∧ bi_least_fixpoint F x) :=
    ⟨fun _ _ _ H => and_ne.ne (NonExpansive.ne H) (NonExpansive.ne H)⟩
  iapply mono_pred (Φ := (bi_least_fixpoint fun Ψ a => iprop(Φ a ∧ F Ψ a))) $$ [], Hy
  iintro !> %x Hx
  isplit
  · iclear HM
    exact (least_fixpoint_unfold_1 ..).trans and_elim_l
  · iapply least_fixpoint_strong_mono $$ [], Hx
    · infer_instance
    iintro !> %_ %_ ⟨-, H⟩
    iexact H

end Strong
end LeastFixpoint




-- Lemma greatest_fixpoint_ne_outer {PROP : bi} {A : ofe}
--     (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)):
--   (∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2 n,
--   x1 ≡{n}≡ x2 → bi_greatest_fixpoint F1 x1 ≡{n}≡ bi_greatest_fixpoint F2 x2.
-- Proof.
--   intros HF x1 x2 n Hx. rewrite /bi_greatest_fixpoint /=.
--   do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
-- Qed.
--
-- (* Both non-expansiveness lemmas do not seem to be interderivable.
--   FIXME: is there some lemma that subsumes both? *)
-- Lemma greatest_fixpoint_ne' {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)):
--   (∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) → NonExpansive (bi_greatest_fixpoint F).
-- Proof. solve_proper. Qed.
-- Global Instance greatest_fixpoint_ne {PROP : bi} {A : ofe} n :
--   Proper (pointwise_relation (A → PROP) (pointwise_relation A (dist n)) ==>
--           dist n ==> dist n) bi_greatest_fixpoint.
-- Proof. solve_proper. Qed.
-- Global Instance greatest_fixpoint_proper {PROP : bi} {A : ofe} :
--   Proper (pointwise_relation (A → PROP) (pointwise_relation A (≡)) ==>
--           (≡) ==> (≡)) bi_greatest_fixpoint.
-- Proof. solve_proper. Qed.
--
-- Section greatest.
--   Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.
--
--   Lemma greatest_fixpoint_unfold_1 x :
--     bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x.
--   Proof using Type*.
--     iDestruct 1 as (Φ) "[#Hincl HΦ]".
--     iApply (bi_mono_pred Φ (bi_greatest_fixpoint F) with "[#]").
--     - iIntros "!>" (y) "Hy". iExists Φ. auto.
--     - by iApply "Hincl".
--   Qed.
--
--   Lemma greatest_fixpoint_unfold_2 x :
--     F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x.
--   Proof using Type*.
--     iIntros "HF". iExists (OfeMor (F (bi_greatest_fixpoint F))).
--     iSplit; last done. iIntros "!>" (y) "Hy /=". iApply (bi_mono_pred with "[#] Hy").
--     iIntros "!>" (z) "?". by iApply greatest_fixpoint_unfold_1.
--   Qed.
--
--   Corollary greatest_fixpoint_unfold x :
--     bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x.
--   Proof using Type*.
--     apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
--   Qed.
--
--   (**
--     The following lemma provides basic coinduction capabilities,
--     by requiring to reestablish the coinduction hypothesis after exactly one step.
--    *)
--   Lemma greatest_fixpoint_coiter (Φ : A → PROP) `{!NonExpansive Φ} :
--     □ (∀ y, Φ y -∗ F Φ y) -∗ ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
--   Proof. iIntros "#HΦ" (x) "Hx". iExists (OfeMor Φ). auto. Qed.
--
--   Lemma greatest_fixpoint_absorbing :
--     (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
--     ∀ x, Absorbing (bi_greatest_fixpoint F x).
--   Proof using Type*.
--     intros ?. rewrite /Absorbing.
--     iApply greatest_fixpoint_coiter; first solve_proper.
--     iIntros "!> %y >HF". iDestruct (greatest_fixpoint_unfold with "HF") as "HF".
--     iApply (bi_mono_pred with "[] HF"); first solve_proper.
--     by iIntros "!> %x HF !>".
--   Qed.
--
-- End greatest.
--
-- Lemma greatest_fixpoint_strong_mono {PROP : bi} {A : ofe}
--   (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}
--   (G : (A → PROP) → (A → PROP)) `{!BiMonoPred G} :
--   □ (∀ Φ x, F Φ x -∗ G Φ x) -∗
--   ∀ x, bi_greatest_fixpoint F x -∗ bi_greatest_fixpoint G x.
-- Proof using Type*.
--   iIntros "#Hmon". iApply greatest_fixpoint_coiter.
--   iIntros "!>" (y) "IH". rewrite greatest_fixpoint_unfold.
--   by iApply "Hmon".
-- Qed.
--
-- (** In addition to [greatest_fixpoint_coiter], we provide two derived, stronger
-- coinduction principles:
--
-- - [greatest_fixpoint_coind] requires to prove
--   [F (λ x, Φ x ∨ bi_greatest_fixpoint F x) y] in the coinductive step instead of
--   [F Φ y] and thus instead allows to prove the original fixpoint again, after
--   taking one step.
-- - [greatest_fixpoint_paco] allows for so-called parameterized coinduction, a
--   stronger coinduction principle, where [F (bi_greatest_fixpoint (λ Ψ a, Φ a ∨ F Ψ a)) y]
--   needs to be established in the coinductive step. It allows to prove the
--   hypothesis [Φ] not just after one step, but after any positive number of
--   unfoldings of the greatest fixpoint. This encodes a way of accumulating
--   "knowledge" in the coinduction hypothesis: if you return to the "initial
--   point" [Φ] of the coinduction after some number of unfoldings (not just one),
--   the proof is done. (Interestingly, this is the dual to [least_fixpoint_ind_wf]).
--   The unfolding lemma [greatest_fixpoint_unfold] and
--   [greatest_fixpoint_strong_mono] may be useful when using this lemma.
--
-- *Example use case:*
--
-- Suppose that [F] defines a coinductive simulation relation, e.g.,
--   [F rec '(e_t, e_s) :=
--     (is_val e_s ∧ is_val e_t ∧ post e_t e_s) ∨
--     (safe e_t ∧ ∀ e_t', step e_t e_t' → ∃ e_s', step e_s e_s' ∧ rec e_t' e_s')],
-- and [sim e_t e_s := bi_greatest_fixpoint F].
-- Suppose you want to show a simulation of two loops,
--   [sim (while ...) (while ...)],
-- i.e., [Φ '(e_t, e_s) := e_t = while ... ∧ e_s = while ...].
-- Then the standard coinduction principle [greatest_fixpoint_coiter] requires to
-- establish the coinduction hypothesis [Φ] after precisely one unfolding of [sim],
-- which is clearly not strong enough if the loop takes multiple steps of
-- computation per iteration. But [greatest_fixpoint_paco] allows to establish a
-- fixpoint to which [Φ] has been added as a disjunct. This fixpoint can be
-- unfolded arbitrarily many times, allowing to establish the coinduction
-- hypothesis after any number of steps. This enables to take multiple simulation
-- steps, before closing the coinduction by establishing the hypothesis [Φ]
-- again. *)
--
-- Section greatest_coind.
--   Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.
--
--   Local Lemma Private_paco_mono `{!NonExpansive Φ} :
--     BiMonoPred (λ (Ψ : A → PROP) (a : A), Φ a ∨ F Ψ a)%I.
--   Proof using Type*.
--     split; last solve_proper.
--     intros Ψ Ψ' Hne Hne'. iIntros "#Mon" (x) "[H1|H2]"; first by iLeft.
--     iRight. iApply (bi_mono_pred with "[] H2"). by iModIntro.
--   Qed.
--   Local Existing Instance Private_paco_mono.
--
--   Lemma greatest_fixpoint_paco (Φ : A → PROP) `{!NonExpansive Φ} :
--     □ (∀ y, Φ y -∗ F (bi_greatest_fixpoint (λ Ψ a, Φ a ∨ F Ψ a)) y) -∗
--     ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
--   Proof using Type*.
--     iIntros "#Hmon" (x) "HΦ". iDestruct ("Hmon" with "HΦ") as "HF".
--     rewrite greatest_fixpoint_unfold. iApply (bi_mono_pred with "[] HF").
--     iIntros "!>" (y) "HG". iApply (greatest_fixpoint_coiter with "[] HG").
--     iIntros "!>" (z) "Hf". rewrite greatest_fixpoint_unfold.
--     iDestruct "Hf" as "[HΦ|$]". by iApply "Hmon".
--   Qed.
--
--   Lemma greatest_fixpoint_coind (Φ : A → PROP) `{!NonExpansive Φ} :
--     □ (∀ y, Φ y -∗ F (λ x, Φ x ∨ bi_greatest_fixpoint F x) y) -∗
--     ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
--   Proof using Type*.
--     iIntros "#Ha". iApply greatest_fixpoint_paco. iModIntro.
--     iIntros (y) "Hy". iSpecialize ("Ha" with "Hy").
--     iApply (bi_mono_pred with "[] Ha"). { solve_proper. }
--     iIntros "!> %x [Hphi | Hgfp]".
--     - iApply greatest_fixpoint_unfold. eauto.
--     - iApply (greatest_fixpoint_strong_mono with "[] Hgfp"); eauto.
--   Qed.
-- End greatest_coind.
