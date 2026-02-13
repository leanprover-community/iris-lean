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

theorem least_fixpoint_affine (H : ∀ x, Affine (F (fun _ => emp) x)) (x : A) :
    Affine (bi_least_fixpoint F x) := by
  constructor
  -- FIXME: Proofmode bug when trying to iapply (not an emp valid)
  -- Error: ∀ (x : A), bi_least_fixpoint F x ⊢ emp is not an emp valid
  refine .trans ?_ <| wand_elim <| (wand_elim <| least_fixpoint_iter (Φ := fun _ => emp) F).trans (forall_elim x)
  iintro H
  isplitr [H]
  · isplit
    · exact true_intro
    · iintro !> %y H
      iapply (H y).affine
      iexact H
  · iexact H

theorem least_fixpoint_absorbing (H : ∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) (x : A) :
    Absorbing (bi_least_fixpoint F x) := by
  constructor
  simp only [absorbingly]
  iapply wand_elim'
  have X := @least_fixpoint_iter PROP A _ _ F (fun _ => (iprop(True -∗ bi_least_fixpoint F x))) _
  have Y := wand_elim <| (wand_elim X).trans (forall_elim x)
  refine .trans ?_ Y
  clear X Y
  iintro H
  isplitr
  · iintro
    sorry
  · iexact H
  -- FIXME: least_fixpoint_iter should be applicible here.
  -- iapply least_fixpoint_iter

--   Lemma least_fixpoint_absorbing :
--     (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
--     ∀ x, Absorbing (bi_least_fixpoint F x).
--   Proof using Type*.
--     intros ? x. rewrite /Absorbing /bi_absorbingly.
--     apply wand_elim_r'. revert x.
--     iApply least_fixpoint_iter; first solve_proper.
--     iIntros "!> %y HF Htrue". iApply least_fixpoint_unfold.
--     iAssert (F (λ x : A, True -∗ bi_least_fixpoint F x) y)%I with "[-]" as "HF".
--     { by iClear "Htrue". }
--     iApply (bi_mono_pred with "[] HF"); first solve_proper.
--     iIntros "!> %x HF". by iApply "HF".
--   Qed.


-- □ ∀ y : A, F (λ x : A, <pers> bi_least_fixpoint F x) y -∗ <pers> bi_least_fixpoint F y
theorem least_fixpoint_persistent_affine
    (H1 : ∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x)))
    (H2 : ∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x)))
    (x : A) : Persistent (bi_least_fixpoint F x) := by
  constructor
  refine .trans ?_ persistently_of_intuitionistically
  istart
  letI _ : NonExpansive fun x => iprop(□ bi_least_fixpoint F x) := sorry
  have X := @least_fixpoint_iter PROP A _ _ F  (fun x => iprop(□ bi_least_fixpoint F x)) _
  have Y := (wand_entails X).trans (forall_elim x)
  refine .trans ?_ Y
  clear X Y
  sorry


--  Lemma least_fixpoint_persistent_affine :
--      →
--      →
--     ∀ x, Persistent (bi_least_fixpoint F x).
--   Proof using Type*.
--     intros ?? x. rewrite /Persistent -intuitionistically_into_persistently_1.
--     revert x. iApply least_fixpoint_iter; first solve_proper.
--     iIntros "!> %y #HF !>". iApply least_fixpoint_unfold.
--     iApply (bi_mono_pred with "[] HF"); first solve_proper.
--     by iIntros "!> %x #?".
--   Qed.



end LeastFixpoint





--
--  Lemma least_fixpoint_persistent_absorbing :
--     (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
--     (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
--     ∀ x, Persistent (bi_least_fixpoint F x).
--   Proof using Type*.
--     intros ??. pose proof (least_fixpoint_absorbing _). unfold Persistent.
--     iApply least_fixpoint_iter; first solve_proper.
--     iIntros "!> %y #HF !>". rewrite least_fixpoint_unfold.
--     iApply (bi_mono_pred with "[] HF"); first solve_proper.
--     by iIntros "!> %x #?".
--   Qed.
-- End least.
--
-- Lemma least_fixpoint_strong_mono
--     {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}
--     (G : (A → PROP) → (A → PROP)) `{!BiMonoPred G} :
--   □ (∀ Φ x, F Φ x -∗ G Φ x) -∗
--   ∀ x, bi_least_fixpoint F x -∗ bi_least_fixpoint G x.
-- Proof.
--   iIntros "#Hmon". iApply least_fixpoint_iter.
--   iIntros "!>" (y) "IH". iApply least_fixpoint_unfold.
--   by iApply "Hmon".
-- Qed.
--
-- (** In addition to [least_fixpoint_iter], we provide two derived, stronger
-- induction principles:
--
-- - [least_fixpoint_ind] allows to assume [F (λ x, Φ x ∧ bi_least_fixpoint F x) y]
--   when proving the inductive step.
--   Intuitively, it does not only offer the induction hypothesis ([Φ] under an
--   application of [F]), but also the induction predicate [bi_least_fixpoint F]
--   itself (under an application of [F]).
-- - [least_fixpoint_ind_wf] intuitively corresponds to a kind of well-founded
--   induction. It provides the hypothesis [F (bi_least_fixpoint (λ Ψ a, Φ a ∧ F Ψ a)) y]
--   and thus allows to assume the induction hypothesis not just below one
--   application of [F], but below any positive number (by unfolding the least
--   fixpoint). The unfolding lemma [least_fixpoint_unfold] as well as
--   [least_fixpoint_strong_mono] can be useful to work with the hypothesis. *)
--
-- Section least_ind.
--   Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.
--
--   Local Lemma Private_wf_pred_mono `{!NonExpansive Φ} :
--     BiMonoPred (λ (Ψ : A → PROP) (a : A), Φ a ∧ F Ψ a)%I.
--   Proof using Type*.
--     split; last solve_proper.
--     intros Ψ Ψ' Hne Hne'. iIntros "#Mon" (x) "Ha". iSplit; first by iDestruct "Ha" as "[$ _]".
--     iDestruct "Ha" as "[_ Hr]". iApply (bi_mono_pred with "[] Hr"). by iModIntro.
--   Qed.
--   Local Existing Instance Private_wf_pred_mono.
--
--   Lemma least_fixpoint_ind_wf (Φ : A → PROP) `{!NonExpansive Φ} :
--     □ (∀ y, F (bi_least_fixpoint (λ Ψ a, Φ a ∧ F Ψ a)) y -∗ Φ y) -∗
--     ∀ x, bi_least_fixpoint F x -∗ Φ x.
--   Proof using Type*.
--     iIntros "#Hmon" (x). rewrite least_fixpoint_unfold. iIntros "Hx".
--     iApply "Hmon". iApply (bi_mono_pred with "[] Hx").
--     iModIntro. iApply least_fixpoint_iter.
--     iIntros "!> %y Hy". rewrite least_fixpoint_unfold.
--     iSplit; last done. by iApply "Hmon".
--   Qed.
--
--   Lemma least_fixpoint_ind (Φ : A → PROP) `{!NonExpansive Φ} :
--     □ (∀ y, F (λ x, Φ x ∧ bi_least_fixpoint F x) y -∗ Φ y) -∗
--     ∀ x, bi_least_fixpoint F x -∗ Φ x.
--   Proof using Type*.
--     iIntros "#Hmon". iApply least_fixpoint_ind_wf. iIntros "!> %y Hy".
--     iApply "Hmon". iApply (bi_mono_pred with "[] Hy"). { solve_proper. }
--     iIntros "!> %x Hx". iSplit.
--     - rewrite least_fixpoint_unfold. iDestruct "Hx" as "[$ _]".
--     - iApply (least_fixpoint_strong_mono with "[] Hx"). iIntros "!>" (??) "[_ $]".
--   Qed.
-- End least_ind.
--
--
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
