/-
(** This file provides a version of the fractional camera whose elements are
in the internal (0,1] of the rational numbers.

Notice that this camera could in principle be obtained by restricting the
validity of the unbounded fractional camera [ufrac]. *)
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

(** Since the standard (0,1] fractional camera is used more often, we define
[frac] through a [Notation] instead of a [Definition]. That way, Coq infers the
[frac] camera by default when using the [Qp] type. *)
Notation frac := Qp (only parsing).

Section frac.
  Context {SI : sidx}.
  Canonical Structure fracO := leibnizO frac.

  Local Instance frac_valid_instance : Valid frac := λ x, (x ≤ 1)%Qp.
  Local Instance frac_pcore_instance : PCore frac := λ _, None.
  Local Instance frac_op_instance : Op frac := λ x y, (x + y)%Qp.

  Lemma frac_valid p : ✓ p ↔ (p ≤ 1)%Qp.
  Proof. done. Qed.
  Lemma frac_valid_1 : ✓ 1%Qp.
  Proof. done. Qed.
  Lemma frac_op p q : p ⋅ q = (p + q)%Qp.
  Proof. done. Qed.
  Lemma frac_included p q : p ≼ q ↔ (p < q)%Qp.
  Proof. by rewrite Qp.lt_sum. Qed.

  Corollary frac_included_weak p q : p ≼ q → (p ≤ q)%Qp.
  Proof. rewrite frac_included. apply Qp.lt_le_incl. Qed.

  Definition frac_ra_mixin : RAMixin frac.
  Proof.
    split; try apply _; try done.
    intros p q. rewrite !frac_valid frac_op=> ?.
    trans (p + q)%Qp; last done. apply Qp.le_add_l.
  Qed.
  Canonical Structure fracR := discreteR frac frac_ra_mixin.

  Global Instance frac_cmra_discrete : CmraDiscrete fracR.
  Proof. apply discrete_cmra_discrete. Qed.
  Global Instance frac_full_exclusive : Exclusive 1%Qp.
  Proof. intros p. apply Qp.not_add_le_l. Qed.
  Global Instance frac_cancelable (q : frac) : Cancelable q.
  Proof. intros n p1 p2 _. apply (inj (Qp.add q)). Qed.
  Global Instance frac_id_free (q : frac) : IdFree q.
  Proof. intros p _. apply Qp.add_id_free. Qed.

  (* This one has a higher precendence than [is_op_op] so we get a [+] instead
     of an [⋅]. *)
  Global Instance frac_is_op q1 q2 : IsOp (q1 + q2)%Qp q1 q2 | 10.
  Proof. done. Qed.
  Global Instance is_op_frac q : IsOp' q (q/2)%Qp (q/2)%Qp.
  Proof. by rewrite /IsOp' /IsOp frac_op Qp.div_2. Qed.
End frac.



-/

