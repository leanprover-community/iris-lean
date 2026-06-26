/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris
open Iris.Std BI OFE ProofMode

@[rocq_alias Fractional]
class Fractional [BI PROP] (Φ : Qp → PROP) where
  fractional p q : Φ (p + q) ⊣⊢ Φ p ∗ Φ q

@[rocq_alias AsFractional]
class AsFractional {PROP : Type u} [BI PROP] (P : PROP) (Φ : Qp → PROP) (q : Qp) where
  as_fractional : P ⊣⊢ Φ q
  as_fractional_fractional : Fractional Φ

section Lemmas
variable {PROP : Type _} [BI PROP] {P P1 P2 : PROP} {Φ : Qp → PROP} {q q1 q2 : Qp}

/-- ## AsFractional manipulation lemmas

The Rocq versions are stated using fewer AsFractional instances, and have postconditions
stated in terms of `Φ`. This version adds more typeclass instances, but has postconditons that
unify against any `IProp`.  -/

@[rocq_alias fractional_as_fractional]
instance (priority := low) fractional_as_fractional [h : Fractional Φ] (q : Qp) :
    AsFractional (Φ q) Φ q where
  as_fractional := .rfl
  as_fractional_fractional := h

@[rocq_alias fractional_split]
theorem fractional_split [hP : AsFractional P Φ (q1 + q2)]
    [hP1 : AsFractional P1 Φ q1] [hP2 : AsFractional P2 Φ q2] : P ⊣⊢ P1 ∗ P2 :=
  hP.as_fractional.trans <|
  (hP.as_fractional_fractional.fractional q1 q2).trans <|
  sep_congr hP1.as_fractional.symm hP2.as_fractional.symm

@[rocq_alias fractional_half]
theorem fractional_half [hP : AsFractional P Φ q] [hP12 : AsFractional P1 Φ q.half] :
    P ⊣⊢ P1 ∗ P1 :=
  hP.as_fractional.trans <|
  (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).trans <|
  sep_congr hP12.as_fractional.symm hP12.as_fractional.symm

@[rocq_alias fractional_merge]
theorem fractional_merge [Fractional Φ] [hP1 : AsFractional P1 Φ q1] [hP2 : AsFractional P2 Φ q2] :
    P1 ∗ P2 ⊢ Φ (q1 + q2) :=
  (sep_mono hP1.as_fractional.1 hP2.as_fractional.1).trans (Fractional.fractional q1 q2).2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_fractional]
instance (priority := default - 10) fromSepFractional [hP : AsFractional P Φ (q1 + q2)] :
    FromSep P (Φ q1) (Φ q2) where
  from_sep := (hP.as_fractional_fractional.fractional q1 q2).2.trans hP.as_fractional.2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_fractional]
instance (priority := default - 10) intoSepFractional [hP : AsFractional P Φ (q1 + q2)] :
    IntoSep P (Φ q1) (Φ q2) where
  into_sep := hP.as_fractional.1.trans (hP.as_fractional_fractional.fractional q1 q2).1

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_fractional_half]
instance (priority := default - 10) fromSepFractionalHalf [hP : AsFractional P Φ q] :
    FromSep P (Φ q.half) (Φ q.half) where
  from_sep :=
    (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).2.trans
    hP.as_fractional.2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_fractional_half]
instance (priority := default - 10) intoSepFractionalHalf [hP : AsFractional P Φ q] :
    IntoSep P (Φ q.half) (Φ q.half) where
  into_sep :=
    hP.as_fractional.1.trans
    (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).1

end Lemmas

section Divide
variable {PROP : Type _} [BI PROP]
open BI.BigSepL

theorem fractional_bigSepL_replicate {Φ : Qp → PROP} [Fractional Φ] (r : Qp) (k : Nat) :
    ∀ (q : Qp), q.val = ((k : Rat) + 1) * r.val →
      Φ q ⊢ [∗list] _x ∈ List.replicate (k + 1) r, Φ r := by
  induction k with
  | zero =>
    intro q hq
    refine .trans ?_ (bigSepL_singleton (Φ := fun _ _ => Φ r)).2
    exact .of_eq (by grind)
  | succ k ih =>
    rintro ⟨q, hq⟩ _
    obtain ⟨r, hr⟩ := r
    have hval : q - r = ((k : Rat) + 1) * r := by grind
    have hpos : (0 : Rat) < q - r := hval ▸ Rat.mul_pos (by grind) hr
    have hsum : ⟨r, hr⟩ + (⟨q - r, hpos⟩ : Qp) = ⟨q, hq⟩ := Subtype.ext (by grind)
    rw [← hsum, List.replicate_succ]
    exact ((Fractional.fractional ⟨r, hr⟩ _).1.trans (sep_mono_right (ih _ hval))).trans
      (bigSepL_cons (Φ := fun _ _ => Φ _)).2

theorem fractional_divide_equal {Φ : Qp → PROP} [Fractional Φ] (q : Qp) (n : Nat) :
    Φ q ⊢ [∗list] _x ∈ List.replicate (n + 1) (q.divide_even (n + 1) (Nat.succ_pos n)),
      Φ (q.divide_even (n + 1) (Nat.succ_pos n)) := by
  refine fractional_bigSepL_replicate _ n q ?_
  have hcast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
  rw [Qp.val_divide_even, hcast, Rat.mul_div_cancel_left _]
  have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
  grind

end Divide
