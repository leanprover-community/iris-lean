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

/-- Any `Φ q` of a fractional `Φ` is `AsFractional`. -/
@[rocq_alias fractional_as_fractional]
instance (priority := 100) fractional_as_fractional [h : Fractional Φ] (q : Qp) :
    AsFractional (Φ q) Φ q where
  as_fractional := .rfl
  as_fractional_fractional := h

/-- Split a fraction `q1 + q2` into the separating conjunction of its parts. -/
@[rocq_alias fractional_split]
theorem fractional_split [hP : AsFractional P Φ (q1 + q2)]
    [hP1 : AsFractional P1 Φ q1] [hP2 : AsFractional P2 Φ q2] : P ⊣⊢ P1 ∗ P2 :=
  have := hP.as_fractional_fractional
  hP.as_fractional.trans <| (Fractional.fractional q1 q2).trans <|
    sep_congr hP1.as_fractional.symm hP2.as_fractional.symm

/-- Halve a fraction into two equal pieces. -/
@[rocq_alias fractional_half]
theorem fractional_half [hP : AsFractional P Φ q] [hP12 : AsFractional P1 Φ q.half] :
    P ⊣⊢ P1 ∗ P1 :=
  have := hP.as_fractional_fractional
  hP.as_fractional.trans <| (Qp.half_add_half q ▸ Fractional.fractional q.half q.half).trans <|
    sep_congr hP12.as_fractional.symm hP12.as_fractional.symm

/-- Merge two fractions back into their sum. -/
@[rocq_alias fractional_merge]
theorem fractional_merge [Fractional Φ]
    [hP1 : AsFractional P1 Φ q1] [hP2 : AsFractional P2 Φ q2] : P1 ∗ P2 ⊢ Φ (q1 + q2) :=
  (sep_mono hP1.as_fractional.1 hP2.as_fractional.1).trans (Fractional.fractional q1 q2).2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_fractional]
instance (priority := default - 10) fromSepFractional [hP : AsFractional P Φ (q1 + q2)] :
    FromSep P (Φ q1) (Φ q2) where
  from_sep :=
    have := hP.as_fractional_fractional
    (Fractional.fractional q1 q2).2.trans hP.as_fractional.2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_fractional]
instance (priority := default - 10) intoSepFractional [hP : AsFractional P Φ (q1 + q2)] :
    IntoSep P (Φ q1) (Φ q2) where
  into_sep :=
    have := hP.as_fractional_fractional
    hP.as_fractional.1.trans (Fractional.fractional q1 q2).1

set_option synthInstance.checkSynthOrder false in
@[rocq_alias from_sep_fractional_half]
instance (priority := default - 10) fromSepFractionalHalf [hP : AsFractional P Φ q] :
    FromSep P (Φ q.half) (Φ q.half) where
  from_sep :=
    have := hP.as_fractional_fractional
    (Qp.half_add_half q ▸ Fractional.fractional q.half q.half).2.trans hP.as_fractional.2

set_option synthInstance.checkSynthOrder false in
@[rocq_alias into_sep_fractional_half]
instance (priority := default - 10) intoSepFractionalHalf [hP : AsFractional P Φ q] :
    IntoSep P (Φ q.half) (Φ q.half) where
  into_sep :=
    have := hP.as_fractional_fractional
    hP.as_fractional.1.trans (Qp.half_add_half q ▸ Fractional.fractional q.half q.half).1

end Lemmas

section Divide
variable {PROP : Type _} [BI PROP]
open BI.BigSepL

/-- Whenever `q = (k+1) * r`, the fraction `Φ q` splits into `k+1` copies of `Φ r`. -/
theorem fractional_bigSepL_replicate {Φ : Qp → PROP} [Fractional Φ] (r : Qp) :
    ∀ (k : Nat) (q : Qp), q.val = ((k : Rat) + 1) * r.val →
      Φ q ⊢ [∗list] _x ∈ List.replicate (k + 1) r, Φ r := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [show q = r from Subtype.ext (by grind)]
    exact (bigSepL_singleton (Φ := fun _ _ => Φ r)).2
  | succ k ih =>
    intro q hq
    have hval : q.val - r.val = ((k : Rat) + 1) * r.val := by grind
    have hpos : (0 : Rat) < q.val - r.val := hval ▸ Rat.mul_pos (by grind) r.2
    have hsum : r + (⟨q.val - r.val, hpos⟩ : Qp) = q := Subtype.ext (by grind)
    rw [← hsum, List.replicate_succ]
    exact ((Fractional.fractional r _).1.trans (sep_mono_right (ih _ hval))).trans
      (bigSepL_cons (Φ := fun _ _ => Φ r)).2

/-- Splitting `Φ q` into `n+1` equal pieces, each owning the fraction `q / (n+1)`. -/
theorem fractional_divide_equal {Φ : Qp → PROP} [Fractional Φ] (q : Qp) (n : Nat) :
    Φ q ⊢ [∗list] _x ∈ List.replicate (n + 1) (q.divide_even (n + 1) (Nat.succ_pos n)),
      Φ (q.divide_even (n + 1) (Nat.succ_pos n)) := by
  refine fractional_bigSepL_replicate _ n q ?_
  have hne : ((n : Rat) + 1) ≠ 0 := by
    have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
    grind
  have hcast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
  rw [Qp.val_divide_even, hcast, Rat.mul_div_cancel_left hne]

end Divide
