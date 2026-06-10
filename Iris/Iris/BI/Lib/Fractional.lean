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
open Iris.Std BI OFE

@[rocq_alias Fractional]
class Fractional [BI PROP] (Φ : Qp → PROP) where
  fractional p q : Φ (p + q) ⊣⊢ Φ p ∗ Φ q

@[rocq_alias AsFractional]
class AsFractional {PROP: Type u} [bi: BI PROP] (P : PROP) (Φ : Qp → PROP) (q : Qp) where
  as_fractional : P ⊣⊢ Φ q
  as_fractional_fractional : Fractional Φ

section Divide
variable {PROP : Type _} [BI PROP]
open BI.BigSepL

-- TODO: Fix this section to adapt to the new Qp changes

theorem fractional_bigSepL_replicate {Φ : Qp → PROP} [Fractional Φ] (r : Qp) :
    ∀ (k : Nat) (q : Qp), q.1 = ((k : Rat) + 1) * r.1 →
    (Φ q ⊢ [∗list] _x ∈ List.replicate (k + 1) r, Φ r) := by
  intro k
  induction k with
  | zero =>
    intro q hq
    rw [show q = r from Subtype.ext (by grind)]
    exact (bigSepL_singleton (Φ := fun _ _ => Φ r) (x := r)).2
  | succ k ih =>
    intro q hq
    have hpos : (0 : Rat) < ((k : Rat) + 1) * r.1 := Rat.mul_pos (by grind) r.2
    have hlt : r < q := by show r.1 < q.1; grind
    obtain ⟨c, hc⟩ : ∃ c,  r + c = q := sorry
    -- obtain ⟨c, hc⟩ := NumericFraction.lt_def.mp hlt
    have hcval : c.1 = ((k : Rat) + 1) * r.1 := by
      have hrc : r.1 + c.1 = q.1 := sorry -- congrArg Subtype.val hc
      grind
    rw [← hc, List.replicate_succ]
    exact ((Fractional.fractional r c).1.trans (sep_mono_right (ih c hcval))).trans
      (bigSepL_cons (Φ := fun _ _ => Φ r) (x := r) (xs := List.replicate (k + 1) r)).2

/-- The number q / n -/
def Rat.divide_even (q : Rat) (n : Nat) : Rat :=
  q.div n

def Qp.divide_even (q : Qp) (n : Nat) (Hn : 0 < n) : Qp where
  val := q.1.div n
  property := sorry

theorem fractional_divide_equal {Φ : Qp → PROP} [Fractional Φ] (q : Qp) (n : Nat) :
    Φ q ⊢ [∗list] _x ∈ List.replicate (n + 1) (q.divide_even (n+1) (by grind)),
      Φ (q.divide_even (n+1) (by grind)) := by
  apply fractional_bigSepL_replicate
  sorry
  -- have h := Qp.ofPNat_mul_div q (n + 1) (Nat.succ_pos n)
  -- have hof : (Qp.ofPNat (n + 1) (Nat.succ_pos n)).1 = (n : Rat) + 1 := by
  --   show ((n + 1 : Nat) : Rat) = (n : Rat) + 1; grind
  -- grind

end Divide
