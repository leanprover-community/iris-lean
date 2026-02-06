import Iris.Algebra.CMRA
import Iris.Algebra.Updates
import Iris.Algebra.OFE

open Iris
-- Local Arguments pcore _ _ !_ /.
-- Local Arguments cmra_pcore _ !_ /.
-- Local Arguments validN _ _ _ !_ /.
-- Local Arguments valid _ _  !_ /.
-- Local Arguments cmra_validN _ _ !_ /.
-- Local Arguments cmra_valid _  !_ /.

inductive CSum (A B : Type _) where
  | inl : A → CSum A B
  | inr : B → CSum A B
  | bot : CSum A B

-- Global Arguments Cinl {_ _} _.
-- Global Arguments Cinr {_ _} _.
-- Global Arguments CsumBot {_ _}.

-- Global Instance: Params (@Cinl) 2 := {}.
-- Global Instance: Params (@Cinr) 2 := {}.
-- Global Instance: Params (@CsumBot) 2 := {}.

-- Global Instance maybe_Cinl {A B} : Maybe (@Cinl A B) := λ x,
--   match x with Cinl a => Some a | _ => None end.
-- Global Instance maybe_Cinr {A B} : Maybe (@Cinr A B) := λ x,
--   match x with Cinr b => Some b | _ => None end.

namespace CSum
section OFE
open OFE
variable [OFE A] [OFE B]

/-! ## COFE -/
@[simp] protected def CSum.Equiv : CSum A B → CSum A B  → Prop
  | CSum.inl a1, CSum.inl a2 => a1 ≡ a2
  | CSum.inr b1, CSum.inr b2 => b1 ≡ b2
  | CSum.bot, CSum.bot => True
  | _, _ => False

@[simp] protected def CSum.Dist (n : Nat) : CSum A B → CSum A B → Prop
  | CSum.inl a1, CSum.inl a2 => a1 ≡{n}≡ a2
  | CSum.inr b1, CSum.inr b2 => b1 ≡{n}≡ b2
  | CSum.bot, CSum.bot => True
  | _, _ => False

instance : OFE (CSum A B) where
  Equiv := CSum.Equiv
  Dist := CSum.Dist
  dist_eqv := by
    intro n
    constructor
    · intro x <;> rcases x <;> simp
    · intro x y
      rcases x <;> rcases y <;> simp at * <;> exact Dist.symm
    · intro x y z
      rcases x <;> rcases y <;> rcases z <;> simp at * <;> exact Dist.trans
  equiv_dist {x y} := by
    constructor
    · intro h n
      rcases x <;> rcases y <;> simp at * <;> exact Equiv.dist h
    · intro h
      rcases x <;> rcases y <;> simp at * <;> exact equiv_dist.mpr h
  dist_lt {n x y m} hn hlt := by
    rcases x <;> rcases y <;> simp at * <;> exact Dist.lt hn hlt

instance : OFE.NonExpansive (inl (A:=A) (B:=B)) where
  ne _ _ _ a := a

theorem inl_inj {a1 a2 : A} (H : (inl (B:=B) a1) ≡ (inl a2)) : a1 ≡ a2 := by
  exact H

theorem inl_inj_dist {n : Nat} {a1 a2 : A}
    (H : (inl (B:=B) a1) ≡{n}≡ (inl a2)) : a1 ≡{n}≡ a2 := by
  exact H

instance : OFE.NonExpansive (inr (A:=A) (B:=B)) where
  ne _ _ _ a := a

theorem inr_inj {b1 b2 : B} (H : (inr (A:=A) b1) ≡ (inr b2)) : b1 ≡ b2 := by
  exact H

theorem inr_inj_dist {n : Nat} {b1 b2 : B}
    (H : (inr (A:=A) b1) ≡{n}≡ (inr b2)) : b1 ≡{n}≡ b2 := by
  exact H

end OFE

