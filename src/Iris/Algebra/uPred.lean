/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

namespace Iris

/-- The data of a uPred object is an indexed proposition over M -/
@[ext]
structure uPred (M : Type _) where
  uPred_holds : Nat → M → Prop

instance : CoeFun (uPred M) (fun _ => Nat -> M → Prop) :=
  ⟨fun x => x.uPred_holds⟩

/-- A uPred is monotone -/
class IsuPred [UCMRA M] (T : uPred M) where
  uPred_mono {n1 n2 x1 x2} : T.uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → T.uPred_holds n2 x2

section upred

variable {M : Type} [UCMRA M]

open uPred

def equiv (P Q : uPred M) : Prop :=
  ∀ n x, ✓{n} x → (P n x ↔ Q n x)

def dist (n : Nat) (P Q : uPred M) : Prop :=
  ∀ n' x, n' ≤ n -> ✓{n'} x → (P n' x ↔ Q n' x)

theorem dist_equiv : Equivalence (dist (M := M) n) where
  refl _ _ _ _ _ := Eq.to_iff rfl
  symm H _ _ A B := iff_comm.mp (H _ _ A B)
  trans H1 H2 _ _ A B := Iff.trans (H1 _ _ A B) (H2 _ _ A B)

theorem equiv_dist {x y : uPred M} : equiv x y ↔ ∀ (n : Nat), dist n x y :=
  ⟨ fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
    fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid ⟩

theorem dist_lt {x y : uPred M} {n m : Nat} (Hdist : dist n x y) (Hlt : m < n) : dist m x y :=
  fun _ _ Hle Hvalid => Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

instance : OFE (uPred M) where
  Equiv := equiv
  Dist := dist
  dist_eqv := dist_equiv
  equiv_dist := equiv_dist
  dist_lt := dist_lt

/- TODO: Some of these will need [IsuPred P] -/

theorem uPred_ne (P : uPred M) n : ∀ {m₁ m₂}, m₁ ≡{n}≡ m₂ → (P n m ↔ P n m₂) := sorry
-- Global Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
-- Proof.
--   intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
-- Qed.

theorem uPred_proper (P : uPred M) n : ∀ {m₁ m₂}, m₁ ≡ m₂ → (P n m ↔ P n m₂) := sorry
-- Global Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
-- Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.


theorem uPred_holds_ne (P Q : uPred M) n₁ n₂ x : P ≡{n₂}≡ Q → n₂ ≤ n₁ → ✓{n2} x → Q n₁ x → P n₂ x := sorry
-- Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
--   P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
-- Proof.
--   intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
-- Qed.

def compl (c : Chain (uPred M)) : uPred M := sorry
    -- fun n x => ∀ n', n' ≤ n -> ✓{n'} x → (c n') n' x,
-- Depends on CMRA lemma
--   Next Obligation.
--     move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
--     - eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; lia.
--     - eapply cmra_includedN_le=>//; lia.
--     - done.
--   Qed.

-- FIXME cleanup
instance uPred_IsCOFE : IsCOFE (uPred M) where
  compl := compl
  conv_compl := by
    intros n c i x Hin Hv
    apply Iff.symm
    apply Iff.trans
    · apply (c.cauchy Hin  _ _ (Nat.le_refl _) Hv)
    apply Iff.symm
    apply Iff.intro
    · sorry -- exact (· _ (Nat.le_refl _) Hv)
    sorry
    -- intro H n' Hn' Hv'
    -- apply (c.cauchy (i := i) Hn' _ _ (Nat.le_refl _) Hv').mp
    -- apply @uPred.uPred_mono
    -- · apply H
    -- · -- UCMRA lemma
    --   sorry
    -- · apply Hn'


def uPredOF F [URFunctor F] (A : Type _) (B : Type _) : Type _ := uPred (F B A)

instance uPredOF_oFunctor [URFunctor F] : COFE.OFunctor (uPredOF F) where
  cofe := sorry
  map := sorry
  map_ne := sorry
  map_id := sorry
  map_comp := sorry

instance uPredOF_oFC [URFunctorContractive F] : COFE.OFunctorContractive (uPredOF F) where
  map_contractive := sorry

end upred
