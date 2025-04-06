/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

namespace Iris

/-- The data of a uPred object is an indexed proposition over M (Bundled version )-/
@[ext]
structure uPred (M : Type _) [UCMRA M] where
  uPred_holds : Nat → M → Prop
  uPred_mono {n1 n2 x1 x2} : uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2

-- The unbundled version: separate out just the uPred_holds field and make
-- the uPred_mono field a typeclass


instance [UCMRA M] : CoeFun (uPred M) (fun _ => Nat -> M → Prop) :=
  ⟨fun x => x.uPred_holds⟩

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

theorem uPred_ne (P : uPred M) n : ∀ {m₁ m₂}, m₁ ≡{n}≡ m₂ → (P n m₁ ↔ P n m₂) := by
  intro m₁ m₂ H
  apply Iff.intro <;> intro H' <;> apply P.uPred_mono H' _ (Nat.le_refl _)
  · apply CMRA.dst_incN H.symm
  · apply CMRA.dst_incN H

theorem uPred_proper (P : uPred M) n : ∀ {m₁ m₂}, m₁ ≡ m₂ → (P n m₁ ↔ P n m₂) :=
  fun H => uPred_ne _ _ (OFE.equiv_dist.mp H _)

theorem uPred_holds_ne (P Q : uPred M) n₁ n₂ x :
    P ≡{n₂}≡ Q → n₂ ≤ n₁ → ✓{n₂} x → Q n₁ x → P n₂ x := by
  intros HPQ Hn Hx HQ
  apply (HPQ _ _ (Nat.le_refl _) Hx).mpr
  apply Q.uPred_mono HQ _ Hn
  apply CMRA.incN_refl

def compl (c : Chain (uPred M)) : uPred M where
  uPred_holds := fun n x => ∀ n', n' ≤ n → ✓{n'} x → (c n') n' x
  uPred_mono := by
    intros n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv
    apply uPred_mono
    · apply HP _ (Nat.le_trans Hn23 Hn12)
      apply CMRA.validN_of_incN _ Hv
      apply CMRA.incN_of_incN_le Hn23 Hx12
    · exact CMRA.incN_of_incN_le Hn23 Hx12
    · exact (Nat.le_refl n3)

instance uPred_IsCOFE : IsCOFE (uPred M) where
  compl := compl
  conv_compl := by
    intros n c i x Hin Hv
    apply Iff.symm
    apply Iff.trans
    · apply (c.cauchy Hin  _ _ (Nat.le_refl _) Hv)
    apply Iff.symm
    apply Iff.intro
    · intro H
      exact (H _ (Nat.le_refl _) Hv)
    intro H n' Hn' Hv'
    apply (c.cauchy (i := i) Hn' _ _ (Nat.le_refl _) Hv').mp
    apply uPred_mono
    · apply H
    · exact CMRA.incN_refl x
    · apply Hn'

def uPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => uPred (F B A)

instance uPredOF_oFunctor [URFunctor F] : COFE.OFunctor (uPredOF F) where
  cofe := by unfold uPredOF; infer_instance
  map := sorry
  map_ne := sorry
  map_id := sorry
  map_comp := sorry

instance uPredOF_oFC [URFunctorContractive F] : COFE.OFunctorContractive (uPredOF F) where
  map_contractive := sorry

end upred
