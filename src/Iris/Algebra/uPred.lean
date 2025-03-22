/-
Copyright (c) 2025 Leo Stefanesco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

namespace Iris

section upred

variable {M : Type} [UCMRA M]

@[ext]
structure uPred (M : Type) [UCMRA M] where
  uPred_holds : Nat -> M -> Prop
  uPred_mono n1 n2 x1 x2 : uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2


instance [UCMRA M] : CoeFun (uPred M) (fun _ => Nat -> M → Prop) := ⟨(uPred.uPred_holds ·)⟩

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

def compl (c : Chain (uPred M)) : uPred M :=
  ⟨ fun n x => ∀ n', n' ≤ n -> ✓{n'} x → (c n') n' x,
--   Next Obligation.
--     move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
--     - eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; lia.
--     - eapply cmra_includedN_le=>//; lia.
--     - done.
--   Qed.
    sorry ⟩


instance uPred_IsCOFE : IsCOFE (uPred M) where
  compl := compl
  conv_compl := by
--   Next Obligation.
--     intros n c; split=>i x Hin Hv.
--     Check (chain_cauchy c i n).
--     etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
--     repeat intro. apply (chain_cauchy c _ i)=>//. by eapply uPred_mono.
--   Qed.
    sorry

end upred
