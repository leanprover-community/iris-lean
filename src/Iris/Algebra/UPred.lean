/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.CMRA
import Iris.Algebra.OFE

namespace Iris
open CMRA

/-- The data of a UPred object is an indexed proposition over M (Bundled version) -/
@[ext]
structure UPred (M : Type _) [UCMRA M] where
  holds : Nat → M → Prop
  mono {n1 n2 x1 x2} : holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → holds n2 x2

instance [UCMRA M] : Inhabited (UPred M) :=
  ⟨fun _ _ => True, fun _ _ _ => ⟨⟩⟩

instance [UCMRA M] : CoeFun (UPred M) (fun _ => Nat → M → Prop) :=
  ⟨fun x => x.holds⟩

section UPred

variable {M : Type} [UCMRA M]

open UPred

def equiv (P Q : UPred M) : Prop :=
  ∀ n x, ✓{n} x → (P n x ↔ Q n x)

def dist (n : Nat) (P Q : UPred M) : Prop :=
  ∀ n' x, n' ≤ n → ✓{n'} x → (P n' x ↔ Q n' x)

theorem dist_equiv : Equivalence (dist (M := M) n) where
  refl _ _ _ _ _ := Eq.to_iff rfl
  symm H _ _ A B := iff_comm.mp (H _ _ A B)
  trans H1 H2 _ _ A B := Iff.trans (H1 _ _ A B) (H2 _ _ A B)

theorem equiv_dist {x y : UPred M} : equiv x y ↔ ∀ (n : Nat), dist n x y :=
  ⟨fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
   fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid⟩

theorem dist_lt {x y : UPred M} {n m : Nat} (Hdist : dist n x y) (Hlt : m < n) : dist m x y :=
  fun _ _ Hle Hvalid => Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

instance : OFE (UPred M) where
  Equiv := equiv
  Dist := dist
  dist_eqv := dist_equiv
  equiv_dist := equiv_dist
  dist_lt := dist_lt

theorem uPred_ne {P : UPred M} {n} {m₁ m₂} (H : m₁ ≡{n}≡ m₂) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' (dst_incN H.symm) (Nat.le_refl _),
   fun H' => P.mono H' (dst_incN H) (Nat.le_refl _)⟩

theorem uPred_proper {P : UPred M} {n} {m₁ m₂} (H : m₁ ≡ m₂) : P n m₁ ↔ P n m₂ :=
  uPred_ne (OFE.equiv_dist.mp H _)

theorem uPred_holds_ne {P Q : UPred M} {n₁ n₂ x}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (HQ : Q n₁ x) : P n₂ x :=
  (HPQ _ _ (Nat.le_refl _) Hx).mpr (Q.mono HQ .rfl Hn)

def compl (c : Chain (UPred M)) : UPred M where
  holds := fun n x => ∀ n', n' ≤ n → ✓{n'} x → (c n') n' x
  mono {n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv} := by
    refine mono _ ?_ (Hx12.le Hn23) (Nat.le_refl _)
    exact HP _ (Nat.le_trans Hn23 Hn12) ((Hx12.le Hn23).validN Hv)

instance uPred_IsCOFE : IsCOFE (UPred M) where
  compl := compl
  conv_compl {n c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ (Nat.le_refl _) Hv).symm
    refine ⟨fun H => H _ (Nat.le_refl _) Hv, fun H n' Hn' Hv' => ?_⟩
    exact (c.cauchy Hn' _ _ (Nat.le_refl _) Hv').mp (mono _ H .rfl Hn')

abbrev UPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => UPred (F B A)

def uPred_map [UCMRA α] [UCMRA β] (f : β -C> α) : UPred α -n> UPred β := by
  refine ⟨fun P => ⟨fun n x => P n (f x), ?_⟩, ⟨?_⟩⟩
  · intro n1 n2 x1 x2 HP Hm Hn
    refine P.mono HP ((Iris.CMRA.Hom.monoN f) _ Hm) Hn
  · intro n x1 x2 Hx1x2 n' y Hn' Hv
    refine Hx1x2 _ _ Hn' (f.validN Hv)

instance uPredOF_oFunctor [URFunctor F] : COFE.OFunctor (UPredOF F) where
  cofe := inferInstance
  map f g := uPred_map (URFunctor.map (F:=F) g f)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ z2 Hn _ :=
    uPred_ne $ URFunctor.map_ne.ne (Hy.le Hn) (Hx.le Hn) z2
  map_id _ _ z _ := uPred_proper $ URFunctor.map_id z
  map_comp f g f' g' _ _ H _ := uPred_proper $ URFunctor.map_comp g' f' g f H

instance uPredOF_oFC [URFunctorContractive F] : COFE.OFunctorContractive (UPredOF F) where
  map_contractive.1 {_ x y} HKL _ _ _ Hn _ := by
    refine uPred_ne $ (URFunctorContractive.map_contractive.1
      (x := (x.snd, x.fst)) (y := (y.snd, y.fst)) ?_ _).le Hn
    exact fun m Hm => ⟨(HKL m Hm).2, (HKL m Hm).1⟩

end UPred
