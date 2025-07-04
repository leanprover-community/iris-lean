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

instance [UCMRA M] : CoeFun (UPred M) (fun _ => Nat → M → Prop) where
  coe x := x.holds

section UPred

variable [UCMRA M]

open UPred

instance : OFE (UPred M) where
  Equiv P Q := ∀ n x, ✓{n} x → (P n x ↔ Q n x)
  Dist n P Q := ∀ n' x, n' ≤ n → ✓{n'} x → (P n' x ↔ Q n' x)
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  equiv_dist := ⟨
    fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
    fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid⟩
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

theorem uPred_ne {P : UPred M} {n} {m₁ m₂} (H : m₁ ≡{n}≡ m₂) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' H.to_incN (Nat.le_refl _),
   fun H' => P.mono H' H.symm.to_incN (Nat.le_refl _)⟩

theorem uPred_proper {P : UPred M} {n} {m₁ m₂} (H : m₁ ≡ m₂) : P n m₁ ↔ P n m₂ :=
  uPred_ne H.dist

theorem uPred_holds_ne {P Q : UPred M} {n₁ n₂ x}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (HQ : Q n₁ x) : P n₂ x :=
  (HPQ _ _ (Nat.le_refl _) Hx).mpr (Q.mono HQ .rfl Hn)

instance : IsCOFE (UPred M) where
  compl c := {
    holds n x := ∀ n', n' ≤ n → ✓{n'} x → (c n') n' x
    mono {n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv} := by
      refine mono _ ?_ (Hx12.le Hn23) (Nat.le_refl _)
      exact HP _ (Nat.le_trans Hn23 Hn12) ((Hx12.le Hn23).validN Hv) }
  conv_compl {n c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ (Nat.le_refl _) Hv).symm
    refine ⟨fun H => H _ (Nat.le_refl _) Hv, fun H n' Hn' Hv' => ?_⟩
    exact (c.cauchy Hn' _ _ (Nat.le_refl _) Hv').mp (mono _ H .rfl Hn')

abbrev UPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => UPred (F B A)

def uPred_map [UCMRA α] [UCMRA β] (f : β -C> α) : UPred α -n> UPred β := by
  refine ⟨fun P => ⟨fun n x => P n (f x), ?_⟩, ⟨?_⟩⟩
  · intro n1 n2 x1 x2 HP Hm Hn
    exact P.mono HP (f.monoN _ Hm) Hn
  · intro n x1 x2 Hx1x2 n' y Hn' Hv
    exact Hx1x2 _ _ Hn' (f.validN Hv)

instance [URFunctor F] : COFE.OFunctor (UPredOF F) where
  cofe := inferInstance
  map f g := uPred_map (URFunctor.map (F := F) g f)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ z2 Hn _ :=
    uPred_ne <| URFunctor.map_ne.ne (Hy.le Hn) (Hx.le Hn) z2
  map_id _ _ z _ := uPred_proper <| URFunctor.map_id z
  map_comp f g f' g' _ _ H _ := uPred_proper <| URFunctor.map_comp g' f' g f H

instance [URFunctorContractive F] : COFE.OFunctorContractive (UPredOF F) where
  map_contractive.1 {_ x y} HKL _ _ _ Hn _ := by
    refine uPred_ne <| (URFunctorContractive.map_contractive.1
      (x := (x.snd, x.fst)) (y := (y.snd, y.fst)) ?_ _).le Hn
    exact fun m Hm => ⟨(HKL m Hm).2, (HKL m Hm).1⟩

end UPred
