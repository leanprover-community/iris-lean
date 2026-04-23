/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE

@[expose] public section

namespace Iris
open CMRA

@[ext]
structure ValidAt (M : Type _) [UCMRA M] (n : Nat) where
  val : M
  property : ✓{n} val

instance {M : Type _} [UCMRA M] {n : Nat} : CoeOut (ValidAt M n) M where
  coe := (·.val)

def ValidAt.le {M : Type _} [UCMRA M] {n m : Nat} (Hle : m ≤ n) : ValidAt M n → ValidAt M m :=
  fun v => ⟨v.val, validN_of_le Hle v.property⟩

@[simp]
theorem ValidAt.le_val {M : Type _} [UCMRA M] {n m : Nat} {Hle : m ≤ n} {v : ValidAt M n} :
  (v.le Hle).val = v.val := by rfl

@[simp]
theorem ValidAt.le_rfl {M : Type _} [UCMRA M] {n : Nat} {Hle : n ≤ n} {v : ValidAt M n} :
  v.le Hle = v := by rfl

/-- The data of a UPred object is an indexed proposition over M (Bundled version) -/
@[ext]
structure UPred (M : Type _) [UCMRA M] where
  holds : (n : Nat) → ValidAt M n → Prop
  mono {n1 n2} {x1 : ValidAt M n1} {x2 : ValidAt M n2} : holds n1 x1 → (x1 : M) ≼{n2} (x2 : M) → (Hle : n2 ≤ n1) → holds n2 x2

def UPred.holds_unpacked {M : Type _} [UCMRA M] (P : UPred M) :
  (n : Nat) → (x : M) → ✓{n} x → Prop := fun n x Hx => P.holds n ⟨x, Hx⟩

def UPred.mono_unpacked {M : Type _} [UCMRA M] (P : UPred M) {n1 n2 : Nat} {x1 x2 : M}
  (Hx1 : ✓{n1} x1) (Hx2 : ✓{n2} x2) : P.holds_unpacked n1 x1 Hx1 → x1 ≼{n2} x2 → n2 ≤ n1 → P.holds_unpacked n2 x2 Hx2 :=
    fun HP Hxle Hle => P.mono HP Hxle Hle

instance [UCMRA M] : Inhabited (UPred M) :=
  ⟨fun _ _ => True, fun _ _ _ => ⟨⟩⟩

instance [UCMRA M] : CoeFun (UPred M) (fun _ => (n : Nat) → ValidAt M n → Prop) where
  coe x := x.holds

section UPred

variable [UCMRA M]

open UPred

instance : OFE (UPred M) where
  Equiv P Q := ∀ n (x : M), (p : ✓{n} x) → (P n ⟨x, p⟩ ↔ Q n ⟨x, p⟩)
  Dist n P Q := ∀ n' (x : M), n' ≤ n → (p : ✓{n'} x) → (P n' ⟨x, p⟩ ↔ Q n' ⟨x, p⟩)
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  equiv_dist := ⟨
    fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
    fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid⟩
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

instance : OFE.Leibniz (UPred M) where
  eq_of_eqv {x y} hequiv := by
    ext n e
    exact hequiv n e.val e.property

theorem uPred_ne {P : UPred M} {n} {m₁ m₂ : ValidAt M n} (H : (m₁ : M) ≡{n}≡ (m₂ : M)) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' H.to_incN (Nat.le_refl _),
   fun H' => P.mono H' H.symm.to_incN (Nat.le_refl _)⟩

theorem uPred_proper {P : UPred M} {n} {m₁ m₂ : ValidAt M n} (H : (m₁ : M) ≡ (m₂ : M)) : P n m₁ ↔ P n m₂ :=
  uPred_ne H.dist

theorem uPred_holds_ne {P Q : UPred M} {n₁ n₂} {x : M}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (Hx' : ✓{n₁} x) (HQ : Q n₁ ⟨x, Hx'⟩) : P n₂ ⟨x, Hx⟩ :=
  (HPQ _ _ (Nat.le_refl _) Hx).mpr (Q.mono HQ .rfl Hn)

instance : IsCOFE (UPred M) where
  compl c := {
    holds n x := ∀ n', (Hle : n' ≤ n) → (c n') n' (x.le Hle)
    mono {n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23} := by
      refine mono _ (HP n3 (Nat.le_trans Hn23 Hn12)) ?_ (Nat.le_refl _)
      exact Hx12.le Hn23
  }
  conv_compl {n c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ (Nat.le_refl _) Hv).symm
    refine ⟨fun H => H _ (Nat.le_refl _), fun H n' Hn' => ?_⟩
    exact (c.cauchy Hn' _ _ (Nat.le_refl _) _).mp (mono _ H .rfl Hn')

abbrev UPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => UPred (F B A)

def uPred_map [UCMRA α] [UCMRA β] (f : β -C> α) : UPred α -n> UPred β := by
  refine ⟨fun P => ⟨fun n x => P n ⟨(f x.val), f.validN x.property⟩, ?_⟩, ⟨?_⟩⟩
  · intro n1 n2 x1 x2 HP Hm Hn
    exact P.mono HP (f.monoN _ Hm) Hn
  · intro n x1 x2 Hx1x2 n' y Hn' Hv
    exact Hx1x2 _ _ Hn' (f.validN Hv)

instance [URFunctor F] : COFE.OFunctor (UPredOF F) where
  cofe := inferInstance
  map f g := uPred_map (URFunctor.map (F := F) g f)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ z2 Hn _ := by
    simp only [uPred_map]
    exact uPred_ne <| URFunctor.map_ne.ne (Hy.le Hn) (Hx.le Hn) z2
  map_id _ _ z _ := by
    simp only [uPred_map]
    exact uPred_proper <| URFunctor.map_id z
  map_comp f g f' g' _ _ H _ := by
    simp only [uPred_map]
    exact uPred_proper <| URFunctor.map_comp g' f' g f H

instance instUPredOFunctorContractive [URFunctorContractive F] : COFE.OFunctorContractive (UPredOF F) where
  map_contractive.1 {n x y} HKL P m a Hmn Ha := by
    refine uPred_ne (P := P) <|
      ((URFunctorContractive.map_contractive.1 (x := (x.snd, x.fst)) (y := (y.snd, y.fst))) ?_ a).le Hmn
    exact fun m Hm => ⟨(HKL m Hm).2, (HKL m Hm).1⟩

end UPred
