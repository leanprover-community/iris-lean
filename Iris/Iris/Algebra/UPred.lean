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

-- EXPERIMENT: UPred Leibniz by construction
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Bi-entailment.20and.20generalized.20rewriting/with/565019365
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
@[ext, rocq_alias uPred]
structure UPred (M : Type _) [UCMRA M] where
  holds : (n : Nat) → ValidAt M n → Prop
  mono {n1 n2} {x1 : ValidAt M n1} {x2 : ValidAt M n2} :
    holds n1 x1 → (x1 : M) ≼{n2} (x2 : M) → (Hle : n2 ≤ n1) → holds n2 x2

def UPred.holds_unpacked {M : Type _} [UCMRA M] (P : UPred M) (n : Nat) (x : M) (Hx : ✓{n} x) :
    Prop :=
  P.holds n ⟨x, Hx⟩

def UPred.mono_unpacked {M : Type _} [UCMRA M] (P : UPred M) {n1 n2 : Nat} {x1 x2 : M}
    (Hx1 : ✓{n1} x1) (Hx2 : ✓{n2} x2) (HP : P.holds_unpacked n1 x1 Hx1) (Hxle : x1 ≼{n2} x2)
    (Hle : n2 ≤ n1) : P.holds_unpacked n2 x2 Hx2 :=
  P.mono HP Hxle Hle

instance [UCMRA M] : Inhabited (UPred M) :=
  ⟨fun _ _ => True, fun _ _ _ => ⟨⟩⟩

instance [UCMRA M] : CoeFun (UPred M) (fun _ => (n : Nat) → ValidAt M n → Prop) where
  coe x := x.holds

section UPred

variable [UCMRA M]

open UPred

@[rocq_alias uPredO]
instance : OFE (UPred M) where
  Dist n P Q := ∀ n' (x : M), n' ≤ n → (p : ✓{n'} x) → (P n' ⟨x, p⟩ ↔ Q n' ⟨x, p⟩)
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  eq_dist {P Q} := by
    refine ⟨fun h _ _ _ _ _ => h ▸ Iff.rfl, fun h => ?_⟩
    ext n e
    exact h n n e.val (Nat.le_refl n) e.property
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

#rocq_ignore uPred_equiv' "Inlined in the `OFE` construction"
#rocq_ignore uPred_equiv "Not needed"
#rocq_ignore uPred_dist' "Inlined in the `OFE` construction"
#rocq_ignore uPred_dist "Not needed"
#rocq_ignore uPred_ofe_mixin "Not needed"


@[rocq_alias uPred_ne]
theorem uPred_ne {P : UPred M} {n} {m₁ m₂ : ValidAt M n} (H : (m₁ : M) ≡{n}≡ (m₂ : M)) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' H.to_incN .refl, fun H' => P.mono H' H.symm.to_incN .refl⟩

@[rocq_alias uPred_proper]
theorem uPred_proper {P : UPred M} {n} {m₁ m₂ : ValidAt M n} (H : (m₁ : M) ≡ (m₂ : M)) : P n m₁ ↔ P n m₂ :=
  uPred_ne H.dist

@[rocq_alias uPred_holds_ne]
theorem uPred_holds_ne {P Q : UPred M} {n₁ n₂} {x : M}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (Hx' : ✓{n₁} x) (HQ : Q n₁ ⟨x, Hx'⟩) : P n₂ ⟨x, Hx⟩ :=
  (HPQ _ _ .refl Hx).mpr (Q.mono HQ .rfl Hn)

@[rocq_alias uPred_cofe]
instance : IsCOFE (UPred M) where
  compl c := {
    holds n x := ∀ n', (Hle : n' ≤ n) → (c n') n' (x.le Hle)
    mono {n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23} := by
      refine mono _ (HP n3 (Nat.le_trans Hn23 Hn12)) ?_ .refl
      exact Hx12.le Hn23
  }
  conv_compl {n c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ .refl Hv).symm
    refine ⟨fun H => H _ .refl, fun H n' Hn' => ?_⟩
    exact (c.cauchy Hn' _ _ .refl _).mp (mono _ H .rfl Hn')

#rocq_ignore uPred_compl "Inlined in the `IsCOFE` construction"

abbrev UPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => UPred (F B A)

@[rocq_alias uPredO_map]
def uPred_map [UCMRA α] [UCMRA β] (f : β -C> α) : UPred α -n> UPred β := by
  refine ⟨fun P => ⟨fun n x => P n ⟨(f x.val), f.validN x.property⟩, ?_⟩, ⟨?_⟩⟩
  · intro n1 n2 x1 x2 HP Hm Hn
    exact P.mono HP (f.monoN _ Hm) Hn
  · intro n x1 x2 Hx1x2 n' y Hn' Hv
    exact Hx1x2 _ _ Hn' (f.validN Hv)

#rocq_ignore uPred_map "Inlined in `uPred_map`"

@[rocq_alias uPredOF]
instance [URFunctor F] : COFE.OFunctor (UPredOF F) where
  ofe := inferInstance
  map f g := uPred_map (URFunctor.map (F := F) g f)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ z2 Hn _ := by
    simp only [uPred_map]
    exact uPred_ne <| URFunctor.map_ne.ne (Hy.le Hn) (Hx.le Hn) z2
  map_id _ _ _ z _ _ := by
    simp only [uPred_map]
    exact uPred_proper <| URFunctor.map_id z
  map_comp f g f' g' _ _ _ H _ _ := by
    simp only [uPred_map]
    exact uPred_proper <| URFunctor.map_comp g' f' g f H

@[rocq_alias uPredOF_contractive]
instance instUPredOFunctorContractive [URFunctorContractive F] : COFE.OFunctorContractive (UPredOF F) where
  map_contractive.1 {n x y} HKL P m a Hmn Ha := by
    refine uPred_ne (P := P) <|
      ((URFunctorContractive.map_contractive.1 (x := (x.snd, x.fst)) (y := (y.snd, y.fst))) ?_ a).le Hmn
    exact fun m Hm => ⟨(HKL m Hm).2, (HKL m Hm).1⟩

end UPred
