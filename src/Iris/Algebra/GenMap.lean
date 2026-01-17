/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.Updates

namespace Iris
open OFE

section GenMap

/- The OFE over gmaps is equivalent to a non-dependent discrete function to an `Option` type with a
`Leibniz` OFE of keys, and an infinite number of unallocated elements.

In this setting, the CMRA is always unital, and as a consequence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.

GenMap is only intended to be used in the construction of the core IProp model. It is a stripped-down
version of the generic heap constructions, which you should use instead. -/

def alter [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a = a' then b else f a'

structure Enum (P : α → Prop) (enum : Nat → α) : Prop where
  inc {n} : P (enum n)
  inj {n m} : enum n = enum m → n = m

def poke [DecidableEq α] (enum : Nat → α) (n : Nat) : Nat → α :=
  fun n' => if n' < n then enum n' else enum (n' + 1)

def Infinite (P : α → Prop) : Prop := ∃ e, Enum P e

def IsFree {β : α → Type _} (f : (a : α) → Option (β a)) : α → Prop := fun a => f a = none

theorem alter_isFree_infinite [DecidableEq α] {f : α → Option β} (H : Infinite (IsFree f)) :
    Infinite (IsFree (alter f a b)) := by
  rcases H with ⟨enum, Henum_inc, Henum_inj⟩
  rcases Classical.em (∃ n₀, enum n₀ = a) with (⟨n₀, Hin⟩|Hout)
  · refine ⟨poke enum n₀, @fun n => ?_, @fun n m => ?_⟩
    · simp [alter, IsFree]; split <;> rename_i h <;> revert h <;> simp [poke]
      · split <;> intro H <;> specialize Henum_inj (Hin ▸ H) <;> omega
      · split <;> refine fun _ => Henum_inc
    · simp [poke]
      split <;> split
      all_goals intro H <;> specialize Henum_inj H <;> grind
  · refine ⟨enum, @fun n => ?_, @fun n m Heq => ?_⟩
    · simp only [not_exists] at Hout; specialize Hout n
      simp only [IsFree, alter] at ⊢
      split
      · rename_i h; exact (Hout h.symm).elim
      · exact Henum_inc
    · exact Henum_inj Heq

theorem Infinite.mono {P Q : α → Prop} (H : Infinite P) (Hmono : ∀ a, P a → Q a) : Infinite Q := by
  rcases H with ⟨enum, Henum_inc, Henum_inj⟩
  exact ⟨enum, Hmono (enum _) Henum_inc, Henum_inj⟩

theorem Infinite.nat_true : Infinite fun (_ : Nat) => True := ⟨id, trivial, id⟩

section GenMapImpl

structure GenMap (α β : Type _) where
  car : α → Option β

instance : CoeFun (GenMap α β) (fun _ => α → Option β) where
  coe := GenMap.car

nonrec def GenMap.alter [DecidableEq α] (g : GenMap α β) (a : α) (b : Option β) : GenMap α β where
  car := alter g.car a b

def GenMap.empty [DecidableEq α] : GenMap α β := ⟨fun _ => none⟩

def GenMap.singleton [DecidableEq α] (x : α) (y : β) : GenMap α β :=
  empty.alter x y

theorem GenMap.empty_map_lookup [DecidableEq α] (γ : α) :
  (GenMap.empty : GenMap α β).car γ = none := rfl

theorem GenMap.singleton_map_in [DecidableEq α] (x : α) (y : β) :
  (GenMap.singleton x y).car x = some y := by
  simp [GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter]

theorem GenMap.singleton_map_none [DecidableEq α] {x : α} {y : β} {x' : α} (h : x' ≠ x) :
    (GenMap.singleton x y).car x' = none := by
  simp [GenMap.singleton, GenMap.alter, Iris.alter, GenMap.empty]
  intro heq; subst heq; contradiction

section OFE
variable (α β : Type _) [OFE β]

instance instOFE_GenMap : OFE (GenMap α β) where
  Equiv := (·.car ≡ ·.car)
  Dist n := (·.car ≡{n}≡ ·.car)
  dist_eqv.refl _ := Dist.of_eq rfl
  dist_eqv.symm := Dist.symm
  dist_eqv.trans := Dist.trans
  equiv_dist := equiv_dist
  dist_lt := Dist.lt
end OFE

section CMRA
open CMRA GenMap

variable (α β : Type _) [CMRA β]

instance instCMRA_GenMap : CMRA (GenMap α β) where
  pcore x := Option.map GenMap.mk <| CMRA.pcore x.car
  op x y := GenMap.mk (x.car • y.car)
  ValidN n x := ✓{n} x.car ∧ (Infinite (IsFree x.car))
  Valid x := ✓ x.car ∧ (Infinite (IsFree x.car))
  op_ne.ne {_ _ _} H := op_ne (α := α → Option β) |>.ne H
  pcore_ne {n x y cx} H Hm := by
    have Hm' : (pcore x.car) = some cx.car := by
      rcases h : (pcore x.car) <;> simp_all
      rw [← Hm]
    rcases pcore_ne H Hm' with ⟨cy', Hcy'1, Hcy'2⟩
    exact ⟨⟨cy'⟩, by simp [Hcy'1], Hcy'2⟩
  validN_ne {n x y H} := by
    refine fun ⟨Hv, ⟨e, Hf, Hi⟩⟩ => ⟨Dist.validN H |>.mp Hv, ?_⟩
    refine ⟨e, @fun n => ?_, Hi⟩
    specialize H (e n); specialize @Hf n; revert H Hf
    cases _ : x.car (e n) <;> cases _ : y.car (e n) <;>
    simp_all [IsFree, OFE.Dist, Option.Forall₂]
  valid_iff_validN {x} := by
    refine ⟨fun ⟨Hv, Hi⟩ n => ⟨Hv.validN, Hi⟩, fun H => ⟨?_, H 0 |>.2⟩⟩
    exact valid_iff_validN.mpr (H · |>.1)
  validN_succ {x n} := fun ⟨Hv, Hi⟩ => ⟨validN_succ Hv, Hi⟩
  validN_op_left {n x y} := by
    simp; rintro Hv Hf
    refine ⟨validN_op_left Hv, ?_⟩
    refine Infinite.mono Hf (fun a => ?_)
    simp [IsFree, op, optionOp]
    cases _ : x.car a <;> cases _ : y.car a  <;> simp
  assoc {x y z} a := by
    cases _ : x.car a <;> cases _ : y.car a <;> cases _ : z.car a <;>
      simp_all [op, OFE.Equiv, Option.Forall₂, optionOp]
    exact assoc
  comm {x y} a := by
    cases _ : x.car a <;> cases _ : y.car a <;>
      simp_all [op, OFE.Equiv, Option.Forall₂, optionOp]
    exact comm
  pcore_op_left {x cx} H := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩
    have _ := pcore_op_left (x := x) (cx := cx)
    simp_all [OFE.Equiv]
  pcore_idem {x cx} H := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩
    simp_all [OFE.Equiv, Option.Forall₂, Option.map]
    apply pcore_idem (x := x) (cx := cx)
    simp [pcore, H]
  pcore_op_mono {x cx} := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩; simp
    refine fun H ⟨y⟩ => ?_
    rcases pcore_op_mono (x := x) (cx := cx) H y with ⟨cy, Hcy⟩
    refine ⟨.mk cy, Hcy⟩
  extend {n x y1 y2} := by
    rintro ⟨Hv, _⟩ H
    rcases extend Hv H with ⟨z1, z2, _, _, _⟩
    exists .mk z1
    exists .mk z2

instance instUCMRA_GenMap : UCMRA (GenMap Nat β) where
  unit := GenMap.empty
  unit_valid := ⟨fun _ => trivial, ⟨id, rfl, id⟩⟩
  unit_left_id := by simp [op, empty, optionOp]
  pcore_unit := by simp [pcore, empty, core, optionCore]

instance : IsTotal (GenMap Nat β) := unit_total

theorem GenMap.alter_valid [DecidableEq α] {g : GenMap α β} (Hb : ✓{n} b) (Hg : ✓{n} g) :
    ✓{n} g.alter a b := by
  rcases g with ⟨g⟩ <;> simp [alter]
  rcases Hg with ⟨Hv, Hi⟩
  refine ⟨fun _ => ?_, alter_isFree_infinite Hi⟩
  simp [Iris.alter] <;> split
  · exact Hb
  · exact Hv _

theorem GenMap.valid_exists_fresh {g : GenMap α β} (Hv : ✓{n} g) : ∃ a : α, g.car a = none := by
  rcases Hv with ⟨_, e, He_inc, _⟩
  exact ⟨e 0, He_inc⟩

theorem GenMap.singleton_map_op [DecidableEq α] (x : α) (y1 y2 : β) :
    (singleton x y1 : GenMap α β) • singleton x y2 = singleton x (y1 • y2) := by
  apply congrArg GenMap.mk
  funext γ
  simp only [CMRA.op, optionOp]
  by_cases h : γ = x
  · subst h; simp [singleton, empty, alter, Iris.alter]
  · simp [singleton, empty, alter, Iris.alter]; grind

theorem GenMap.singleton_map_pcore [DecidableEq α] (x : α) (y : β) (γ : α) :
    ((singleton x y : GenMap α β).car γ).bind pcore =
    if γ = x then pcore y else none := by
  by_cases h : γ = x
  · subst h
    simp [singleton_map_in]
  · simp_all [singleton_map_none h]

-- Validity lemmas for singleton_map
theorem GenMap.validN_singleton_map_in [DecidableEq α] (x : α) (y : β) (n : Nat) :
    ✓{n} (singleton x y).car x → ✓{n} y := by
  rw [singleton_map_in]
  simp [ValidN, optionValidN]

theorem GenMap.op_singleton_comm [DecidableEq α] {mf : GenMap α β} {x : α} (y : β) :
  IsFree mf.car x →
  (GenMap.singleton x y) • mf ≡ mf.alter x (some y) := by
  intro H_free k
  by_cases heq : k = x
  · subst heq; simp only [op, alter, Iris.alter, singleton, empty_map_lookup, optionOp, ↓reduceIte]; rw [H_free]
  · simp [op, alter, Iris.alter, singleton, empty_map_lookup, if_neg (heq ∘ Eq.symm), optionOp]

theorem GenMap.validN_op_comm [DecidableEq α] {m mf : GenMap α β} (x : α) (y : β) (H : IsFree mf.car x) :
  ✓{n} m.alter x y • mf ↔ ✓{n} (m • mf).alter x y := by
  apply Dist.validN
  intro k; simp [IsFree] at H
  by_cases heq : k = x
  · -- Case: k = x
    subst heq
    simp [CMRA.op, GenMap.alter, Iris.alter, H, optionOp]
  · -- Case: k ≠ γ
    simp only [CMRA.op, alter, Iris.alter]
    have : x ≠ k := heq ∘ Eq.symm
    rw [if_neg this, if_neg this]

end CMRA

section OFunctors
open COFE CMRA

abbrev GenMapOF (C : Type _) (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => GenMap C (F A B)

abbrev GenMap.lift [OFE α] [OFE β] (f : α -n> β) : GenMap T α -n> GenMap T β where
  f g := .mk fun t => Option.map f (g.car t)
  ne.ne {n x1 x2} H γ := by
    specialize H γ
    simp [Option.map]
    split <;> split <;> simp_all
    exact NonExpansive.ne H

instance instOFunctor_GenMapOF (F : OFunctorPre) [OFunctor F] :
    OFunctor (GenMapOF Nat F) where
  cofe {A B _ _} := instOFE_GenMap Nat (F A B)
  map f₁ f₂ := GenMap.lift <| OFunctor.map (F := F) f₁ f₂
  map_ne.ne {n x1 x2} Hx {y1 y2} Hy k γ := by
    simp only [OFE.Dist, Option.Forall₂, Option.map]
    cases _ : k.car γ <;> simp
    exact OFunctor.map_ne.ne Hx Hy _
  map_id {α β _ _} x γ := by
    simp only [Option.map]; cases _ : x.car γ <;> simp [OFunctor.map_id]
  map_comp _ _ _ _ x γ := by
    simp only [Option.map]; cases _ : x.car γ <;> simp [OFunctor.map_comp]

instance GenMapOF_instURFunctor (F : COFE.OFunctorPre) [RFunctor F] :
    URFunctor (GenMapOF Nat F) where
  map f g := {
    toHom := GenMap.lift <| OFunctor.map f g
    validN {n x} hv := by
      rcases hv with ⟨hv, ⟨e, Hf, Hi⟩⟩
      refine ⟨fun z => ?_, ⟨e, @fun n => ?_, Hi⟩⟩
      · cases h : x.car z with
        | none => simp [Option.map, ValidN, optionValidN, h]
        | some v =>
          simp only [Option.map, ValidN, optionValidN, h]
          have Hvalid := @(URFunctor.map (F := OptionOF F) f g).validN n v
          simp only [CMRA.ValidN, optionValidN, URFunctor.map] at Hvalid
          have hv' := hv z; simp only [h, ValidN, optionValidN] at hv'
          exact Hvalid hv'
      · simp_all [IsFree, Option.map]
    pcore x γ := by
      have Hcore := @(URFunctor.map (F := OptionOF F) f g).pcore (x.car γ)
      simp only [Option.map] at Hcore ⊢
      cases h : (x.car γ) <;> simp [CMRA.core, Option.getD, optionCore] at Hcore ⊢
      rename_i v
      simp [OFE.Equiv, Option.Forall₂, URFunctor.map, Option.bind, h, optionCore,
            OFunctor.map, optionMap, Option.map] at Hcore
      cases h' : pcore v <;> cases h'' : pcore ((OFunctor.map f g).f v) <;>
        simp_all [RFunctor.toOFunctor]
    op z x γ := by
      have Hop := @(URFunctor.map (F := OptionOF F) f g).op (z.car γ) (x.car γ)
      simp only [Option.map, RFunctor.toOFunctor, op, optionOp, URFunctor.map] at Hop ⊢
      cases h : z.car γ <;> cases h' : x.car γ <;> simp_all [OFunctor.map, optionMap]
  }
  map_ne.ne := OFunctor.map_ne.ne
  map_id := OFunctor.map_id
  map_comp := OFunctor.map_comp

instance GenMapOF_instURFC (F : COFE.OFunctorPre) [HURF : RFunctorContractive F] :
    URFunctorContractive (GenMapOF Nat F) where
  map_contractive.1 h x n := by
    rename_i n x' y'
    let Heqv := @(URFunctorContractive.map_contractive (F := OptionOF F)).1 _ x' y' h (x.car n)
    simp [Function.uncurry, URFunctor.map, Option.map] at Heqv ⊢
    cases h : x.car n <;> simp
    rw [h] at Heqv
    exact Heqv

end OFunctors

