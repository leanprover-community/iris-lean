/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates

@[expose] public section

namespace Iris
open OFE

section GenMap

/-! ## GenMap

The OFE over gmaps is equivalent to a non-dependent discrete function to an `Option` type with a
`Leibniz` OFE of keys, and a finite number of allocated elements.

In this setting, the CMRA is always unital, and as a consequence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.

GenMap is only intended to be used in the construction of the core IProp model.
It is a stripped-down version of the generic heap constructions, which you should
use instead. -/

def alter (f : Nat → β) (a : Nat) (b : β) : Nat → β :=
  fun a' => if a = a' then b else f a'

/-- A GenMap is a partial map from `Nat` to `β` with finite support.
The `bound` field witnesses that all keys ≥ some `N` map to `none`. -/
structure GenMap (β : Type _) where
  car : Nat → Option β
  bound : ∃ N, ∀ k, N ≤ k → car k = none

instance : CoeFun (GenMap β) (fun _ => Nat → Option β) where
  coe := GenMap.car

nonrec def GenMap.alter (g : GenMap β) (a : Nat) (b : Option β) : GenMap β where
  car := alter g.car a b
  bound := by
    obtain ⟨N, hN⟩ := g.bound
    refine ⟨max N (a + 1), fun k hk => ?_⟩
    simp only [Iris.alter]
    split
    next heq => subst heq; omega
    next => exact hN k (by omega)

def GenMap.empty : GenMap β := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

def GenMap.singleton (x : Nat) (y : β) : GenMap β :=
  empty.alter x y

theorem GenMap.empty_map_lookup (γ : Nat) : (GenMap.empty : GenMap β).car γ = none := rfl

theorem GenMap.singleton_map_in (x : Nat) (y : β) :
    (GenMap.singleton x y).car x = some y := by
  simp [GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter]

theorem GenMap.singleton_map_none {x : Nat} {y : β} {x' : Nat} (h : x' ≠ x) :
    (GenMap.singleton x y).car x' = none := by
  simp [GenMap.singleton, GenMap.alter, Iris.alter, GenMap.empty]
  rintro rfl
  contradiction

/-- Any GenMap has a fresh key (one mapping to `none`). -/
theorem GenMap.exists_fresh (g : GenMap β) : ∃ k, g.car k = none := by
  obtain ⟨N, hN⟩ := g.bound
  exact ⟨N, hN N (Nat.le_refl N)⟩

/-- Given a GenMap and a predicate that is satisfied by infinitely many naturals
(witnessed by: for any N, there exists k ≥ N with P k), we can find a fresh key
satisfying P. -/
theorem GenMap.exists_fresh_sat (g : GenMap β) {P : Nat → Prop}
    (hP : ∀ N, ∃ k, N ≤ k ∧ P k) : ∃ k, g.car k = none ∧ P k := by
  obtain ⟨N, hN⟩ := g.bound
  obtain ⟨k, hk_ge, hk_P⟩ := hP N
  exact ⟨k, hN k hk_ge, hk_P⟩

/-- `IsFree f a` means key `a` maps to `none` in `f`. Retained for compatibility
with downstream proofs that pattern-match on this. -/
def IsFree {β : α → Type _} (f : (a : α) → Option (β a)) : α → Prop :=
  fun a => f a = none

/-! ## OFE -/

section OFE
variable (β : Type _) [OFE β]

instance instOFE_GenMap : OFE (GenMap β) where
  Equiv := (·.car ≡ ·.car)
  Dist n := (·.car ≡{n}≡ ·.car)
  dist_eqv.refl _ := Dist.of_eq rfl
  dist_eqv.symm := Dist.symm
  dist_eqv.trans := Dist.trans
  equiv_dist := equiv_dist
  dist_lt := Dist.lt
end OFE

@[ext] theorem GenMap.ext {a b : GenMap β} (h : a.car = b.car) : a = b := by
  obtain ⟨ca, ba⟩ := a
  obtain ⟨cb, bb⟩ := b
  simp at h; subst h; rfl

/-! ## CMRA -/

section CMRA
open CMRA GenMap

variable (β : Type _) [CMRA β]

theorem op_bound (x y : GenMap β) :
    ∃ N, ∀ k, N ≤ k → (x.car • y.car) k = none := by
  obtain ⟨Nx, hx⟩ := x.bound
  obtain ⟨Ny, hy⟩ := y.bound
  refine ⟨max Nx Ny, fun k hk => ?_⟩
  simp [CMRA.op, optionOp, hx k (by omega), hy k (by omega)]

theorem pcore_bound (x : GenMap β) (cx : Nat → Option β)
    (hpc : CMRA.pcore x.car = some cx) :
    ∃ N, ∀ k, N ≤ k → cx k = none := by
  obtain ⟨N, hN⟩ := x.bound
  have hcx : cx = fun k => CMRA.core (x.car k) := (Option.some.inj hpc).symm
  refine ⟨N, fun k hk => ?_⟩
  rw [hcx]
  simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]

theorem extend_bound {n : Nat} {x : GenMap β}
    {y1 y2 : Nat → Option β} (Hv : ✓{n} x.car) (He : x.car ≡{n}≡ y1 • y2) :
    let F k := CMRA.extend (Hv k) (He k)
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).1) k = none) ∧
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).2.1) k = none) := by
  obtain ⟨N, hN⟩ := x.bound
  have aux : ∀ k, N ≤ k → ∀ (z₁ z₂ : Option β),
      x.car k ≡ z₁ • z₂ → z₁ = none ∧ z₂ = none := by
    intro k hk z₁ z₂ hp1
    have _ : none ≡ z₁ • z₂ := (hN k hk) ▸ hp1
    cases z₁ <;> cases z₂ <;> simp_all [CMRA.op, optionOp, OFE.Equiv, Option.Forall₂]
  constructor
  · exact ⟨N, fun k hk => (aux k hk _ _ (CMRA.extend (Hv k) (He k)).2.2.1).1⟩
  · exact ⟨N, fun k hk => (aux k hk _ _ (CMRA.extend (Hv k) (He k)).2.2.1).2⟩

def pcore_genmap (x : GenMap β) : Option (GenMap β) :=
  some ⟨fun k => CMRA.core (x.car k), by
    obtain ⟨N, hN⟩ := x.bound
    refine ⟨N, fun k hk => ?_⟩
    simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]⟩

instance instCMRA_GenMap : CMRA (GenMap β) where
  pcore := pcore_genmap β
  op x y := ⟨x.car • y.car, op_bound β x y⟩
  ValidN n x := ✓{n} x.car
  Valid x := ✓ x.car
  op_ne.ne {_ _ _} H := op_ne (α := Nat → Option β) |>.ne H
  pcore_ne {n x y cx} H Hm := by
    refine ⟨⟨fun k => CMRA.core (y.car k), ?_⟩, by simp [pcore_genmap], fun k => ?_⟩
    · obtain ⟨N, hN⟩ := y.bound
      exact ⟨N, fun k hk => by simp [CMRA.core, CMRA.pcore, optionCore, hN k hk]⟩
    · suffices hcx : cx.car = fun k => CMRA.core (x.car k) by rw [hcx]; exact (H k).core
      simp only [pcore_genmap, Option.some.injEq] at Hm
      exact (congrArg GenMap.car Hm).symm
  validN_ne {n x y H} := Dist.validN H |>.mp
  valid_iff_validN {x} :=
    ⟨fun Hv n => Hv.validN, fun H => valid_iff_validN.mpr (H ·)⟩
  validN_succ {x n} := validN_succ
  validN_op_left {n x y} := validN_op_left
  assoc {x y z} a := by
    cases _ : x.car a <;> cases _ : y.car a <;> cases _ : z.car a <;>
      simp_all [op, OFE.Equiv, Option.Forall₂, optionOp]
    exact assoc
  comm {x y} a := by
    cases _ : x.car a <;> cases _ : y.car a <;>
      simp_all [op, OFE.Equiv, Option.Forall₂, optionOp]
    exact comm
  pcore_op_left {x cx} H := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    intro k
    have H : cx.car k = CMRA.core (x.car k) := congrFun hcx k
    simp only [CMRA.op, optionOp, H]
    exact core_op (x.car k)
  pcore_idem {x cx} H := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    simp only [pcore_genmap, OFE.Equiv, Option.Forall₂]
    intro k
    have H : cx.car k = CMRA.core (x.car k) := congrFun hcx k
    simp only [H]
    exact core_idem (x.car k)
  pcore_op_mono {x cx} H y := by
    have hcx : cx.car = fun k => CMRA.core (x.car k) := by
      simp [pcore_genmap] at H; exact (congrArg GenMap.car H).symm
    have hpc_fun : CMRA.pcore x.car = some cx.car := by rw [hcx]; rfl
    obtain ⟨cy, Hcy⟩ := pcore_op_mono hpc_fun y.car
    refine ⟨⟨cy, ?_⟩, ?_⟩
    · obtain ⟨N, hN⟩ := op_bound β x y
      refine ⟨N, fun k hk => ?_⟩
      have hxyk := hN k hk
      simp [CMRA.op, optionOp] at hxyk
      cases hx : x.car k <;> cases hy : y.car k <;> simp_all
      have hcxy : CMRA.core (x.car • y.car) k = none := by
        simp [CMRA.core, CMRA.pcore, optionCore, hx, hy, CMRA.op, optionOp]
      have hHeqk := Hcy k
      simp only [CMRA.core, CMRA.pcore, optionCore, CMRA.op, optionOp,
        hx, hy, Option.bind] at hHeqk
      cases hcy : cy k <;> simp_all
    · intro k
      have hHeqk := Hcy k
      simp [CMRA.core, CMRA.pcore, optionCore, CMRA.op, optionOp] at hHeqk ⊢
      exact hHeqk
  extend {n x y1 y2} := by
    intro Hv H
    have eb := extend_bound β Hv H
    let F k := CMRA.extend (Hv k) (H k)
    exact ⟨⟨fun k => (F k).1, eb.1⟩, ⟨fun k => (F k).2.1, eb.2⟩,
      fun k => (F k).2.2.1, fun k => (F k).2.2.2.1, fun k => (F k).2.2.2.2⟩

instance instUCMRA_GenMap : UCMRA (GenMap β) where
  unit := GenMap.empty
  unit_valid _ := trivial
  unit_left_id {x} k := by
    simp only [CMRA.op, optionOp, empty]
    cases x.car k <;> simp [OFE.Equiv, Option.Forall₂]
  pcore_unit k := by
    simp [OFE.Equiv, Option.Forall₂, empty, CMRA.core, CMRA.pcore, optionCore]

instance : IsTotal (GenMap β) := unit_total

theorem GenMap.alter_valid {g : GenMap β} (Hb : ✓{n} b) (Hg : ✓{n} g) :
    ✓{n} g.alter a b := by
  intro k
  simp only [GenMap.alter, Iris.alter]
  split
  · exact Hb
  · exact Hg k

theorem GenMap.valid_exists_fresh {g : GenMap β} (_Hv : ✓{n} g) : ∃ a : Nat, g.car a = none :=
  g.exists_fresh

theorem GenMap.singleton_map_op (x : Nat) (y1 y2 : β) :
    (singleton x y1 : GenMap β) • singleton x y2 = singleton x (y1 • y2) := by
  apply GenMap.ext
  funext γ
  simp only [CMRA.op, optionOp]
  by_cases h : γ = x
  · subst h; simp [singleton, empty, alter, Iris.alter]
  · simp only [singleton, empty, alter, Iris.alter]
    have : x ≠ γ := Ne.symm h
    simp [if_neg this]

theorem GenMap.singleton_map_pcore (x : Nat) (y : β) (γ : Nat) :
    ((singleton x y : GenMap β).car γ).bind pcore =
    if γ = x then pcore y else none := by
  by_cases h : γ = x
  · subst h
    simp [singleton_map_in]
  · simp_all [singleton_map_none h]

theorem GenMap.validN_singleton_map_in (x : Nat) (y : β) (n : Nat) :
    ✓{n} (singleton x y).car x → ✓{n} y := by
  rw [singleton_map_in]
  simp [ValidN, optionValidN]

theorem GenMap.op_singleton_comm {mf : GenMap β} {x : Nat} (y : β)
    (H_free : IsFree mf.car x) :
    GenMap.singleton x y • mf ≡ mf.alter x (some y) := by
  intro k
  simp only [IsFree] at H_free
  by_cases heq : k = x
  · subst heq
    simp only [CMRA.op, optionOp, alter, Iris.alter, singleton, empty, ↓reduceIte]
    rw [H_free]
  · simp only [CMRA.op, optionOp, alter, Iris.alter, singleton, empty]
    have : x ≠ k := Ne.symm heq
    rw [if_neg this, if_neg this]

theorem GenMap.validN_op_comm {m mf : GenMap β} (x : Nat) (y : β) (H : IsFree mf.car x) :
    ✓{n} m.alter x (some y) • mf ↔ ✓{n} (m • mf).alter x (some y) := by
  apply Dist.validN
  intro k
  simp only [IsFree] at H
  by_cases heq : k = x
  · subst heq
    simp only [CMRA.op, alter, Iris.alter, ↓reduceIte, optionOp]
    rw [H]
  · simp only [CMRA.op, alter, Iris.alter]
    have : x ≠ k := Ne.symm heq
    rw [if_neg this, if_neg this]

end CMRA

/-! ## OFunctors -/

section OFunctors
open COFE CMRA

abbrev GenMapOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => GenMap (F A B)

abbrev GenMap.lift [OFE α] [OFE β] (f : α -n> β) : GenMap α -n> GenMap β where
  f g := ⟨fun t => Option.map f (g.car t), by
    obtain ⟨N, hN⟩ := g.bound
    exact ⟨N, fun k hk => by simp [Option.map, hN k hk]⟩⟩
  ne.ne {n x1 x2} H γ := by
    specialize H γ
    simp [Option.map]
    split <;> split <;> simp_all
    exact NonExpansive.ne H

instance instOFunctor_GenMapOF (F : OFunctorPre) [OFunctor F] :
    OFunctor (GenMapOF F) where
  cofe {A B _ _} := instOFE_GenMap (F A B)
  map f₁ f₂ := GenMap.lift <| OFunctor.map (F := F) f₁ f₂
  map_ne.ne {n x1 x2} Hx {y1 y2} Hy k γ := by
    simp only [OFE.Dist, Option.Forall₂, Option.map]
    cases _ : k.car γ <;> simp
    exact OFunctor.map_ne.ne Hx Hy _
  map_id {α β _ _} x γ := by
    simp only [Option.map]; cases _ : x.car γ <;> simp [OFunctor.map_id]
  map_comp _ _ _ _ x γ := by
    simp only [Option.map]; cases _ : x.car γ <;> simp [OFunctor.map_comp]

instance instURFunctor_GenMapOF (F : COFE.OFunctorPre) [RFunctor F] :
    URFunctor (GenMapOF F) where
  map f g := {
    toHom := GenMap.lift <| OFunctor.map f g
    validN {n x} hv z := by
      cases h : x.car z with
      | none => simp [Option.map, h, CMRA.ValidN, optionValidN]
      | some v =>
        simp only [Option.map, CMRA.ValidN, optionValidN, h]
        have Hvalid := @(URFunctor.map (F := OptionOF F) f g).validN n v
        simp only [CMRA.ValidN, optionValidN, URFunctor.map] at Hvalid
        have hv' := hv z
        simp only [h, CMRA.ValidN, optionValidN] at hv'
        exact Hvalid hv'
    pcore x γ := by
      have Hcore := @(URFunctor.map (F := OptionOF F) f g).pcore (x.car γ)
      simp only [CMRA.pcore, optionCore, Option.bind, Option.map, URFunctor.map,
                 OFunctor.map, optionMap, CMRA.core] at Hcore ⊢
      cases h : x.car γ with
      | none => simp
      | some v =>
        simp only [h] at Hcore ⊢
        cases h' : pcore v <;> cases h'' : pcore ((OFunctor.map f g).f v) <;>
          simp_all [RFunctor.toOFunctor, OFE.Equiv, Option.Forall₂]
    op z x γ := by
      have Hop := @(URFunctor.map (F := OptionOF F) f g).op (z.car γ) (x.car γ)
      simp only [Option.map, RFunctor.toOFunctor, CMRA.op, optionOp, URFunctor.map] at Hop ⊢
      cases h : z.car γ <;> cases h' : x.car γ <;>
        simp_all [OFunctor.map, optionMap, OFE.Equiv, Option.Forall₂]
  }
  map_ne.ne := OFunctor.map_ne.ne
  map_id := OFunctor.map_id
  map_comp := OFunctor.map_comp

instance instURFunctorContractive_GenMapOF (F : COFE.OFunctorPre) [RFunctorContractive F] :
    URFunctorContractive (GenMapOF F) where
  map_contractive.1 h x γ := by
    next n x' y' =>
    have Heqv := @(URFunctorContractive.map_contractive (F := OptionOF F)).1 _ x' y' h (x.car γ)
    simp only [Function.uncurry, URFunctor.map, Option.map] at Heqv ⊢
    cases hc : x.car γ <;> simp [OFE.Dist, Option.Forall₂]
    rw [hc] at Heqv
    exact Heqv

end OFunctors

end GenMap

end Iris
