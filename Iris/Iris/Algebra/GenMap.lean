/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Janine Lohse
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates

@[expose] public section

namespace Iris

variable {SI : stepindex (Type _)} [instSI : SIdx SI]
local stepindex SI
open OFE

section GenMap

/-! ## GenMap

The OFE over gmaps is equivalent to a non-dependent discrete function to an `Option` type with a
OFE of keys, and a finite number of allocated elements.

In this setting, the ORA is always unital, and as a consequence the oFunctors do not require
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
  dist n := (·.car ≡{n}≡ ·.car)
  dist_eqv.refl _ := Dist.of_eq rfl
  dist_eqv.symm := Dist.symm
  dist_eqv.trans := Dist.trans
  eq_dist' {x y} := by
    refine ⟨fun h _ => h ▸ .rfl, fun h => ?_⟩
    obtain ⟨cx, bx⟩ := x; obtain ⟨cy, by'⟩ := y
    have : cx = cy := eq_dist_2 h
    subst this; rfl
  dist_lt := Dist.lt
end OFE

theorem GenMap.singleton_discreteE {v : β} [OFE β] [DiscreteE v] :
    DiscreteE (GenMap.singleton (β := β) k v) where
  discrete {y} H := OFE.eq_dist_2 <| by
    intro n γ'
    specialize H γ'
    simp only [GenMap.singleton, GenMap.alter, GenMap.empty, Iris.alter] at H ⊢
    split
    · next heq => simp only [heq, ite_true] at H ⊢; exact (Option.some_is_discrete.discrete H).dist
    · next hne => simp only [hne, ite_false] at H ⊢; exact (Option.none_is_discrete.discrete H).dist

theorem GenMap.empty_discreteE [OFE β] : DiscreteE (GenMap.empty (β := β)) where
  discrete {y} H := OFE.eq_dist_2 <| by
    intro n γ'
    specialize H γ'
    simp only [GenMap.empty] at H ⊢
    exact (Option.none_is_discrete.discrete H).dist

@[ext] theorem GenMap.ext {a b : GenMap β} (h : a.car = b.car) : a = b := by
  obtain ⟨ca, ba⟩ := a
  obtain ⟨cb, bb⟩ := b
  simp at h; subst h; rfl

theorem GenMap.alter_of_lookup {g : GenMap β} {x : Nat} {y : Option β} (h : g.car x = y) :
    g.alter x y = g :=
  GenMap.ext <| funext fun k => by
    simp only [alter, Iris.alter]
    grind

theorem GenMap.alter_alter (g : GenMap β) (x : Nat) (y y' : Option β) :
    (g.alter x y).alter x y' = g.alter x y' :=
  GenMap.ext <| funext fun _ => by simp only [alter, Iris.alter]; split <;> rfl

/-! ## ORA -/

section RAData
open GenMap PCore

section
variable (β : Type _) [Op β]

theorem op_bound (x y : GenMap β) :
    ∃ N, ∀ k, N ≤ k → (x.car • y.car) k = none := by
  obtain ⟨Nx, hx⟩ := x.bound
  obtain ⟨Ny, hy⟩ := y.bound
  refine ⟨max Nx Ny, fun k hk => ?_⟩
  simp [Op.op, optionOp, hx k (by omega), hy k (by omega)]

@[reducible] instance GenMap.raOp : Op (GenMap β) where
  op x y := ⟨x.car • y.car, op_bound β x y⟩
  assoc {_ _ _} := GenMap.ext Op.assoc
  comm {_ _} := GenMap.ext Op.comm
end

section
variable (β : Type _) [PCore β]

def pcore_genmap (x : GenMap β) : Option (GenMap β) := some ⟨fun k => core (x.car k), by
    obtain ⟨N, hN⟩ := x.bound
    refine ⟨N, fun k hk => ?_⟩
    simp [core, PCore.pcore, optionCore, hN k hk]⟩

@[reducible] instance GenMap.raPCore : PCore (GenMap β) where
  pcore := pcore_genmap β
  pcore_idem {x _} H := by
    obtain rfl := Option.some.inj H
    refine congrArg some (GenMap.ext (funext fun k => ?_))
    simp only [core, PCore.pcore, Option.getD_some, optionCore]
    rcases x.car k with _|a <;> simp
    rcases h : PCore.pcore a with _|b
    · simp
    · simp [PCore.pcore_idem h]
end

instance GenMap.instRA (β : Type _) [RA β] : RA (GenMap β) where
  pcore_op_left {x _} H := by
    obtain rfl := Option.some.inj H
    exact GenMap.ext (funext fun k => ORA.core_op (x.car k))

instance GenMap.instURA (β : Type _) [RA β] : URA (GenMap β) where
  unit := GenMap.empty
  unit_left_id {x} := GenMap.ext <| funext fun k => by
    change optionOp none (x.car k) = x.car k
    cases x.car k <;> rfl
  pcore_unit := rfl
  total _ := ⟨_, rfl⟩

end RAData

section ORA
open ORA GenMap


variable (β : Type _) [RA β] [ORA β]

theorem pcore_bound (x : GenMap β) (cx : Nat → Option β)
    (hpc : pcore x.car = some cx) :
    ∃ N, ∀ k, N ≤ k → cx k = none := by
  obtain ⟨N, hN⟩ := x.bound
  have hcx : cx = fun k => core (x.car k) := (Option.some.inj hpc).symm
  refine ⟨N, fun k hk => ?_⟩
  rw [hcx]
  simp [core, pcore, optionCore, hN k hk]

theorem extend_bound {n : SI} {x : GenMap β}
    {y1 y2 : Nat → Option β} (Hv : ✓{n} x.car) (He : x.car ≡{n}≡ y1 • y2) :
    let F k := extend (Hv k) (He k)
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).1) k = none) ∧
    (∃ N, ∀ k, N ≤ k → (fun k => (F k).2.1) k = none) := by
  obtain ⟨N, hN⟩ := x.bound
  have aux : ∀ k, N ≤ k → ∀ (z₁ z₂ : Option β),
      x.car k = z₁ • z₂ → z₁ = none ∧ z₂ = none := by
    intro k hk z₁ z₂ hp1
    have h : none = z₁ • z₂ := (hN k hk) ▸ hp1
    cases z₁ <;> cases z₂
    · exact ⟨rfl, rfl⟩
    all_goals exact absurd h (by simp [op, optionOp])
  constructor
  · exact ⟨N, fun k hk => (aux k hk _ _ (extend (Hv k) (He k)).2.2.1).1⟩
  · exact ⟨N, fun k hk => (aux k hk _ _ (extend (Hv k) (He k)).2.2.1).2⟩

@[reducible] def GenMap.raValid : _root_.Iris.Valid SI (GenMap β) where
  ValidN n x := ✓{n} x.car
  Valid x := ✓ x.car
  valid_iff_validN {_x} := ⟨fun Hv _ => Hv.validN, fun H => valid_iff_validN.mpr (H ·)⟩

@[reducible] def GenMap.raOrdered : Ordered SI (GenMap β) where
  OrderN n x y := x.car ≼ₒ{n} y.car
  Order x y := x.car ≼ₒ y.car
  ordN_trans := ordN_trans
  ord_trans := ord_trans
  ordN_of_ord n h := ordN_of_ord n h

attribute [local instance] GenMap.raOrdered in
theorem GenMap.raOrderedNE : OrderedNE (GenMap β) where
  ordN_ne {n x x' y y'} ex ey h :=
    show x'.car ≼ₒ{n} y'.car from ordN_ne (x := x.car) (y := y.car) ex ey h
  ordN_le h le := ordN_le (α := Nat → Option β) h le

section
attribute [local instance] GenMap.raValid GenMap.raOrdered
  GenMap.raOrderedNE

@[simp] theorem GenMap.op_car (x y : GenMap β) : (x • y).car = x.car • y.car := rfl

theorem GenMap.increasing_apply {x : GenMap β} (h : Increasing x) (k : Nat) :
    Increasing (x.car k) where
  increasing b := by
    simpa [alter, Iris.alter, DiscreteFun.op_apply] using h.increasing (empty.alter k b) k

theorem GenMap.increasing_car {x : GenMap β} (h : Increasing x) : Increasing x.car :=
  DiscreteFun.increasing_iff.mpr (increasing_apply β h)

theorem GenMap.increasing_of_car {x : GenMap β} (h : Increasing x.car) : Increasing x where
  increasing z := h.increasing z.car

instance instORA_GenMap : ORA (GenMap β) where
  toValid := GenMap.raValid β
  op_ne {x} := ⟨fun n y₁ y₂ H => by
    change (x.car • y₁.car) ≡{n}≡ (x.car • y₂.car)
    exact (op_ne (x := x.car)).ne (n := n) (x₁ := y₁.car) (x₂ := y₂.car) H⟩
  pcore_ne {n : SI} {x y cx} H Hm := by
    refine ⟨⟨fun k => core (y.car k), ?_⟩, by simp [PCore.pcore, pcore_genmap], fun k => ?_⟩
    · obtain ⟨N, hN⟩ := y.bound
      exact ⟨N, fun k hk => by simp [core, pcore, optionCore, hN k hk]⟩
    · suffices hcx : cx.car = fun k => core (x.car k) by rw [hcx]; exact (H k).core
      simp only [PCore.pcore, pcore_genmap, Option.some.injEq] at Hm
      exact (congrArg GenMap.car Hm).symm
  validN_ne {n : SI} {x y} H := (Dist.validN (n := n) (x := x.car) (y := y.car) H).mp
  validN_le {n n' : SI} {x} := validN_le (n := n) (n' := n') (x := x.car)
  toOrderedNE := GenMap.raOrderedNE β
  validN_op_left {n : SI} {x y} h := validN_op_left (n := n) (x := x.car) (y := y.car) h
  extend {n : SI} {x y1 y2} := by
    intro Hv H
    have eb := extend_bound β Hv H
    let F k := extend (Hv k) (H k)
    exact ⟨⟨fun k => (F k).1, eb.1⟩, ⟨fun k => (F k).2.1, eb.2⟩,
      OFE.eq_dist_2 fun _ k => ((F k).2.2.1).dist, fun k => (F k).2.2.2.1, fun k => (F k).2.2.2.2⟩
  toOrdered := GenMap.raOrdered β
  op_monoN_left_ord {n : SI} {x y} z h := op_monoN_left_ord (n := n) (x := x.car) (y := y.car) z.car h
  op_mono_left_ord z h := op_mono_left_ord (SI := SI) z.car h
  validN_of_ordN {n : SI} {x y} h v := validN_of_ordN (n := n) (x := x.car) (y := y.car) h v
  pcore_monoN_ord {_ x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_ordN_core (SI := SI) (x := x.car) (y := y.car) h⟩
  pcore_mono_ord {x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_mono_ord (SI := SI) (x := x.car) (y := y.car) h⟩
  pcore_order_op {x _} e y := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_op_mono_ord (SI := SI) x.car y.car⟩
  pcore_increasing {x _} e := by
    obtain rfl := Option.some.inj e
    exact increasing_of_car β (inferInstance : Increasing (core x.car))
  increasing_closed h h' := increasing_of_car β (increasing_closed (increasing_car β h) h')
  ordN_extend {n : SI} {sn} {x y} hs v h :=
    let ⟨z, hz, ez⟩ := ordN_extend (α := Nat → Option β) (n := n) (x := x.car) (y := y.car) hs v h
    let ⟨N, hN⟩ := x.bound
    ⟨⟨z, N, fun k hk => dist_none.mp (hN k hk ▸ ez k)⟩, hz, ez⟩

end

instance instUCMRA_GenMap : UORA (GenMap β) where
  toORA := instORA_GenMap β
  unit_valid := show ✓[SI] (GenMap.empty (β := β)).car from fun _ => trivial
  ord_refl x := show x.car ≼ₒ[SI] x.car from fun k => OrderRefl.ord_refl (SI := SI) (x.car k)

instance instIncOrdGenMap [IncOrd SI β] : IncOrd SI (GenMap β) :=
  IncOrd.of_increasing fun x => GenMap.increasing_of_car β (IncOrd.increasing x.car)

instance instOrdIncGenMap [OrdInc SI β] : OrdInc SI (GenMap β) where
  ord_inc {x y} h := by
    obtain ⟨z, hz⟩ := (inferInstance : OrdInc SI (Nat → Option β)).ord_inc
      (x := x.car) (y := y.car) h
    obtain ⟨N, hN⟩ := y.bound
    exact ⟨⟨z, N, fun k hk => Option.eq_none_of_op_eq_none_right ((congrFun hz k).symm.trans (hN k hk))⟩,
      GenMap.ext hz⟩
  ordN_incN {n : SI} {x y} h :=
    let ⟨z, hz⟩ := (inferInstance : OrdInc SI (Nat → Option β)).ordN_incN
      (n := n) (x := x.car) (y := y.car) h
    let ⟨N, hN⟩ := y.bound
    ⟨⟨z, N, fun k hk =>
      Option.eq_none_of_op_eq_none_right (dist_none.mp ((hz k).symm.trans (.of_eq (hN k hk))))⟩, hz⟩

instance instIsIncGenMap [IsInc β] : IsInc (GenMap β) := {}

theorem GenMap.singleton_ord_mono {x : Nat} {y y' : β} (h : y ≼ₒ[SI] y') :
    (singleton x y : GenMap β) ≼ₒ[SI] singleton x y' := fun x' => by
  by_cases hx : x' = x
  · subst hx; rw [singleton_map_in, singleton_map_in]; exact .inr h
  · rw [singleton_map_none hx, singleton_map_none hx]

theorem GenMap.alter_valid {n : SI} {g : GenMap β} (Hb : ✓{n} b) (Hg : ✓{n} g) :
    ✓{n} g.alter a b := by
  intro k
  simp only [GenMap.alter, Iris.alter]
  split
  · exact Hb
  · exact Hg k

theorem GenMap.valid_exists_fresh {n : SI} {g : GenMap β} (_Hv : ✓{n} g) : ∃ a : Nat, g.car a = none :=
  g.exists_fresh

theorem GenMap.singleton_map_op (x : Nat) (y1 y2 : β) :
    (singleton x y1 : GenMap β) • singleton x y2 = singleton x (y1 • y2) := by
  apply GenMap.ext
  funext γ
  simp only [op, optionOp]
  by_cases h : γ = x
  · subst h; simp [singleton, empty, alter, Iris.alter]
  · simp only [singleton, empty, alter, Iris.alter]
    have : x ≠ γ := Ne.symm h
    simp [ite_eq_right this]

theorem GenMap.singleton_map_pcore (x : Nat) (y : β) (γ : Nat) :
    ((singleton x y : GenMap β).car γ).bind pcore =
    if γ = x then pcore y else none := by
  by_cases h : γ = x
  · subst h
    simp [singleton_map_in]
  · simp_all [singleton_map_none h]

theorem GenMap.validN_singleton_map_in (x : Nat) (y : β) (n : SI) :
    ✓{n} (singleton x y).car x → ✓{n} y := by
  rw [singleton_map_in]
  simp [ValidN, optionValidN]

theorem GenMap.op_singleton_comm {mf : GenMap β} {x : Nat} (y : β)
    (H_free : IsFree mf.car x) :
    GenMap.singleton x y • mf = mf.alter x (some y) := by
  refine GenMap.ext (funext fun k => ?_)
  simp only [IsFree] at H_free
  by_cases heq : k = x
  · subst heq
    simp only [op, optionOp, alter, Iris.alter, singleton, empty, ↓reduceIte]
    simp [H_free]
  · simp only [op, optionOp, alter, Iris.alter, singleton, empty]
    have : x ≠ k := Ne.symm heq
    simp [ite_eq_right this]

theorem GenMap.singleton_op_alter_none {g : GenMap β} {x : Nat} {y : β} (h : g.car x = some y) :
    GenMap.singleton x y • g.alter x none = g := by
  rw [op_singleton_comm _ y (by simp [IsFree, alter, Iris.alter]), alter_alter,
    alter_of_lookup h]

theorem GenMap.validN_op_comm {n : SI} {m mf : GenMap β} (x : Nat) (y : β) (H : IsFree mf.car x) :
    ✓{n} m.alter x (some y) • mf ↔ ✓{n} (m • mf).alter x (some y) := by
  apply Dist.validN
  intro k
  simp only [IsFree] at H
  by_cases heq : k = x
  · subst heq
    simp only [op, alter, Iris.alter, ↓reduceIte, optionOp]
    simp [H]
  · simp only [op, alter, Iris.alter]
    have : x ≠ k := Ne.symm heq
    simp [ite_eq_right this]

end ORA

/-! ## OFunctors -/

section OFunctors
open COFE ORA

abbrev GenMapOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => GenMap (F A B)

abbrev GenMap.lift [OFE α] [OFE β] (f : α -n> β) : GenMap α -n> GenMap β where
  f g := ⟨fun t => Option.map f (g.car t), by
    obtain ⟨N, hN⟩ := g.bound
    exact ⟨N, fun k hk => by simp [Option.map, hN k hk]⟩⟩
  ne.ne {n : SI} {x1 x2} H γ := by
    specialize H γ
    simp [Option.map]
    split <;> split <;> simp_all
    exact NonExpansive.ne H

instance instOFunctor_GenMapOF (F : OFunctorPre) [OFunctor F] :
    OFunctor (GenMapOF F) where
  ofe {A B _ _} := instOFE_GenMap (F A B)
  map f₁ f₂ := GenMap.lift <| OFunctor.map (F := F) f₁ f₂
  map_ne.ne {n : SI} {x1 x2} Hx {y1 y2} Hy k γ := by
    simp only [OFE.Dist, Option.map]
    cases _ : k.car γ <;> simp
    exact OFunctor.map_ne.ne Hx Hy _
  map_id {α β _ _} x := OFE.eq_dist_2 <| by
    intro _ γ
    simp only [Option.map]; cases _ : x.car γ <;> simp
    exact (OFunctor.map_id _).dist
  map_comp _ _ _ _ x := OFE.eq_dist_2 <| by
    intro _ γ
    simp only [Option.map]; cases _ : x.car γ <;> simp
    exact (OFunctor.map_comp _ _ _ _ _).dist

instance instURFunctor_GenMapOF (F : COFE.OFunctorPre (SI := SI)) [RFunctor SI F] :
    URFunctor SI (GenMapOF F) where
  map f g := {
    toHom := GenMap.lift <| OFunctor.map f g
    validN {n : SI} {x} hv z := by
      cases h : x.car z with
      | none => simp [Option.map, h, ValidN, optionValidN]
      | some v =>
        simp only [Option.map, ValidN, optionValidN, h]
        have Hvalid := @(URFunctor.map (F := OptionOF F) f g).validN n v
        simp only [ValidN, optionValidN, URFunctor.map] at Hvalid
        have hv' := hv z
        simp only [h, ValidN, optionValidN] at hv'
        exact Hvalid hv'
    pcore x := OFE.eq_dist_2 (SI := SI) <| by
      intro _ γ
      have Hcore := @(URFunctor.map (F := OptionOF (SI := SI) F) f g).pcore (x.car γ)
      simp only [pcore, optionCore, Option.bind, Option.map, URFunctor.map,
                 OFunctor.map, core] at Hcore ⊢
      cases h : x.car γ with
      | none => simp
      | some v =>
        revert Hcore
        cases h' : pcore v <;> cases h'' : pcore ((OFunctor.map f g).f v) <;>
          simp_all [Option.mapC, optionMap]
    op z x := OFE.eq_dist_2 (SI := SI) <| by
      intro _ γ
      have Hop := @(URFunctor.map (F := OptionOF (SI := SI) F) f g).op (z.car γ) (x.car γ)
      simp only [Option.map, op, optionOp, URFunctor.map] at Hop ⊢
      cases h : z.car γ <;> cases h' : x.car γ <;> simp_all [OFunctor.map]
      exact ((RFunctor.map f g).op _ _).dist
    monoN_ord h t := (URFunctor.map (F := OptionOF (SI := SI) F) f g).monoN_ord (h t)
    mono_ord h t := (URFunctor.map (F := OptionOF (SI := SI) F) f g).mono_ord (h t)
    increasing h := GenMap.increasing_of_car _ <| DiscreteFun.increasing_iff.mpr fun t =>
        (URFunctor.map (F := OptionOF (SI := SI) F) f g).increasing (GenMap.increasing_apply _ h t)
  }
  map_ne.ne := OFunctor.map_ne.ne
  map_id x := OFunctor.map_id x
  map_comp f g f' g' x := OFunctor.map_comp f g f' g' x

instance instRFunctorAffineGenMapOF (F : COFE.OFunctorPre (SI := SI)) [RFunctor SI F] [RFunctorAffine SI F] :
    RFunctorAffine SI (GenMapOF F) where
  affine := inferInstance

instance instURFunctorContractive_GenMapOF (F : COFE.OFunctorPre (SI := SI)) [RFunctorContractive SI F] :
    URFunctorContractive SI (GenMapOF F) where
  map_contractive.1 h x γ := by
    next n x' y' =>
    have Heqv := @(URFunctorContractive.map_contractive (F := OptionOF F)).1 _ x' y' h (x.car γ)
    simp only [Function.uncurry, URFunctor.map, Option.map] at Heqv ⊢
    cases hc : x.car γ <;> simp [OFE.Dist]
    rw [hc] at Heqv
    exact Heqv

end OFunctors

end GenMap

end Iris
