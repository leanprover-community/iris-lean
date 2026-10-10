/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Iris.Std.Positives
public import Iris.Std.CoPset
public import Iris.Std.PartialMap
public import Iris.Algebra.CMRA
public import Iris.Algebra.Heap
public import Iris.Algebra.IsOp
public import Iris.Algebra.Updates
public import Iris.Algebra.LeibnizSet

namespace Iris

variable {SI : stepindex (Type _)} [instSI : SIdx SI]
local stepindex SI

@[expose] public section

open Iris Iris.Std PartialMap

/-!
The camera [ReservationMap A H] over a camera [A] extends [LawfulPartialMap H Pos]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : CoPset] which represent the right to allocate a map entry at any position
[k ∈ E]. The key connectives are [ReservationMap.singleton k a] (the "points-to"
assertion of this map), which associates data [a : A] with a key [k : Pos],
and [ReservationMap.token E] (the reservation token), which says
that no data has been associated with the indices in the mask [E]. The important
properties of this camera are:

• The lemma [ReservationMap.token_union] enables one to split [ReservationMap.token]
  w.r.t. disjoint union. That is, if we have [E1 ## E2], then we get
  [ReservationMap.token (E1 ∪ E2) = ReservationMap.token E1 • ReservationMap.token E2].
• The lemma [ReservationMap.alloc] provides a frame preserving update to
  associate data to a key: [ReservationMap.token E ~~> ReservationMap.data k a]
  provided [k ∈ E] and [✓ a].

NOTE: The keys type is currently fixed to be [Pos], though should be generalized
in the future.
-/

@[ext, rocq_alias reservation_map]
structure ReservationMap (A : Type) (H : Type → Type) where
  data : H A
  token : CoPsetDisjL

def ReservationMap.mkData (data : H A) :
    ReservationMap A H := .mk data ∅

@[rocq_alias reservation_map_data]
def ReservationMap.singleton [LawfulPartialMap H Pos] (k : Pos) (a : A) :
    ReservationMap A H := ReservationMap.mkData {[k := a]}

@[rocq_alias reservation_map_token]
def ReservationMap.mkToken [LawfulPartialMap H Pos] (e : CoPset) :
    ReservationMap A H := .mk ∅ (.valid e)

section OFE

open OFE

variable [LawfulPartialMap H Pos] [OFE A]

#rocq_ignore reservation_map_ofe_mixin "Not needed"
#rocq_ignore reservation_map_equiv "Part of OFE instance"
#rocq_ignore reservation_map_dist "Part of OFE instance"

@[rocq_alias reservation_mapO]
instance : OFE (ReservationMap A H) where
  dist n x y := x.data ≡{n}≡ y.data ∧ x.token ≡{n}≡ y.token
  dist_eqv := {
    refl _ := And.intro .rfl rfl,
    symm h := And.intro h.left.symm h.right.symm,
    trans h₁ h₂ := And.intro (h₁.left.trans h₂.left) (h₁.right.trans h₂.right)
  }
  eq_dist' {x y} := by
    refine ⟨fun h _ => h ▸ ⟨.rfl, .rfl⟩, fun H => ?_⟩
    obtain ⟨xd, xt⟩ := x; obtain ⟨yd, yt⟩ := y
    simp only [ReservationMap.mk.injEq]
    exact ⟨eq_dist_2 fun n => (H n).1, eq_dist_2 fun n => (H n).2⟩
  dist_lt h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

@[rocq_alias reservation_map_ofe_discrete]
instance instDiscreteReservationMap [Discrete A] : Discrete (ReservationMap A H) where
  discrete_0 h := ReservationMap.ext (discrete_0 h.left) (discrete_0 h.right)

instance instNonExpansiveReservationMapData :
    NonExpansive (ReservationMap.mkData (H := H) (A := A)) where
  ne _ _ _ h := ⟨h, rfl⟩

@[rocq_alias ReservationMap_ne]
instance instNonExpansive₂ReservationMapMk :
    NonExpansive₂ (ReservationMap.mk (H := H) (A := A)) where
  ne _ _ _ hd _ _ ht := ⟨hd, ht⟩

@[rocq_alias reservation_map_data_proj_ne]
instance instNonExpansiveReservationMapDataProj :
    NonExpansive (ReservationMap.data (H := H) (A := A)) where
  ne _ _ _ h := h.left

#rocq_ignore ReservationMap_proper "Derivable using NonExpansive.eqv"
#rocq_ignore reservation_map_data_proj_proper "Derivable using NonExpansive.eqv"

#rocq_ignore reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias reservation_map_data_ne]
instance instNonExpansiveReservationMapSingleton :
    NonExpansive (ReservationMap.singleton (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, rfl⟩

@[rocq_alias ReservationMap_discrete]
instance instDiscreteEReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (ReservationMap.mk a b) where
  discrete h := ReservationMap.ext (DiscreteE.discrete h.1) (DiscreteE.discrete h.2)

@[rocq_alias reservation_map_data_discrete]
instance instDiscreteEReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (ReservationMap.singleton (H := H) k a) :=
  by unfold ReservationMap.singleton ReservationMap.mkData;  infer_instance

@[rocq_alias reservation_map_token_discrete]
instance instDiscreteEReservationMapToken :
    DiscreteE (ReservationMap.mkToken (H := H) (A := A) e) :=
  by unfold ReservationMap.mkToken; infer_instance

end OFE

section ORA

open OFE ORA DisjointLeibnizSet

namespace ReservationMap

variable [LawfulPartialMap H Pos]

@[rocq_alias reservation_map_pcore_instance]
def core [PCore A] (x : ReservationMap A H) : ReservationMap A H := mk (PCore.core x.data) ∅

@[simp]
theorem core_data [PCore A] (x : ReservationMap A H) : x.core.data = PCore.core x.data := rfl

@[simp]
theorem core_token [PCore A] (x : ReservationMap A H) : x.core.token = ∅ := rfl

@[rocq_alias reservation_map_op_instance]
def op [Op A] [Op CoPsetDisjL] (x y : ReservationMap A H) : ReservationMap A H :=
  mk (x.data • y.data) (x.token • y.token)

@[reducible] instance raOp [Op A] [Op CoPsetDisjL] : Op (ReservationMap A H) where
  op := op
  assoc := ReservationMap.ext Op.assoc Op.assoc
  comm := ReservationMap.ext Op.comm Op.comm

@[reducible] instance raPCore [PCore A] : PCore (ReservationMap A H) where
  pcore x := some x.core
  pcore_idem {x _} h := by
    cases Option.some_inj.mp h
    cases e : PCore.pcore x.data
    · simp [core, PCore.core, e]
    · simp [core, PCore.core, e, PCore.pcore_idem e]

@[simp]
theorem op_data [Op A] [Op CoPsetDisjL] (x y : ReservationMap A H) : (x • y).data = x.data • y.data := rfl

@[simp]
theorem op_token [Op A] [Op CoPsetDisjL] (x y : ReservationMap A H) : (x • y).token = x.token • y.token := rfl

instance raRA [RA A] : RA (ReservationMap A H) where
  pcore_op_left {x _} h := by
    cases h
    exact ReservationMap.ext (core_op x.data) (pcore_op_left' (x := x.token) rfl)

instance raURA [RA A] : URA (ReservationMap A H) where
  unit := mk ∅ ∅
  unit_left_id {x} := ReservationMap.ext
    (Algebra.MonoidOps.op_left_id : (∅ : H A) • x.data = x.data) (pcore_op_left' rfl)
  pcore_unit := congrArg some (ReservationMap.ext Heap.core_empty rfl)
  total _ := ⟨_, rfl⟩

variable [RA A] [ORA A]

@[rocq_alias reservation_map_validN_instance]
def ValidN (n : SI) (x : ReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓{n} x.data ∧ ∀i, get? x.data i = none ∨ i ∉ e
  | .error => False

@[indexed, rocq_alias reservation_map_valid_instance]
def Valid (x : ReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓ x.data ∧ ∀i, get? x.data i = none ∨ i ∉ e
  | .error => False

#rocq_ignore reservation_map_valid_eq "Definitional unfolding of Valid"
#rocq_ignore reservation_map_validN_eq "Definitional unfolding of ValidN"

theorem validN_iff {n : SI} {x : ReservationMap A H} :
    x.ValidN n ↔ ✓{n} x.data ∧ ✓{n} x.token ∧ ∀ i, get? x.data i = none ∨ i ∉ x.token := by
  refine ⟨fun h => ?_, fun ⟨vd, vt, disj⟩ => ?_⟩
  · simp only [ValidN] at h
    exact match eq : x.token with
    | .valid s => ⟨(eq ▸ h).left, (valid_0_iff_validN n).mp trivial, (eq ▸ h).right⟩
    | .error => (eq ▸ h).elim
  · simp only [ValidN]
    cases h : x.token
    · simp only [h] at disj
      exact ⟨vd, disj⟩
    · exact ((h ▸ not_valid_invalid (SI := SI) (S := CoPset)) vt)

theorem valid_iff {x : ReservationMap A H} :
    x.Valid (SI := SI) ↔ ✓[SI] x.data ∧ ✓[SI] x.token ∧ ∀ i, get? x.data i = none ∨ i ∉ x.token := by
  refine ⟨fun h => ?_, fun ⟨vd, vt, disj⟩ => ?_⟩
  · simp only [Valid] at h
    exact match eq : x.token with
    | .valid s => ⟨(eq ▸ h).left, valid_mapN (fun n a => a) trivial, (eq ▸ h).right⟩
    | .error => (eq ▸ h).elim
  · simp only [Valid]
    cases h : x.token
    · simp only [h] at disj
      exact ⟨vd, disj⟩
    · exact ((h ▸ not_valid_invalid (S := CoPset)) vt)

@[rocq_alias reservation_map_data_proj_validN]
theorem validN_data_of_validN {n : SI} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.data := (validN_iff.mp h).left

@[rocq_alias reservation_map_token_proj_validN]
theorem validN_token_of_validN {n : SI} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.token := (validN_iff.mp h).right.left

theorem validN_disj {n : SI} {x : ReservationMap A H} (h : x.ValidN n) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (validN_iff.mp h).right.right i

theorem valid_data_of_valid {x : ReservationMap A H} (h : x.Valid (SI := SI)) :
    ✓ x.data := (valid_iff.mp h).left

theorem valid_token_of_valid {x : ReservationMap A H} (h : x.Valid (SI := SI)) :
    ✓ x.token := (valid_iff.mp h).right.left

theorem valid_disj {x : ReservationMap A H} (h : x.Valid (SI := SI)) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (valid_iff.mp h).right.right i

theorem validN_mono {n : SI} {x y : ReservationMap A H} (hd : ✓{n} y.data → ✓{n} x.data)
    (hdom : ∀ i, get? y.data i = none → get? x.data i = none) (ht : ∃ w, y.token = x.token • w)
    (v : y.ValidN n) : x.ValidN n := by
  obtain ⟨w, hw⟩ := ht
  have vt : ✓{n} (x.token • w) := hw ▸ validN_token_of_validN v
  refine validN_iff.mpr ⟨hd (validN_data_of_validN v), validN_op_left vt,
    fun i => (validN_disj v i).imp (hdom i) fun hy hx => hy ?_⟩
  exact hw ▸ (mem_iff_of_validN_union vt i).mpr (.inl hx)

#rocq_ignore reservation_map_cmra_mixin "Not needed"
#rocq_ignore reservation_map_ucmra_mixin "Not needed"
#rocq_ignore reservation_mapR "Derivable using UCMRA"

@[reducible] def raValid : _root_.Iris.Valid SI (ReservationMap A H) where
  Valid := Valid (SI := SI)
  ValidN := ValidN
  valid_iff_validN {x} := by
    refine ⟨fun h n => ?_, fun v => ?_⟩
    · refine validN_iff.mpr ⟨?_, ?_, ?_⟩
      · exact Valid.validN (valid_data_of_valid h)
      · exact (valid_0_iff_validN n).mp (valid_token_of_valid h)
      · exact valid_disj h
    · refine valid_iff.mpr ⟨?_, ?_, ?_⟩
      · exact valid_iff_validN.mpr (fun n => validN_data_of_validN (v n))
      · exact valid_iff_validN.mpr (fun n => validN_token_of_validN (v n))
      · exact validN_disj (v 0)

@[reducible] def raOrdered : Ordered SI (ReservationMap A H) where
  OrderN n x y := x.data ≼ₒ{n} y.data ∧ x.token ≼ₒ{n} y.token
  Order x y := x.data ≼ₒ y.data ∧ x.token ≼ₒ y.token
  ordN_trans h1 h2 := ⟨ordN_trans h1.1 h2.1, ordN_trans h1.2 h2.2⟩
  ord_trans h1 h2 := ⟨ord_trans h1.1 h2.1, ord_trans h1.2 h2.2⟩
  ordN_of_ord n h := ⟨ordN_of_ord n h.1, ordN_of_ord n h.2⟩

attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE (ReservationMap A H) where
  ordN_ne ex ey h := ⟨ordN_ne ex.1 ey.1 h.1, ordN_ne ex.2 ey.2 h.2⟩
  ordN_le h le := ⟨ordN_le h.1 le, ordN_le h.2 le⟩

section
attribute [local instance] raOrdered raValid raOrderedNE

theorem increasing_data {v : ReservationMap A H} (h : Increasing v) : Increasing v.data where
  increasing w := (h.increasing (mk w ∅)).1

theorem increasing_token {v : ReservationMap A H} (h : Increasing v) : Increasing v.token where
  increasing w := (h.increasing (mk ∅ w)).2

theorem increasing_mk {v : ReservationMap A H}
    (hd : Increasing v.data) (ht : Increasing v.token) : Increasing v where
  increasing w := ⟨hd.increasing w.data, ht.increasing w.token⟩

open ReservationMap in
instance instORAReservationMap : ORA (ReservationMap A H) where
  toValid := raValid
  op_ne := ⟨fun _ _ _ h => ⟨Dist.op_r h.left, Dist.op_r h.right⟩⟩
  pcore_ne {n : SI} {x y cx} e pe := by
    cases Option.some_inj.mp pe.symm
    refine ⟨_, rfl, ?_, .rfl⟩
    simp [Dist.core e.left]
  validN_ne {n : SI} {x y} h v := by
    refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
    · exact (Dist.validN h.left).mp (validN_data_of_validN v)
    · exact (Dist.validN h.right).mp (validN_token_of_validN v)
    · cases (validN_disj v) i with
      | inl gn =>
        refine .inl <| ?_
        rw [←dist_none (n := n)]
        refine .trans (h.left i).symm ?_
        simp [gn]
      | inr ni =>
        refine .inr fun hc => ni ?_
        rw [congrFun ((congrArg Membership.mem h.right)) i]
        exact hc
  validN_le {n n' : SI} {x} v hle := by
    refine validN_iff.mpr ⟨?_, ?_, ?_⟩
    · exact validN_le (validN_data_of_validN v) hle
    · exact (valid_0_iff_validN n').mp ((valid_0_iff_validN n).mpr (validN_token_of_validN v))
    · exact validN_disj v
  toOrderedNE := raOrderedNE
  validN_op_left {_ x y} := validN_mono validN_op_left
    (fun _ h => Option.eq_none_of_op_eq_none_left ((Heap.get?_op _ _).symm.trans h)) ⟨y.token, rfl⟩
  extend {n : SI} {x y₁ y₂} v exy := by
    obtain ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := extend (validN_data_of_validN v) exy.left
    exact ⟨mk z₁ y₁.token, mk z₂ y₂.token, ReservationMap.ext xzz exy.right,
      And.intro zy₁ rfl, And.intro zy₂ rfl⟩
  toOrdered := raOrdered
  op_monoN_left_ord z h := ⟨op_monoN_left_ord z.data h.1, op_monoN_left_ord z.token h.2⟩
  op_mono_left_ord z h := ⟨op_mono_left_ord z.data h.1, op_mono_left_ord z.token h.2⟩
  validN_of_ordN h := validN_mono (validN_of_ordN h.1)
    (fun i hi => Option.eq_none_of_ordN_none (hi ▸ h.1 i)) h.2
  pcore_monoN_ord | h, rfl => ⟨_, rfl, core_ordN_core h.1, core_ordN_core h.2⟩
  pcore_mono_ord | h, rfl => ⟨_, rfl, core_mono_ord h.1, core_mono_ord h.2⟩
  pcore_order_op {x _} e y := by
    cases Option.some_inj.mp e
    exact ⟨_, rfl, core_op_mono_ord x.data y.data, core_op_mono_ord x.token y.token⟩
  pcore_increasing {x _} e := by
    cases Option.some_inj.mp e
    exact increasing_mk (v := x.core) (increasing_core x.data) (increasing_core x.token)
  increasing_closed {n : SI} {x y} h h' :=
    increasing_mk
      (increasing_closed (increasing_data h) (Or.imp (·.1) (·.1) h'))
      (increasing_closed (increasing_token h) (Or.imp (·.2) (·.2) h'))
  ordN_extend {n : SI} {sn} {x y} hs v h := by
    obtain ⟨zd, hzd, ed⟩ := ordN_extend hs (validN_data_of_validN v) h.1
    obtain ⟨zt, hzt, et⟩ := ordN_extend hs (validN_token_of_validN v) h.2
    exact ⟨mk zd zt, ⟨hzd, hzt⟩, ed, et⟩

end

instance instIncOrd [IncOrd A] : IncOrd (ReservationMap A H) := IncOrd.of_increasing fun v =>
    increasing_mk (IncOrd.increasing v.data) (IncOrd.increasing v.token)

@[rocq_alias reservation_mapUR]
instance : UORA (ReservationMap A H) where
  toORA := instORAReservationMap
  unit_valid := ⟨Heap.valid_empty, fun _ => .inr CoPset.mem_empty⟩
  ord_refl x := ⟨ord_refl x.data, ord_refl x.token⟩

@[rocq_alias reservation_map_included]
theorem inc_iff {x y : ReservationMap A H} :
    x ≼ y ↔ x.data ≼ y.data ∧ x.token ≼ y.token := by
  constructor
  · exact fun ⟨z, H⟩ => ⟨⟨z.data, H ▸ rfl⟩, ⟨z.token, H ▸ rfl⟩⟩
  · obtain ⟨yd, yt⟩ := y
    rintro ⟨⟨z₁, rfl⟩, ⟨z₂, rfl⟩⟩
    exact ⟨mk z₁ z₂, rfl⟩

theorem ord_iff {x y : ReservationMap A H} :
    x ≼ₒ y ↔ x.data ≼ₒ y.data ∧ x.token ≼ₒ y.token := .rfl

theorem ordN_iff {n : SI} {x y : ReservationMap A H} :
    x ≼ₒ{n} y ↔ x.data ≼ₒ{n} y.data ∧ x.token ≼ₒ{n} y.token := .rfl

instance instOrdInc [OrdInc A] : OrdInc (ReservationMap A H) where
  ord_inc h :=
    have : OrdInc (H A) := inferInstance
    inc_iff.mpr ⟨Iris.ord_inc h.1, Iris.ord_inc h.2⟩
  ordN_incN h :=
    have : OrdInc (H A) := inferInstance
    let ⟨z₁, h₁⟩ := Iris.ordN_incN h.1
    let ⟨z₂, h₂⟩ := Iris.ordN_incN h.2
    ⟨mk z₁ z₂, h₁, h₂⟩

instance instIsInc [IsInc A] : IsInc (ReservationMap A H) := {}

@[rocq_alias reservation_map_cmra_discrete]
instance [ORA.Discrete SI A] : ORA.Discrete SI (ReservationMap A H) where
  discrete_valid {_} v := by
    refine valid_iff.mpr ⟨?_, ?_, ?_⟩
    · exact discrete_valid (validN_data_of_validN v)
    · exact validN_token_of_validN v
    · exact validN_disj v
  discrete_ord h := ⟨fun k => discrete_ord (h.1 k), discrete_ord h.2⟩

#rocq_ignore reservation_map_empty_instance "Part of UCMRA instance"

@[rocq_alias reservation_map_data_core_id]
instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (singleton (H := H) k a) where
  core_id := congrArg some
    (ReservationMap.ext (core_eqv_self (PartialMap.singleton k a : H A)) rfl)

theorem split_valid {x : ReservationMap A H} (vx : ✓[SI] x) :
    ∃ (d : H A) (t : CoPset), x = mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  match hh : xt with
  | .error =>
    subst hh
    exact ((not_valid_invalid (S := CoPset)) (valid_token_of_valid vx)).elim
  | .valid t =>
    refine ⟨xd, t, ReservationMap.ext ?_ ?_⟩
    · exact (Heap.op_empty_right).symm
    · exact (pcore_op_left' rfl).symm

theorem split_validN {n : SI} {x : ReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x = mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  have H := validN_token_of_validN vx
  match hh : xt with
  | .error => subst hh; exact ((not_valid_invalid (SI := SI) (S := CoPset)) H).elim
  | .valid t =>
    refine ⟨xd, t, ReservationMap.ext ?_ ?_⟩
    · exact (Heap.op_empty_right).symm
    · exact (pcore_op_left' rfl).symm

theorem valid_data {d : H A} : ✓[SI] (mkData (H := H) d) ↔ ✓[SI] d :=
  ⟨valid_data_of_valid, fun h => valid_iff.mpr ⟨h, ⟨⟩, fun p => .inr (mem_empty p)⟩⟩

theorem validN_data {n : SI} {d : H A} : ✓{n} (mkData (H := H) d) ↔ ✓{n} d :=
  ⟨validN_data_of_validN, fun h => validN_iff.mpr ⟨h, ⟨⟩, (fun p => .inr (mem_empty p))⟩⟩

@[rocq_alias reservation_map_data_valid]
theorem valid_singleton (k : Pos) (a : A) : ✓ (singleton (H := H) k a) ↔ ✓ a :=
  (valid_data).trans Heap.singleton_valid_iff

theorem validN_singleton {n : SI} (k : Pos) (a : A) : ✓{n} (singleton (H := H) k a) ↔ ✓{n} a :=
  (validN_data).trans Heap.singleton_validN_iff

@[rocq_alias reservation_map_token_valid]
theorem valid_token : ✓ (mkToken (H := H) (A := A) e) :=
  ⟨Heap.valid_empty, fun i => .inl (get?_empty i)⟩

theorem data_op (a b : H A) : mkData (a • b) = mkData a • mkData b :=
  ReservationMap.ext rfl (pcore_op_left_L rfl).symm

@[rocq_alias reservation_map_data_op]
theorem singleton_op k (a b : A) :
    singleton (H := H) k (a • b) = singleton (H := H) k a • singleton k b := by
  exact (congrArg mkData Heap.singleton_op_singleton.symm).trans (data_op _ _)

theorem token_op (a b : CoPset) (h : a ## b) :
    mkToken (H := H) (A := A) (a ∪ b) = mkToken (H := H) (A := A) a • mkToken b := by
  refine ReservationMap.ext ?_ ?_
  · simp only [mkToken, op_data]
    exact Algebra.MonoidOps.op_left_id.symm
  · simp [mkToken, op, ORA.op, h]

theorem disj_of_validN_data_op_token {n : SI} {a : H A} {b : CoPset} (h : ✓{n} mkData a • mkToken b) (i : Pos) :
    get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [mkData, mkToken, op_data, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [mkData, mkToken, op_token] at h'
    rw [mem_iff_of_valid_union (SI := SI), not_or] at h'
    · exact .inr <| h'.right
    · exact ((pcore_op_left' rfl).symm : (_ : DisjointLeibnizSet CoPset) = _) ▸ valid_set

theorem disj_of_valid_data_op_token (a : H A) (b : CoPset) (h : ✓ mkData a • mkToken b) (i : Pos) :
  get? a i = none ∨ i ∉ b := disj_of_validN_data_op_token (h.validN (n := 0)) i

theorem validN_data_op_token {n : SI} (a : H A) (b : CoPset) (vd : ✓{n} mkData a)
    (disj : ∀ i, get? a i = none ∨ i ∉ b) : ✓{n} mkData a • mkToken b := by
  have abdp : (mkData a • mkToken b).data = a :=
    show a • ∅ = a from Algebra.MonoidOps.op_right_id
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
  · exact abdp.symm ▸ (validN_data).mp vd
  · simp [mkData, mkToken, eo, validN_set]
  · simp [mkData, mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa [h] using .inl <| rfl
    | inr h => simpa [eo] using .inr h

theorem valid_data_op_token (a : H A) (b : CoPset) (vd : ✓[SI] mkData a)
    (disj : ∀ i, get? a i = none ∨ i ∉ b) : ✓[SI] mkData a • mkToken b := by
  have abdp : (mkData a • mkToken b).data = a :=
    show a • ∅ = a from Algebra.MonoidOps.op_right_id
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine valid_iff.mpr ⟨?_, ?_, fun i => ?_⟩
  · exact abdp.symm ▸ (valid_data).mp vd
  · simp [op_token, mkData, mkToken, eo, valid_set]
  · simp only [mkData, mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa only [h] using .inl <| rfl
    | inr h => simpa only [eo] using .inr h

theorem singleton_mono_ord {k} {a b : A} (Hab : a ≼ₒ b) :
    singleton (H := H) k a ≼ₒ singleton k b :=
  ⟨Heap.singleton_ord_singleton_mono Hab, ord_refl _⟩

@[rocq_alias reservation_map_data_mono]
theorem singleton_mono {k} {a b : A} (Hab : a ≼ b) :
    singleton (H := H) k a ≼ singleton k b :=
  let ⟨z, hz⟩ := Hab
  ⟨singleton k z, (congrArg (singleton k) hz).trans (singleton_op k a z)⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias reservation_map_data_is_op]
instance {d : IsOp.Direction} {a b₁ b₂ : A} [hv : IsOp d a b₁ b₂] :
    IsOp d (singleton (H := H) k a) (singleton k b₁) (singleton k b₂) where
  is_op := (congrArg (singleton k) hv.is_op).trans (singleton_op k b₁ b₂)

@[rocq_alias reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂) :
    mkToken (H := H) (A := A) (e₁ ∪ e₂) = mkToken (H := H) (A := A) e₁ • mkToken e₂ := by
  refine ReservationMap.ext ?_ ?_
  · simp only [mkToken, op_data]
    exact Algebra.MonoidOps.op_left_id.symm
  · simp [mkToken, op, ORA.op, he]

@[rocq_alias reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    mkToken (H := H) (A := A) e₂ = mkToken (H := H) (A := A) e₁ • mkToken (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

@[rocq_alias reservation_map_token_valid_op]
theorem valid_token_op_iff_disj {e₁ e₂} :
    ✓[SI] (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔ e₁ ## e₂ :=
  ⟨fun h => valid_op_iff_disj.mp (valid_token_of_valid h),
   fun h => by rw [← token_union h]; exact valid_token⟩

theorem validN_token_op_iff_disj {n : SI} {e₁ e₂} :
    ✓{n} (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔ e₁ ## e₂ where
  mp h := (valid_op_iff_disj (SI := SI)).mp (validN_token_of_validN h)
  mpr h := by
    refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
    · change ✓{n} ∅ • (∅ : H A)
      rw [(Algebra.MonoidOps.op_left_id (a := (∅ : H A)) : (∅ : H A) • ∅ = ∅)]
      exact Heap.valid_empty.validN
    · simpa [ORA.op, mkToken, op, h] using validN_set
    · simpa [mkToken, op_data, op_token, Heap.get?_op, get?_empty] using .inl rfl

theorem valid_op?_of_valid_singleton_op {n : SI} {a : A} {x : H A} (h : ✓{n} (singleton k a • mkData x)) :
    ✓{n} a •? get? x k := by
  match h' : get? x k with
  | none => simpa [op?] using (validN_singleton (H := H) k a).mp (validN_op_left h)
  | some g =>
    simp only [op?]
    have vdp := (validN_data_of_validN h) k
    simp only [ORA.op, op, singleton, mkData, Heap.op, get?_merge, Option.merge,
      LawfulPartialMap.get?_singleton, ↓reduceIte, h'] at vdp
    exact vdp

theorem valid_singleton_op_of_valid_op? {n : SI} {a : A} {x : H A} (vx : ✓{n} x) (h : ✓{n} a •? get? x k) :
    ✓{n} singleton k a • mkData x := by
  refine (data_op (PartialMap.singleton k a) x) ▸ ?_
  refine (validN_data).mpr fun i => ?_
  rw [Heap.get?_op]
  by_cases ki : k = i
  · simp only [← ki, LawfulPartialMap.get?_singleton, ↓reduceIte, Option.some_op_opM]; exact h
  · simp only [LawfulPartialMap.get?_singleton, ki, ↓reduceIte]; exact Heap.validN_get? vx

@[rocq_alias reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a) :
    mkToken (H := H) e ~~> singleton k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_singleton k a).mpr va
  | some z =>
    have ⟨d, t, ze⟩ := split_validN (validN_op_right vo)
    have vedt : ✓{n} mkToken e • (mkData d • mkToken t) := ze ▸ vo
    have disj : ∀ (i : Pos), get? d i = none ∨ ¬i ∈ e :=
      disj_of_validN_data_op_token
        ((comm' (x := mkToken e) (y := mkData d)) ▸
          validN_op_left ((assoc' (x := mkToken e) (y := mkData d) (z := mkToken t)) ▸ vedt))
    change ✓{n} singleton k a • z
    rw [ze, assoc']
    refine (data_op (PartialMap.singleton k a) d) ▸ ?_
    refine validN_data_op_token (PartialMap.singleton k a • d) t ?_ ?_
    · refine (data_op (PartialMap.singleton k a) d) ▸ ?_
      apply valid_singleton_op_of_valid_op?
      · exact validN_data.mp (validN_op_left ((comm' (x := mkToken e) (y := mkData d)) ▸
          validN_op_left ((assoc' (x := mkToken e) (y := mkData d) (z := mkToken t)) ▸ vedt)))
      · exact (disj k).elim (fun h => h ▸ Valid.validN va) (absurd hke)
    · simp only [ORA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro i
      grind [disj_of_validN_data_op_token (ze ▸ validN_op_right vo),
        validN_token_op_iff_disj.mp (validN_op_right
          ((assoc' (x := mkData d) (y := mkToken t) (z := mkToken e)).symm ▸
            (comm' (x := mkToken e) (y := mkData d • mkToken t)) ▸ vedt)) i]

@[rocq_alias reservation_map_updateP]
theorem updateP {P} {Q : ReservationMap A H → Prop} k a (ap : a ~~>: P)
    (apq : ∀ a', P a' → Q (singleton k a')) : singleton k a ~~>: Q := by
  intro n mz vaz
  match mz with
  | none =>
    obtain ⟨y, py, vy⟩ := ap n none ((validN_singleton k a).mp vaz)
    exact ⟨_, (apq y py), (validN_singleton k y).mpr vy⟩
  | some z =>
    obtain ⟨d, t, ze⟩ := split_validN (validN_op_right vaz)
    obtain ⟨y, py, vy⟩ := ap n (get? d k)
      (valid_op?_of_valid_singleton_op
        (validN_op_left ((assoc' (x := singleton k a) (y := mkData d) (z := mkToken t)) ▸
          (ze ▸ vaz : ✓{n} singleton k a • (mkData d • mkToken t)))))
    refine ⟨singleton k y, apq y py, ?_⟩
    simp only [ORA.op?] at vaz ⊢
    rw [ze, assoc']
    refine (data_op (PartialMap.singleton k y) d) ▸ ?_
    refine validN_data_op_token _ _ ?_ ?_
    · refine (data_op (PartialMap.singleton k y) d) ▸ ?_
      refine valid_singleton_op_of_valid_op? ?_ vy
      refine validN_data.mp ?_
      exact validN_op_left <| ze ▸ validN_op_right vaz
    · have ddt := disj_of_validN_data_op_token (ze ▸ validN_op_right vaz)
      have dde := disj_of_validN_data_op_token
        (show ✓{n} singleton (H := H) k a • mkToken t from
          (comm' (α := ReservationMap A H)) ▸
            validN_op_right ((assoc' (α := ReservationMap A H)).symm ▸
              (comm' (α := ReservationMap A H)) ▸
                (ze ▸ vaz : ✓{n} singleton k a • (mkData d • mkToken t))))
      simp only [ORA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at ddt dde ⊢
      grind

@[rocq_alias reservation_map_update]
theorem reservation_map_update {k} {a b : A} (uab : a ~~> b) :
    singleton (H := H) k a ~~> singleton k b :=
  Update.of_updateP <| updateP k a (.of_update uab) fun _ => congrArg (singleton k)

end ReservationMap

end ORA

end

end Iris
