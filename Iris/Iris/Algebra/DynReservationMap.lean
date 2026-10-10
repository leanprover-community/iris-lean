/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Janine Lohse
-/
module

public import Iris.Std.CoPset
public import Iris.Std.GenSets
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

open Iris.Std PartialMap

universe u v

/-!
The camera [DynReservationMap A H] over a camera [A] extends [LawfulPartialMap H Pos]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : CoPset] which represent the right to allocate a map entry at any position
[k ∈ E]. Unlike [ReservationMap], [DynReservationMap] supports dynamically
allocating these tokens, including infinite sets of them.
-/

@[ext, rocq_alias dyn_reservation_map]
structure DynReservationMap (A : Type u) (H : Type u → Type v) where
  data : H A
  token : DisjointLeibnizSet CoPset

variable {A : Type u} {H : Type u → Type v}

@[rocq_alias dyn_reservation_map_data]
def DynReservationMap.mkData [LawfulPartialMap H Pos] (k : Pos) (a : A) :
    DynReservationMap A H := .mk {[k := a]} ∅

@[rocq_alias dyn_reservation_map_token]
def DynReservationMap.mkToken [LawfulPartialMap H Pos] (e : CoPset) :
    DynReservationMap A H := .mk ∅ (.valid e)

#rocq_ignore to_reservation_map "OFE/CMRA are built directly, not via an isomorphism"
#rocq_ignore from_reservation_map "OFE/CMRA are built directly, not via an isomorphism"

section OFE

open OFE

variable [LawfulPartialMap H Pos] [OFE A]

#rocq_ignore dyn_reservation_map_ofe_mixin "Not needed"
#rocq_ignore dyn_reservation_map_equiv "Part of OFE instance"
#rocq_ignore dyn_reservation_map_dist "Part of OFE instance"

@[rocq_alias dyn_reservation_mapO]
instance : OFE (DynReservationMap A H) where
  dist n x y := x.data ≡{n}≡ y.data ∧ x.token ≡{n}≡ y.token
  dist_eqv := {
    refl _ := And.intro .rfl rfl,
    symm h := And.intro h.left.symm h.right.symm,
    trans h₁ h₂ := And.intro (h₁.left.trans h₂.left) (h₁.right.trans h₂.right)
  }
  eq_dist' {x y} := by
    refine ⟨fun h _ => h ▸ ⟨.rfl, .rfl⟩, fun H => ?_⟩
    exact DynReservationMap.ext (eq_dist_2 fun n => (H n).1) (eq_dist_2 fun n => (H n).2)
  dist_lt h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

@[rocq_alias dyn_reservation_map_ofe_discrete]
instance instDiscreteDynReservationMap [Discrete A] : Discrete (DynReservationMap A H) where
  discrete_0 h := DynReservationMap.ext (discrete_0 h.left) (discrete_0 h.right)

@[rocq_alias DynReservationMap_ne]
instance instNonExpansive₂DynReservationMapMk :
    NonExpansive₂ (DynReservationMap.mk (H := H) (A := A)) where
  ne _ _ _ hd _ _ ht := ⟨hd, ht⟩

@[rocq_alias dyn_reservation_map_data_proj_ne]
instance instNonExpansiveDynReservationMapDataProj :
    NonExpansive (DynReservationMap.data (H := H) (A := A)) where
  ne _ _ _ h := h.left

#rocq_ignore DynReservationMap_proper "Derivable using NonExpansive.eqv"
#rocq_ignore dyn_reservation_map_data_proj_proper "Derivable using NonExpansive.eqv"
#rocq_ignore dyn_reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias dyn_reservation_map_data_ne]
instance instNonExpansiveDynReservationMapSingleton :
    NonExpansive (DynReservationMap.mkData (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, rfl⟩

@[rocq_alias DynReservationMap_discrete]
instance instDiscreteEDynReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (DynReservationMap.mk a b) where
  discrete h := DynReservationMap.ext (DiscreteE.discrete h.1) (DiscreteE.discrete h.2)

@[rocq_alias dyn_reservation_map_data_discrete]
instance instDiscreteEDynReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (DynReservationMap.mkData (H := H) k a) :=
  by unfold DynReservationMap.mkData; infer_instance

@[rocq_alias dyn_reservation_map_token_discrete]
instance instDiscreteEDynReservationMapToken :
    DiscreteE (DynReservationMap.mkToken (H := H) (A := A) e) :=
  by unfold DynReservationMap.mkToken; infer_instance

end OFE

section ORA

open OFE ORA DisjointLeibnizSet LawfulSet

namespace DynReservationMap

section

variable [LawfulPartialMap H Pos]

def core [PCore A] (x : DynReservationMap A H) : DynReservationMap A H := mk (PCore.core x.data) ∅

#rocq_ignore dyn_reservation_map_pcore_instance "Use CMRA core instead"

@[simp]
theorem core_data [PCore A] (x : DynReservationMap A H) : x.core.data = PCore.core x.data := rfl

@[simp]
theorem core_token [PCore A] (x : DynReservationMap A H) : x.core.token = ∅ := rfl

@[rocq_alias dyn_reservation_map_op_instance]
def op [Op A] [Op CoPsetDisjL] (x y : DynReservationMap A H) : DynReservationMap A H :=
  mk (x.data • y.data) (x.token • y.token)

@[reducible] instance raOp [Op A] [Op CoPsetDisjL] : Op (DynReservationMap A H) where
  op := op
  assoc := DynReservationMap.ext Op.assoc Op.assoc
  comm := DynReservationMap.ext Op.comm Op.comm

@[reducible] instance raPCore [PCore A] : PCore (DynReservationMap A H) where
  pcore x := some x.core
  pcore_idem {x cx} h := by
    cases Option.some_inj.mp h.symm
    rcases x with ⟨xd, xt⟩
    change some (mk (PCore.core (PCore.core xd)) ∅) = some (mk (PCore.core xd) ∅)
    unfold PCore.core
    cases hd : PCore.pcore xd with
    | none => simp [hd]
    | some c => simp [PCore.pcore_idem hd]

@[simp]
theorem op_data [Op A] [Op CoPsetDisjL] (x y : DynReservationMap A H) : (x • y).data = x.data • y.data := rfl

@[simp]
theorem op_token [Op A] [Op CoPsetDisjL] (x y : DynReservationMap A H) : (x • y).token = x.token • y.token := rfl

instance raRA [RA A] : RA (DynReservationMap A H) where
  pcore_op_left {x _} h := by
    cases h
    exact DynReservationMap.ext (core_op x.data) (pcore_op_left' (x := x.token) rfl)

instance raURA [RA A] : URA (DynReservationMap A H) where
  unit := mk ∅ ∅
  unit_left_id {x} := DynReservationMap.ext
    (Algebra.MonoidOps.op_left_id : (∅ : H A) • x.data = x.data) (pcore_op_left' rfl)
  pcore_unit := congrArg some (DynReservationMap.ext Heap.core_empty rfl)
  total _ := ⟨_, rfl⟩

variable [RA A] [ORA A]

@[rocq_alias dyn_reservation_map_validN_instance]
def ValidN (n : SI) (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓{n} x.data ∧ setInfinite (⊤ \ e) ∧ ∀ i, get? x.data i = none ∨ i ∉ e
  | .error => False

@[indexed, rocq_alias dyn_reservation_map_valid_instance]
def Valid (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓ x.data ∧ setInfinite (⊤ \ e) ∧ ∀ i, get? x.data i = none ∨ i ∉ e
  | .error => False

#rocq_ignore dyn_reservation_map_valid_eq "Definitional unfolding of Valid"
#rocq_ignore dyn_reservation_map_validN_eq "Definitional unfolding of ValidN"

/-- The complement of the token's mask `e` is infinite, i.e. there are always infinitely many keys
still available to reserve. This is a validity requirement of `DynReservationMap`. -/
def Infinite (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => setInfinite ((⊤ : CoPset) \ e)
  | .error => True

theorem validN_iff {n : SI} {x : DynReservationMap A H} :
    x.ValidN n ↔ ✓{n} x.data ∧ ✓{n} x.token ∧ x.Infinite ∧
      ∀ i, get? x.data i = none ∨ i ∉ x.token := by
  refine ⟨fun h => ?_, fun ⟨vd, vt, inf, disj⟩ => ?_⟩
  · simp only [ValidN, Infinite] at h ⊢
    cases eq : x.token with
    | valid s =>
      simp only [eq] at h ⊢
      exact ⟨h.left, trivial, h.right.left, h.right.right⟩
    | error => simp only [eq] at h
  · simp only [ValidN]
    cases h : x.token
    · simp only [h, Infinite] at disj inf
      exact ⟨vd, inf, disj⟩
    · exact ((h ▸ not_valid_invalid (SI := SI) (S := CoPset)) vt)

theorem valid_iff {x : DynReservationMap A H} :
    x.Valid (SI := SI) ↔ ✓[SI] x.data ∧ ✓[SI] x.token ∧ x.Infinite ∧
      ∀ i, get? x.data i = none ∨ i ∉ x.token := by
  refine ⟨fun h => ?_, fun ⟨vd, vt, inf, disj⟩ => ?_⟩
  · simp only [Valid, Infinite] at h ⊢
    cases eq : x.token with
    | valid s =>
      simp only [eq] at h ⊢
      exact ⟨h.left, valid_set, h.right.left, h.right.right⟩
    | error => simp only [eq] at h
  · simp only [Valid]
    cases h : x.token
    · simp only [h, Infinite] at disj inf
      exact ⟨vd, inf, disj⟩
    · exact ((h ▸ not_valid_invalid (S := CoPset)) vt)

theorem validN_data_of_validN {n : SI} {x : DynReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.data := (validN_iff.mp h).left

theorem validN_token_of_validN {n : SI} {x : DynReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.token := (validN_iff.mp h).right.left

theorem validN_infinite {n : SI} {x : DynReservationMap A H} (h : x.ValidN n) :
    x.Infinite := (validN_iff.mp h).right.right.left

theorem validN_disj {n : SI} {x : DynReservationMap A H} (h : x.ValidN n) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (validN_iff.mp h).right.right.right i

theorem valid_data_of_valid {x : DynReservationMap A H} (h : x.Valid (SI := SI)) :
    ✓ x.data := (valid_iff.mp h).left

theorem valid_token_of_valid {x : DynReservationMap A H} (h : x.Valid (SI := SI)) :
    ✓ x.token := (valid_iff.mp h).right.left

theorem valid_infinite {x : DynReservationMap A H} (h : x.Valid (SI := SI)) :
    x.Infinite := (valid_iff.mp h).right.right.left

theorem valid_disj {x : DynReservationMap A H} (h : x.Valid (SI := SI)) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (valid_iff.mp h).right.right.right i

omit [ORA A] in
theorem infinite_op_left {n : SI} {x y : DynReservationMap A H} (vt : ✓{n} (x.token • y.token))
    (inf : (x • y).Infinite) : x.Infinite := by
  match ht : x.token, hy : y.token with
  | .error, _ => exact (not_validN_invalid (ht ▸ validN_op_left vt)).elim
  | .valid e₁, .error => exact (not_validN_invalid (hy ▸ validN_op_right vt)).elim
  | .valid e₁, .valid e₂ =>
    have hv : ✓{n} (DisjointLeibnizSet.valid e₁ • DisjointLeibnizSet.valid e₂) :=
      ht ▸ hy ▸ vt
    have hdisj : e₁ ## e₂ := (valid_op_iff_disj (SI := SI)).mp hv
    simp only [Infinite, ht] at ⊢
    simp only [Infinite, op, ht, hy, ORA.op, hdisj, ↓reduceIte] at inf
    exact setInfinite_mono
      (fun i hi => mem_diff.mpr ⟨(mem_diff.mp hi).left,
        fun hc => (mem_diff.mp hi).right (mem_union.mpr (.inl hc))⟩) inf

theorem validN_mono {n : SI} {x y : DynReservationMap A H} (hd : ✓{n} y.data → ✓{n} x.data)
    (hdom : ∀ i, get? y.data i = none → get? x.data i = none) (ht : ∃ w, y.token = x.token • w)
    (v : y.ValidN n) : x.ValidN n := by
  obtain ⟨w, hw⟩ := ht
  have vt : ✓{n} (x.token • w) := hw ▸ validN_token_of_validN v
  refine validN_iff.mpr ⟨hd (validN_data_of_validN v), validN_op_left vt,
    infinite_op_left (y := mk ∅ w) vt (by rw [Infinite, op_token, ← hw]; exact validN_infinite v),
    fun i => (validN_disj v i).imp (hdom i) fun hy hx => hy ?_⟩
  exact hw ▸ (mem_iff_of_validN_union vt i).mpr (.inl hx)

#rocq_ignore dyn_reservation_map_cmra_mixin "Not needed"
#rocq_ignore dyn_reservation_map_ucmra_mixin "Not needed"
#rocq_ignore dyn_reservation_mapR "Derivable using UCMRA"
#rocq_ignore dyn_reservation_map_empty_instance "Part of UCMRA instance"

@[reducible] def raValid : _root_.Iris.Valid SI (DynReservationMap A H) where
  Valid := Valid (SI := SI)
  ValidN := ValidN
  valid_iff_validN {x} := by
    refine ⟨fun h n => ?_, fun v => ?_⟩
    · refine validN_iff.mpr ⟨?_, ?_, ?_, ?_⟩
      · exact Valid.validN (valid_data_of_valid h)
      · exact (valid_0_iff_validN n).mp (valid_token_of_valid h)
      · exact valid_infinite h
      · exact valid_disj h
    · refine valid_iff.mpr ⟨?_, ?_, ?_, ?_⟩
      · exact valid_iff_validN.mpr (fun n => validN_data_of_validN (v n))
      · exact valid_iff_validN.mpr (fun n => validN_token_of_validN (v n))
      · exact validN_infinite (v 0)
      · exact validN_disj (v 0)

@[reducible] def raOrdered : Ordered SI (DynReservationMap A H) where
  OrderN n x y := x.data ≼ₒ{n} y.data ∧ x.token ≼ₒ{n} y.token
  Order x y := x.data ≼ₒ y.data ∧ x.token ≼ₒ y.token
  ordN_trans h1 h2 := ⟨ordN_trans h1.1 h2.1, ordN_trans h1.2 h2.2⟩
  ord_trans h1 h2 := ⟨ord_trans h1.1 h2.1, ord_trans h1.2 h2.2⟩
  ordN_of_ord n h := ⟨ordN_of_ord n h.1, ordN_of_ord n h.2⟩

attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE (DynReservationMap A H) where
  ordN_ne ex ey h := ⟨ordN_ne ex.1 ey.1 h.1, ordN_ne ex.2 ey.2 h.2⟩
  ordN_le h le := ⟨ordN_le h.1 le, ordN_le h.2 le⟩

section
attribute [local instance] raOrdered raValid raOrderedNE

theorem increasing_data {v : DynReservationMap A H} (h : Increasing v) : Increasing v.data where
  increasing w := (h.increasing (mk w ∅)).1

theorem increasing_token {v : DynReservationMap A H} (h : Increasing v) : Increasing v.token where
  increasing w := (h.increasing (mk ∅ w)).2

theorem increasing_mk {v : DynReservationMap A H}
    (hd : Increasing v.data) (ht : Increasing v.token) : Increasing v where
  increasing w := ⟨hd.increasing w.data, ht.increasing w.token⟩

instance instORADynReservationMap : ORA (DynReservationMap A H) where
  toValid := raValid
  op_ne := ⟨fun _ _ _ h => ⟨Dist.op_r h.left, Dist.op_r h.right⟩⟩
  pcore_ne {n : SI} {x y cx} e pe := by
    cases Option.some_inj.mp pe.symm
    refine ⟨_, rfl, ?_, .rfl⟩
    simp [Dist.core e.left]
  validN_ne {n : SI} {x y} h v := by
    refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
    · exact (Dist.validN h.left).mp (validN_data_of_validN v)
    · exact (Dist.validN h.right).mp (validN_token_of_validN v)
    · rw [Infinite, ← h.right]
      exact validN_infinite v
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
    refine validN_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact validN_le (validN_data_of_validN v) hle
    · exact (valid_0_iff_validN n').mp ((valid_0_iff_validN n).mpr (validN_token_of_validN v))
    · exact validN_infinite v
    · exact validN_disj v
  toOrderedNE := raOrderedNE
  validN_op_left {_ x y} := validN_mono validN_op_left
    (fun _ h => Option.eq_none_of_op_eq_none_left ((Heap.get?_op _ _).symm.trans h)) ⟨y.token, rfl⟩
  extend {n : SI} {x y₁ y₂} v exy := by
    obtain ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := extend (validN_data_of_validN v) exy.left
    exact ⟨mk z₁ y₁.token, mk z₂ y₂.token, DynReservationMap.ext xzz exy.right,
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
    exact increasing_mk (v := mk _ ∅) (increasing_core x.data)
      (increasing_core x.token)
  increasing_closed {n : SI} {x y} h h' :=
    increasing_mk
      (increasing_closed (increasing_data h) (Or.imp (·.1) (·.1) h'))
      (increasing_closed (increasing_token h) (Or.imp (·.2) (·.2) h'))
  ordN_extend {n : SI} {sn} {x y} hs v h := by
    obtain ⟨zd, hzd, ed⟩ := ordN_extend hs (validN_data_of_validN v) h.1
    obtain ⟨zt, hzt, et⟩ := ordN_extend hs (validN_token_of_validN v) h.2
    exact ⟨mk zd zt, ⟨hzd, hzt⟩, ed, et⟩

end

instance instIncOrd [IncOrd A] : IncOrd (DynReservationMap A H) := IncOrd.of_increasing fun v =>
    increasing_mk (IncOrd.increasing v.data) (IncOrd.increasing v.token)

@[rocq_alias dyn_reservation_mapUR]
instance instUCMRADynReservationMap : UORA SI (DynReservationMap A H) where
  toORA := instORADynReservationMap
  unit_valid := valid_iff.mpr ⟨Heap.valid_empty, valid_set,
    show setInfinite ((⊤ : CoPset) \ ∅) by rw [diff_empty]; exact top_infinite,
    fun _ => .inr (mem_empty _)⟩
  ord_refl x := ⟨ord_refl x.data, ord_refl x.token⟩

@[rocq_alias dyn_reservation_map_included]
theorem inc_iff {x y : DynReservationMap A H} :
    x ≼ y ↔ x.data ≼ y.data ∧ x.token ≼ y.token := by
  refine ⟨fun ⟨z, hz⟩ => ⟨⟨z.data, congrArg (·.data) hz⟩,
    ⟨z.token, congrArg (·.token) hz⟩⟩, ?_⟩
  exact fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ =>
    ⟨mk z₁ z₂, DynReservationMap.ext hz₁ hz₂⟩

theorem ord_iff {x y : DynReservationMap A H} :
    x ≼ₒ y ↔ x.data ≼ₒ y.data ∧ x.token ≼ₒ y.token := .rfl

theorem ordN_iff {n : SI} {x y : DynReservationMap A H} :
    x ≼ₒ{n} y ↔ x.data ≼ₒ{n} y.data ∧ x.token ≼ₒ{n} y.token := .rfl

instance instOrdInc [OrdInc A] : OrdInc (DynReservationMap A H) where
  ord_inc h := inc_iff.mpr ⟨Iris.ord_inc h.1, Iris.ord_inc h.2⟩
  ordN_incN h :=
    let ⟨z₁, h₁⟩ := Iris.ordN_incN h.1
    let ⟨z₂, h₂⟩ := Iris.ordN_incN h.2
    ⟨mk z₁ z₂, h₁, h₂⟩

instance instIsInc [IsInc A] : IsInc (DynReservationMap A H) := {}

@[rocq_alias dyn_reservation_map_data_proj_validN]
theorem data_proj_validN {n : SI} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.data :=
  validN_data_of_validN h

@[rocq_alias dyn_reservation_map_token_proj_validN]
theorem token_proj_validN {n : SI} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.token :=
  validN_token_of_validN h

@[rocq_alias dyn_reservation_map_cmra_discrete]
instance [ORA.Discrete SI A] : ORA.Discrete SI (DynReservationMap A H) where
  discrete_valid {_} v := valid_iff.mpr ⟨discrete_valid (validN_data_of_validN v),
    validN_token_of_validN v, validN_infinite v, validN_disj v⟩
  discrete_ord h := ⟨fun k => discrete_ord (h.1 k), discrete_ord h.2⟩

@[rocq_alias dyn_reservation_map_data_core_id]
instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (mkData (H := H) k a) where
  core_id := congrArg some <| congrArg (mk (token := ∅))
    (core_eqv_self (PartialMap.singleton k a : H A))

theorem split_validN {n : SI} {x : DynReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x = mk d ∅ • mkToken t := by
  rcases x with ⟨xd, xt⟩
  cases xt with
  | error => exact (not_validN_invalid (S := CoPset) (validN_token_of_validN vx)).elim
  | valid t =>
    exact ⟨xd, t, DynReservationMap.ext
      (Algebra.MonoidOps.op_right_id : xd • (∅ : H A) = xd).symm (pcore_op_left' rfl).symm⟩

theorem valid_mkData_singleton : ✓[SI] (mkData (H := H) k a) ↔ ✓[SI] ({[k := a]} : H A) :=
  ⟨valid_data_of_valid, fun h => valid_iff.mpr ⟨h, valid_set, top_infinite,
    fun p => .inr (mem_empty p)⟩⟩

theorem validN_mkData_singleton {n : SI} : ✓{n} (mkData (H := H) k a) ↔ ✓{n} ({[k := a]} : H A) :=
  ⟨validN_data_of_validN, fun h => validN_iff.mpr ⟨h, validN_set, top_infinite,
    fun p => .inr (mem_empty p)⟩⟩

@[rocq_alias dyn_reservation_map_data_valid]
theorem valid_mkData (k : Pos) (a : A) : ✓ (mkData (H := H) k a) ↔ ✓ a :=
  valid_mkData_singleton.trans Heap.singleton_valid_iff

theorem validN_mkData {n : SI} (k : Pos) (a : A) : ✓{n} (mkData (H := H) k a) ↔ ✓{n} a :=
  validN_mkData_singleton.trans Heap.singleton_validN_iff

@[rocq_alias dyn_reservation_map_token_valid]
theorem valid_token {e : CoPset} :
    ✓[SI] (mkToken (H := H) (A := A) e) ↔ setInfinite ((⊤ : CoPset) \ e) :=
  ⟨valid_infinite, fun hinf => valid_iff.mpr
    ⟨Heap.valid_empty, valid_set, hinf, fun i => .inl (get?_empty i)⟩⟩

@[rocq_alias dyn_reservation_map_data_op]
theorem mkData_op k (a b : A) :
    mkData (H := H) k (a • b) = mkData (H := H) k a • mkData k b :=
  DynReservationMap.ext Heap.singleton_op_singleton.symm (pcore_op_right_L rfl).symm

theorem mkData_mono_ord {k} {a b : A} (Hab : a ≼ₒ b) :
    mkData (H := H) k a ≼ₒ mkData k b :=
  ⟨Heap.singleton_ord_singleton_mono Hab, ord_refl _⟩

@[rocq_alias dyn_reservation_map_data_mono]
theorem mkData_mono {k} {a b : A} (Hab : a ≼ b) :
    mkData (H := H) k a ≼ mkData k b :=
  let ⟨z, hz⟩ := Hab
  ⟨mkData k z, (congrArg (mkData k) hz).trans (mkData_op k a z)⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias dyn_reservation_map_data_is_op]
instance {d : IsOp.Direction} {a b₁ b₂ : A} [hv : IsOp d a b₁ b₂] :
    IsOp d (mkData (H := H) k a) (mkData k b₁) (mkData k b₂) where
  is_op := (congrArg (mkData k) hv.is_op).trans (mkData_op k b₁ b₂)

@[rocq_alias dyn_reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂) :
    mkToken (H := H) (A := A) (e₁ ∪ e₂) = mkToken (H := H) (A := A) e₁ • mkToken e₂ :=
  DynReservationMap.ext (Algebra.MonoidOps.op_left_id : (∅ : H A) • ∅ = ∅).symm
    (by simp [mkToken, op, ORA.op, he])

@[rocq_alias dyn_reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    mkToken (H := H) (A := A) e₂ = mkToken (H := H) (A := A) e₁ • mkToken (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

theorem disj_of_validN_data_op_token {n : SI} {a : H A} {b : CoPset}
    (h : ✓{n} mk a ∅ • mkToken b) (i : Pos) : get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [mkToken, op_data, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [mkToken, op_token] at h'
    rw [mem_iff_of_valid_union (SI := SI), not_or] at h'
    · exact .inr h'.right
    · exact ((pcore_op_left' rfl).symm : (_ : DisjointLeibnizSet CoPset) = _) ▸ valid_set

theorem infinite_data_op_token {n : SI} {a : H A} {b : CoPset} (h : ✓{n} mk a ∅ • mkToken b) :
    setInfinite ((⊤ : CoPset) \ b) := by
  simpa only [Infinite, show (mk a ∅ • mkToken b).token = .valid b from
    pcore_op_left_L rfl] using validN_infinite h

theorem validN_data_op_token {n : SI} {a : H A} {b : CoPset} (vd : ✓{n} a)
    (inf : setInfinite ((⊤ : CoPset) \ b)) (disj : ∀ i, get? a i = none ∨ i ∉ b) :
    ✓{n} mk a ∅ • mkToken b := by
  have abdp : (mk a ∅ • mkToken b).data = a :=
    show a • ∅ = a from Algebra.MonoidOps.op_right_id
  have eo : ∅ • DisjointLeibnizSet.valid b = .valid b := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
  · exact abdp.symm ▸ vd
  · simp [mkToken, eo, validN_set]
  · rw [Infinite, show (mk a ∅ • mkToken b).token = .valid b from pcore_op_left_L rfl]
    exact inf
  · simp [mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa [h] using .inl rfl
    | inr h => simpa [eo] using .inr h

theorem valid_op?_of_valid_mkData_op_data {n : SI} {a : A} {x : H A}
    (h : ✓{n} (mkData k a • mk x ∅)) : ✓{n} a •? get? x k := by
  match h' : get? x k with
  | none => simpa [op?] using (validN_mkData (H := H) k a).mp (validN_op_left h)
  | some g =>
    simp only [op?]
    apply Option.some_validN.mp
    simpa only [ORA.op, op, mkData, op_data, Heap.op, get?_merge, Option.merge,
      LawfulPartialMap.get?_singleton, ↓reduceIte, h'] using (validN_data_of_validN h) k

theorem valid_mkData_op_data_of_valid_op? {n : SI} {a : A} {x : H A} (vx : ✓{n} x)
    (h : ✓{n} a •? get? x k) : ✓{n} mkData k a • mk x ∅ := by
  have htok : (mkData k a • mk x ∅).token = .valid (∅ : CoPset) := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · change ✓{n} ({[k := a]} : H A) • x
    intro i
    rw [Heap.get?_op]
    by_cases ki : k = i
    · simp only [← ki, LawfulPartialMap.get?_singleton, ↓reduceIte, Option.some_op_opM]
      exact h
    · simp only [LawfulPartialMap.get?_singleton, ki, ↓reduceIte]
      exact Heap.validN_get? vx
  · exact htok ▸ validN_set
  · rw [Infinite, htok]
    exact top_infinite
  · exact fun i => .inr (htok.symm ▸ mem_empty i)

theorem validN_token_op_iff_disj {n : SI} {e₁ e₂} :
    ✓{n} (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔
      e₁ ## e₂ ∧ setInfinite ((⊤ : CoPset) \ (e₁ ∪ e₂)) := by
  refine ⟨fun h => ⟨(valid_op_iff_disj (SI := SI)).mp (validN_token_of_validN h), ?_⟩,
    fun ⟨hdisj, hinf⟩ => by
      rw [← token_union hdisj]; exact (valid_token.mpr hinf).validN⟩
  have hdisj := (valid_op_iff_disj (SI := SI)).mp (validN_token_of_validN h)
  simpa only [Infinite, op_token, op, mkToken, ORA.op, hdisj, ↓reduceIte] using validN_infinite h

@[rocq_alias dyn_reservation_map_token_valid_op]
theorem valid_token_op {e₁ e₂} :
    ✓ (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔
      e₁ ## e₂ ∧ setInfinite ((⊤ : CoPset) \ (e₁ ∪ e₂)) :=
  ⟨fun h => (validN_token_op_iff_disj (n := 0)).mp h.validN,
   fun h => valid_iff_validN.mpr fun _ => validN_token_op_iff_disj.mpr h⟩

@[rocq_alias dyn_reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a) :
    mkToken (H := H) e ~~> mkData k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_mkData k a).mpr va
  | some z =>
    have ⟨d, t, ze⟩ := split_validN (validN_op_right vo)
    have vdt := ze ▸ validN_op_right vo
    have vedt : ✓{n} mkToken e • (mk d ∅ • mkToken t) := ze ▸ vo
    have disj : ∀ i : Pos, get? d i = none ∨ i ∉ e :=
      disj_of_validN_data_op_token
        ((comm' (α := DynReservationMap A H)) ▸
          validN_op_left ((assoc' (α := DynReservationMap A H)) ▸ vedt))
    change ✓{n} mkData k a • z
    rw [ze, assoc', ← (show mk ({[k := a]} • d) ∅ = mkData k a • mk d ∅ from
      DynReservationMap.ext rfl (pcore_op_right_L rfl).symm)]
    refine validN_data_op_token ?_ (infinite_data_op_token vdt) ?_
    · refine validN_data_of_validN <| valid_mkData_op_data_of_valid_op? ?_ ?_
      · exact validN_data_of_validN
          (validN_op_left ((comm' (α := DynReservationMap A H)) ▸
            validN_op_left ((assoc' (α := DynReservationMap A H)) ▸ vedt)))
      · exact (disj k).elim (fun h => h ▸ Valid.validN va) (absurd hke)
    · simp only [ORA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro i
      grind [disj_of_validN_data_op_token vdt,
        (validN_token_op_iff_disj.mp
          (validN_op_right ((assoc' (α := DynReservationMap A H)).symm ▸
            (comm' (α := DynReservationMap A H)) ▸ vedt))).left i]

@[rocq_alias dyn_reservation_map_updateP]
theorem updateP {P} {Q : DynReservationMap A H → Prop} k a (ap : a ~~>: P)
    (apq : ∀ a', P a' → Q (mkData k a')) : mkData k a ~~>: Q := by
  intro n mz vaz
  match mz with
  | none =>
    obtain ⟨y, py, vy⟩ := ap n none ((validN_mkData k a).mp vaz)
    exact ⟨_, apq y py, (validN_mkData k y).mpr vy⟩
  | some z =>
    obtain ⟨d, t, ze⟩ := split_validN (validN_op_right vaz)
    have vdt := ze ▸ validN_op_right vaz
    obtain ⟨y, py, vy⟩ := ap n (get? d k)
      (valid_op?_of_valid_mkData_op_data
        (validN_op_left ((assoc' (α := DynReservationMap A H)) ▸
          (ze ▸ vaz : ✓{n} mkData k a • (mk d ∅ • mkToken t)))))
    refine ⟨mkData k y, apq y py, ?_⟩
    simp only [ORA.op?] at vaz ⊢
    rw [ze, assoc', ← (show mk ({[k := y]} • d) ∅ = mkData k y • mk d ∅ from
      DynReservationMap.ext rfl (pcore_op_right_L rfl).symm)]
    refine validN_data_op_token ?_ (infinite_data_op_token vdt) ?_
    · exact validN_data_of_validN <| valid_mkData_op_data_of_valid_op?
        (validN_data_of_validN (validN_op_left vdt)) vy
    · have ddt := disj_of_validN_data_op_token vdt
      have dde := disj_of_validN_data_op_token
        (show ✓{n} mkData (H := H) k a • mkToken t from
          (comm' (α := DynReservationMap A H)) ▸
            validN_op_right ((assoc' (α := DynReservationMap A H)).symm ▸
              (comm' (α := DynReservationMap A H)) ▸
                (ze ▸ vaz : ✓{n} mkData k a • (mk d ∅ • mkToken t))))
      simp only [ORA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at ddt dde ⊢
      grind

@[rocq_alias dyn_reservation_map_update]
theorem update {k} {a b : A} (uab : a ~~> b) :
    mkData (H := H) k a ~~> mkData k b :=
  Update.of_updateP <| updateP k a (.of_update uab) fun _ => congrArg (mkData k)

end

section

variable [LawfulFiniteMap H Pos]

/-- The domain of a finite map `m : H A`, viewed as a finite `CoPset`. -/
def domCoPset (m : H A) : CoPset := FiniteMap.dom_set m

theorem mem_domCoPset {m : H A} {i : Pos} : i ∈ domCoPset m ↔ get? m i ≠ none :=
  (LawfulFiniteMap.mem_dom_set (S := CoPset)).trans (Option.isSome_iff_ne_none (o := get? m i))

variable [RA A] [ORA A]

@[rocq_alias dyn_reservation_map_reserve]
theorem reserve (Q : DynReservationMap A H → Prop)
    (HQ : ∀ e : CoPset, setInfinite e → Q (mkToken e)) :
    (unit : DynReservationMap A H) ~~>: Q := by
  intro n mz vo
  have ⟨mf, Ef, hz, vmf, hinf, hdisj⟩ :
      ∃ (mf : H A) (Ef : CoPset), (unit •? mz) = mk mf ∅ • mkToken Ef ∧
        ✓{n} mf ∧ setInfinite ((⊤ : CoPset) \ Ef) ∧
        ∀ i, get? mf i = none ∨ i ∉ Ef := by
    match mz with
    | none =>
      exact ⟨∅, ∅, DynReservationMap.ext (Heap.op_empty_left).symm
        (pcore_op_left_L rfl).symm,
        Heap.valid_empty.validN, top_infinite, fun i => .inl (get?_empty i)⟩
    | some z =>
      have vz : ✓{n} z := unit_left_id (x := z) ▸ vo
      obtain ⟨mf, Ef, hze⟩ := split_validN vz
      have vze := hze ▸ vz
      refine ⟨mf, Ef, (unit_left_id (x := z)).trans hze, ?_, ?_, ?_⟩
      · exact validN_data_of_validN (validN_op_left vze)
      · exact infinite_data_op_token vze
      · exact disj_of_validN_data_op_token vze
  obtain ⟨E₁, E₂, hEunion, hEdisj, hE₁inf, hE₂inf⟩ :=
    split_infinite ((⊤ : CoPset) \ (Ef ∪ domCoPset mf))
      (setInfinite_mono
        (fun i hi =>
          have ⟨hiTEf, hiD⟩ := LawfulSet.mem_diff.mp hi
          LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun hmem =>
            (LawfulSet.mem_union.mp hmem).elim (LawfulSet.mem_diff.mp hiTEf).right hiD⟩)
        (difference_infinite hinf ofList_finite))
  have hE₁Ef : E₁ ## Ef := fun i ⟨h₁, hEf⟩ =>
    (LawfulSet.mem_diff.mp (hEunion ▸ LawfulSet.mem_union.mpr (.inl h₁))).right
      (LawfulSet.mem_union.mpr (.inl hEf))
  refine ⟨mkToken E₁, HQ E₁ hE₁inf, ?_⟩
  rw [← unit_right_id (x := mkToken (H := H) (A := A) E₁), op_opM_assoc, hz, assoc',
    comm' (x := mkToken E₁), ← assoc', ← token_union hE₁Ef]
  refine validN_data_op_token vmf ?_ ?_
  · refine setInfinite_mono (fun i hi => ?_) hE₂inf
    have hiX := hEunion ▸ LawfulSet.mem_union.mpr (.inr hi)
    refine LawfulSet.mem_diff.mpr ⟨(LawfulSet.mem_diff.mp hiX).left, fun hmem => ?_⟩
    cases LawfulSet.mem_union.mp hmem with
    | inl h₁ => exact hEdisj i ⟨h₁, hi⟩
    | inr hEf => exact (LawfulSet.mem_diff.mp hiX).right (LawfulSet.mem_union.mpr (.inl hEf))
  · intro i
    by_cases hmem : i ∈ E₁ ∪ Ef
    · refine .inl ?_
      cases LawfulSet.mem_union.mp hmem with
      | inl h₁ =>
        have hiX := hEunion ▸ LawfulSet.mem_union.mpr (.inl h₁)
        exact Decidable.not_not.mp <| mt mem_domCoPset.mpr fun hd =>
          (LawfulSet.mem_diff.mp hiX).right (LawfulSet.mem_union.mpr (.inr hd))
      | inr hEf => exact (hdisj i).elim id fun h => absurd hEf h
    · exact .inr hmem

@[rocq_alias dyn_reservation_map_reserve']
theorem reserve' :
    (unit : DynReservationMap A H) ~~>: fun x => ∃ e : CoPset, setInfinite e ∧ x = mkToken e :=
  reserve _ fun e hinf => ⟨e, hinf, rfl⟩

end

end DynReservationMap

end ORA

end

end Iris
