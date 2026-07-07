/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

import Iris.Std.Positives
public import Iris.Std.CoPset
public import Iris.Std.GenSets
public import Iris.Std.PartialMap
public import Iris.Algebra.CMRA
public import Iris.Algebra.Heap
public import Iris.Algebra.IsOp
public import Iris.Algebra.Updates
public import Iris.Algebra.LeibnizSet

namespace Iris

@[expose] public section

open Iris Std PartialMap

/-!
The camera [DynReservationMap A H] over a camera [A] extends [LawfulPartialMap H Pos]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : CoPset] which represent the right to allocate a map entry at any position
[k ∈ E]. Unlike [ReservationMap], [DynReservationMap] supports dynamically
allocating these tokens, including infinite sets of them.
-/

@[rocq_alias dyn_reservation_map]
structure DynReservationMap (A : Type) (H : Type → Type) where
  data : H A
  token : DisjointLeibnizSet CoPset

def DynReservationMap.mkData [LawfulPartialMap H Pos] (data : H A) :
    DynReservationMap A H := .mk data ∅

@[rocq_alias dyn_reservation_map_data]
def DynReservationMap.singleton [LawfulPartialMap H Pos] (k : Pos) (a : A) :
    DynReservationMap A H := DynReservationMap.mkData {[k := a]}

@[rocq_alias dyn_reservation_map_token]
def DynReservationMap.mkToken [LawfulPartialMap H Pos] (e : CoPset) :
    DynReservationMap A H := .mk ∅ (.valid e)

#rocq_ignore to_reservation_map "Not needed; the OFE/CMRA are built directly, not via an isomorphism"
#rocq_ignore from_reservation_map "Not needed; the OFE/CMRA are built directly, not via an isomorphism"

section OFE

open OFE

variable [LawfulPartialMap H Pos] [OFE A]

#rocq_ignore dyn_reservation_map_ofe_mixin "Not needed"

@[rocq_alias dyn_reservation_mapO]
instance : OFE (DynReservationMap A H) where
  Equiv x y := x.data ≡ y.data ∧ x.token ≡ y.token
  Dist n x y := x.data ≡{n}≡ y.data ∧ x.token ≡{n}≡ y.token
  dist_eqv := {
    refl _ := ⟨.rfl, rfl⟩,
    symm h := ⟨h.left.symm, h.right.symm⟩,
    trans h₁ h₂ := ⟨h₁.left.trans h₂.left, h₁.right.trans h₂.right⟩
  }
  equiv_dist :=
    ⟨fun h n => ⟨equiv_dist.mp h.left n, h.right⟩,
     fun h => ⟨equiv_dist.mpr (h · |>.left), (h 0).right⟩⟩
  dist_lt h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

@[rocq_alias dyn_reservation_map_ofe_discrete]
instance instDiscreteDynReservationMap [Discrete A] : Discrete (DynReservationMap A H) where
  discrete_0 h := ⟨discrete_0 h.left, discrete_0 h.right⟩

instance instNonExpansiveDynReservationMapData :
    NonExpansive (DynReservationMap.mkData (H := H) (A := A)) where
  ne _ _ _ h := ⟨h, rfl⟩

#rocq_ignore dyn_reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias dyn_reservation_map_data_ne]
instance instNonExpansiveDynReservationMapSingleton :
    NonExpansive (DynReservationMap.singleton (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, rfl⟩

@[rocq_alias DynReservationMap_discrete]
instance instDiscreteEDynReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (DynReservationMap.mk a b) where
  discrete := fun ⟨ha, hb⟩ => ⟨DiscreteE.discrete ha, DiscreteE.discrete hb⟩

@[rocq_alias dyn_reservation_map_data_discrete]
instance instDiscreteEDynReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (DynReservationMap.singleton (H := H) k a) :=
  by unfold DynReservationMap.singleton DynReservationMap.mkData; infer_instance

@[rocq_alias dyn_reservation_map_token_discrete]
instance instDiscreteEDynReservationMapToken :
    DiscreteE (DynReservationMap.mkToken (H := H) (A := A) e) :=
  by unfold DynReservationMap.mkToken; infer_instance

end OFE

section CMRA

open OFE CMRA DisjointLeibnizSet LawfulSet

namespace DynReservationMap

section

variable [LawfulPartialMap H Pos] [CMRA A]

def ValidN (n : Nat) (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓{n} x.data ∧ setInfinite (⊤ \ e) ∧ ∀ i, get? x.data i = none ∨ i ∉ e
  | .error => False

def Valid (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓ x.data ∧ setInfinite (⊤ \ e) ∧ ∀ i, get? x.data i = none ∨ i ∉ e
  | .error => False

/-- The complement of the token's mask `e` is infinite, i.e. there are always infinitely many keys
still available to reserve. This is a validity requirement of `DynReservationMap`. -/
def Infinite (x : DynReservationMap A H) : Prop :=
  match x.token with
  | .valid e => setInfinite ((⊤ : CoPset) \ e)
  | .error => True

theorem validN_iff {n : Nat} {x : DynReservationMap A H} :
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
    · exact ((h ▸ not_valid_invalid (S := CoPset)) vt)

theorem valid_iff {x : DynReservationMap A H} :
    x.Valid ↔ ✓ x.data ∧ ✓ x.token ∧ x.Infinite ∧
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

theorem validN_data_of_validN {n : Nat} {x : DynReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.data := (validN_iff.mp h).left

theorem validN_token_of_validN {n : Nat} {x : DynReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.token := (validN_iff.mp h).right.left

theorem validN_infinite {n : Nat} {x : DynReservationMap A H} (h : x.ValidN n) :
    x.Infinite := (validN_iff.mp h).right.right.left

theorem validN_disj {n : Nat} {x : DynReservationMap A H} (h : x.ValidN n) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (validN_iff.mp h).right.right.right i

theorem valid_data_of_valid {x : DynReservationMap A H} (h : x.Valid) :
    ✓ x.data := (valid_iff.mp h).left

theorem valid_token_of_valid {x : DynReservationMap A H} (h : x.Valid) :
    ✓ x.token := (valid_iff.mp h).right.left

theorem valid_infinite {x : DynReservationMap A H} (h : x.Valid) :
    x.Infinite := (valid_iff.mp h).right.right.left

theorem valid_disj {x : DynReservationMap A H} (h : x.Valid) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (valid_iff.mp h).right.right.right i

def core (x : DynReservationMap A H) : DynReservationMap A H := mk (CMRA.core x.data) ∅

@[simp]
theorem core_data (x : DynReservationMap A H) : x.core.data = CMRA.core x.data := rfl

@[simp]
theorem core_token (x : DynReservationMap A H) : x.core.token = CMRA.core x.token := rfl

def op (x y : DynReservationMap A H) : DynReservationMap A H :=
  mk (x.data • y.data) (x.token • y.token)

@[simp]
theorem op_data' (x y : DynReservationMap A H) : (x.op y).data = x.data • y.data := rfl

@[simp]
theorem op_token' (x y : DynReservationMap A H) : (x.op y).token = x.token • y.token := rfl

theorem infinite_op_left {x y : DynReservationMap A H} (vt : ✓{n} (x.token • y.token))
    (inf : (x.op y).Infinite) : x.Infinite := by
  match ht : x.token, hy : y.token with
  | .error, _ => exact (not_validN_invalid (ht ▸ validN_op_left vt)).elim
  | .valid e₁, .error => exact (not_validN_invalid (hy ▸ validN_op_right vt)).elim
  | .valid e₁, .valid e₂ =>
    have hv : ✓{n} (DisjointLeibnizSet.valid e₁ • DisjointLeibnizSet.valid e₂) :=
      ht ▸ hy ▸ vt
    have hdisj : e₁ ## e₂ := by
      by_cases h : e₁ ## e₂
      · exact h
      · simp only [CMRA.op, h, ↓reduceIte] at hv; exact hv.elim
    simp only [Infinite, ht] at ⊢
    simp only [Infinite, op_token', ht, hy, CMRA.op, hdisj, ↓reduceIte] at inf
    exact setInfinite_mono
      (fun i hi => mem_diff.mpr ⟨(mem_diff.mp hi).left,
        fun hc => (mem_diff.mp hi).right (mem_union.mpr (.inl hc))⟩) inf

#rocq_ignore dyn_reservation_map_cmra_mixin "Not needed"
#rocq_ignore dyn_reservation_map_ucmra_mixin "Not needed"
#rocq_ignore dyn_reservation_mapR "Derivable using UCMRA"

@[rocq_alias dyn_reservation_mapUR]
instance : UCMRA (DynReservationMap A H) where
  pcore := some ∘ core
  Valid := Valid
  ValidN := ValidN
  op := op
  op_ne := ⟨fun n x₁ x₂ h => ⟨Dist.op_r h.left, Dist.op_r h.right⟩⟩
  pcore_ne {n x y cx} e pe := by
    cases Option.some_inj.mp pe.symm
    refine ⟨core y, rfl, ?_, ?_⟩
    · simp [Dist.core e.left]
    · simp [Dist.core e.right]
  validN_ne {n x y} h v := by
    refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
    · exact (Dist.validN h.left).mp (validN_data_of_validN v)
    · exact (Dist.validN h.right).mp (validN_token_of_validN v)
    · have hinf := validN_infinite v
      simp only [Infinite] at hinf ⊢
      rw [← h.right]
      exact hinf
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
  validN_succ {x n} v := by
    refine validN_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact validN_succ (validN_data_of_validN v)
    · exact (valid_0_iff_validN n).mp (validN_token_of_validN (n := n.succ) v)
    · exact validN_infinite v
    · exact validN_disj v
  validN_op_left {n x y} v := by
    refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
    · exact validN_op_left (validN_data_of_validN v)
    · exact validN_op_left (validN_token_of_validN v)
    · exact infinite_op_left (validN_token_of_validN v) (validN_infinite v)
    · cases (validN_disj v) i with
      | inl aa =>
        simp only [op_data', Heap.get?_op] at aa
        exact .inl <| Option.eq_none_of_op_eq_none_left aa
      | inr bb =>
        refine .inr fun HK => bb ?_
        refine (mem_iff_of_validN_union (validN_token_of_validN v) i).mpr ?_
        exact .inl HK
  assoc := ⟨CMRA.assoc, CMRA.assoc⟩
  comm := ⟨CMRA.comm, CMRA.comm⟩
  pcore_op_left {x cx} h := by
    refine ⟨?_, ?_⟩
    · simp [←Option.some_inj.mp h, op_data', core_data, core_op x.data]
    · simp [←Option.some_inj.mp h, op_token', core_token, core_op_L]
  pcore_idem {x cx} h := by
    refine ⟨?_, ?_⟩
    · simp [←Option.some_inj.mp h, core_data, core_idem x.data]
    · simp [←Option.some_inj.mp h, core_token, core_idem_L]
  pcore_op_mono {x cx} h y := by
    obtain ⟨z, hz⟩ := core_op_mono x.data y.data
    obtain ⟨w, hw⟩ := core_op_mono x.token y.token
    refine ⟨mk z w, ?_, ?_⟩
    · simp [op_data', core_data, (Option.some_inj.mp h.symm), hz]
    · simp only [core_token, op_token', (Option.some_inj.mp h.symm), leibniz]
      exact hw
  extend {n x y₁ y₂} v exy := by
    obtain ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := CMRA.extend (validN_data_of_validN v) exy.left
    refine ⟨mk z₁ y₁.token, mk z₂ y₂.token, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [op_data', xzz]
      · simp only [op_token', leibniz]
        exact exy.right
    · exact ⟨zy₁, rfl⟩
    · exact ⟨zy₂, rfl⟩
  unit := mk ∅ ∅
  unit_valid := valid_iff.mpr ⟨Heap.valid_empty, valid_set,
    show setInfinite ((⊤ : CoPset) \ ∅) by rw [diff_empty]; exact top_infinite,
    fun _ => .inr (mem_empty _)⟩
  unit_left_id {x} := ⟨by simp only [op, Algebra.MonoidOps.op_left_id], pcore_op_left' rfl⟩
  pcore_unit := ⟨Heap.core_empty, .rfl⟩

@[simp]
theorem op_data (x y : DynReservationMap A H) : (x • y).data = x.data • y.data := rfl

@[simp]
theorem op_token (x y : DynReservationMap A H) : (x • y).token = x.token • y.token := rfl

@[rocq_alias dyn_reservation_map_included]
theorem included {x y : DynReservationMap A H} :
    x ≼ y ↔ x.data ≼ y.data ∧ x.token ≼ y.token := by
  refine ⟨fun ⟨z, hz⟩ => ⟨⟨z.data, hz.left⟩, ⟨z.token, hz.right⟩⟩, ?_⟩
  exact fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨mk z₁ z₂, hz₁, hz₂⟩

@[rocq_alias dyn_reservation_map_data_proj_validN]
theorem data_proj_validN {n} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.data :=
  validN_data_of_validN h

@[rocq_alias dyn_reservation_map_token_proj_validN]
theorem token_proj_validN {n} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.token :=
  validN_token_of_validN h

@[rocq_alias dyn_reservation_map_cmra_discrete]
instance [CMRA.Discrete A] : CMRA.Discrete (DynReservationMap A H) where
  discrete_valid {_} v := by
    refine valid_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact discrete_valid (validN_data_of_validN v)
    · exact validN_token_of_validN v
    · exact validN_infinite v
    · exact validN_disj v

@[rocq_alias dyn_reservation_map_data_core_id]
instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (singleton (H := H) k a) where
  core_id := by
    refine ⟨?_, rfl⟩
    simp [singleton, mkData, core_eqv_self (PartialMap.singleton k a)]

theorem empty_infinite : setInfinite ((⊤ : CoPset) \ ∅) := by
  rw [diff_empty]; exact top_infinite

theorem split_valid {x : DynReservationMap A H} (vx : ✓ x) :
    ∃ (d : H A) (t : CoPset), x ≡ mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  match hh : xt with
  | .error =>
    exact ((not_valid_invalid (S := CoPset)) (hh ▸ (valid_token_of_valid vx))).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simp [mkData, mkToken, op_data, Algebra.MonoidOps.op_right_id.symm]
    · simp only [mkData, mkToken, op_token, leibniz]
      exact (pcore_op_left_L rfl).symm

theorem split_validN {x : DynReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x ≡ mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  have h := validN_token_of_validN vx
  match hh : xt with
  | .error => exact ((not_valid_invalid (S := CoPset)) (hh ▸ h)).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simpa [mkData, mkToken, op_data] using Algebra.MonoidOps.op_right_id.symm
    · exact (pcore_op_left' rfl).symm

theorem valid_data {d : H A} : ✓ (mkData (H := H) d) ↔ ✓ d :=
  ⟨valid_data_of_valid, fun h => valid_iff.mpr ⟨h, valid_set, empty_infinite,
    fun p => .inr (mem_empty p)⟩⟩

theorem validN_data {d : H A} : ✓{n} (mkData (H := H) d) ↔ ✓{n} d :=
  ⟨validN_data_of_validN, fun h => validN_iff.mpr ⟨h, validN_set, empty_infinite,
    fun p => .inr (mem_empty p)⟩⟩

@[rocq_alias dyn_reservation_map_data_valid]
theorem valid_singleton (k : Pos) (a : A) : ✓ (singleton (H := H) k a) ↔ ✓ a :=
  valid_data.trans Heap.singleton_valid_iff

theorem validN_singleton (k : Pos) (a : A) : ✓{n} (singleton (H := H) k a) ↔ ✓{n} a :=
  validN_data.trans Heap.singleton_validN_iff

@[rocq_alias dyn_reservation_map_token_valid]
theorem valid_token {e : CoPset} :
    ✓ (mkToken (H := H) (A := A) e) ↔ setInfinite ((⊤ : CoPset) \ e) := by
  refine ⟨fun h => valid_infinite h, fun hinf =>
    valid_iff.mpr ⟨Heap.valid_empty, valid_set, ?_, ?_⟩⟩
  · exact hinf
  · exact fun i => .inl (get?_empty i)

theorem data_op (a b : H A) : mkData (a • b) ≡ mkData a • mkData b :=
  ⟨.rfl, (pcore_op_right_L rfl).symm⟩

@[rocq_alias dyn_reservation_map_data_op]
theorem singleton_op k (a b : A) :
    singleton (H := H) k (a • b) ≡ singleton (H := H) k a • singleton k b := by
  refine ((data_op _ _).symm.trans ?_).symm
  exact NonExpansive.eqv (fun i => .of_eq (Heap.singleton_op_singleton i))

@[rocq_alias dyn_reservation_map_data_mono]
theorem singleton_mono {k} {a b : A} (Hab : a ≼ b) :
    singleton (H := H) k a ≼ singleton k b :=
  let ⟨z, hz⟩ := Hab
  ⟨singleton k z, (NonExpansive.eqv hz).trans (singleton_op k a z)⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias dyn_reservation_map_data_is_op]
instance {ia ib₁ ib₂ : ProofMode.InOut} {a b₁ b₂ : A} [hv : IsOp ia a ib₁ b₁ ib₂ b₂] :
    IsOp ia (singleton (H := H) k a) ib₁ (singleton k b₁) ib₂ (singleton k b₂) where
  is_op := .trans (NonExpansive.eqv hv.is_op) (singleton_op k b₁ b₂)

@[rocq_alias dyn_reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂) :
    mkToken (H := H) (A := A) (e₁ ∪ e₂) ≡ mkToken e₁ • mkToken e₂ := by
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [mkToken, get?_empty, op_data, Heap.get?_op] using .rfl
  · simp [mkToken, CMRA.op, he]

@[rocq_alias dyn_reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    mkToken (H := H) (A := A) e₂ ≡ mkToken e₁ • mkToken (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

@[rocq_alias dyn_reservation_map_token_valid_op]
theorem valid_token_op {e₁ e₂} :
    ✓ (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔
      e₁ ## e₂ ∧ setInfinite ((⊤ : CoPset) \ (e₁ ∪ e₂)) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hdisj, hinf⟩ => ?_⟩
  · exact valid_op_iff_disj.mp (valid_token_of_valid h)
  · have hdisj := valid_op_iff_disj.mp (valid_token_of_valid h)
    have hinf := valid_infinite h
    have htok :
        (mkToken (H := H) (A := A) e₁ • mkToken e₂).token = .valid (e₁ ∪ e₂) := by
      show DisjointLeibnizSet.valid e₁ • DisjointLeibnizSet.valid e₂ = _
      simp only [CMRA.op, hdisj, ↓reduceIte]
    simp only [Infinite, htok] at hinf
    exact hinf
  · exact (Equiv.valid (token_union hdisj)).mp (valid_token.mpr hinf)

theorem disj_of_validN_data_op_token {a : H A} {b : CoPset} (h : ✓{n} mkData a • mkToken b)
    (i : Pos) : get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [mkData, mkToken, op_data, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [mkData, mkToken, op_token] at h'
    rw [mem_iff_of_valid_union, not_or] at h'
    · exact .inr <| h'.right
    · exact valid_of_eqv (pcore_op_left' rfl).symm valid_set

theorem infinite_data_op_token {a : H A} {b : CoPset} (h : ✓{n} mkData a • mkToken b) :
    setInfinite ((⊤ : CoPset) \ b) := by
  have hinf := validN_infinite h
  have eo : (mkData a • mkToken b).token = .valid b := pcore_op_left_L rfl
  rw [Infinite, eo] at hinf
  exact hinf

theorem validN_data_op_token {n : Nat} (a : H A) (b : CoPset) (vd : ✓{n} mkData a)
    (inf : setInfinite ((⊤ : CoPset) \ b)) (disj : ∀ i, get? a i = none ∨ i ∉ b) :
    ✓{n} mkData a • mkToken b := by
  have abdp : (mkData a • mkToken b).data ≡ a :=
    show a • ∅ ≡ a from Algebra.MonoidOps.op_right_id
  have eo : ∅ • DisjointLeibnizSet.valid b = .valid b := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
  · exact validN_of_eqv abdp.symm ((validN_data).mp vd)
  · simp [mkData, mkToken, eo, validN_set]
  · rw [Infinite, show (mkData a • mkToken b).token = .valid b from pcore_op_left_L rfl]
    exact inf
  · simp [mkData, mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa [h] using .inl <| rfl
    | inr h => simpa [eo] using .inr h

theorem valid_op?_of_valid_singleton_op {a : A} {x : H A} (h : ✓{n} (singleton k a • mkData x)) :
    ✓{n} a •? get? x k := by
  match h' : get? x k with
  | none => simpa [op?] using (validN_singleton (H := H) k a).mp (validN_op_left h)
  | some g =>
    simp only [op?]
    have vdp := (validN_data_of_validN h) k
    simp only [CMRA.op, singleton, mkData, op_data', Heap.op, get?_merge, Option.merge,
      LawfulPartialMap.get?_singleton, ↓reduceIte, h'] at vdp
    exact vdp

theorem valid_singleton_op_of_valid_op? {a : A} {x : H A} (vx : ✓{n} x) (h : ✓{n} a •? get? x k) :
    ✓{n} singleton k a • mkData x := by
  refine validN_of_eqv (data_op (PartialMap.singleton k a) x) ?_
  refine (validN_data).mpr fun i => ?_
  rw [Heap.get?_op]
  by_cases ki : k = i
  · simp only [← ki, LawfulPartialMap.get?_singleton, ↓reduceIte, Option.some_op_opM]; exact h
  · simp only [LawfulPartialMap.get?_singleton, ki, ↓reduceIte]; exact Heap.validN_get? vx

theorem validN_token_op_iff_disj {e₁ e₂} :
    ✓{n} (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔
      e₁ ## e₂ ∧ setInfinite ((⊤ : CoPset) \ (e₁ ∪ e₂)) where
  mp h := ⟨valid_op_iff_disj.mp (validN_token_of_validN h), by
    have hdisj := valid_op_iff_disj.mp (validN_token_of_validN h)
    have hinf := validN_infinite h
    have htok :
        (mkToken (H := H) (A := A) e₁ • mkToken e₂).token = .valid (e₁ ∪ e₂) := by
      show DisjointLeibnizSet.valid e₁ • DisjointLeibnizSet.valid e₂ = _
      simp only [CMRA.op, hdisj, ↓reduceIte]
    simp only [Infinite, htok] at hinf
    exact hinf⟩
  mpr := fun ⟨hdisj, hinf⟩ => validN_of_eqv (token_union hdisj) (valid_token.mpr hinf).validN

@[rocq_alias dyn_reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a) :
    mkToken (H := H) e ~~> singleton k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_singleton k a).mpr va
  | some z =>
    have ⟨d, t, ze⟩ := split_validN (validN_op_right vo)
    have vedt : ✓{n} mkToken e • (mkData d • mkToken t) := validN_of_eqv (op_right_eqv _ ze) vo
    have disj : ∀ (i : Pos), get? d i = none ∨ ¬i ∈ e :=
      disj_of_validN_data_op_token (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt)))
    have inf : setInfinite ((⊤ : CoPset) \ t) :=
      infinite_data_op_token (validN_of_eqv ze (validN_op_right vo))
    refine validN_of_eqv (op_right_eqv _ ze.symm) ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (mkToken t) (data_op _ _)) ?_
    refine validN_data_op_token (PartialMap.singleton k a • d) t ?_ inf ?_
    · refine validN_of_eqv (data_op _ _).symm ?_
      apply valid_singleton_op_of_valid_op?
      · exact validN_data.mp
          (validN_op_left (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt))))
      · exact (disj k).elim (fun h => h ▸ Valid.validN va) (absurd hke)
    · simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro i
      grind [disj_of_validN_data_op_token (validN_of_eqv ze (validN_op_right vo)),
        (validN_token_op_iff_disj.mp
          (validN_op_right (validN_of_eqv assoc.symm (validN_of_eqv comm vedt)))).left i]

@[rocq_alias dyn_reservation_map_updateP]
theorem updateP {P} {Q : DynReservationMap A H → Prop} k a (ap : a ~~>: P)
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
        (validN_op_left (validN_of_eqv CMRA.assoc
          (validN_of_eqv (op_right_eqv (singleton k a) ze) vaz))))
    refine ⟨singleton k y, apq y py, ?_⟩
    simp only [CMRA.op?] at vaz ⊢
    have inf : setInfinite ((⊤ : CoPset) \ t) :=
      infinite_data_op_token (validN_of_eqv ze (validN_op_right vaz))
    refine validN_of_eqv (op_right_eqv (singleton k y) ze).symm ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (mkToken t) (data_op _ _)) ?_
    refine validN_data_op_token _ _ ?_ inf ?_
    · refine validN_of_eqv (data_op _ _).symm ?_
      refine valid_singleton_op_of_valid_op? ?_ vy
      refine validN_data.mp ?_
      exact validN_op_left <| validN_of_eqv ze (validN_op_right vaz)
    · have ddt := disj_of_validN_data_op_token (validN_of_eqv ze (validN_op_right vaz))
      have dde := disj_of_validN_data_op_token <| validN_of_eqv CMRA.comm
        (validN_op_right (validN_of_eqv CMRA.assoc.symm
          (validN_of_eqv CMRA.comm (validN_of_eqv (CMRA.cmra_op_ne2.eqv .rfl ze) vaz))))
      simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at ddt dde ⊢
      grind

@[rocq_alias dyn_reservation_map_update]
theorem update {k} {a b : A} (uab : a ~~> b) :
    singleton (H := H) k a ~~> singleton k b :=
  Update.of_updateP <| updateP k a (.of_update uab) fun _ => congrArg (singleton k)

end

-- The dynamic reservation of a fresh infinite token set requires a finite map, so that its
-- domain can be avoided when picking the fresh set.
section

variable [LawfulFiniteMap H Pos]

/-- The domain of a finite map `m : H A`, viewed as a finite `CoPset`. -/
def domCoPset (m : H A) : CoPset := FiniteMap.dom_set m

theorem mem_domCoPset {m : H A} {i : Pos} : i ∈ domCoPset m ↔ get? m i ≠ none :=
  (LawfulFiniteMap.mem_dom_set (S := CoPset)).trans (Option.isSome_iff_ne_none (o := get? m i))

theorem domCoPset_finite {m : H A} : setFinite (domCoPset m) := ofList_finite

variable [CMRA A]

@[rocq_alias dyn_reservation_map_reserve]
theorem reserve (Q : DynReservationMap A H → Prop)
    (HQ : ∀ e : CoPset, setInfinite e → Q (mkToken e)) :
    (UCMRA.unit : DynReservationMap A H) ~~>: Q := by
  intro n mz vo
  have ⟨mf, Ef, hz, vmf, hinf, hdisj⟩ :
      ∃ (mf : H A) (Ef : CoPset), (UCMRA.unit •? mz) ≡ mkData mf • mkToken Ef ∧
        ✓{n} mf ∧ setInfinite ((⊤ : CoPset) \ Ef) ∧
        ∀ i, get? mf i = none ∨ i ∉ Ef := by
    match mz with
    | none =>
      exact ⟨∅, ∅, ⟨show (∅ : H A) ≡ ∅ • ∅ from Algebra.MonoidOps.op_left_id.symm,
        (pcore_op_left_L rfl).symm⟩, Heap.valid_empty.validN, empty_infinite,
        fun i => .inl (get?_empty i)⟩
    | some z =>
      have vz : ✓{n} z := validN_of_eqv (unit_left_id (x := z)) vo
      obtain ⟨mf, Ef, hze⟩ := split_validN vz
      refine ⟨mf, Ef, (unit_left_id (x := z)).trans hze, ?_, ?_, ?_⟩
      · exact validN_data.mp (validN_op_left (validN_of_eqv hze vz))
      · exact infinite_data_op_token (validN_of_eqv hze vz)
      · exact disj_of_validN_data_op_token (validN_of_eqv hze vz)
  obtain ⟨E₁, E₂, hEunion, hEdisj, hE₁inf, hE₂inf⟩ :=
    CoPset.split_infinite ((⊤ : CoPset) \ (Ef ∪ domCoPset mf))
      (setInfinite_mono
        (fun i hi =>
          have ⟨hiTEf, hiD⟩ := LawfulSet.mem_diff.mp hi
          LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun hmem =>
            (LawfulSet.mem_union.mp hmem).elim (LawfulSet.mem_diff.mp hiTEf).right hiD⟩)
        (difference_infinite hinf domCoPset_finite))
  have hE₁Ef : E₁ ## Ef := fun i ⟨h₁, hEf⟩ =>
    (LawfulSet.mem_diff.mp (hEunion ▸ LawfulSet.mem_union.mpr (.inl h₁))).right
      (LawfulSet.mem_union.mpr (.inl hEf))
  have hframe : mkToken E₁ •? mz ≡ mkToken E₁ • (mkData mf • mkToken Ef) :=
    (show mkToken E₁ •? mz ≡ mkToken E₁ • (UCMRA.unit •? mz) from
      match mz with
      | none => (unit_right_id (x := mkToken E₁)).symm
      | some z => op_right_eqv (mkToken E₁) (unit_left_id (x := z)).symm).trans
        (op_right_eqv (mkToken E₁) hz)
  refine ⟨mkToken E₁, HQ E₁ hE₁inf, ?_⟩
  refine validN_of_eqv hframe.symm ?_
  have hrearrange :
      mkToken E₁ • (mkData mf • mkToken Ef) ≡ mkData mf • (mkToken E₁ • mkToken Ef) :=
    CMRA.assoc.trans
      ((op_left_eqv (mkToken Ef) (CMRA.comm (x := mkToken E₁) (y := mkData mf))).trans
        CMRA.assoc.symm)
  refine validN_of_eqv hrearrange.symm ?_
  refine validN_of_eqv (op_right_eqv (mkData mf) (token_union hE₁Ef)) ?_
  refine validN_data_op_token mf (E₁ ∪ Ef) (validN_data.mpr vmf) ?_ ?_
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
        have hnd : i ∉ domCoPset mf :=
          fun hd => (LawfulSet.mem_diff.mp hiX).right (LawfulSet.mem_union.mpr (.inr hd))
        exact Decidable.not_not.mp (mt mem_domCoPset.mpr hnd)
      | inr hEf => exact (hdisj i).elim id fun h => absurd hEf h
    · exact .inr hmem

@[rocq_alias dyn_reservation_map_reserve']
theorem reserve' :
    (UCMRA.unit : DynReservationMap A H) ~~>:
      fun x => ∃ e : CoPset, setInfinite e ∧ x = mkToken e :=
  reserve _ fun e hinf => ⟨e, hinf, rfl⟩

end

end DynReservationMap

end CMRA
