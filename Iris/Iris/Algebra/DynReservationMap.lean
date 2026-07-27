/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
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

@[expose] public section

open Std PartialMap

universe u v

/-!
The camera [DynReservationMap A H] over a camera [A] extends [LawfulPartialMap H Pos]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : CoPset] which represent the right to allocate a map entry at any position
[k ∈ E]. Unlike [ReservationMap], [DynReservationMap] supports dynamically
allocating these tokens, including infinite sets of them.
-/

@[rocq_alias dyn_reservation_map]
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

@[rocq_alias dyn_reservation_mapO]
instance : OFE (DynReservationMap A H) where
  Dist n x y := x.data ≡{n}≡ y.data ∧ x.token ≡{n}≡ y.token
  dist_eqv := {
    refl _ := ⟨.rfl, rfl⟩,
    symm h := ⟨h.left.symm, h.right.symm⟩,
    trans h₁ h₂ := ⟨h₁.left.trans h₂.left, h₁.right.trans h₂.right⟩
  }
  eq_dist {x y} := by
    refine ⟨fun h _ => h ▸ ⟨.rfl, .rfl⟩, fun H => ?_⟩
    obtain ⟨xd, xt⟩ := x; obtain ⟨yd, yt⟩ := y
    simp only [DynReservationMap.mk.injEq]
    exact ⟨eq_dist.mpr fun n => (H n).1, eq_dist.mpr fun n => (H n).2⟩
  dist_lt h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

@[rocq_alias dyn_reservation_map_ofe_discrete]
instance instDiscreteDynReservationMap [Discrete A] : Discrete (DynReservationMap A H) where
  discrete_0 h := fun n => ⟨(discrete_0 h.left) n, (discrete_0 h.right) n⟩

#rocq_ignore dyn_reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias dyn_reservation_map_data_ne]
instance instNonExpansiveDynReservationMapSingleton :
    NonExpansive (DynReservationMap.mkData (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, rfl⟩

@[rocq_alias DynReservationMap_discrete]
instance instDiscreteEDynReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (DynReservationMap.mk a b) where
  discrete := fun h n => ⟨(DiscreteE.discrete h.1) n, (DiscreteE.discrete h.2) n⟩

@[rocq_alias dyn_reservation_map_data_discrete]
instance instDiscreteEDynReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (DynReservationMap.mkData (H := H) k a) :=
  by unfold DynReservationMap.mkData; infer_instance

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
    have hdisj : e₁ ## e₂ := valid_op_iff_disj.mp hv
    simp only [Infinite, ht] at ⊢
    simp only [Infinite, op_token', ht, hy, CMRA.op, hdisj, ↓reduceIte] at inf
    exact setInfinite_mono
      (fun i hi => mem_diff.mpr ⟨(mem_diff.mp hi).left,
        fun hc => (mem_diff.mp hi).right (mem_union.mpr (.inl hc))⟩) inf

#rocq_ignore dyn_reservation_map_cmra_mixin "Not needed"
#rocq_ignore dyn_reservation_map_ucmra_mixin "Not needed"
#rocq_ignore dyn_reservation_mapR "Derivable using UCMRA"

@[rocq_alias dyn_reservation_mapUR]
instance instUCMRADynReservationMap : UCMRA (DynReservationMap A H) where
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
  assoc := fun n => ⟨CMRA.assoc n, CMRA.assoc n⟩
  comm := fun n => ⟨CMRA.comm n, CMRA.comm n⟩
  pcore_op_left {x cx} h := by
    refine fun n => ⟨?_, ?_⟩
    · simp only [←Option.some_inj.mp h, op_data', core_data]
      exact (core_op x.data) n
    · simp [←Option.some_inj.mp h, op_token', core_token, core_op_L]
  pcore_idem {x cx} h := by
    cases Option.some_inj.mp h.symm
    rcases x with ⟨xd, xt⟩
    apply OFE.Equiv.of_eq
    grind only [core, OFE.Equiv.to_eq, core_idem]
  pcore_op_mono {x cx} h y := by
    obtain ⟨z, hz⟩ := core_op_mono x.data y.data
    obtain ⟨w, hw⟩ := core_op_mono x.token y.token
    refine ⟨mk z w, fun n => ⟨?_, ?_⟩⟩
    · simp only [op_data', core_data, (Option.some_inj.mp h.symm)]
      exact hz n
    · simp only [core_token, op_token', (Option.some_inj.mp h.symm)]
      exact hw n
  extend {n x y₁ y₂} v exy := by
    obtain ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := CMRA.extend (validN_data_of_validN v) exy.left
    exact ⟨mk z₁ y₁.token, mk z₂ y₂.token, (fun m => ⟨xzz m, exy.right⟩),
      ⟨zy₁, rfl⟩, ⟨zy₂, rfl⟩⟩
  unit := mk ∅ ∅
  unit_valid := valid_iff.mpr ⟨Heap.valid_empty, valid_set,
    show setInfinite ((⊤ : CoPset) \ ∅) by rw [diff_empty]; exact top_infinite,
    fun _ => .inr (mem_empty _)⟩
  unit_left_id {x} := fun n => ⟨(Algebra.MonoidOps.op_left_id : (∅ : H A) • x.data ≡ x.data) n,
    (pcore_op_left' (OFE.Equiv.of_eq rfl)) n⟩
  pcore_unit := fun n => ⟨Heap.core_empty n, .rfl⟩

@[simp]
theorem op_data (x y : DynReservationMap A H) : (x • y).data = x.data • y.data := rfl

@[simp]
theorem op_token (x y : DynReservationMap A H) : (x • y).token = x.token • y.token := rfl

@[rocq_alias dyn_reservation_map_included]
theorem included {x y : DynReservationMap A H} :
    x ≼ y ↔ x.data ≼ y.data ∧ x.token ≼ y.token := by
  refine ⟨fun ⟨z, hz⟩ => ⟨⟨z.data, fun n => (hz n).left⟩,
    ⟨z.token, fun n => (hz n).right⟩⟩, ?_⟩
  exact fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨mk z₁ z₂, fun n => ⟨hz₁ n, hz₂ n⟩⟩

@[rocq_alias dyn_reservation_map_data_proj_validN]
theorem data_proj_validN {n} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.data :=
  validN_data_of_validN h

@[rocq_alias dyn_reservation_map_token_proj_validN]
theorem token_proj_validN {n} {x : DynReservationMap A H} (h : ✓{n} x) : ✓{n} x.token :=
  validN_token_of_validN h

@[rocq_alias dyn_reservation_map_cmra_discrete]
instance [CMRA.Discrete A] : CMRA.Discrete (DynReservationMap A H) where
  discrete_valid {_} v := valid_iff.mpr ⟨discrete_valid (validN_data_of_validN v),
    validN_token_of_validN v, validN_infinite v, validN_disj v⟩

@[rocq_alias dyn_reservation_map_data_core_id]
instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (mkData (H := H) k a) where
  core_id := OFE.Equiv.of_eq <| congrArg some <| congrArg (mk (token := ∅))
    (core_eqv_self (PartialMap.singleton k a : H A)).to_eq

theorem split_validN {x : DynReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x ≡ mk d ∅ • mkToken t := by
  rcases x with ⟨xd, xt⟩
  cases xt with
  | error => exact (not_validN_invalid (S := CoPset) (validN_token_of_validN vx)).elim
  | valid t =>
    refine ⟨xd, t, fun m => ⟨?_, ?_⟩⟩
    · exact (show xd ≡ xd • (∅ : H A) from Algebra.MonoidOps.op_right_id.symm) m
    · exact ((pcore_op_left' (OFE.Equiv.of_eq rfl)).symm) m

theorem valid_mkData_singleton : ✓ (mkData (H := H) k a) ↔ ✓ ({[k := a]} : H A) :=
  ⟨valid_data_of_valid, fun h => valid_iff.mpr ⟨h, valid_set, top_infinite,
    fun p => .inr (mem_empty p)⟩⟩

theorem validN_mkData_singleton : ✓{n} (mkData (H := H) k a) ↔ ✓{n} ({[k := a]} : H A) :=
  ⟨validN_data_of_validN, fun h => validN_iff.mpr ⟨h, validN_set, top_infinite,
    fun p => .inr (mem_empty p)⟩⟩

@[rocq_alias dyn_reservation_map_data_valid]
theorem valid_mkData (k : Pos) (a : A) : ✓ (mkData (H := H) k a) ↔ ✓ a :=
  valid_mkData_singleton.trans Heap.singleton_valid_iff

theorem validN_mkData (k : Pos) (a : A) : ✓{n} (mkData (H := H) k a) ↔ ✓{n} a :=
  validN_mkData_singleton.trans Heap.singleton_validN_iff

@[rocq_alias dyn_reservation_map_token_valid]
theorem valid_token {e : CoPset} :
    ✓ (mkToken (H := H) (A := A) e) ↔ setInfinite ((⊤ : CoPset) \ e) :=
  ⟨valid_infinite, fun hinf => valid_iff.mpr
    ⟨Heap.valid_empty, valid_set, hinf, fun i => .inl (get?_empty i)⟩⟩

@[rocq_alias dyn_reservation_map_data_op]
theorem mkData_op k (a b : A) :
    mkData (H := H) k (a • b) ≡ mkData k a • mkData k b :=
  fun _ => ⟨(fun i => Dist.of_eq (Heap.singleton_op_singleton i).symm),
    Dist.of_eq (pcore_op_right_L rfl).symm⟩

@[rocq_alias dyn_reservation_map_data_mono]
theorem mkData_mono {k} {a b : A} (Hab : a ≼ b) :
    mkData (H := H) k a ≼ mkData k b :=
  let ⟨z, hz⟩ := Hab
  ⟨mkData k z, (NonExpansive.eqv hz).trans (mkData_op k a z)⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias dyn_reservation_map_data_is_op]
instance {d : IsOp.Direction} {a b₁ b₂ : A} [hv : IsOp d a b₁ b₂] :
    IsOp d (mkData (H := H) k a) (mkData k b₁) (mkData k b₂) where
  is_op := .trans (NonExpansive.eqv hv.is_op) (mkData_op k b₁ b₂)

@[rocq_alias dyn_reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂) :
    mkToken (H := H) (A := A) (e₁ ∪ e₂) ≡ mkToken e₁ • mkToken e₂ := by
  refine fun n => ⟨fun i => ?_, ?_⟩
  · simpa only [mkToken, get?_empty, op_data, Heap.get?_op] using .rfl
  · simp [mkToken, CMRA.op, he]

@[rocq_alias dyn_reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    mkToken (H := H) (A := A) e₂ ≡ mkToken e₁ • mkToken (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

theorem disj_of_validN_data_op_token {a : H A} {b : CoPset}
    (h : ✓{n} mk a ∅ • mkToken b) (i : Pos) : get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [mkToken, op_data, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [mkToken, op_token] at h'
    rw [mem_iff_of_valid_union, not_or] at h'
    · exact .inr h'.right
    · exact valid_of_eqv (pcore_op_left' (OFE.Equiv.of_eq rfl)).symm valid_set

theorem infinite_data_op_token {a : H A} {b : CoPset} (h : ✓{n} mk a ∅ • mkToken b) :
    setInfinite ((⊤ : CoPset) \ b) := by
  simpa only [Infinite, show (mk a ∅ • mkToken b).token = .valid b from
    pcore_op_left_L rfl] using validN_infinite h

theorem validN_data_op_token {n : Nat} {a : H A} {b : CoPset} (vd : ✓{n} a)
    (inf : setInfinite ((⊤ : CoPset) \ b)) (disj : ∀ i, get? a i = none ∨ i ∉ b) :
    ✓{n} mk a ∅ • mkToken b := by
  have abdp : (mk a ∅ • mkToken b).data ≡ a :=
    show a • ∅ ≡ a from Algebra.MonoidOps.op_right_id
  have eo : ∅ • DisjointLeibnizSet.valid b = .valid b := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, ?_, fun i => ?_⟩
  · exact abdp.symm.to_eq ▸ vd
  · simp [mkToken, eo, validN_set]
  · rw [Infinite, show (mk a ∅ • mkToken b).token = .valid b from pcore_op_left_L rfl]
    exact inf
  · simp [mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa [h] using .inl rfl
    | inr h => simpa [eo] using .inr h

theorem valid_op?_of_valid_mkData_op_data {a : A} {x : H A}
    (h : ✓{n} (mkData k a • mk x ∅)) : ✓{n} a •? get? x k := by
  match h' : get? x k with
  | none => simpa [op?] using (validN_mkData (H := H) k a).mp (validN_op_left h)
  | some g =>
    simp only [op?]
    apply Option.some_validN.mp
    simpa only [CMRA.op, mkData, op_data', Heap.op, get?_merge, Option.merge,
      LawfulPartialMap.get?_singleton, ↓reduceIte, h'] using (validN_data_of_validN h) k

theorem valid_mkData_op_data_of_valid_op? {a : A} {x : H A} (vx : ✓{n} x)
    (h : ✓{n} a •? get? x k) : ✓{n} mkData k a • mk x ∅ := by
  have htok : (mkData k a • mk x ∅).token = .valid (∅ : CoPset) := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · show ✓{n} ({[k := a]} : H A) • x
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

theorem validN_token_op_iff_disj {e₁ e₂} :
    ✓{n} (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔
      e₁ ## e₂ ∧ setInfinite ((⊤ : CoPset) \ (e₁ ∪ e₂)) := by
  refine ⟨fun h => ⟨valid_op_iff_disj.mp (validN_token_of_validN h), ?_⟩,
    fun ⟨hdisj, hinf⟩ => validN_of_eqv (token_union hdisj) (valid_token.mpr hinf).validN⟩
  have hdisj := valid_op_iff_disj.mp (validN_token_of_validN h)
  simpa only [Infinite, op_token', mkToken, CMRA.op, hdisj, ↓reduceIte] using validN_infinite h

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
    have vdt := ze.to_eq ▸ validN_op_right vo
    have vedt : ✓{n} mkToken e • (mk d ∅ • mkToken t) :=
      (op_right_eqv _ ze).to_eq ▸ vo
    have disj : ∀ i : Pos, get? d i = none ∨ i ∉ e :=
      disj_of_validN_data_op_token
        (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt)))
    change ✓{n} mkData k a • z
    rw [← (op_right_eqv _ ze.symm).to_eq, ← CMRA.assoc.symm.to_eq,
      ← (op_left_eqv (mkToken t)
      (show mk ({[k := a]} • d) ∅ ≡ mkData k a • mk d ∅ from
        fun n => ⟨.rfl, Dist.of_eq (pcore_op_right_L rfl).symm⟩)).to_eq]
    refine validN_data_op_token ?_ (infinite_data_op_token vdt) ?_
    · refine validN_data_of_validN <| valid_mkData_op_data_of_valid_op? ?_ ?_
      · exact validN_data_of_validN
          (validN_op_left (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt))))
      · exact (disj k).elim (fun h => h ▸ Valid.validN va) (absurd hke)
    · simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro i
      grind [disj_of_validN_data_op_token vdt,
        (validN_token_op_iff_disj.mp
          (validN_op_right (validN_of_eqv assoc.symm (validN_of_eqv comm vedt)))).left i]

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
    have vdt := ze.to_eq ▸ validN_op_right vaz
    obtain ⟨y, py, vy⟩ := ap n (get? d k)
      (valid_op?_of_valid_mkData_op_data
        (validN_op_left (validN_of_eqv CMRA.assoc
          (validN_of_eqv (op_right_eqv (mkData k a) ze) vaz))))
    refine ⟨mkData k y, apq y py, ?_⟩
    simp only [CMRA.op?] at vaz ⊢
    rw [← (op_right_eqv (mkData k y) ze).symm.to_eq, ← CMRA.assoc.symm.to_eq,
      ← (op_left_eqv (mkToken t)
      (show mk ({[k := y]} • d) ∅ ≡ mkData k y • mk d ∅ from
        fun n => ⟨.rfl, Dist.of_eq (pcore_op_right_L rfl).symm⟩)).to_eq]
    refine validN_data_op_token ?_ (infinite_data_op_token vdt) ?_
    · exact validN_data_of_validN <| valid_mkData_op_data_of_valid_op?
        (validN_data_of_validN (validN_op_left vdt)) vy
    · have ddt := disj_of_validN_data_op_token vdt
      have dde := disj_of_validN_data_op_token <| validN_of_eqv CMRA.comm
        (validN_op_right (validN_of_eqv CMRA.assoc.symm
          (validN_of_eqv CMRA.comm (validN_of_eqv (CMRA.cmra_op_ne2.eqv .rfl ze) vaz))))
      simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
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

variable [CMRA A]

@[rocq_alias dyn_reservation_map_reserve]
theorem reserve (Q : DynReservationMap A H → Prop)
    (HQ : ∀ e : CoPset, setInfinite e → Q (mkToken e)) :
    (UCMRA.unit : DynReservationMap A H) ~~>: Q := by
  intro n mz vo
  have ⟨mf, Ef, hz, vmf, hinf, hdisj⟩ :
      ∃ (mf : H A) (Ef : CoPset), (UCMRA.unit •? mz) ≡ mk mf ∅ • mkToken Ef ∧
        ✓{n} mf ∧ setInfinite ((⊤ : CoPset) \ Ef) ∧
        ∀ i, get? mf i = none ∨ i ∉ Ef := by
    match mz with
    | none =>
      exact ⟨∅, ∅, (fun n =>
        ⟨(show (∅ : H A) ≡ ∅ • ∅ from Algebra.MonoidOps.op_left_id.symm) n,
          Dist.of_eq (pcore_op_left_L rfl).symm⟩), Heap.valid_empty.validN, top_infinite,
        fun i => .inl (get?_empty i)⟩
    | some z =>
      have vz : ✓{n} z := (unit_left_id (x := z)).to_eq ▸ vo
      obtain ⟨mf, Ef, hze⟩ := split_validN vz
      have vze := hze.to_eq ▸ vz
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
  have hframe : (mkToken (H := H) (A := A) E₁) •? mz ≡
      mkToken E₁ • ((mk mf ∅ : DynReservationMap A H) • mkToken Ef) :=
    (show (mkToken (H := H) (A := A) E₁) •? mz ≡
        mkToken E₁ • (UCMRA.unit •? mz) from
      match mz with
      | none => (unit_right_id (x := mkToken E₁)).symm
      | some z => op_right_eqv (mkToken E₁) (unit_left_id (x := z)).symm).trans
        (op_right_eqv (mkToken E₁) hz)
  refine ⟨mkToken E₁, HQ E₁ hE₁inf, ?_⟩
  have hrearrange :
      (mkToken (H := H) (A := A) E₁) • ((mk mf ∅ : DynReservationMap A H) • mkToken Ef) ≡
        (mk mf ∅ : DynReservationMap A H) • (mkToken E₁ • mkToken Ef) :=
    CMRA.assoc.trans
      ((op_left_eqv (mkToken Ef) (CMRA.comm (x := mkToken E₁) (y := mk mf ∅))).trans
        CMRA.assoc.symm)
  rw [← hframe.symm.to_eq, ← hrearrange.symm.to_eq,
    ← (op_right_eqv (mk mf ∅ : DynReservationMap A H) (token_union hE₁Ef)).to_eq]
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
    (UCMRA.unit : DynReservationMap A H) ~~>:
      fun x => ∃ e : CoPset, setInfinite e ∧ x = mkToken e :=
  reserve _ fun e hinf => ⟨e, hinf, rfl⟩

end

end DynReservationMap

end CMRA
