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

@[expose] public section

open Iris Std PartialMap

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

@[rocq_alias reservation_map]
structure ReservationMap (A : Type) (H : Type → Type) where
  dataProj : H A
  tokenProj : DisjointLeibnizSet CoPset

def ReservationMap.data [LawfulPartialMap H Pos] (data : H A) :
    ReservationMap A H := .mk data ∅

@[rocq_alias reservation_map_data]
def ReservationMap.singleton [LawfulPartialMap H Pos] (k : Pos) (a : A) :
    ReservationMap A H := ReservationMap.data {[k := a]}

@[rocq_alias reservation_map_token]
def ReservationMap.token [LawfulPartialMap H Pos] (e : CoPset) :
    ReservationMap A H := .mk ∅ (.valid e)

section OFE

open OFE

variable [LawfulPartialMap H Pos] [OFE A]

#rocq_ignore reservation_map_ofe_mixin "Not needed"

@[rocq_alias reservation_mapO]
instance : OFE (ReservationMap A H) where
  Equiv x y := x.dataProj ≡ y.dataProj ∧ x.tokenProj ≡ y.tokenProj
  Dist n x y := x.dataProj ≡{n}≡ y.dataProj ∧ x.tokenProj ≡{n}≡ y.tokenProj
  dist_eqv := {
    refl _ := ⟨.rfl, rfl⟩,
    symm h := ⟨h.left.symm, h.right.symm⟩,
    trans h₁ h₂ := ⟨h₁.left.trans h₂.left, h₁.right.trans h₂.right⟩
  }
  equiv_dist :=
    ⟨fun h n => ⟨equiv_dist.mp h.left n, h.right⟩,
     fun h => ⟨equiv_dist.mpr (h · |>.left), (h 0).right⟩⟩
  dist_lt h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

@[rocq_alias reservation_map_ofe_discrete]
instance instDiscreteReservationMap [Discrete A] : Discrete (ReservationMap A H) where
  discrete_0 h := ⟨discrete_0 h.left, discrete_0 h.right⟩

instance instNonExpansiveReservationMapData :
    NonExpansive (ReservationMap.data (H := H) (A := A)) where
  ne _ _ _ h := ⟨h, Dist.rfl⟩

#rocq_ignore reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias reservation_map_data_ne]
instance instNonExpansiveReservationMapSingleton :
    NonExpansive (ReservationMap.singleton (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, Dist.rfl⟩

@[rocq_alias ReservationMap_discrete]
instance instDiscreteEReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (ReservationMap.mk a b) where
  discrete := fun ⟨ha, hb⟩ => ⟨DiscreteE.discrete ha, DiscreteE.discrete hb⟩

@[rocq_alias reservation_map_data_discrete]
instance instDiscreteEReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (ReservationMap.singleton (H := H) k a) :=
  by unfold ReservationMap.singleton ReservationMap.data;  infer_instance

@[rocq_alias reservation_map_token_discrete]
instance instDiscreteEReservationMapToken :
    DiscreteE (ReservationMap.token (H := H) (A := A) e) :=
  by unfold ReservationMap.token; infer_instance

end OFE

section CMRA

open OFE CMRA DisjointLeibnizSet

namespace ReservationMap

variable [LawfulPartialMap H Pos] [CMRA A]

def ValidN (n : Nat) (x : ReservationMap A H) : Prop :=
  match x.tokenProj with
  | .valid e => ✓{n} x.dataProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ e
  | .error => False

def Valid (x : ReservationMap A H) : Prop :=
  match x.tokenProj with
  | .valid e => ✓ x.dataProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ e
  | .error => False

def validN_unpack {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.dataProj ∧ ✓{n} x.tokenProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := by
  simp only [ValidN] at h
  exact match eq : x.tokenProj with
  | .valid s => ⟨(eq ▸ h).left, (valid_0_iff_validN n).mp trivial, (eq ▸ h).right⟩
  | .error => (eq ▸ h).elim

theorem validN_dataProj_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.dataProj := (validN_unpack h).left

theorem validN_tokenProj_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.tokenProj := (validN_unpack h).right.left

theorem validN_disj {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) (i : Pos) :
  get? x.dataProj i = none ∨ i ∉ x.tokenProj := (validN_unpack h).right.right i

theorem validN_of_parts {n : Nat} {x : ReservationMap A H} (vd : ✓{n} x.dataProj)
    (vt : ✓{n} x.tokenProj) (disj : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj) :
    x.ValidN n := by
  simp only [ValidN]
  cases h : x.tokenProj
  · simp only [h] at disj
    exact ⟨vd, disj⟩
  · exact ((h ▸ not_valid_invalid (S := CoPset)) vt)

def valid_unpack {x : ReservationMap A H} (h : x.Valid) :
    ✓ x.dataProj ∧ ✓ x.tokenProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := by
  simp only [Valid] at h
  exact match eq : x.tokenProj with
  | .valid s => ⟨(eq ▸ h).left, valid_mapN (fun n a => a) trivial, (eq ▸ h).right⟩
  | .error => (eq ▸ h).elim

theorem valid_dataProj_of_valid {x : ReservationMap A H} (h : x.Valid) :
    ✓ x.dataProj := (valid_unpack h).left

theorem valid_tokenProj_of_valid {x : ReservationMap A H} (h : x.Valid) :
    ✓ x.tokenProj := (valid_unpack h).right.left

theorem valid_disj {x : ReservationMap A H} (h : x.Valid) (i : Pos):
    get? x.dataProj i = none ∨ i ∉ x.tokenProj := (valid_unpack h).right.right i

theorem valid_of_parts {x : ReservationMap A H} (vd : ✓ x.dataProj) (vt : ✓ x.tokenProj)
    (disj : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj) : x.Valid := by
  simp only [Valid]
  cases h : x.tokenProj
  · simp only [h] at disj
    exact ⟨vd, disj⟩
  · exact (h ▸ not_valid_invalid) vt

def core (x : ReservationMap A H) : ReservationMap A H := mk (CMRA.core x.dataProj) ∅

@[simp]
theorem core_dataProj (x : ReservationMap A H) :
  x.core.dataProj = CMRA.core x.dataProj := rfl

@[simp]
theorem core_tokenProj (x : ReservationMap A H) : x.core.tokenProj = CMRA.core x.tokenProj :=
  rfl

def op (x y : ReservationMap A H) : ReservationMap A H :=
  mk (x.dataProj • y.dataProj) (x.tokenProj • y.tokenProj)

@[simp]
theorem op_dataProj' (x y : ReservationMap A H): (x.op y).dataProj = x.dataProj • y.dataProj :=
  rfl

@[simp]
theorem op_tokenProj' (x y : ReservationMap A H): (x.op y).tokenProj = x.tokenProj • y.tokenProj :=
  rfl

#rocq_ignore reservation_map_cmra_mixin "Not needed"
#rocq_ignore reservation_map_ucmra_mixin "Not needed"
#rocq_ignore reservation_mapR "Derivable using UCMRA"

@[rocq_alias reservation_mapUR]
instance : UCMRA (ReservationMap A H) where
  pcore := some ∘ core
  Valid := Valid
  ValidN := ValidN
  op := op
  op_ne := ⟨fun n x₁ x₂ h => ⟨Dist.op_r h.left, Dist.op_r h.right⟩⟩
  pcore_ne {n x y cx} e pe := by
    cases Option.some_inj.mp pe.symm
    refine ⟨core y, rfl, ?_, ?_⟩
    · simp [core_dataProj, Dist.core e.left]
    · simp [core_tokenProj, Dist.core e.right]
  validN_ne {n x y} h v := by
    refine validN_of_parts ?_ ?_ ?_
    · exact (Dist.validN h.left).mp (validN_dataProj_of_validN v)
    · exact (Dist.validN h.right).mp (validN_tokenProj_of_validN v)
    · intro i
      cases (validN_disj v) i with
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
    refine ⟨?_, ?_⟩
    · intro h n
      refine validN_of_parts ?_ ?_ ?_
      · exact Valid.validN (valid_dataProj_of_valid h)
      · exact (valid_0_iff_validN n).mp (valid_tokenProj_of_valid h)
      · exact valid_disj h
    · intro v
      refine valid_of_parts ?_ ?_ ?_
      · exact valid_iff_validN.mpr (fun n => validN_dataProj_of_validN (v n))
      · exact valid_iff_validN.mpr (fun n => validN_tokenProj_of_validN (v n))
      · exact validN_disj (v 0)
  validN_succ {x n} v := by
    refine validN_of_parts ?_ ?_ ?_
    · exact validN_succ (validN_dataProj_of_validN v)
    · exact (valid_0_iff_validN n).mp (validN_tokenProj_of_validN (n := n.succ) v)
    · exact validN_disj v
  validN_op_left {n x y} v := by
    refine validN_of_parts ?_ ?_ ?_
    · exact validN_op_left (validN_dataProj_of_validN v)
    · exact validN_op_left (validN_tokenProj_of_validN v)
    · intro i
      cases (validN_disj v) i with
      | inl aa =>
        simp only [op_dataProj', Heap.get?_op] at aa
        exact .inl <| Option.eq_none_of_op_eq_none_left aa
      | inr bb =>
        refine .inr fun HK => bb ?_
        refine (mem_iff_of_validN_union (validN_tokenProj_of_validN v) i).mpr ?_
        exact .inl HK
  assoc := ⟨CMRA.assoc, CMRA.assoc⟩
  comm := ⟨CMRA.comm, CMRA.comm⟩
  pcore_op_left {x cx} h := by
    refine ⟨?_, ?_⟩
    · simp [←Option.some_inj.mp h, op_dataProj', core_dataProj, core_op x.dataProj]
    · simp [←Option.some_inj.mp h, op_tokenProj', core_tokenProj, core_op_L]
  pcore_idem {x cx} h := by
    refine ⟨?_, ?_⟩
    · simp [←Option.some_inj.mp h, core_dataProj, core_idem x.dataProj]
    · simp [←Option.some_inj.mp h, core_tokenProj, core_idem_L]
  pcore_op_mono {x cx} h y := by
    obtain ⟨z, hz⟩ := core_op_mono x.dataProj y.dataProj
    obtain ⟨w, hw⟩ := core_op_mono x.tokenProj y.tokenProj
    refine ⟨mk z w, ?_, ?_⟩
    · simp [op_dataProj', core_dataProj, (Option.some_inj.mp h.symm), hz]
    · simp only [core_tokenProj, op_tokenProj', (Option.some_inj.mp h.symm), leibniz]
      exact hw
  extend {n x y₁ y₂} v exy := by
    obtain ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := CMRA.extend (validN_dataProj_of_validN v) exy.left
    refine ⟨mk z₁ y₁.tokenProj, mk z₂ y₂.tokenProj, ?_, ?_, ?_⟩
    · exact ⟨by simp [op_dataProj', xzz], by simpa [op_tokenProj'] using exy.right⟩
    · exact ⟨zy₁, rfl⟩
    · exact ⟨zy₂, rfl⟩
  unit := mk ∅ ∅
  unit_valid := ⟨Heap.valid_empty, fun _ => .inr CoPset.mem_empty⟩
  unit_left_id {x} := ⟨by simp only [op, Algebra.MonoidOps.op_left_id], pcore_op_left' rfl⟩
  pcore_unit := ⟨Heap.core_empty, .rfl⟩

@[simp]
theorem op_dataProj (x y : ReservationMap A H): (x • y).dataProj = x.dataProj • y.dataProj :=
  rfl

@[simp]
theorem op_tokenProj (x y : ReservationMap A H): (x • y).tokenProj = x.tokenProj • y.tokenProj :=
  rfl

@[rocq_alias reservation_map_cmra_discrete]
instance [CMRA.Discrete A] : CMRA.Discrete (ReservationMap A H) where
  discrete_valid {_} v :=
    valid_of_parts (discrete_valid (validN_dataProj_of_validN v))
      (validN_tokenProj_of_validN v) (validN_disj v)

instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (singleton (H := H) k a) where
  core_id := by
    refine ⟨?_, rfl⟩
    simp [singleton, data, core_eqv_self (PartialMap.singleton k a)]

theorem split_valid {x : ReservationMap A H} (vx : ✓ x) :
    ∃ (d : H A) (t : CoPset), x ≡ data d • token t := by
  rcases x with ⟨xd, xt⟩
  match hh : xt with
  | .error =>
    exact ((not_valid_invalid (S := CoPset)) (hh ▸ (valid_tokenProj_of_valid vx))).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simp [data, token, op_dataProj, Algebra.MonoidOps.op_right_id.symm]
    . simp only [data, token, op_tokenProj, leibniz]
      exact (pcore_op_left_L rfl).symm

theorem split_validN {x : ReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x ≡ data d • token t := by
  rcases x with ⟨xd, xt⟩
  have H := validN_tokenProj_of_validN vx
  match hh : xt with
  | .error => exact ((not_valid_invalid (S := CoPset)) (hh ▸ H)).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simpa [data, token, op_dataProj] using Algebra.MonoidOps.op_right_id.symm
    . exact (pcore_op_left' rfl).symm

theorem valid_data {d : H A} : ✓ (data (H := H) d) ↔ ✓ d :=
  ⟨valid_dataProj_of_valid, fun h => valid_of_parts h ⟨⟩ (fun p => .inr (mem_empty p))⟩

theorem validN_data {d : H A} : ✓{n} (data (H := H) d) ↔ ✓{n} d :=
  ⟨validN_dataProj_of_validN, fun h => validN_of_parts h ⟨⟩ (fun p => .inr (mem_empty p))⟩

@[rocq_alias reservation_map_data_valid]
theorem valid_singleton (k : Pos) (a : A) : ✓ (singleton (H := H) k a) ↔ ✓ a :=
  (valid_data).trans Heap.singleton_valid_iff

theorem validN_singleton (k : Pos) (a : A) : ✓{n} (singleton (H := H) k a) ↔ ✓{n} a :=
  (validN_data).trans Heap.singleton_validN_iff

@[rocq_alias reservation_map_token_valid]
theorem valid_token : ✓ (token (H := H) (A := A) e) :=
  ⟨Heap.valid_empty, fun i => .inl (get?_empty i)⟩

theorem data_op (a b : H A) : data (a • b) ≡ data a • data b :=
  ⟨.rfl, (pcore_op_right_L rfl).symm⟩

@[rocq_alias reservation_map_data_op]
theorem singleton_op k (a b : A) :
    singleton (H := H) k (a • b) ≡ singleton (H := H) k a • singleton k b := by
  refine ((data_op _ _).symm.trans ?_).symm
  exact NonExpansive.eqv (fun i => .of_eq (Heap.singleton_op_singleton i))

theorem token_op (a b : CoPset) (h : a ## b) :
    token (H := H) (A := A) (a ∪ b) ≡ token a • token b := by
  refine ⟨show ∅ ≡ (∅ : H A) • ∅ from Algebra.MonoidOps.op_left_id.symm, ?_⟩
  simp [token, CMRA.op, op_tokenProj', h]

theorem disj_of_validN_data_op_token {a : H A} {b : CoPset} (h : ✓{n} data a • token b) (i : Pos) :
    get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [data, token, op_dataProj, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [data, token, op_tokenProj] at h'
    rw [mem_iff_of_valid_union, not_or] at h'
    · exact .inr <| fun hh => h'.right hh
    · exact valid_of_eqv (pcore_op_left' rfl).symm valid_set

theorem disj_of_valid_data_op_token (a : H A) (b : CoPset) (h : ✓ data a • token b) (i : Pos) :
  get? a i = none ∨ i ∉ b := disj_of_validN_data_op_token (h.validN (n := 0)) i

theorem validN_data_op_token {n : Nat} (a : H A) (b : CoPset) (vd : ✓{n} data a)
    (disj : ∀ i, get? a i = none ∨ i ∉ b) : ✓{n} data a • token b := by
  have abdp : (data a • token b).dataProj ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine validN_of_parts (validN_of_eqv abdp.symm ((validN_data).mp vd))
    (by simp [op_tokenProj, data, token, eo, validN_set])
    fun i => ?_
  simp only [data, token, op_dataProj, Heap.get?_op, get?_empty, op_tokenProj]
  cases disj i with
  | inl h => simpa [h] using .inl <| rfl
  | inr h => simpa [eo] using .inr h

theorem valid_data_op_token (a : H A) (b : CoPset) (vd : ✓ data a)
    (disj : ∀i, get? a i = none ∨ i ∉ b) : ✓ data a • token b := by
  have abdp : (data a • token b).dataProj ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine valid_of_parts (valid_of_eqv abdp.symm ((valid_data).mp vd))
    (by simp [op_tokenProj, data, token, eo, valid_set])
    fun i => ?_
  simp only [data, token, op_dataProj, Heap.get?_op, get?_empty, op_tokenProj]
  cases disj i with
  | inl h => simpa only [h] using .inl <| rfl
  | inr h => simpa only [eo] using .inr h

@[rocq_alias reservation_map_data_mono]
theorem singleton_mono {k} {a b : A} (Hab : a ≼ b) : singleton (H := H) k a ≼ singleton k b :=
  let ⟨z, hz⟩ := Hab
  ⟨singleton k z, (NonExpansive.eqv hz).trans (singleton_op k a z)⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias reservation_map_data_is_op]
instance {ia ib₁ ib₂ : ProofMode.InOut} {a b₁ b₂ : A} [hv : IsOp ia a ib₁ b₁ ib₂ b₂] :
    IsOp ia (singleton (H := H) k a) ib₁ (singleton k b₁) ib₂ (singleton k b₂) where
  is_op := .trans (NonExpansive.eqv hv.is_op ) (singleton_op k b₁ b₂)

@[rocq_alias reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂) :
    token (H := H) (A := A) (e₁ ∪ e₂) ≡ token e₁ • token e₂ := by
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [token, get?_empty, op_dataProj, Heap.get?_op] using .rfl
  · simp [token, CMRA.op, he]

@[rocq_alias reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    token (H := H) (A := A) e₂ ≡ token e₁ • token (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

@[rocq_alias reservation_map_token_valid_op]
theorem valid_token_op_iff_disj {e₁ e₂} :
    ✓ (token (H := H) (A := A) e₁ • token e₂) ↔ e₁ ## e₂ :=
  ⟨fun h => valid_op_iff_disj.mp (valid_tokenProj_of_valid h),
   fun h => (Equiv.valid (token_union h)).mp valid_token⟩

theorem validN_token_op_iff_disj {e₁ e₂} :
    ✓{n} (token (H := H) (A := A) e₁ • token e₂) ↔ e₁ ## e₂ where
  mp h := valid_op_iff_disj.mp (validN_tokenProj_of_validN h)
  mpr h := by
    refine validN_of_parts ?_ ?_ fun i => ?_
    · show ✓{n} ∅ • (∅ : H A)
      refine validN_of_eqv Algebra.MonoidOps.op_left_id.symm ?_
      exact Heap.valid_empty.validN
    · simpa [CMRA.op, token, op, h] using validN_set
    · simpa [token, op_dataProj, op_tokenProj, Heap.get?_op, get?_empty] using .inl rfl

theorem valid_op?_of_valid_singleton_op {a : A} {x : H A} (h : ✓{n} (singleton k a • data x)) :
    ✓{n} a •? get? x k := by
  match h' : get? x k with
  | none => simpa [op?] using (validN_singleton (H := H) k a).mp (validN_op_left h)
  | some g =>
    simp only [op?]
    have vdp := (validN_dataProj_of_validN h) k
    simp only [CMRA.op, singleton, data, op_dataProj', Heap.op, get?_merge, Option.merge,
      LawfulPartialMap.get?_singleton, ↓reduceIte, h'] at vdp
    exact vdp

theorem valid_singleton_op_of_valid_op? {a : A} {x : H A} (vx : ✓{n} x) (h : ✓{n} a •? get? x k) :
    ✓{n} singleton k a • data x := by
  refine validN_of_eqv (data_op (PartialMap.singleton k a) x) ?_
  refine (validN_data).mpr fun i => ?_
  rw [Heap.get?_op]
  by_cases ki : k = i
  · simpa only [← ki, LawfulPartialMap.get?_singleton, ↓reduceIte, Option.some_op_opM] using h
  · simpa only [LawfulPartialMap.get?_singleton, ki, ↓reduceIte] using Heap.validN_get? vx

@[rocq_alias reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a) : token (H := H) e ~~> singleton k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_singleton k a).mpr va
  | some z =>
    have ⟨d, t, ze⟩ := split_validN (validN_op_right vo)
    have vedt : ✓{n} token e • (data d • token t) := validN_of_eqv (op_right_eqv _ ze) vo
    have disj : ∀ (i : Pos), get? d i = none ∨ ¬i ∈ e:=
      disj_of_validN_data_op_token (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt)))
    refine validN_of_eqv (op_right_eqv _ ze.symm) ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (token t) (data_op _ _)) ?_
    refine validN_data_op_token (PartialMap.singleton k a • d) t ?_ ?_
    · refine validN_of_eqv (data_op _ _).symm ?_
      apply valid_singleton_op_of_valid_op?
      · exact validN_data.mp (validN_op_left (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt))))
      · exact (disj k).elim (fun h => h ▸ Valid.validN va) (absurd hke)
    · simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro i
      grind [disj_of_validN_data_op_token (validN_of_eqv ze (validN_op_right vo)),
        validN_token_op_iff_disj.mp (validN_op_right (validN_of_eqv assoc.symm (validN_of_eqv comm vedt))) i]

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
        (validN_op_left (validN_of_eqv CMRA.assoc
          (validN_of_eqv (op_right_eqv (singleton k a) ze) vaz))))
    refine ⟨singleton k y, apq y py, ?_⟩
    simp only [CMRA.op?] at vaz ⊢
    refine validN_of_eqv (op_right_eqv (singleton k y) ze).symm ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (token t) (data_op _ _)) ?_
    refine validN_data_op_token _ _ ?_ ?_
    · refine validN_of_eqv (data_op _ _).symm ?_
      refine valid_singleton_op_of_valid_op? ?_ vy
      refine validN_data.mp ?_
      exact validN_op_left $ validN_of_eqv ze (validN_op_right vaz)
    · have ddt := disj_of_validN_data_op_token (validN_of_eqv ze (validN_op_right vaz))
      have dde := disj_of_validN_data_op_token <| validN_of_eqv CMRA.comm
        (validN_op_right (validN_of_eqv CMRA.assoc.symm
          (validN_of_eqv CMRA.comm (validN_of_eqv (CMRA.cmra_op_ne2.eqv .rfl ze) vaz))))
      simp only [CMRA.op, Heap.op, get?_merge, LawfulPartialMap.get?_singleton,
        Option.merge_eq_none_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at ddt dde ⊢
      grind

@[rocq_alias reservation_map_update]
theorem reservation_map_update {k} {a b : A} (uab : a ~~> b):
    singleton (H := H) k a ~~> singleton k b :=
  Update.of_updateP <| updateP k a (.of_update uab) fun _ => congrArg (singleton k)

end ReservationMap

end CMRA
