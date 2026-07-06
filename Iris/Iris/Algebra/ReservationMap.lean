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
  data : H A
  token : CoPsetDisjL

def ReservationMap.mkData [LawfulPartialMap H Pos] (data : H A) :
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

@[rocq_alias reservation_mapO]
instance : OFE (ReservationMap A H) where
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

@[rocq_alias reservation_map_ofe_discrete]
instance instDiscreteReservationMap [Discrete A] : Discrete (ReservationMap A H) where
  discrete_0 h := ⟨discrete_0 h.left, discrete_0 h.right⟩

instance instNonExpansiveReservationMapData :
    NonExpansive (ReservationMap.mkData (H := H) (A := A)) where
  ne _ _ _ h := ⟨h, rfl⟩

#rocq_ignore reservation_map_data_proper "Derivable using NonExpansive.eqv"

@[rocq_alias reservation_map_data_ne]
instance instNonExpansiveReservationMapSingleton :
    NonExpansive (ReservationMap.singleton (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, rfl⟩

@[rocq_alias ReservationMap_discrete]
instance instDiscreteEReservationMapMk {a : H A} [DiscreteE a] :
    DiscreteE (ReservationMap.mk a b) where
  discrete := fun ⟨ha, hb⟩ => ⟨DiscreteE.discrete ha, DiscreteE.discrete hb⟩

@[rocq_alias reservation_map_data_discrete]
instance instDiscreteEReservationMapSingleton {a : A} [DiscreteE a] :
    DiscreteE (ReservationMap.singleton (H := H) k a) :=
  by unfold ReservationMap.singleton ReservationMap.mkData;  infer_instance

@[rocq_alias reservation_map_token_discrete]
instance instDiscreteEReservationMapToken :
    DiscreteE (ReservationMap.mkToken (H := H) (A := A) e) :=
  by unfold ReservationMap.mkToken; infer_instance

end OFE

section CMRA

open OFE CMRA DisjointLeibnizSet

namespace ReservationMap

variable [LawfulPartialMap H Pos] [CMRA A]

def ValidN (n : Nat) (x : ReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓{n} x.data ∧ ∀i, get? x.data i = none ∨ i ∉ e
  | .error => False

def Valid (x : ReservationMap A H) : Prop :=
  match x.token with
  | .valid e => ✓ x.data ∧ ∀i, get? x.data i = none ∨ i ∉ e
  | .error => False

theorem validN_iff {n : Nat} {x : ReservationMap A H} :
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
    · exact ((h ▸ not_valid_invalid (S := CoPset)) vt)

theorem valid_iff {x : ReservationMap A H} :
    x.Valid ↔ ✓ x.data ∧ ✓ x.token ∧ ∀ i, get? x.data i = none ∨ i ∉ x.token := by
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

theorem validN_data_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.data := (validN_iff.mp h).left

theorem validN_token_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) :
    ✓{n} x.token := (validN_iff.mp h).right.left

theorem validN_disj {n : Nat} {x : ReservationMap A H} (h : x.ValidN n) (i : Pos) :
    get? x.data i = none ∨ i ∉ x.token := (validN_iff.mp h).right.right i

theorem valid_data_of_valid {x : ReservationMap A H} (h : x.Valid) :
    ✓ x.data := (valid_iff.mp h).left

theorem valid_token_of_valid {x : ReservationMap A H} (h : x.Valid) :
    ✓ x.token := (valid_iff.mp h).right.left

theorem valid_disj {x : ReservationMap A H} (h : x.Valid) (i : Pos):
    get? x.data i = none ∨ i ∉ x.token := (valid_iff.mp h).right.right i

def core (x : ReservationMap A H) : ReservationMap A H := mk (CMRA.core x.data) ∅

@[simp]
theorem core_data (x : ReservationMap A H) : x.core.data = CMRA.core x.data := rfl

@[simp]
theorem core_token (x : ReservationMap A H) : x.core.token = CMRA.core x.token := rfl

def op (x y : ReservationMap A H) : ReservationMap A H := mk (x.data • y.data) (x.token • y.token)

@[simp]
theorem op_data' (x y : ReservationMap A H) : (x.op y).data = x.data • y.data := rfl

@[simp]
theorem op_token' (x y : ReservationMap A H) : (x.op y).token = x.token • y.token := rfl

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
    · simp [Dist.core e.left]
    · simp [Dist.core e.right]
  validN_ne {n x y} h v := by
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
  validN_succ {x n} v := by
    refine validN_iff.mpr ⟨?_, ?_, ?_⟩
    · exact validN_succ (validN_data_of_validN v)
    · exact (valid_0_iff_validN n).mp (validN_token_of_validN (n := n.succ) v)
    · exact validN_disj v
  validN_op_left {n x y} v := by
    refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
    · exact validN_op_left (validN_data_of_validN v)
    · exact validN_op_left (validN_token_of_validN v)
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
  unit_valid := ⟨Heap.valid_empty, fun _ => .inr CoPset.mem_empty⟩
  unit_left_id {x} := ⟨by simp only [op, Algebra.MonoidOps.op_left_id], pcore_op_left' rfl⟩
  pcore_unit := ⟨Heap.core_empty, .rfl⟩

@[simp]
theorem op_data (x y : ReservationMap A H): (x • y).data = x.data • y.data := rfl

@[simp]
theorem op_token (x y : ReservationMap A H): (x • y).token = x.token • y.token := rfl

@[rocq_alias reservation_map_cmra_discrete]
instance [CMRA.Discrete A] : CMRA.Discrete (ReservationMap A H) where
  discrete_valid {_} v := by
    refine valid_iff.mpr ⟨?_, ?_, ?_⟩
    · exact discrete_valid (validN_data_of_validN v)
    · exact validN_token_of_validN v
    · exact validN_disj v

instance instCoreIdSingleton {a : A} [CoreId a] : CoreId (singleton (H := H) k a) where
  core_id := by
    refine ⟨?_, rfl⟩
    simp [singleton, mkData, core_eqv_self (PartialMap.singleton k a)]

theorem split_valid {x : ReservationMap A H} (vx : ✓ x) :
    ∃ (d : H A) (t : CoPset), x ≡ mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  match hh : xt with
  | .error =>
    exact ((not_valid_invalid (S := CoPset)) (hh ▸ (valid_token_of_valid vx))).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simp [mkData, mkToken, op_data, Algebra.MonoidOps.op_right_id.symm]
    . simp only [mkData, mkToken, op_token, leibniz]
      exact (pcore_op_left_L rfl).symm

theorem split_validN {x : ReservationMap A H} (vx : ✓{n} x) :
    ∃ (d : H A) (t : CoPset), x ≡ mkData d • mkToken t := by
  rcases x with ⟨xd, xt⟩
  have H := validN_token_of_validN vx
  match hh : xt with
  | .error => exact ((not_valid_invalid (S := CoPset)) (hh ▸ H)).elim
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simpa [mkData, mkToken, op_data] using Algebra.MonoidOps.op_right_id.symm
    . exact (pcore_op_left' rfl).symm

theorem valid_data {d : H A} : ✓ (mkData (H := H) d) ↔ ✓ d :=
  ⟨valid_data_of_valid, fun h => valid_iff.mpr ⟨h, ⟨⟩, fun p => .inr (mem_empty p)⟩⟩

theorem validN_data {d : H A} : ✓{n} (mkData (H := H) d) ↔ ✓{n} d :=
  ⟨validN_data_of_validN, fun h => validN_iff.mpr ⟨h, ⟨⟩, (fun p => .inr (mem_empty p))⟩⟩

@[rocq_alias reservation_map_data_valid]
theorem valid_singleton (k : Pos) (a : A) : ✓ (singleton (H := H) k a) ↔ ✓ a :=
  (valid_data).trans Heap.singleton_valid_iff

theorem validN_singleton (k : Pos) (a : A) : ✓{n} (singleton (H := H) k a) ↔ ✓{n} a :=
  (validN_data).trans Heap.singleton_validN_iff

@[rocq_alias reservation_map_token_valid]
theorem valid_token : ✓ (mkToken (H := H) (A := A) e) :=
  ⟨Heap.valid_empty, fun i => .inl (get?_empty i)⟩

theorem data_op (a b : H A) : mkData (a • b) ≡ mkData a • mkData b :=
  ⟨.rfl, (pcore_op_right_L rfl).symm⟩

@[rocq_alias reservation_map_data_op]
theorem singleton_op k (a b : A) :
    singleton (H := H) k (a • b) ≡ singleton (H := H) k a • singleton k b := by
  refine ((data_op _ _).symm.trans ?_).symm
  exact NonExpansive.eqv (fun i => .of_eq (Heap.singleton_op_singleton i))

theorem token_op (a b : CoPset) (h : a ## b) :
    mkToken (H := H) (A := A) (a ∪ b) ≡ mkToken a • mkToken b := by
  refine ⟨show ∅ ≡ (∅ : H A) • ∅ from Algebra.MonoidOps.op_left_id.symm, ?_⟩
  simp [mkToken, CMRA.op, op_token', h]

theorem disj_of_validN_data_op_token {a : H A} {b : CoPset} (h : ✓{n} mkData a • mkToken b) (i : Pos) :
    get? a i = none ∨ i ∉ b := by
  cases validN_disj h i with
  | inl h =>
    simp only [mkData, mkToken, op_data, Heap.get?_op, get?_empty] at h
    exact .inl <| Option.eq_none_of_op_eq_none_left h
  | inr h' =>
    simp only [mkData, mkToken, op_token] at h'
    rw [mem_iff_of_valid_union, not_or] at h'
    · exact .inr <| h'.right
    · exact valid_of_eqv (pcore_op_left' rfl).symm valid_set

theorem disj_of_valid_data_op_token (a : H A) (b : CoPset) (h : ✓ mkData a • mkToken b) (i : Pos) :
  get? a i = none ∨ i ∉ b := disj_of_validN_data_op_token (h.validN (n := 0)) i

theorem validN_data_op_token {n : Nat} (a : H A) (b : CoPset) (vd : ✓{n} mkData a)
    (disj : ∀ i, get? a i = none ∨ i ∉ b) : ✓{n} mkData a • mkToken b := by
  have abdp : (mkData a • mkToken b).data ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
  · exact validN_of_eqv abdp.symm ((validN_data).mp vd)
  · simp [mkData, mkToken, eo, validN_set]
  · simp [mkData, mkToken, op_data, Heap.get?_op, get?_empty, op_token]
    cases disj i with
    | inl h => simpa [h] using .inl <| rfl
    | inr h => simpa [eo] using .inr h

theorem valid_data_op_token (a : H A) (b : CoPset) (vd : ✓ mkData a)
    (disj : ∀i, get? a i = none ∨ i ∉ b) : ✓ mkData a • mkToken b := by
  have abdp : (mkData a • mkToken b).data ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • valid b = .valid b := pcore_op_left_L rfl
  refine valid_iff.mpr ⟨?_, ?_, fun i => ?_⟩
  · exact valid_of_eqv abdp.symm ((valid_data).mp vd)
  · simp [op_token, mkData, mkToken, eo, valid_set]
  · simp only [mkData, mkToken, op_data, Heap.get?_op, get?_empty, op_token]
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
    mkToken (H := H) (A := A) (e₁ ∪ e₂) ≡ mkToken e₁ • mkToken e₂ := by
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [mkToken, get?_empty, op_data, Heap.get?_op] using .rfl
  · simp [mkToken, CMRA.op, he]

@[rocq_alias reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂) :
    mkToken (H := H) (A := A) e₂ ≡ mkToken e₁ • mkToken (e₂ \ e₁) := by
  refine .trans ?_ (token_union LawfulSet.disjoint_diff_right)
  rw [LawfulSet.subset_union_diff he]

@[rocq_alias reservation_map_token_valid_op]
theorem valid_token_op_iff_disj {e₁ e₂} :
    ✓ (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔ e₁ ## e₂ :=
  ⟨fun h => valid_op_iff_disj.mp (valid_token_of_valid h),
   fun h => (Equiv.valid (token_union h)).mp valid_token⟩

theorem validN_token_op_iff_disj {e₁ e₂} :
    ✓{n} (mkToken (H := H) (A := A) e₁ • mkToken e₂) ↔ e₁ ## e₂ where
  mp h := valid_op_iff_disj.mp (validN_token_of_validN h)
  mpr h := by
    refine validN_iff.mpr ⟨?_, ?_, fun i => ?_⟩
    · show ✓{n} ∅ • (∅ : H A)
      refine validN_of_eqv Algebra.MonoidOps.op_left_id.symm ?_
      exact Heap.valid_empty.validN
    · simpa [CMRA.op, mkToken, op, h] using validN_set
    · simpa [mkToken, op_data, op_token, Heap.get?_op, get?_empty] using .inl rfl

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

@[rocq_alias reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a) : mkToken (H := H) e ~~> singleton k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_singleton k a).mpr va
  | some z =>
    have ⟨d, t, ze⟩ := split_validN (validN_op_right vo)
    have vedt : ✓{n} mkToken e • (mkData d • mkToken t) := validN_of_eqv (op_right_eqv _ ze) vo
    have disj : ∀ (i : Pos), get? d i = none ∨ ¬i ∈ e:=
      disj_of_validN_data_op_token (validN_of_eqv comm (validN_op_left (validN_of_eqv assoc vedt)))
    refine validN_of_eqv (op_right_eqv _ ze.symm) ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (mkToken t) (data_op _ _)) ?_
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
    refine validN_of_eqv (op_left_eqv (mkToken t) (data_op _ _)) ?_
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
