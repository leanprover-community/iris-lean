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

-- The camera [ReservationMap A H] over a camera [A] extends [LawfulPartialMap H Pos]
-- with a notion of "reservation tokens" for a (potentially infinite) set
-- [E : CoPset] which represent the right to allocate a map entry at any position
-- [k ∈ E].  The key connectives are [ReservationMap.singleton k a] (the "points-to"
-- assertion of this map), which associates data [a : A] with a key [k : Pos],
-- and [ReservationMap.token E] (the reservation token), which says
-- that no data has been associated with the indices in the mask [E]. The important
-- properties of this camera are:
--
-- • The lemma [ReservationMap.token_union] enables one to split [ReservationMap.token]
--   w.r.t. disjoint union. That is, if we have [E1 ## E2], then we get
--   [ReservationMap.token (E1 ∪ E2) = ReservationMap.token E1 • ReservationMap.token E2].
-- • The lemma [ReservationMap.alloc] provides a frame preserving update to
--   associate data to a key: [ReservationMap.token E ~~> ReservationMap.data k a]
--   provided [k ∈ E] and [✓ a].
--
-- In the future, it could be interesting to generalize this map to arbitrary key
-- types instead of hard-coding [Pos].

@[rocq_alias reservation_map]
structure ReservationMap (A : Type) (H : Type → Type) where
  dataProj : H A
  tokenProj : DisjointLeibnizSet CoPset

def ReservationMap.data [LawfulPartialMap H Pos] (data : H A)
    : ReservationMap A H := .mk data ∅

@[rocq_alias reservation_data]
def ReservationMap.singleton [LawfulPartialMap H Pos] (k : Pos) (a : A)
    : ReservationMap A H := ReservationMap.data {[k := a]}

@[rocq_alias reservation_token]
def ReservationMap.token [LawfulPartialMap H Pos] (e : CoPset)
    : ReservationMap A H := .mk ∅ (.valid e)

section OFE

open OFE

variable [LawfulPartialMap H Pos] [OFE A]

instance : OFE (ReservationMap A H) where
  Equiv x y := x.dataProj ≡ y.dataProj ∧ x.tokenProj ≡ y.tokenProj
  Dist n x y := x.dataProj ≡{n}≡ y.dataProj ∧ x.tokenProj ≡{n}≡ y.tokenProj
  dist_eqv {n} := {
    refl x := by refine ⟨OFE.Dist.rfl, rfl⟩,
    symm h := ⟨Dist.symm h.left, Eq.symm h.right⟩,
    trans h₁ h₂ := ⟨Dist.trans h₁.left h₂.left, Eq.trans h₁.right h₂.right⟩
  }
  equiv_dist {x y} := {
    mp h := fun n => ⟨equiv_dist.mp h.left n, h.right⟩,
    mpr h := ⟨equiv_dist.mpr (fun n => (h n).left), (h 0).right⟩
  }
  dist_lt {n x y m} h lt := ⟨dist_lt h.left lt, dist_lt h.right lt⟩

instance [Discrete A] : Discrete (ReservationMap A H) where
  discrete_0 h := ⟨discrete_0 h.left, discrete_0 h.right⟩

instance : NonExpansive (ReservationMap.data (H := H) (A := A)) where
  ne _ _ _ h := ⟨h, Dist.rfl⟩

instance : NonExpansive (ReservationMap.singleton (H := H) (A := A) k) where
  ne _ _ _ h := ⟨singleton_dist h k, Dist.rfl⟩

instance {a : H A} [DiscreteE a] : DiscreteE (ReservationMap.mk a b) where
  discrete := fun ⟨ha, hb⟩ => ⟨DiscreteE.discrete ha, DiscreteE.discrete hb⟩

instance {a : A} [DiscreteE a] : DiscreteE (ReservationMap.singleton (H := H) k a) :=
  by unfold ReservationMap.singleton ReservationMap.data;  infer_instance

instance : DiscreteE (ReservationMap.token (H := H) (A := A) e) :=
  by unfold ReservationMap.token;  infer_instance

end OFE

section CMRA

open CMRA

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

def validN_unpack {n : Nat} {x : ReservationMap A H} (h : x.ValidN n)
    : ✓{n} x.dataProj ∧ ✓{n} x.tokenProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := by
  unfold ValidN at h
  match eq : x.tokenProj with
  | .valid s =>
    have := eq ▸ h
    exact ⟨this.left, (valid_0_iff_validN n).mp trivial, this.right⟩
  | .error => exact (eq ▸ h).elim

theorem validN_dataProj_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n)
    : ✓{n} x.dataProj := (validN_unpack h).left

theorem validN_tokenProj_of_validN {n : Nat} {x : ReservationMap A H} (h : x.ValidN n)
    : ✓{n} x.tokenProj := (validN_unpack h).right.left

theorem validN_disj {n : Nat} {x : ReservationMap A H} (h : x.ValidN n)
    : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := (validN_unpack h).right.right

theorem validN_of_parts {n : Nat} {x : ReservationMap A H}
    (vd : ✓{n} x.dataProj) (vt : ✓{n} x.tokenProj)
    (disj : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj)
    : x.ValidN n := by
  unfold ValidN at ⊢
  cases h : x.tokenProj
  · simp [h] at disj
    exact ⟨vd, disj⟩
  · exact absurd vt (h ▸ DisjointLeibnizSet.not_valid_invalid (S := CoPset))

def valid_unpack {x : ReservationMap A H} (h : x.Valid)
    : ✓ x.dataProj ∧ ✓ x.tokenProj ∧ ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := by
  unfold Valid at h
  match eq : x.tokenProj with
  | .valid s =>
    exact ⟨(eq ▸ h).left, valid_mapN (fun n a => a) trivial, (eq ▸ h).right⟩
  | .error => exact (eq ▸ h).elim

theorem valid_dataProj_of_valid {x : ReservationMap A H} (h : x.Valid)
    : ✓ x.dataProj := (valid_unpack h).left

theorem valid_tokenProj_of_valid {x : ReservationMap A H} (h : x.Valid)
    : ✓ x.tokenProj := (valid_unpack h).right.left

theorem valid_disj {x : ReservationMap A H} (h : x.Valid)
    : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj := (valid_unpack h).right.right

theorem valid_of_parts {x : ReservationMap A H}
    (vd : ✓ x.dataProj) (vt : ✓ x.tokenProj)
    (disj : ∀i, get? x.dataProj i = none ∨ i ∉ x.tokenProj)
    : x.Valid := by
  unfold Valid at ⊢
  cases h : x.tokenProj
  · simp [h] at disj
    exact ⟨vd, disj⟩
  · exact absurd vt (h ▸ DisjointLeibnizSet.not_valid_invalid)

def core (x : ReservationMap A H) : ReservationMap A H :=
  mk (CMRA.core x.dataProj) ∅

theorem core_dataProj (x : ReservationMap A H) : x.core.dataProj = CMRA.core x.dataProj :=
  rfl

theorem core_tokenProj (x : ReservationMap A H) : x.core.tokenProj = CMRA.core x.tokenProj :=
  rfl

def op (x y : ReservationMap A H) : ReservationMap A H :=
  mk (x.dataProj • y.dataProj) (x.tokenProj • y.tokenProj)

theorem op_dataProj' (x y : ReservationMap A H): (x.op y).dataProj = x.dataProj • y.dataProj :=
  rfl

theorem op_tokenProj' (x y : ReservationMap A H): (x.op y).tokenProj = x.tokenProj • y.tokenProj :=
  rfl

instance : CMRA (ReservationMap A H) where
  pcore := some ∘ core
  Valid := Valid
  ValidN := ValidN
  op := op
  op_ne := { ne n x₁ x₂ h := ⟨OFE.Dist.op_r h.left, OFE.Dist.op_r h.right⟩ }
  pcore_ne {n x y cx} e pe := by
    have : cx = x.core := Option.some_inj.mp pe.symm
    refine ⟨core y, rfl, ?_, ?_⟩
    · simp [this, core_dataProj, OFE.Dist.core e.left]
    · simp [this, core_tokenProj, OFE.Dist.core e.right]
  validN_ne {n x y} h v := by
    have ⟨ep, et⟩ := h
    apply validN_of_parts
    · exact (OFE.Dist.validN ep).mp (validN_dataProj_of_validN v)
    · exact (OFE.Dist.validN et).mp (validN_tokenProj_of_validN v)
    · intro i
      cases (validN_disj v) i with
      | inl gn =>
        have : none ≡{n}≡ get? y.dataProj i := gn ▸ OFE.some_dist_some.mp (ep i)
        exact .inl <| OFE.dist_none.mp this.symm
      | inr ni =>
        exact .inr <| Eq.mpr_not (congrFun (congrArg Membership.mem et.symm) i) ni
  valid_iff_validN {x} := {
    mp h n := by
      apply validN_of_parts
      · exact Valid.validN (valid_dataProj_of_valid h)
      · exact (valid_0_iff_validN n).mp (valid_tokenProj_of_valid h)
      · exact valid_disj h
    mpr v := by
      apply valid_of_parts
      · exact valid_iff_validN.mpr (fun n => validN_dataProj_of_validN (v n))
      · exact valid_iff_validN.mpr (fun n => validN_tokenProj_of_validN (v n))
      · exact validN_disj (v 0)
  }
  validN_succ {x n} v := by
    apply validN_of_parts
    · exact validN_succ (validN_dataProj_of_validN v)
    · exact (valid_0_iff_validN n).mp (validN_tokenProj_of_validN (n := n.succ) v)
    · exact validN_disj v
  validN_op_left {n x y} v := by
    have a : ✓{n} x.dataProj • y.dataProj := validN_dataProj_of_validN v
    have b : ✓{n} x.tokenProj • y.tokenProj := validN_tokenProj_of_validN v
    apply validN_of_parts
    · exact validN_op_left a
    · exact validN_op_left b
    · intro i
      cases (validN_disj v) i with
      | inl aa =>
        simp [op_dataProj', Heap.get?_op_eq_get?_op_get?] at aa
        exact .inl <| Option.eq_none_of_op_eq_none_left aa
      | inr bb => exact .inr <| bb ∘ (DisjointLeibnizSet.mem_iff_of_validN_union b i).mpr ∘ .inl
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
    have := Option.some_inj.mp h.symm
    have ⟨z, hz⟩ := core_op_mono x.dataProj y.dataProj
    have ⟨w, hw⟩ := core_op_mono x.tokenProj y.tokenProj
    refine ⟨mk z w, ?_, ?_⟩
    · simp [op_dataProj', core_dataProj, congrArg (·.dataProj) this, hz]
    · simp [op_tokenProj', core_tokenProj, congrArg (·.tokenProj) this]
      exact hw
  extend {n x y₁ y₂} v exy := by
    have aa := exy.left
    simp [op_dataProj'] at aa
    have bb := validN_dataProj_of_validN v
    let ⟨z₁, z₂, xzz, zy₁, zy₂⟩ := CMRA.extend bb aa
    refine ⟨mk z₁ y₁.tokenProj, mk z₂ y₂.tokenProj, ?_, ?_, ?_⟩
    · exact ⟨by simp [op_dataProj', xzz], by simp [op_tokenProj'];  exact exy.right⟩
    · exact ⟨zy₁, rfl⟩
    · exact ⟨zy₂, rfl⟩

theorem op_dataProj (x y : ReservationMap A H): (x • y).dataProj = x.dataProj • y.dataProj :=
  rfl

theorem op_tokenProj (x y : ReservationMap A H): (x • y).tokenProj = x.tokenProj • y.tokenProj :=
  rfl

instance : UCMRA (ReservationMap A H) where
  unit := mk ∅ ∅
  unit_valid := ⟨Heap.valid_empty, fun _ => .inr CoPset.mem_empty⟩
  unit_left_id {x} := ⟨
    show empty • x.dataProj ≡ x.dataProj from Algebra.MonoidOps.op_left_id,
    pcore_op_left' rfl
  ⟩
  pcore_unit := ⟨Heap.core_empty, OFE.Equiv.rfl⟩

@[rocq_alias reservation_map_cmra_discrete]
instance [Discrete A] : Discrete (ReservationMap A H) where
  discrete_valid {_} v :=
    valid_of_parts (discrete_valid (validN_dataProj_of_validN v))
      (validN_tokenProj_of_validN v) (validN_disj v)

instance {a : A} [CMRA.CoreId a] : CoreId (singleton (H := H) k a) where
  core_id :=
    ⟨ by simp [core_dataProj, singleton, data,
        core_eqv_self (PartialMap.singleton k a)],
      rfl ⟩

theorem split_valid {x : ReservationMap A H} (vx : ✓ x)
    : ∃(d : H A) (t : _), x ≡ data d • token t := by
  rcases x with ⟨xd, xt⟩
  have := valid_tokenProj_of_valid vx
  match hh : xt with
  | .error => exact absurd (hh ▸ this) (DisjointLeibnizSet.not_valid_invalid (S := CoPset))
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simp [data, token, op_dataProj, OFE.Equiv.symm Algebra.MonoidOps.op_right_id]
    . simp [data, token, op_tokenProj]
      exact Eq.symm (pcore_op_left_L rfl)

theorem split_validN {x : ReservationMap A H} (vx : ✓{n} x)
    : ∃(d : H A) (t : _), x ≡ data d • token t := by
  rcases x with ⟨xd, xt⟩
  have := validN_tokenProj_of_validN vx
  match hh : xt with
  | .error => exact absurd (hh ▸ this) (DisjointLeibnizSet.not_valid_invalid (S := CoPset))
  | .valid t =>
    refine ⟨xd, t, ?_, ?_⟩
    · simp [data, token, op_dataProj]
      exact OFE.Equiv.symm Algebra.MonoidOps.op_right_id
    . dsimp [data, token, op_tokenProj]
      exact OFE.Equiv.symm (pcore_op_left' rfl)

theorem valid_data {d : H A}
    : ✓ (data (H := H) d) ↔ ✓ d where
  mp := valid_dataProj_of_valid
  mpr h := valid_of_parts h ⟨⟩ (fun p => .inr (DisjointLeibnizSet.mem_empty p))

theorem validN_data {d : H A}
    : ✓{n} (data (H := H) d) ↔ ✓{n} d where
  mp := validN_dataProj_of_validN
  mpr h := validN_of_parts h ⟨⟩ (fun p => .inr (DisjointLeibnizSet.mem_empty p))

@[rocq_alias reservation_map_data_valid]
theorem valid_singleton (k : Pos) (a : A)
    : ✓ (singleton (H := H) k a) ↔ ✓ a :=
  (valid_data).trans Heap.singleton_valid_iff

theorem validN_singleton (k : Pos) (a : A)
    : ✓{n} (singleton (H := H) k a) ↔ ✓{n} a :=
  (validN_data).trans Heap.singleton_validN_iff

@[rocq_alias reservation_map_token_valid]
theorem valid_token : ✓ (token (H := H) (A := A) e) :=
  ⟨Heap.valid_empty, fun i => .inl (get?_empty i)⟩

theorem data_op (a b : H A) : data (a • b) ≡ data a • data b :=
  ⟨OFE.Equiv.rfl, (pcore_op_right_L rfl).symm⟩

open Classical in
@[rocq_alias reservation_map_data_op]
theorem singleton_op k (a b : A)
    : singleton (H := H) k (a • b) ≡ singleton (H := H) k a • singleton k b := by
  refine ((data_op _ _).symm.trans ?_).symm
  refine OFE.NonExpansive.eqv (fun i => OFE.Equiv.of_eq (Heap.singleton_op_singleton i))

theorem token_op (a b : CoPset) (h : a ## b)
    : token (H := H) (A := A) (a ∪ b) ≡ token a • token b := by
  refine ⟨show ∅ ≡ (∅ : H A) • ∅ from Algebra.MonoidOps.op_left_id.symm, ?_⟩
  simp [token, CMRA.op, op_tokenProj', h]

theorem disj_of_validN_data_op_token {a : H A} {b : CoPset}
    (h : ✓{n} data a • token (H := H) (A := A) b)
    : ∀i, get? a i = none ∨ i ∉ b
  := by
    intro i
    cases validN_disj h i with
    | inl h =>
      left
      simp [op_dataProj, data, token, Heap.get?_op_eq_get?_op_get?, get?_empty] at h
      exact Option.eq_none_of_op_eq_none_left h
    | inr h =>
      right
      simp [op_tokenProj, data, token] at h
      have aa : ∅ • (DisjointLeibnizSet.valid b) ≡ DisjointLeibnizSet.valid b :=
        pcore_op_left' rfl
      intro hh
      exact absurd hh ((congrFun (congrArg Membership.mem aa.symm) i) ▸ h)

theorem disj_of_valid_data_op_token (a : H A) (b : CoPset)
    (h : ✓ data a • token (H := H) (A := A) b)
    : ∀i, get? a i = none ∨ i ∉ b
  := by
    intro i
    cases valid_disj h i with
    | inl h =>
      left
      simp [op_dataProj, data, token, Heap.get?_op_eq_get?_op_get?, get?_empty] at h
      exact Option.eq_none_of_op_eq_none_left h
    | inr h =>
      right
      simp [op_tokenProj, data, token] at h
      have aa : ∅ • (DisjointLeibnizSet.valid b) ≡ DisjointLeibnizSet.valid b :=
        pcore_op_left' rfl
      intro hh
      exact absurd hh ((congrFun (congrArg Membership.mem aa.symm) i) ▸ h)

theorem validN_data_op_token {n : Nat} (a : H A) (b : CoPset)
    (vd : ✓{n} data a) (disj : ∀i, get? a i = none ∨ i ∉ b)
    : ✓{n} data a • token (H := H) (A := A) b := by
  have abdp : (data a • token b).dataProj ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • DisjointLeibnizSet.valid b = .valid b := pcore_op_left_L rfl
  refine validN_of_parts
    (validN_of_eqv abdp.symm ((validN_data).mp vd))
    (by simp [op_tokenProj, data, token, eo, DisjointLeibnizSet.validN_set])
    ?_
  · intro i
    simp [op_dataProj, op_tokenProj, data, token, Heap.get?_op_eq_get?_op_get?, get?_empty]
    cases disj i with
    | inl h =>
      left
      simp [h]
      rfl
    | inr h =>
      right
      simp [eo]
      exact h

theorem valid_data_op_token (a : H A) (b : CoPset)
    (vd : ✓ data a) (disj : ∀i, get? a i = none ∨ i ∉ b)
    : ✓ data a • token (H := H) (A := A) b := by
  have abdp : (data a • token b).dataProj ≡ a :=
    show a • ∅ ≡ a from (Algebra.MonoidOps.op_right_id)
  have eo : ∅ • DisjointLeibnizSet.valid b = .valid b := pcore_op_left_L rfl
  refine valid_of_parts
    (valid_of_eqv abdp.symm ((valid_data).mp vd))
    (by simp [op_tokenProj, data, token, eo, DisjointLeibnizSet.valid_set])
    ?_
  · intro i
    simp [op_dataProj, op_tokenProj, data, token, Heap.get?_op_eq_get?_op_get?, get?_empty]
    cases disj i with
    | inl h =>
      left
      simp [h]
      rfl
    | inr h =>
      right
      simp [eo]
      exact h

@[rocq_alias reservation_map_data_mono]
theorem singleton_mono k (a b : A)
    : a ≼ b → singleton (H := H) k a ≼ singleton k b :=
  fun ⟨z, hz⟩ => ⟨singleton k z,
    (OFE.NonExpansive.eqv hz).trans (singleton_op k a z)⟩

-- instance does not provide concrete values for (semi-)out-params
-- instance {ia ib₁ ib₂ : ProofMode.InOut} {a b₁ b₂ : A} [IsOp ia a ib₁ b₁ ib₂ b₂]
--     : IsOp
--       ia (data (H := H) k a)
--       ib₁ (data k b₁)
--       ib₂ (data k b₂) where
--   is_op := sorry

@[rocq_alias reservation_map_token_union]
theorem token_union {e₁ e₂} (he : e₁ ## e₂)
    : token (H := H) (A := A) (e₁ ∪ e₂) ≡
      token e₁ (H := H) (A := A) • token e₂ := by
  refine ⟨fun i => ?_, ?_⟩
  · simp [token, op_dataProj, Heap.get?_op_eq_get?_op_get?, get?_empty]
    exact OFE.Equiv.rfl
  · simp [token, op_tokenProj];  simp [CMRA.op, he]

@[rocq_alias reservation_map_token_difference]
theorem token_difference {e₁ e₂} (he : e₁ ⊆ e₂)
    : token (H := H) (A := A) e₂ ≡
      token e₁ (H := H) (A := A) • token (e₂ \ e₁) := by
  have dj : e₁ ## e₂ \ e₁ := LawfulSet.disjoint_diff_right
  have eud : e₁ ∪ e₂ \ e₁ = e₁ ∪ e₂ :=
    CoPset.ext (fun p => by grind [CoPset.in_union, CoPset.in_diff])
  have eu : e₁ ∪ e₂ = e₂ := LawfulSet.union_subset_absorption he
  have := eu ▸ eud ▸ token_union (H := H) (A := A) dj
  exact this

@[rocq_alias reservation_map_token_valid_op]
theorem valid_token_op_iff_disj {e₁ e₂}
    : ✓ (token (H := H) (A := A) e₁ • token e₂) ↔ e₁ ## e₂ where
  mp h := DisjointLeibnizSet.valid_op_iff_disj.mp (valid_tokenProj_of_valid h)
  mpr h := (OFE.Equiv.valid (token_union h)).mp valid_token

theorem validN_token_op_iff_disj {e₁ e₂}
    : ✓{n} (token (H := H) (A := A) e₁ • token e₂) ↔ e₁ ## e₂ where
  mp h := DisjointLeibnizSet.valid_op_iff_disj.mp (validN_tokenProj_of_validN h)
  mpr h := by
    if hh : e₁ ## e₂ then
      apply validN_of_parts
      · show ✓{n} ∅ • (∅ : H A)
        refine validN_of_eqv (Algebra.MonoidOps.op_left_id).symm ?_
        intro k
        simp [get?_empty]
        exact validN_succ trivial
      · simp [token, op_tokenProj];  simp [CMRA.op, hh]
        exact DisjointLeibnizSet.validN_set
      · intro i
        simp [token, op_dataProj, op_tokenProj, Heap.get?_op_eq_get?_op_get?, get?_empty]
        exact .inl rfl
    else
      exact absurd h hh

theorem valid_op?_of_valid_singleton_op {a : A} {x : H A} (h : ✓{n} (singleton k a • data x))
    : ✓{n} a •? get? x k := by
  have vdp := (validN_dataProj_of_validN h) k
  simp [CMRA.op, op_dataProj', data, singleton, get?_merge,
    LawfulPartialMap.get?_singleton, Option.merge] at vdp
  have va : ✓{n} a := (validN_singleton k a).mp (validN_op_left h)
  match h : get? x k with
  | none => exact va
  | some g =>
    simp [h] at vdp
    exact vdp

theorem valid_singleton_op_of_valid_op? {a : A} {x : H A} (vx : ✓{n} x) (h : ✓{n} a •? get? x k)
    : ✓{n} singleton k a • data x := by
  refine validN_of_eqv (data_op (PartialMap.singleton k a) x) ?_
  refine (validN_data).mpr ?_
  intro i
  rw [Heap.get?_op_eq_get?_op_get?]
  if ki : k = i then
    simp [←ki, LawfulPartialMap.get?_singleton, Option.some_op_opM]
    exact h
  else
    simp [ki, LawfulPartialMap.get?_singleton]
    exact Heap.validN_get? vx

@[rocq_alias reservation_map_alloc]
theorem alloc {e k} {a : A} (hke : k ∈ e) (va : ✓ a)
    : token (H := H) e ~~> singleton k a := by
  intro n mz vo
  match mz with
  | none => exact Valid.validN <| (valid_singleton k a).mpr va
  | some z =>
    show ✓{n} singleton k a • z

    have vz : ✓{n} z := validN_op_right vo
    have ⟨d, t, ze⟩ := split_validN vz
    have vedt : ✓{n} token e • (data d • token t) := validN_of_eqv (op_right_eqv _ ze) vo
    have vdt : ✓{n} data d • token t := validN_of_eqv ze vz
    have vde : ✓{n} data d • token e := by
      have := validN_of_eqv CMRA.assoc vedt
      have := validN_op_left this
      exact validN_of_eqv CMRA.comm this
    have vet : ✓{n} token (H := H) (A := A) t • token e := by
      have := validN_of_eqv CMRA.comm vedt
      have := validN_of_eqv CMRA.assoc.symm this
      exact validN_op_right this
    have disj := disj_of_validN_data_op_token vde

    refine validN_of_eqv (op_right_eqv _ ze.symm) ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (token t) (data_op _ _)) ?_
    refine validN_data_op_token (PartialMap.singleton k a • d) t ?_ ?_
    · refine validN_of_eqv (data_op _ _).symm ?_
      apply valid_singleton_op_of_valid_op?
      · exact validN_data.mp (validN_op_left vde)
      · have := (disj k).elim id (absurd hke)
        exact this ▸ Valid.validN va
    · simp [CMRA.op, get?_merge, LawfulPartialMap.get?_singleton]
      intro i
      grind [disj_of_validN_data_op_token vdt, validN_token_op_iff_disj.mp vet i]

@[rocq_alias reservation_map_updateP]
theorem updateP {P} {Q : ReservationMap A H → Prop} k a
    (ap : a ~~>: P) (apq : ∀ a', P a' → Q (singleton k a')) :
    singleton k a ~~>: Q := by
  intro n mz vaz
  match mz with
  | none =>
    have uu : ✓{n} a := (validN_singleton k a).mp vaz
    have ⟨y, py, vy⟩ := ap n none uu
    have ss := apq y py
    have : ✓{n} singleton (H := H) k y := (validN_singleton k y).mpr vy
    refine ⟨_, ss, this⟩
  | some z =>
    have vz : ✓{n} z := validN_op_right vaz
    have ⟨d, t, ze⟩ := split_validN vz

    have vadt : ✓{n} singleton k a • (data d • token t) :=
      validN_of_eqv (op_right_eqv (singleton k a) ze) vaz
    have vdt : ✓{n} data d • token t := validN_of_eqv ze vz
    have vad : ✓{n} (singleton k a • data d) :=
      validN_op_left (validN_of_eqv CMRA.assoc vadt)
    have vat : ✓{n} singleton (H := H) k a • token t := by
        have : ✓{n} singleton k a • (token t • data d) :=
          validN_of_eqv (op_right_eqv _ CMRA.comm) vadt
        have : ✓{n} (singleton (H := H) k a • token t) • data d :=
          validN_of_eqv (CMRA.assoc) this
        exact validN_op_left this
    have ⟨y, py, vy⟩ := ap n (get? d k) (valid_op?_of_valid_singleton_op vad)

    refine ⟨singleton k y, apq y py, ?_⟩
    refine validN_of_eqv (op_right_eqv (singleton k y) ze).symm ?_
    refine validN_of_eqv CMRA.assoc.symm ?_
    refine validN_of_eqv (op_left_eqv (token t) (data_op _ _)) ?_

    apply validN_data_op_token
    · refine validN_of_eqv (data_op _ _).symm ?_
      exact valid_singleton_op_of_valid_op? (validN_data.mp (validN_op_right vad)) vy
    · have dat := disj_of_validN_data_op_token vat
      have ddt := disj_of_validN_data_op_token vdt
      simp [CMRA.op, get?_merge, LawfulPartialMap.get?_singleton] at ⊢ dat ddt
      grind

@[rocq_alias reservation_map_update]
theorem reservation_map_update k (a b : A) (uab : a ~~> b):
    singleton (H := H) k a ~~> singleton k b := by
  have := UpdateP.of_update uab
  apply Update.of_updateP
  exact updateP k a this fun a' => congrArg (singleton k)

end ReservationMap

end CMRA
