/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.IsOp
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Updates
public import Iris.Algebra.List
public import Iris.Algebra.BigOp
public import Iris.Std.Infinite
public import Iris.Std.Set
public import Iris.Std.PartialMap
meta import Iris.Std.RocqPorting

@[expose] public section

variable {SI : Type _} [instSI : Iris.SIdx SI]

open Iris Std

section OFE

open OFE

namespace PartialMap

@[rocq_alias gmap_ofe_mixin, rocq_alias gmapO]
instance instOFE [LawfulPartialMap M K] [OFE SI V] : OFE SI (M V) where
  dist n s0 s1 := get? s0 ≡{n}≡ get? s1
  dist_eqv     := ⟨fun _ => .of_eq rfl, (·.symm), (·.trans ·)⟩
  eq_dist' {s0 s1} := by
    rw [← LawfulPartialMap.equiv_iff_eq]
    exact ⟨fun h n k => Dist.of_eq (h k), fun h k => eq_dist_2 fun (n : SI) => h n k⟩
  dist_lt      := dist_lt

#rocq_ignore gmap_dist "Included in the OFE instance"

@[simp] def toMap [LawfulPartialMap M K] [OFE SI V] : (M V) -n>[SI] (K → Option V) where
  f x := get? x
  ne.1 {_ _ _} H k := H k

@[simp] def ofMap [LawfulPartialMap M K] [R : RepFunMap M K] [OFE SI V] :  (K → Option V) -n>[SI] (M V) where
  f x := of_fun x
  ne.1 {_ _ _} H k := by simp only [get_of_fun, H k]

#rocq_ignore gmapO_leibniz "OFE is Leibniz; use equality"

@[rocq_alias lookup_ne]
instance get?_ne [LawfulPartialMap M K] [OFE SI V] (k : K) : NonExpansive SI (get? · k : M V → Option V) where
  ne {_ _ _} Ht := Ht k

/-- Total lookup is non-expansive in the map. -/
@[rocq_alias lookup_total_ne]
instance getD_ne [LawfulPartialMap M K] [OFE SI V] (k : K) (d : V) :
    NonExpansive SI (PartialMap.getD · k d : M V → V) where
  ne {_ m₁ m₂} Ht := by
    have h := Ht k
    rcases h₁ : get? m₁ k with _ | v <;> rcases h₂ : get? m₂ k with _ | w <;>
      simp_all [PartialMap.getD, OFE.Dist, HasDist.dist, Option.Forall₂]

@[rocq_alias insert_ne]
instance [LawfulPartialMap M K] [OFE SI V] (k : K) : NonExpansive₂ SI (insert · k · : M V → V → M V) where
  ne {_ _ _} Hv {_ _} Ht k' := by
    by_cases h : k = k'
    · simp [get?_insert_eq h, Ht]
    · simp [get?_insert_ne h, Hv k']

theorem eqv_of_Equiv [OFE SI V] [LawfulPartialMap M K] {t1 t2 : M V} (H : PartialMap.equiv t1 t2) : t1 = t2 :=
  eq_dist_2 fun (_ : SI) k => Dist.of_eq (H k)

instance [LawfulPartialMap M K] [OFE SI V] (op : K → V → V → V) [∀ k, NonExpansive₂ SI (op k)] :
    NonExpansive₂ SI (merge (M := M) op) where
  ne _ {_ _} Ht {_ _} Hs k := by simp only [get?_merge]; exact NonExpansive₂.ne (Ht k) (Hs k)

open Classical in
@[rocq_alias delete_ne]
instance [LawfulPartialMap M K] [OFE SI V] (k : K) : NonExpansive SI (delete · k : M V → M V) where
  ne {_ _ _} Ht k' := by
    by_cases h : k = k'
    · simp [get?_delete_eq h]
    · simp [get?_delete_ne h, Ht k']

/-- `bindAlter` is non-expansive in both the alteration and the map. -/
@[rocq_alias partial_alter_ne, rocq_alias alter_ne]
theorem bindAlter_dist [LawfulPartialMap M K] [OFE SI V] [OFE SI V'] {n : SI}
    {f g : K → V → Option V'} {m₁ m₂ : M V}
    (Hf : ∀ {k v w}, v ≡{n}≡ w → f k v ≡{n}≡ g k w) (Hm : m₁ ≡{n}≡ m₂) :
    bindAlter f m₁ ≡{n}≡ bindAlter g m₂ := by
  intro k
  specialize Hm k
  revert Hm
  simp only [OFE.Dist, HasDist.dist, Option.Forall₂, get?_bindAlter]
  cases get? m₁ k <;> cases get? m₂ k <;> simp_all
  exact Hf

/-- `merge` is non-expansive in both the merge function and the maps. -/
@[rocq_alias merge_ne, rocq_alias union_with_ne]
theorem merge_dist [LawfulPartialMap M K] [OFE SI V] {n : SI} {f g : K → V → V → V}
    {m₁ m₁' m₂ m₂' : M V}
    (Hf : ∀ {k v v' w w'}, v ≡{n}≡ v' → w ≡{n}≡ w' → f k v w ≡{n}≡ g k v' w')
    (H₁ : m₁ ≡{n}≡ m₁') (H₂ : m₂ ≡{n}≡ m₂') : merge f m₁ m₂ ≡{n}≡ merge g m₁' m₂' := by
  intro k
  specialize H₁ k
  specialize H₂ k
  revert H₁ H₂
  simp only [OFE.Dist, HasDist.dist, Option.Forall₂, get?_merge, Option.merge]
  cases get? m₁ k <;> cases get? m₁' k <;> cases get? m₂ k <;> cases get? m₂' k <;> simp_all

/-- `zipWith` is non-expansive in both the combining function and the maps. -/
@[rocq_alias map_zip_with_ne]
theorem zipWith_dist [LawfulPartialMap M K] [OFE SI V] [OFE SI V'] [OFE SI V''] {n : SI}
    {f g : V → V' → V''} {m₁ m₁' : M V} {m₂ m₂' : M V'}
    (Hf : ∀ {v v' w w'}, v ≡{n}≡ v' → w ≡{n}≡ w' → f v w ≡{n}≡ g v' w')
    (H₁ : m₁ ≡{n}≡ m₁') (H₂ : m₂ ≡{n}≡ m₂') :
    PartialMap.zipWith f m₁ m₂ ≡{n}≡ PartialMap.zipWith g m₁' m₂' :=
  bindAlter_dist (fun {k _ _} Hv => by
    have h := H₂ k
    revert h
    cases get? m₂ k <;> cases get? m₂' k <;> simp_all [OFE.Dist, HasDist.dist, Option.Forall₂]) H₁

theorem isSome_get?_eq_of_dist [LawfulPartialMap M K] [OFE SI V] {n : SI} {m₁ m₂ : M V}
    (H : m₁ ≡{n}≡ m₂) (k : K) : (get? m₁ k).isSome = (get? m₂ k).isSome := by
  specialize H k
  revert H
  cases get? m₁ k <;> cases get? m₂ k <;> simp_all [OFE.Dist, HasDist.dist, Option.Forall₂]

@[rocq_alias gmap_union_ne]
instance [LawfulPartialMap M K] [OFE SI V] : NonExpansive₂ SI ((· ∪ ·) : M V → M V → M V) where
  ne _ {_ _} H₁ {_ _} H₂ := merge_dist (fun H _ => H) H₁ H₂

/-- `intersectionWith` is non-expansive in the combining function and in both maps. -/
@[rocq_alias intersection_with_ne]
theorem intersectionWith_dist [LawfulPartialMap M K] [OFE SI V] {n : SI}
    {f g : K → V → V → Option V} {m₁ m₁' m₂ m₂' : M V}
    (Hf : ∀ {k v v' w w'}, v ≡{n}≡ v' → w ≡{n}≡ w' → f k v w ≡{n}≡ g k v' w')
    (H₁ : m₁ ≡{n}≡ m₁') (H₂ : m₂ ≡{n}≡ m₂') :
    PartialMap.intersectionWith f m₁ m₂ ≡{n}≡ PartialMap.intersectionWith g m₁' m₂' :=
  bindAlter_dist (fun {k _ _} Hv => by
    have h := H₂ k
    revert h
    cases get? m₂ k <;> cases get? m₂' k <;> simp_all [OFE.Dist, HasDist.dist, Option.Forall₂]) H₁

/-- `differenceWith` is non-expansive in the combining function and in both maps. -/
@[rocq_alias difference_with_ne]
theorem differenceWith_dist [LawfulPartialMap M K] [OFE SI V] {n : SI}
    {f g : K → V → V → Option V} {m₁ m₁' m₂ m₂' : M V}
    (Hf : ∀ {k v v' w w'}, v ≡{n}≡ v' → w ≡{n}≡ w' → f k v w ≡{n}≡ g k v' w')
    (H₁ : m₁ ≡{n}≡ m₁') (H₂ : m₂ ≡{n}≡ m₂') :
    PartialMap.differenceWith f m₁ m₂ ≡{n}≡ PartialMap.differenceWith g m₁' m₂' :=
  bindAlter_dist (fun {k _ _} Hv => by
    have h := H₂ k
    revert h
    cases get? m₂ k <;> cases get? m₂' k <;> simp_all [OFE.Dist, HasDist.dist, Option.Forall₂]) H₁

@[rocq_alias gmap_intersection_ne]
instance [LawfulPartialMap M K] [OFE SI V] : NonExpansive₂ SI ((· ∩ ·) : M V → M V → M V) where
  ne _ {_ _} H₁ {_ _} H₂ := intersectionWith_dist (fun H _ => H) H₁ H₂

@[rocq_alias gmap_difference_ne]
instance [LawfulPartialMap M K] [OFE SI V] : NonExpansive₂ SI ((· \ ·) : M V → M V → M V) where
  ne _ {_ _} H₁ {_ _} H₂ := differenceWith_dist (fun _ _ => .of_eq rfl) H₁ H₂

@[rocq_alias gmap_disjoint_ne]
theorem disjoint_dist_iff [LawfulPartialMap M K] [OFE SI V] {n : SI} {m₁ m₁' m₂ m₂' : M V}
    (H₁ : m₁ ≡{n}≡ m₁') (H₂ : m₂ ≡{n}≡ m₂') :
    PartialMap.disjoint m₁ m₂ ↔ PartialMap.disjoint m₁' m₂' :=
  forall_congr' fun k => not_congr <| and_congr
    (by rw [isSome_get?_eq_of_dist H₁ k]) (by rw [isSome_get?_eq_of_dist H₂ k])

open Classical in
@[rocq_alias gmap_union_dist_eq]
theorem union_dist_iff [LawfulPartialMap M K] [OFE SI V] {n : SI} {m m₁ m₂ : M V} :
    m ≡{n}≡ m₁ ∪ m₂ ↔ ∃ m₁' m₂', m = m₁' ∪ m₂' ∧ m₁' ≡{n}≡ m₁ ∧ m₂' ≡{n}≡ m₂ := by
  refine ⟨fun hm => ⟨PartialMap.filter (fun k _ => (get? m₁ k).isSome) m,
      PartialMap.zipWith (fun v _ => v) m₂ m₁ ∪ PartialMap.filter (fun k _ => (get? m₂ k).isSome) m,
      LawfulPartialMap.equiv_iff_eq.mp fun k => ?_, fun k => ?_, fun k => ?_⟩,
    fun ⟨_, _, hm, h₁, h₂⟩ => hm ▸ NonExpansive₂.ne h₁ h₂⟩
  all_goals
    specialize hm k
    revert hm
    simp only [OFE.Dist, HasDist.dist, Option.Forall₂, LawfulPartialMap.get?_union,
      LawfulPartialMap.get?_filter, LawfulPartialMap.get?_zipWith]
    cases get? m k <;> cases get? m₁ k <;> cases get? m₂ k <;> simp_all

open Iris.Algebra in
@[rocq_alias big_opM_ne_2]
theorem bigOpM_dist_2 [LawfulFiniteMap M' K] [OFE SI M] {op : M → M → M} {unit : M}
    [MonoidOps op unit] [NonExpansive₂ SI op] [OFE SI V]
    {Φ Ψ : K → V → M} {m₁ m₂ : M' V} {n : SI} (hm : m₁ ≡{n}≡ m₂)
    (hf : ∀ {k y₁ y₂}, get? m₁ k = some y₁ → get? m₂ k = some y₂ → y₁ ≡{n}≡ y₂ →
      Φ k y₁ ≡{n}≡ Ψ k y₂) :
    ([^ op map] k ↦ y ∈ m₁, Φ k y) ≡{n}≡ ([^ op map] k ↦ y ∈ m₂, Ψ k y) :=
  BigOpM.bigOpM_gen_proper_2 OFE.Dist.of_eq OFE.dist_equivalence MonoidOps.op_dist
    (PartialMap.isSome_get?_eq_of_dist hm) fun {k _ _} h₁ h₂ => hf h₁ h₂ <| by
      have hmk := hm k
      rw [h₁, h₂] at hmk
      exact OFE.some_dist_some.mp hmk

@[rocq_alias gmap_dom_ne]
theorem dom_eq_of_dist [LawfulPartialMap M K] [OFE SI V] {n : SI} {m₁ m₂ : M V}
    (H : m₁ ≡{n}≡ m₂) : PartialMap.dom m₁ = PartialMap.dom m₂ :=
  funext fun k => congrArg (· = true) (isSome_get?_eq_of_dist H k)

/-- Building a map out of a list of consecutive keys is non-expansive. -/
@[rocq_alias map_seq_ne]
instance [LawfulFiniteMap M Nat] [OFE SI V] (start : Nat) :
    NonExpansive SI (FiniteMap.map_seq (M := M) start : List V → M V) where
  ne {_ _ _} h k := by
    rw [LawfulFiniteMap.get?_map_seq, LawfulFiniteMap.get?_map_seq]
    split
    · exact NonExpansive.ne (f := fun l : List V => l[k - start]?) h
    · exact .rfl

/-- Project a chain of stores through its kth coordinate to a chain of values. -/
@[rocq_alias gmap_chain]
def chain [LawfulPartialMap M K] [OFE SI V] (k : K) (c : Chain SI (M V)) : Chain SI (Option V) where
  chain i := get? (c i) k
  cauchy Hni := c.cauchy Hni k

theorem chain_get [LawfulPartialMap M K] [OFE SI V] (k : K) (c : Chain SI (M V)) :
    (chain k c) i = get? (c i) k := by simp [chain]

end PartialMap

@[rocq_alias gmap_compl, rocq_alias gmap_cofe]
instance Heap.instCOFE [SIdxFinite SI] [LawfulPartialMap M K] [COFE SI V] : COFE SI (M V) where
  compl c := bindAlter (fun _ => COFE.compl <| c.map ⟨_, PartialMap.get?_ne ·⟩) (c 0)
  conv_compl {_ c} k := by
    rw [get?_bindAlter]
    rcases H : get? (c.chain 0) k
    · simp [← PartialMap.chain_get, Chain.chain_none_const (c := PartialMap.chain k c) (n := 0) (H▸rfl)]
    · exact IsCOFE.conv_compl
  lbcompl := (·.elim)
  conv_lbcompl := (·.elim)
  lbcompl_ne := (·.elim)

#rocq_ignore gmap_compl "Included in COFE instance"

@[rocq_alias gmap_ofe_discrete]
instance instDiscreteHeap [LawfulPartialMap M K] [OFE SI V] [Discrete SI V] : Discrete SI (M V) where
  discrete_0 h := OFE.eq_dist_2 (SI := SI) <| by
    intro _ k
    exact (Discrete.discrete_0 (h k)).dist

@[rocq_alias gmap_singleton_discrete]
instance instDiscreteESingleton [LawfulPartialMap M K] [DecidableEq K] [OFE SI V] {v : V}
    [ha : DiscreteE SI v] {k : K} : DiscreteE SI (PartialMap.singleton (M := M) k v) where
  discrete {y} h := OFE.eq_dist_2 (SI := SI) <| by
    intro n k'
    by_cases hh : k = k'
    · simp only [LawfulPartialMap.get?_singleton, hh, ↓reduceIte]
      refine (Option.some_is_discrete.discrete (.trans ?_ (h k'))).dist
      simp [LawfulPartialMap.get?_singleton, hh, ↓reduceIte]
    · simp only [LawfulPartialMap.get?_singleton, hh, ↓reduceIte]
      refine (Option.none_is_discrete.discrete (.trans ?_ (h k'))).dist
      simp [LawfulPartialMap.get?_singleton, hh, ↓reduceIte]

@[rocq_alias gmap_empty_discrete]
instance instDiscreteEEmpty [LawfulPartialMap M K] [OFE SI V] : DiscreteE SI (∅ : M V) where
  discrete {y} h := OFE.eq_dist_2 (SI := SI) <| by
    intro n k
    simp only [LawfulPartialMap.get?_empty]
    refine (DiscreteE.discrete (.trans ?_ (h k))).dist
    simp [LawfulPartialMap.get?_empty]

@[rocq_alias singleton_ne]
theorem singleton_dist [LawfulPartialMap M K] [DecidableEq K] [OFE SI V] {n : SI} {x y : V}
    (h : x ≡{n}≡ y) (k : K) : PartialMap.singleton (M := M) k x ≡{n}≡ PartialMap.singleton k y := by
  intro k'
  simp only [LawfulPartialMap.get?_singleton]
  split <;> simp [h]

open Classical in
@[rocq_alias insert_idN]
theorem insert_idN [LawfulPartialMap M K] [OFE SI V] {n : SI} {m : M V} {i : K} {x : V}
    (h : get? m i ≡{n}≡ some x) : insert m i x ≡{n}≡ m := fun k => by
  by_cases hk : i = k
  · subst hk
    rw [get?_insert_eq rfl]
    exact h.symm
  · rw [get?_insert_ne hk]

open Classical in
@[rocq_alias gmap_lookup_discrete]
instance instDiscreteEGet? [LawfulPartialMap M K] [OFE SI V] {m : M V} [DiscreteE SI m] {i : K} :
    DiscreteE SI (get? m i) where
  discrete {y} h := by
    rcases y with _ | v
    · revert h
      cases get? m i <;> simp_all [OFE.Dist, HasDist.dist, Option.Forall₂]
    · refine (congrArg (get? · i)
        (DiscreteE.discrete (SI := SI) (y := insert m i v) fun k => ?_)).trans (get?_insert_eq rfl)
      by_cases hk : i = k
      · subst hk
        rw [get?_insert_eq rfl]
        exact h
      · rw [get?_insert_ne hk] <;> exact .rfl

open Classical in
@[rocq_alias gmap_insert_discrete]
instance [LawfulPartialMap M K] [OFE SI V] {m : M V} {i : K} {x : V} [DiscreteE SI x] [DiscreteE SI m] :
    DiscreteE SI (insert m i x) where
  discrete {y} h := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    have hk' := h k
    by_cases hk : i = k
    · rw [get?_insert_eq hk] at hk' ⊢
      exact Option.some_is_discrete.discrete hk'
    · rw [get?_insert_ne hk] at hk' ⊢
      exact DiscreteE.discrete hk'

end OFE

section ORA
open ORA

/- ## A ORA on Heaps -/

namespace Heap

open PartialMap

variable [LawfulPartialMap M K]

@[simp, rocq_alias gmap_op_instance, rocq_alias gmap_op]
def op [Op V] (s1 s2 : M V) : M V := merge (fun _ => Op.op) s1 s2
@[simp, rocq_alias gmap_unit_instance]
def unit : M V := ∅
@[simp, rocq_alias gmap_pcore_instance]
def pcore [PCore V] (s : M V) : Option (M V) := some <| bindAlter (fun _ => PCore.pcore) s

@[reducible]
instance raOp [Op V] : Op (M V) where
  op := op
  assoc {x y z} := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp only [op, get?_merge]
    cases get? x k <;> cases get? y k <;> cases get? z k <;> simp [Option.merge]
    exact Op.assoc
  comm {x y} := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp only [op, get?_merge]
    cases get? x k <;> cases get? y k <;> simp [Option.merge]
    exact Op.comm

@[reducible]
instance raPCore [PCore V] : PCore (M V) where
  pcore := pcore
  pcore_idem {x cx} H := by
    simp only [pcore, Option.some.injEq] at H
    simp only [pcore, ← H, Option.some.injEq]
    refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
    simp [get?_bindAlter]
    rcases get? x k with (_|v) <;> simp
    cases HY : PCore.pcore v; simp
    exact PCore.pcore_idem HY

/-- `MonoidOps` for heaps over any `Op V` (`ucmraMonoidOps` would need `URA V`). -/
instance instMonoidOps [Op V] : Algebra.MonoidOps (Op.op (α := M V)) ∅ where
  op_assoc := Op.assoc.symm
  op_comm := Op.comm
  op_left_id {m} := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp only [Op.op, op, get?_merge, get?_empty]
    cases get? m k <;> rfl

@[rocq_alias lookup_op]
theorem get?_op [Op V] (x y : M V) : get? (x • y) i = get? x i • get? y i := by
  simp only [ORA.op, op, get?_merge, Option.merge, optionOp]
  grind

@[rocq_alias lookup_core]
theorem get?_core [PCore V] (m : M V) (i : K) : get? (core m) i = core (get? m i) := by
  simp only [core, ORA.pcore, pcore, Option.getD_some, get?_bindAlter, optionCore]

instance raRA [RA V] : RA (M V) where
  pcore_op_left {x cx} H := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp only [← Option.getD_some (a := cx) (b := cx), ORA.op, op, get?_merge]
    cases Hcx : get? cx k <;> cases hx : get? x k <;>
      simp <;>
      simp only [ORA.pcore, pcore, Option.some.injEq] at H
    · rw [← H, get?_bindAlter, hx] at Hcx
      cases Hcx
    · refine pcore_op_left ?_
      simp [← Hcx, ← H, get?_bindAlter, hx]

instance raURA [RA V] : URA (M V) where
  unit := unit
  unit_left_id := LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp [ORA.op, get?_merge, get?_empty]
  pcore_unit := congrArg some <| LawfulPartialMap.equiv_iff_eq.mp fun k => by
    simp [get?_bindAlter, get?_empty]
  total _ := Option.isSome_iff_exists.mp rfl

@[rocq_alias lookup_included]
theorem lookup_inc [Op V] {m1 m2 : M V} :
    (∃ (z : M V), m2 = op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) = (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    refine .trans (congrArg (get? · i) Hz) ?_
    simp only [ORA.op, op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    refine LawfulPartialMap.equiv_iff_eq.mp fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [ORA.op, optionOp, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

variable [RA V] [ORA SI V]
@[simp, rocq_alias gmap_valid_instance]
def valid (s : M V) : Prop := ∀ k, ✓[SI] get? s k
@[simp, rocq_alias gmap_validN_instance]
def validN (n : SI) (s : M V) : Prop := ∀ k, ✓{n} get? s k

@[rocq_alias lookup_includedN]
theorem lookup_incN {n : SI} {m1 m2 : M V} :
    (∃ (z : M V), m2 ≡{n}≡ op m1 z) ↔
    ∀ i, (∃ z, (get? m2 i) ≡{n}≡ (get? m1 i) • z) := by
  refine ⟨fun ⟨z, Hz⟩ i => ?_, fun H => ?_⟩
  · refine ⟨get? z i, ?_⟩
    refine .trans (get?_ne i |>.ne Hz) ?_
    simp only [op, ORA.op, get?_merge]
    cases get? m1 i <;> cases get? z i <;> simp
  · obtain ⟨f, Hf⟩ := Classical.axiomOfChoice H
    exists bindAlter (fun k _ => f k) m2
    refine fun i => (Hf i).trans ?_
    specialize Hf i; revert Hf
    simp [ORA.op, get?_merge, get?_bindAlter]
    cases get? m2 i <;> cases get? m1 i <;> cases f i <;> simp

@[reducible]
def raValid : _root_.Iris.Valid SI (M V) where
  ValidN := validN
  Valid := valid
  valid_iff_validN :=
    ⟨fun H n k => valid_iff_validN.mp (H k) n,
     fun H k => valid_iff_validN.mpr (H · k)⟩

@[reducible] def raOrdered : Ordered SI (M V) where
  OrderN n m m' := ∀ k, get? m k ≼ₒ{n} get? m' k
  Order m m' := ∀ k, get? m k ≼ₒ[SI] get? m' k
  ordN_trans h₁ h₂ k := ordN_trans (h₁ k) (h₂ k)
  ord_trans h₁ h₂ k := ord_trans (h₁ k) (h₂ k)
  ordN_of_ord n h k := ordN_of_ord n (h k)

attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE SI (M V) where
  ordN_ne em em' h k := ordN_ne ((get?_ne k).ne em) ((get?_ne k).ne em') (h k)
  ordN_le h le k := ordN_le (h k) le

section
attribute [local instance] raValid raOrdered raOrderedNE

theorem increasing_get? {m : M V} (h : Increasing SI m) (k : K) : Increasing SI (get? m k) where
  increasing
    | none => by simpa [get?_op, get?_empty] using h.increasing unit k
    | some v => by simpa [get?_op, get?_insert_eq rfl] using h.increasing (insert ∅ k v) k

theorem increasing_iff {m : M V} : Increasing SI m ↔ ∀ k, Increasing SI (get? m k) :=
  ⟨increasing_get?, fun h => ⟨fun m' k => by rw [get?_op]; exact (h k).increasing _⟩⟩

open OFE in
@[rocq_alias gmapR, rocq_alias gmap_cmra_mixin]
instance instStoreCMRA : ORA SI (M V) where
  toValid := raValid
  op_ne.ne _ x1 x2 H i := by
    rename_i x _
    specialize H i; revert H
    simp [Op.op, get?_merge]
    cases get? x1 i <;> cases get? x2 i <;> cases get? x i <;> simp
    apply op_right_dist
  pcore_ne {n : SI} {x y _} H := by
    simp only [PCore.pcore, pcore, Option.some.injEq, exists_eq_left']
    refine (· ▸ fun k => ?_); specialize H k; revert H
    rw [get?_bindAlter, get?_bindAlter]
    cases get? x k <;> cases get? y k <;> simp
    exact (NonExpansive.ne ·)
  validN_ne {n : SI} {x y} Hx H k :=
    validN_ne (NonExpansive.ne (f := (get? · k : M V → Option V)) Hx) (H k)
  validN_le H le k := validN_le (H k) le
  toOrderedNE := raOrderedNE
  validN_op_left {n : SI} {x1 x2} H k := by
    refine validN_op_left (y := get? x2 k) ?_
    specialize H k; revert H
    simp only [ORA.op, op, get?_merge, Option.merge]
    cases get? x1 k <;> cases get? x2 k <;> simp [optionOp]
  extend {n : SI} {x y1 y2} Hm Heq := by
    have Hslice i : get? x i ≡{n}≡ get? y1 i • get? y2 i := by
      refine (get?_ne i |>.ne Heq).trans ?_
      simp [ORA.op, get?_merge, optionOp]
      cases get? y1 i <;> cases get? y2 i <;> simp
    let extendF (i : K) := extend (Hm i) (Hslice i)
    exists bindAlter (fun k (_ : V) => extendF k |>.fst) y1
    exists bindAlter (fun k (_ : V) => extendF k |>.snd.fst) y2
    simp [ORA.op, op]
    refine ⟨eq_dist_2 fun (_ : SI) i => ?_, fun i => ?_, fun i => ?_⟩
    all_goals rcases hF : extendF i with ⟨z1, z2, Hm, Hz1, Hz2⟩
    · refine Hm.dist.trans ?_
      simp [get?_merge, ORA.op, optionOp, Option.merge, get?_bindAlter]
      rw [hF]
      cases z1 <;> cases z2 <;> simp_all
      · cases h : (get? y2 i) <;> simp; simp [h] at Hz2
      · cases h : (get? y1 i) <;> simp; simp [h] at Hz1
      · cases h : (get? y2 i) <;> simp; simp [h] at Hz2
        cases h : (get? y1 i) <;> simp; simp [h] at Hz1
    · cases h : get? y1 i
      · rw [get?_bindAlter]
        simp [h]
      · rw [get?_bindAlter]
        simp only [h, hF, Option.bind_some]
        refine Hz1.trans (.of_eq h)
    · cases h : get? y2 i
      · rw [get?_bindAlter]
        simp [h]
      · rw [get?_bindAlter, hF]
        simp only [h, Option.bind_some]
        refine Hz2.trans (.of_eq h)
  toOrdered := raOrdered
  op_monoN_left_ord z h k := by rw [get?_op, get?_op]; exact op_monoN_left_ord _ (h k)
  op_mono_left_ord z h k := by rw [get?_op, get?_op]; exact op_mono_left_ord _ (h k)
  validN_of_ordN h v k := validN_of_ordN (h k) (v k)
  pcore_monoN_ord {_ x y cx} h e := ⟨core y, rfl, fun k => by
    rw [(Option.some.inj e.symm : cx = core x), get?_core, get?_core]; exact core_ordN_core (h k)⟩
  pcore_mono_ord {x y cx} h e := ⟨core y, rfl, fun k => by
    rw [(Option.some.inj e.symm : cx = core x), get?_core, get?_core]; exact core_mono_ord (h k)⟩
  pcore_order_op {x cx} e y := ⟨core (x • y), rfl, fun k => by
    rw [(Option.some.inj e.symm : cx = core x), get?_core, get?_core, get?_op]
    exact core_op_mono_ord _ _⟩
  pcore_increasing {x cx} e := (Option.some.inj e.symm : cx = core x) ▸
    increasing_iff.mpr fun k => (get?_core x k).symm ▸ increasing_core _
  increasing_closed h h' := increasing_iff.mpr fun k =>
      increasing_closed (increasing_get? h k) (h'.imp (fun e => (get?_ne k).ne e) (· k))
  ordN_extend {n : SI} {x y} v h :=
    let ⟨f, hf⟩ := Classical.axiomOfChoice fun k => ordN_extend (v k) (h k)
    have hfx : ∀ k, get? (bindAlter (fun k _ => f k) x) k = f k := fun k => by
      rw [get?_bindAlter]
      cases hx : get? x k
      · exact (OFE.dist_none.mp (hx ▸ (hf k).2)).symm
      · rfl
    ⟨bindAlter (fun k _ => f k) x, fun k => by rw [hfx]; exact (hf k).1,
      fun k => by rw [hfx]; exact (hf k).2⟩

end

@[rocq_alias gmap_ucmra_mixin, rocq_alias gmapUR]
instance instStoreUCMRA : UORA SI (M V) where
  toORA := instStoreCMRA
  unit_valid k := by rw [show get? (UnitOp.unit : M V) k = none from get?_empty k]; trivial
  ord_refl _ := fun _ => ord_refl _

instance instIncOrd [IncOrd SI V] : IncOrd SI (M V) :=
  IncOrd.of_increasing fun _ => increasing_iff.mpr fun _ => IncOrd.increasing _

instance instOrdInc [OrdInc SI V] : OrdInc SI (M V) where
  ord_inc h := lookup_inc.mpr fun i =>
    @OrdInc.ord_inc SI instSI (Option V) inferInstance _ _ _ _ _ (h i)
  ordN_incN h := lookup_incN.mpr fun i =>
    @OrdInc.ordN_incN SI instSI (Option V) _ _ _ _ _ _ _ (h i)

instance instIsInc [IsInc SI V] : IsInc SI (M V) := {}

theorem lookup_ordN {n : SI} {m1 m2 : M V} : m1 ≼ₒ{n} m2 ↔ ∀ i, get? m1 i ≼ₒ{n} get? m2 i := .rfl

theorem lookup_ord {m1 m2 : M V} : m1 ≼ₒ[SI] m2 ↔ ∀ i, get? m1 i ≼ₒ[SI] get? m2 i := .rfl

@[rocq_alias gmap_op_empty_l_L]
theorem op_empty_left {m : M V} : (∅ : M V) • m = m := unit_left_id_L

@[rocq_alias gmap_op_empty_r]
theorem op_empty_right {m : M V} : m • (∅ : M V) = m := unit_right_id_L

end Heap
end ORA

namespace Heap

open PartialMap LawfulPartialMap

variable {K V : Type _} [LawfulPartialMap M K] [RA V] [ORA SI V]

open ORA

@[rocq_alias lookup_opM]
theorem get?_opM (m : M V) (mm : Option (M V)) (i : K) :
    get? (m •? mm) i = get? m i • mm.bind (get? · i) := by
  cases mm with
  | none =>
    change get? m i = get? m i • none
    cases get? m i <;> rfl
  | some m' => exact get?_op m m'

@[rocq_alias lookup_op_homomorphism]
instance (i : K) : Algebra.MonoidHomomorphism (ORA.op (α := M V)) (ORA.op (α := Option V))
    ∅ none (· = ·) (get? · i) where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper h₁ h₂ := h₁ ▸ h₂ ▸ rfl
  map_op := get?_op ..
  map_unit := get?_empty i

theorem valid_empty : ✓[SI] (∅ : M V) :=
  fun k => by simp [ORA.Valid, show get? ∅ k = none from get?_empty (M := M) k]

@[rocq_alias lookup_validN_Some]
theorem validN_get?_validN {n : SI} {m : M V} (Hv : ✓{n} m) (He : get? m i ≡{n}≡ some x) : ✓{n} x := by
  specialize Hv i; revert Hv
  rcases h : get? m i <;> simp [h] at He
  exact OFE.Dist.validN He |>.mp

theorem validN_get? {n : SI} {m : M V} (v : ✓{n} m) : ✓{n} get? m i :=
  match hh : get? m i with
  | none => ⟨⟩
  | some z => show ✓{n} z from validN_get?_validN v (OFE.Dist.of_eq hh)

@[rocq_alias lookup_valid_Some]
theorem valid_get?_valid {m : M V} (Hv : ✓[SI] m) (He : get? m i = some x) : ✓[SI] x :=
  valid_iff_validN.mpr (fun _ => validN_get?_validN Hv.validN He.dist)

theorem valid_get? {m : M V} (v : ✓[SI] m) : ✓[SI] get? m i :=
  valid_iff_validN.mpr (fun _ => Valid.validN (v i))

open Classical in
@[rocq_alias insert_validN]
theorem insert_validN {n : SI} {m : M V} (Hx : ✓{n} x) (Hm : ✓{n} m) : ✓{n} (insert m i x) := by
  intro k
  rw [get?_insert]; split
  · exact Hx
  · apply Hm

@[rocq_alias insert_valid]
theorem insert_valid {m : M V} (Hx : ✓[SI] x) (Hm : ✓[SI] m) : ✓[SI] (insert m i x) :=
  valid_iff_validN.mpr (fun _ => insert_validN Hx.validN Hm.validN)

open Classical in
@[rocq_alias singleton_valid]
theorem singleton_valid_iff : ✓[SI] (singleton i x : M V) ↔ ✓[SI] x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
@[rocq_alias singleton_validN]
theorem singleton_validN_iff {n : SI} : ✓{n} (singleton i x : M V) ↔ ✓{n} x := by
  refine ⟨fun H => ?_, fun H k => ?_⟩
  · specialize H i; rw [get?_singleton_eq rfl] at H; trivial
  · rw [get?_singleton]; split <;> trivial

open Classical in
@[rocq_alias delete_validN]
theorem delete_validN {n : SI} {m : M V} (Hv : ✓{n} m) : ✓{n} (delete m i) := by
  intro k
  rw [get?_delete]; split
  · trivial
  · exact Hv k

@[rocq_alias delete_valid]
theorem delete_valid {m : M V} (Hv : ✓[SI] m) : ✓[SI] (delete m i) :=
  valid_iff_validN.mpr (fun _ => delete_validN Hv.validN)

open Classical in
@[rocq_alias insert_singleton_op]
theorem insert_equiv_singleton_op_singleton {m : M V} (Hemp : get? m i = none) :
    equiv (insert m i x) (singleton i x • m) := by
  refine (fun k => ?_)
  simp [ORA.op, Heap.op, get?_merge, Option.merge, get?_singleton, get?_insert]
  split <;> rename_i He
  · rw [← He, Hemp]
  · cases (get? m k) <;> rfl

theorem insert_eq_singleton_op_singleton {m : M V} (Hemp : get? m i = none) :
    insert m i x = singleton i x • m :=
  equiv_iff_eq.mp (insert_equiv_singleton_op_singleton Hemp)

theorem core_empty : core (∅ : M V) = ∅ := equiv_iff_eq.mp <| by
  intro k
  simp [core, ORA.pcore, get?_empty, get?_bindAlter]

open Classical in
@[rocq_alias singleton_core']
theorem core_singleton_equiv {i : K} {x : V} {cx : V} (Hpcore : ORA.pcore x = some cx) :
    equiv (core <| singleton i x : M V) (singleton i cx) := by
  refine fun k => ?_
  simp [← Hpcore, core, ORA.pcore, get?_singleton, get?_bindAlter]
  split <;> rfl

@[rocq_alias singleton_core]
theorem singleton_core_eq {i : K} {x : V} {cx} (Hpcore : ORA.pcore x = some cx) :
    core (singleton i x : M V) = singleton i cx  :=
  equiv_iff_eq.mp (core_singleton_equiv Hpcore)

@[rocq_alias singleton_core_total]
theorem singleton_core_total_eq [IsTotal V] {i : K} {x : V} :
    core (singleton i x : M V) = singleton i (core x) :=
  equiv_iff_eq.mp <| core_singleton_equiv (pcore_eq_core x)

open Classical in
@[rocq_alias singleton_op]
theorem singleton_op_singleton {i : K} {x y : V} :
    (singleton i x : M V) • (singleton i y) = (singleton i (x • y)) := by
  refine equiv_iff_eq.mp fun k => ?_
  simp only [ORA.op, Heap.op, get?_merge, get?_singleton]
  split <;> simp [Option.merge]

open Classical in
set_option synthInstance.checkSynthOrder false in
@[rocq_alias singleton_is_op]
instance {d : IsOp.Direction} {i : K} {x x₁ x₂ : V} [h : IsOp d x x₁ x₂] :
    IsOp d (singleton i x : M V) (singleton i x₁ : M V) (singleton i x₂ : M V) where
  is_op := by rw [h.is_op, ← singleton_op_singleton]

open Classical in
@[rocq_alias gmap_core_id]
theorem coreId_of_get? {m : M V} (h : ∀ {i x}, get? m i = some x → CoreId x) : CoreId m where
  core_id := congrArg some <| equiv_iff_eq.mp fun k => by
    rw [get?_bindAlter]
    rcases hk : get? m k with _ | v
    · simp
    · simp [(h hk).core_id]

@[rocq_alias gmap_core_id']
instance {m : M V} [I : ∀ x : V, CoreId x] : CoreId m where
  core_id := congrArg some <| equiv_iff_eq.mp fun k => by
    rw [get?_bindAlter]
    cases get? m k <;> simp
    exact core_id

open Classical in
@[rocq_alias gmap_singleton_core_id]
instance [CoreId (x : V)] : CoreId (singleton i x : M V) where
  core_id := congrArg some <| equiv_iff_eq.mp fun k => by
    simp [get?_bindAlter, get?_singleton]
    split <;> simp
    exact core_id

open Classical in
theorem singleton_ordN_singleton_iff {n : SI} :
    (singleton i x : M V) ≼ₒ{n} (singleton i y : M V) ↔ some x ≼ₒ{n} some y := by
  refine ⟨fun h => by simpa [get?_singleton_eq rfl] using h i, fun h k => ?_⟩
  by_cases hk : i = k
  · subst hk; simpa [get?_singleton_eq rfl] using h
  · simp only [get?_singleton, hk, ↓reduceIte]; trivial

open Classical in
theorem singleton_ord_singleton_iff :
    (singleton i x : M V) ≼ₒ[SI] (singleton i y : M V) ↔ some x ≼ₒ[SI] some y := by
  refine ⟨fun h => by simpa [get?_singleton_eq rfl] using h i, fun h k => ?_⟩
  by_cases hk : i = k
  · subst hk; simpa [get?_singleton_eq rfl] using h
  · simp only [get?_singleton, hk, ↓reduceIte]; trivial

theorem singleton_ord_singleton_mono (Hinc : x ≼ₒ[SI] y) :
    (singleton i x : M V) ≼ₒ[SI] (singleton i y) :=
  singleton_ord_singleton_iff.mpr (Or.inr Hinc)

theorem total_singleton_ord_singleton_iff [OrderRefl SI V] :
    (singleton i x : M V) ≼ₒ[SI] (singleton i y) ↔ x ≼ₒ[SI] y :=
  singleton_ord_singleton_iff.trans Option.some_ord_some_iff_orderRefl

open Classical in
theorem singleton_ordN_iff {n : SI} [IncOrd SI V] {m : M V} :
    (singleton i x) ≼ₒ{n} m ↔ ∃ y, (get? m i ≡{n}≡ some y) ∧ some x ≼ₒ{n} some y := by
  refine ⟨fun h => ?_, fun ⟨y, Hy, Hxy⟩ k => ?_⟩
  · have ⟨y, hy, hxy⟩ := Option.exists_of_some_ordN (get?_singleton_eq (M := M) rfl ▸ h i)
    exact ⟨y, .of_eq hy, hxy⟩
  · by_cases hk : i = k
    · subst hk; rw [get?_singleton_eq rfl]; exact ordN_ne .rfl Hy.symm Hxy
    · simp only [get?_singleton, hk, ↓reduceIte]; exact ordN_unit

open Classical in
theorem singleton_ord_iff [IncOrd SI V] {m : M V} :
    (singleton i x) ≼ₒ[SI] m ↔ ∃ y, (get? m i = some y) ∧ some x ≼ₒ[SI] some y := by
  refine ⟨fun h => Option.exists_of_some_ord (get?_singleton_eq (M := M) rfl ▸ h i),
    fun ⟨y, Hy, Hxy⟩ k => ?_⟩
  · by_cases hk : i = k
    · subst hk; rw [get?_singleton_eq rfl, Hy]; exact Hxy
    · simp only [get?_singleton, hk, ↓reduceIte]; exact ord_unit

theorem ord_dom_ord {m1 m2 : M V} (Hinc : m1 ≼ₒ[SI] m2) : Set.Included (dom m1) (dom m2) :=
  fun i => Option.isSome_mono_ord (Hinc i)

open Classical in
@[rocq_alias singleton_includedN_l]
theorem singleton_incN_iff {n : SI} {m : M V} :
    (singleton i x) ≼{n} m ↔ ∃ y, (get? m i ≡{n}≡ some y) ∧ some x ≼{n} some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · specialize Hz i; revert Hz
    simp only [ORA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · intro _
      exists x
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · cases z
    · exists (PartialMap.delete m i)
      intros j
      simp [ORA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [ORA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      intros j
      simp [ORA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [ORA.op]
      · simp

open Classical in
@[rocq_alias singleton_included_l]
theorem singleton_inc_iff {m : M V} :
    (singleton i x) ≼ m ↔ ∃ y, (get? m i = some y) ∧ some x ≼ some y := by
  refine ⟨fun ⟨z, Hz⟩ => ?_, fun ⟨y, Hy, z, Hz⟩ => ?_⟩
  · replace Hz := congrArg (get? · i) Hz; revert Hz
    simp only [ORA.op, Heap.op, get?_merge, get?_singleton_eq rfl]
    rcases get? z i with (_|v)
    · exact (⟨x, ·, none, rfl⟩)
    · refine (⟨x • v, ·, ?_⟩)
      exists v
  · cases z
    · exists (PartialMap.delete m i)
      refine equiv_iff_eq.mp fun j => ?_
      simp [ORA.op, get?_merge, get?_singleton, get?_delete]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [ORA.op]
      · simp
    · rename_i z
      exists (PartialMap.insert m i z)
      refine equiv_iff_eq.mp fun j => ?_
      simp [ORA.op, get?_merge, get?_singleton, get?_insert]
      split
      · rename_i h
        simp
        refine (h ▸ Hy).trans <| Hz.trans ?_
        simp [ORA.op]
      · simp

@[rocq_alias singleton_included_exclusive_l]
theorem exclusive_singleton_inc_iff {m : M V} (He : Exclusive SI x) (Hv : ✓[SI] m) :
    (singleton i x) ≼ m ↔ (get? m i = some x) := by
  refine singleton_inc_iff.trans ⟨fun ⟨y, Hy, Hxy⟩ => ?_, fun _ => ?_⟩
  · suffices x = y by exact Hy.trans <| (OFE.some_eqv_some).mpr this.symm
    exact Option.eqv_of_inc_exclusive Hxy <| valid_get?_valid Hv Hy
  · exact ⟨x, ‹_›, none, rfl⟩

@[rocq_alias singleton_included]
theorem singleton_inc_singleton_iff :
    (singleton i x : M V) ≼ (singleton i y : M V) ↔ some x ≼ some y := by
  refine singleton_inc_iff.trans ⟨fun ⟨z, Hz, Hxz⟩ => ?_, fun H => ?_⟩
  · exact (Hz.symm.trans <| get?_singleton_eq rfl) ▸ Hxz
  · refine ⟨y, ?_, H⟩
    exact get?_singleton_eq rfl

theorem exclusive_singleton_ord_iff [IncOrd SI V] [OrdInc SI V] {m : M V} (He : Exclusive SI x)
    (Hv : ✓[SI] m) :
    (singleton i x) ≼ₒ[SI] m ↔ (get? m i = some x) :=
  inc_iff_ord.symm.trans (exclusive_singleton_inc_iff He Hv)

@[rocq_alias singleton_included_total]
theorem total_singleton_inc_singleton_iff [IsTotal V] :
    (singleton i x : M V) ≼ (singleton i y) ↔ x ≼ y :=
  singleton_inc_singleton_iff.trans <| Option.some_inc_some_iff_is_total

@[rocq_alias singleton_included_mono]
theorem singleton_inc_singleton_mono (Hinc : x ≼ y) :
    (singleton i x : M V) ≼ (singleton i y) :=
  singleton_inc_singleton_iff.mpr <| Option.some_inc_some_iff.mpr <| .inr Hinc

open Classical in
@[rocq_alias singleton_cancelable]
instance [H : Cancelable SI (some x)] : Cancelable SI (singleton i x : M V) where
  cancelableN {n : SI} {m1 m2} Hv He j := by
    specialize Hv j; revert Hv
    specialize He j; revert He
    simp only [ORA.op, Heap.op, get?_merge, Option.merge, get?_singleton]
    by_cases He : i = j
    · simp_all only [↓reduceIte]
      intro Hv He
      cases _ : get? m1 j <;> cases _ : get? m2 j
      all_goals apply H.cancelableN
      all_goals simp_all [ORA.op, optionOp]
    · cases get? m1 j <;> cases get? m2 j <;> simp_all

@[rocq_alias gmap_cancelable]
instance {m : M V} [Hid : ∀ x : V, IdFree SI x] [Hc : ∀ x : V, Cancelable SI x] : Cancelable SI m where
  cancelableN {n : SI} {m1 m2} Hv He i := by
    apply cancelableN (x := get? m i)
    · specialize Hv i; revert Hv
      simp [ORA.op, Heap.op, get?_merge, optionOp]
      cases _ : get? m i <;> cases _ : get? m1 i <;> simp_all
    · specialize He i; revert He
      simp [get?_merge, ORA.op, Heap.op, optionOp]
      cases get? m i <;> cases get? m1 i <;> cases get? m2 i <;> simp_all

@[rocq_alias insert_op]
theorem insert_op {m1 m2 : M (Option V)} :
    (insert (m1 • m2) i (x • y)) = (insert m1 i x • insert m2 i y) := by
  refine equiv_iff_eq.mp fun j => ?_
  by_cases He : i = j
  · simp [ORA.op, get?_insert_eq He, get?_merge]
  · simp [ORA.op, get?_insert_ne He, get?_merge]

@[rocq_alias gmap_op_union]
theorem disjoint_op_equiv_union {m1 m2 : M V} (Hd : Set.Disjoint (dom m1) (dom m2)) :
    equiv (m1 • m2) (union m1 m2) := by
  refine fun j => ?_
  simp [ORA.op, Heap.op, get?_merge]
  rcases _ : get? m1 j <;> cases _ : get? m2 j <;> simp_all
  refine (Hd j ?_).elim
  simp_all [dom]

theorem disjoint_op_eq_union {m1 m2 : M V} (H : Set.Disjoint (dom m1) (dom m2)) :
    m1 • m2 = union m1 m2 :=
  equiv_iff_eq.mp (disjoint_op_equiv_union H)

@[rocq_alias gmap_op_valid0_disjoint]
theorem valid0_disjoint_dom {m1 m2 : M V} (Hv : ✓{(0 : SI)} (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive SI x) :
    Set.Disjoint (dom m1) (dom m2) := by
  rintro k
  simp only [dom, Option.isSome]
  rcases HX : get? m1 k with (_|x) <;> simp
  rcases HY : get? m2 k with (_|y) <;> simp
  apply (H HX).1 y
  simp [ORA.op, ORA.ValidN] at Hv; specialize Hv k; revert Hv
  simp [get?_merge, HX, HY]

@[rocq_alias gmap_op_valid_disjoint]
theorem valid_disjoint_dom {m1 m2 : M V} (Hv : ✓[SI] (m1 • m2)) (H : ∀ {k x}, get? m1 k = some x → Exclusive SI x) :
    Set.Disjoint (dom m1) (dom m2) :=
  valid0_disjoint_dom (Valid.validN Hv) H

@[rocq_alias dom_op]
theorem dom_op_union (m1 m2 : M V) : dom (m1 • m2) = Set.Union (dom m1) (dom m2) := by
  refine funext fun k => ?_
  cases get? m1 k <;> cases get? m2 k <;> simp_all [ORA.op, dom, Set.Union, get?_merge]

@[rocq_alias dom_included]
theorem inc_dom_inc {m1 m2 : M V} (Hinc : m1 ≼ m2) : Set.Included (dom m1) (dom m2) := by
  intro i
  unfold dom
  rcases lookup_inc.mp Hinc i with ⟨z, Hz⟩
  revert Hz
  cases get? m1 i <;> cases get? m2 i <;> cases z <;> simp [ORA.op, optionOp]

theorem map_mono_ord [RA V'] [ORA SI V'] [IncOrd SI V'] (f : V → V') (hf : ∀ x y : V, x ≼ₒ[SI] y → f x ≼ₒ[SI] f y)
    {m1 m2 : M V} (Hinc : m1 ≼ₒ[SI] m2) : PartialMap.map f m1 ≼ₒ[SI] PartialMap.map f m2 :=
  lookup_ord.mpr fun i => by rw [get?_map, get?_map]; exact Option.map_mono_ord f hf (Hinc i)

@[rocq_alias gmap_fmap_mono]
theorem map_mono [RA V'] (f : V → V') (hf : ∀ x y : V, x ≼ y → f x ≼ f y) {m1 m2 : M V}
    (Hinc : m1 ≼ m2) : PartialMap.map f m1 ≼ PartialMap.map f m2 := by
  refine lookup_inc.mpr fun i => ?_
  obtain ⟨z, hz⟩ := Option.map_mono f hf (lookup_inc.mp Hinc i)
  exact ⟨z, by rw [get?_map, get?_map, hz]⟩

open Iris.Algebra in
open Classical in
@[rocq_alias big_opM_singletons]
theorem bigOpM_singletons {M' : Type _ → Type _} {K V : Type _}
    [LawfulFiniteMap M' K] [RA V] (m : M' V) :
    ([^ ORA.op map] k ↦ x ∈ m, PartialMap.singleton k x) = m := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp => exact BigOpM.bigOpM_empty _
  | hins i x m hi ih =>
    rw [BigOpM.bigOpM_insert_eq _ x hi, ih]
    exact (equiv_iff_eq.mp (Heap.insert_equiv_singleton_op_singleton hi)).symm

open Iris.Algebra in
open Classical in
@[rocq_alias big_opS_gset_to_gmap, rocq_alias big_opS_gset_to_gmap_L]
theorem bigOpS_ofSet {A S : Type _} [LawfulFiniteSet S A] {M' : Type _ → Type _}
    {V : Type _} [LawfulFiniteMap M' A] [RA V] (a : V) (s : S) :
    ([^ ORA.op set] k ∈ s, (PartialMap.singleton k a : M' V)) = FiniteMap.ofSet a s := by
  induction s using FiniteSet.set_ind with
  | hemp =>
    rw [BigOpS.bigOpS_empty, LawfulFiniteMap.ofSet_empty]
  | hadd x X hx ih =>
    refine (BigOpS.bigOpS_insert hx).trans ?_
    rw [ih, LawfulFiniteMap.ofSet_insert]
    exact (LawfulPartialMap.equiv_iff_eq.mp
      (Heap.insert_equiv_singleton_op_singleton (LawfulFiniteMap.get?_ofSet_of_not_mem hx))).symm

@[rocq_alias gmap_cmra_discrete]
nonrec instance [HD : Discrete SI V] [LawfulPartialMap M K] : Discrete SI (M V) where
  discrete_0 {_ _} H := by
    refine OFE.eq_dist_2 (SI := SI) ?_
    exact fun _ k => (OFE.Discrete.discrete_0 (H k)).dist
  discrete_valid {_} := (Discrete.discrete_valid <| · ·)
  discrete_ord h k := discrete_ord (h k)

/-! ## Frame-preserving updates -/

open Classical in
@[rocq_alias insert_updateP]
theorem insert_updateP {P : V → Prop} {Q : M V → Prop} {m : M V} {i : K} {x : V}
    (hx : x ~~>:[SI] P) (hQ : ∀ y, P y → Q (insert m i y)) : insert m i x ~~>:[SI] Q := by
  refine UpdateP.total.mpr fun n mf hv => ?_
  have hi : ✓{n} (some x • get? mf i) := by
    have hvi := hv i
    rwa [get?_op, get?_insert_eq rfl] at hvi
  obtain ⟨_ | y, hy, hvy⟩ := UpdateP.option' P x hx n (some (get? mf i)) hi
  · exact hy.elim
  refine ⟨insert m i y, hQ y hy, fun k => ?_⟩
  by_cases hk : i = k
  · subst hk
    rw [get?_op, get?_insert_eq rfl]
    exact hvy
  · have hvk := hv k
    rw [get?_op, get?_insert_ne hk] at hvk ⊢
    exact hvk

@[rocq_alias insert_updateP']
theorem insert_updateP' {P : V → Prop} {m : M V} {i : K} {x : V} (hx : x ~~>:[SI] P) :
    insert m i x ~~>:[SI] fun m' => ∃ y, m' = insert m i y ∧ P y :=
  insert_updateP hx fun y hy => ⟨y, rfl, hy⟩

@[rocq_alias insert_update]
theorem insert_update {m : M V} {i : K} {x y : V} (h : x ~~>[SI] y) :
    insert m i x ~~>[SI] insert m i y :=
  .of_updateP <| insert_updateP (.of_update h) fun _ => congrArg _

@[rocq_alias singleton_updateP]
theorem singleton_updateP {P : V → Prop} {Q : M V → Prop} {i : K} {x : V}
    (hx : x ~~>:[SI] P) (hQ : ∀ y, P y → Q (singleton i y)) : (singleton i x : M V) ~~>:[SI] Q :=
  insert_updateP hx hQ

@[rocq_alias singleton_updateP']
theorem singleton_updateP' {P : V → Prop} {i : K} {x : V} (hx : x ~~>:[SI] P) :
    (singleton i x : M V) ~~>:[SI] fun m => ∃ y, m = singleton i y ∧ P y :=
  insert_updateP' hx

@[rocq_alias singleton_update]
theorem singleton_update {i : K} {x y : V} (h : x ~~>[SI] y) :
    (singleton i x : M V) ~~>[SI] singleton i y :=
  insert_update h

open Classical in
@[rocq_alias delete_update]
theorem delete_update {m : M V} {i : K} : m ~~>[SI] delete m i := by
  refine Update.total.mpr fun n mf hv k => ?_
  have hvk := hv k
  rw [get?_op] at hvk ⊢
  by_cases hk : i = k
  · rw [get?_delete_eq hk]
    exact validN_op_right hvk
  · rwa [get?_delete_ne hk]

end Heap

/-! ## Allocation -/

section Freshness

open ORA PartialMap LawfulPartialMap

variable [LawfulFiniteMap M K]

namespace Heap

variable [RA V] [ORA SI V]

open Classical in
@[rocq_alias alloc_updateP_strong_dep]
theorem alloc_updateP_strong_dep {Q : M V → Prop} {I : K → Prop} {m : M V} {f : K → V}
    (hI : PredInfinite I) (hf : ∀ i, get? m i = none → I i → ✓[SI] f i)
    (hQ : ∀ i, get? m i = none → I i → Q (insert m i (f i))) : m ~~>:[SI] Q := by
  refine UpdateP.total.mpr fun n mf hv => ?_
  obtain ⟨i, hIi, hi⟩ := hI ((toList (m • mf)).map (·.1))
  obtain ⟨hmi, hmfi⟩ := (Option.op_none_iff _ _).mp (by
    rw [← get?_op m mf (i := i)]
    rcases hm : get? (m • mf) i with _ | v
    · rfl
    · exact absurd (List.mem_map_of_mem (toList_get.mpr hm)) hi)
  refine ⟨insert m i (f i), hQ i hmi hIi, fun k => ?_⟩
  by_cases hk : i = k
  · subst hk
    rw [get?_op, get?_insert_eq rfl, hmfi]
    exact (hf i hmi hIi).validN
  · have hvk := hv k
    rw [get?_op, get?_insert_ne hk]
    rwa [get?_op] at hvk

@[rocq_alias alloc_updateP_strong]
theorem alloc_updateP_strong {Q : M V → Prop} {I : K → Prop} {m : M V} {x : V}
    (hI : PredInfinite I) (hx : ✓[SI] x)
    (hQ : ∀ i, get? m i = none → I i → Q (insert m i x)) : m ~~>:[SI] Q :=
  alloc_updateP_strong_dep (f := fun _ => x) hI (fun _ _ _ => hx) hQ

@[rocq_alias alloc_updateP]
theorem alloc_updateP [InfiniteType K] {Q : M V → Prop} {m : M V} {x : V} (hx : ✓[SI] x)
    (hQ : ∀ i, get? m i = none → Q (insert m i x)) : m ~~>:[SI] Q :=
  alloc_updateP_strong PredInfinite.true hx fun i hi _ => hQ i hi

@[rocq_alias alloc_updateP_cofinite]
theorem alloc_updateP_cofinite [InfiniteType K] {Q : M V → Prop} {m : M V} {x : V}
    (J : List K) (hx : ✓[SI] x)
    (hQ : ∀ i, get? m i = none → i ∉ J → Q (insert m i x)) : m ~~>:[SI] Q :=
  alloc_updateP_strong (PredInfinite.not_mem J) hx hQ

@[rocq_alias alloc_updateP_strong_dep']
theorem alloc_updateP_strong_dep' {I : K → Prop} {m : M V} {f : K → V}
    (hI : PredInfinite I) (hf : ∀ i, get? m i = none → I i → ✓[SI] f i) :
    m ~~>:[SI] fun m' => ∃ i, I i ∧ m' = insert m i (f i) ∧ get? m i = none :=
  alloc_updateP_strong_dep hI hf fun i hi hIi => ⟨i, hIi, rfl, hi⟩

@[rocq_alias alloc_updateP_strong']
theorem alloc_updateP_strong' {I : K → Prop} {m : M V} {x : V}
    (hI : PredInfinite I) (hx : ✓[SI] x) :
    m ~~>:[SI] fun m' => ∃ i, I i ∧ m' = insert m i x ∧ get? m i = none :=
  alloc_updateP_strong hI hx fun i hi hIi => ⟨i, hIi, rfl, hi⟩

@[rocq_alias alloc_updateP']
theorem alloc_updateP' [InfiniteType K] {m : M V} {x : V} (hx : ✓[SI] x) :
    m ~~>:[SI] fun m' => ∃ i, m' = insert m i x ∧ get? m i = none :=
  alloc_updateP hx fun i hi => ⟨i, rfl, hi⟩

@[rocq_alias alloc_updateP_cofinite']
theorem alloc_updateP_cofinite' [InfiniteType K] {m : M V} {x : V} (J : List K) (hx : ✓[SI] x) :
    m ~~>:[SI] fun m' => ∃ i, i ∉ J ∧ m' = insert m i x ∧ get? m i = none :=
  alloc_updateP_cofinite J hx fun i hi hJ => ⟨i, hJ, rfl, hi⟩

end Heap

end Freshness

section Properties

open ORA PartialMap LawfulPartialMap

variable [LawfulPartialMap M K] [RA V] [ORA SI V]

namespace Heap

open Classical in
@[rocq_alias alloc_unit_singleton_updateP]
theorem alloc_unit_singleton_updateP {P : V → Prop} {Q : M V → Prop} {u : V} {i : K}
    (hu : ✓[SI] u) (hid : ∀ x : V, u • x = x) (hx : u ~~>:[SI] P)
    (hQ : ∀ y, P y → Q (singleton i y)) : (∅ : M V) ~~>:[SI] Q := by
  refine UpdateP.total.mpr fun n gf hv => ?_
  have hi : ✓{n} (u •? get? gf i) := by
    have hvi := hv i
    rw [get?_op, get?_empty] at hvi
    rcases hgf : get? gf i with _ | z
    · exact hu.validN
    · rw [hgf] at hvi
      change ✓{n} (u • z)
      rw [hid z]
      exact hvi
  obtain ⟨y, hy, hvy⟩ := hx n (get? gf i) hi
  refine ⟨singleton i y, hQ y hy, fun k => ?_⟩
  by_cases hk : i = k
  · subst hk
    rw [get?_op, get?_singleton_eq rfl, Option.some_op_opM]
    exact hvy
  · have hvk := hv k
    rw [get?_op, get?_singleton_ne hk]
    rwa [get?_op, get?_empty] at hvk

@[rocq_alias alloc_unit_singleton_updateP']
theorem alloc_unit_singleton_updateP' {P : V → Prop} {u : V} {i : K}
    (hu : ✓[SI] u) (hid : ∀ x : V, u • x = x) (hx : u ~~>:[SI] P) :
    (∅ : M V) ~~>:[SI] fun m => ∃ y, m = singleton i y ∧ P y :=
  alloc_unit_singleton_updateP hu hid hx fun y hy => ⟨y, rfl, hy⟩

@[rocq_alias alloc_unit_singleton_update]
theorem alloc_unit_singleton_update {u : V} {i : K} {y : V}
    (hu : ✓[SI] u) (hid : ∀ x : V, u • x = x) (h : u ~~>[SI] y) :
    (∅ : M V) ~~>[SI] (singleton i y : M V) :=
  .of_updateP <| alloc_unit_singleton_updateP hu hid (.of_update h) fun _ => congrArg _

/-! ## Local updates -/

@[rocq_alias gmap_local_update]
theorem local_update {m1 m2 m1' m2' : M V}
    (h : ∀ i, (get? m1 i, get? m2 i) ~l~>[SI] (get? m1' i, get? m2' i)) :
    ((m1, m2) : M V × M V) ~l~>[SI] (m1', m2') := by
  refine (local_update_unital (SI := SI)).mpr fun n z hv he => ?_
  have he' i : get? m1 i ≡{n}≡ get? m2 i •? some (get? z i) :=
    (he i).trans (.of_eq (get?_op m2 z))
  exact ⟨fun i => (h i n _ (hv i) (he' i)).1,
    fun i => (h i n _ (hv i) (he' i)).2.trans (.of_eq (get?_op m2' z).symm)⟩

open Classical in
@[rocq_alias alloc_local_update]
theorem alloc_local_update {m1 m2 : M V} {i : K} {x : V}
    (hi : get? m1 i = none) (hx : ✓[SI] x) :
    ((m1, m2) : M V × M V) ~l~>[SI] (insert m1 i x, insert m2 i x) := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_insert_eq rfl, get?_insert_eq rfl, hi]
    exact LocalUpdate.alloc_option _ hx
  · rw [get?_insert_ne hj, get?_insert_ne hj]

@[rocq_alias alloc_singleton_local_update]
theorem alloc_singleton_local_update {m : M V} {i : K} {x : V}
    (hi : get? m i = none) (hx : ✓[SI] x) :
    ((m, ∅) : M V × M V) ~l~>[SI] (insert m i x, singleton i x) :=
  alloc_local_update hi hx

open Classical in
@[rocq_alias insert_local_update]
theorem insert_local_update {m1 m2 : M V} {i : K} {x y x' y' : V}
    (hi1 : get? m1 i = some x) (hi2 : get? m2 i = some y) (h : (x, y) ~l~>[SI] (x', y')) :
    ((m1, m2) : M V × M V) ~l~>[SI] (insert m1 i x', insert m2 i y') := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_insert_eq rfl, get?_insert_eq rfl, hi1, hi2]
    exact .option h
  · rw [get?_insert_ne hj, get?_insert_ne hj]

open Classical in
@[rocq_alias singleton_local_update_any]
theorem singleton_local_update_any {m : M V} {i : K} {y x' y' : V}
    (h : ∀ x, get? m i = some x → (x, y) ~l~>[SI] (x', y')) :
    ((m, singleton i y) : M V × M V) ~l~>[SI] (insert m i x', singleton i y') := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_insert_eq rfl, get?_singleton_eq rfl, get?_singleton_eq rfl]
    rcases hm : get? m i with _ | x
    · refine LocalUpdate.total_valid0 fun _ _ hinc => ?_
      obtain ⟨_ | z, hz⟩ := hinc <;> simp_all [ORA.op, optionOp]
    · exact .option (h x hm)
  · rw [get?_insert_ne hj, get?_singleton_ne hj, get?_singleton_ne hj]

@[rocq_alias singleton_local_update]
theorem singleton_local_update {m : M V} {i : K} {x y x' y' : V}
    (hi : get? m i = some x) (h : (x, y) ~l~>[SI] (x', y')) :
    ((m, singleton i y) : M V × M V) ~l~>[SI] (insert m i x', singleton i y') :=
  singleton_local_update_any fun _ hx => Option.some.inj (hi.symm.trans hx) ▸ h

open Classical in
@[rocq_alias delete_local_update]
theorem delete_local_update {m1 m2 : M V} {i : K} (x : V) [Exclusive SI x]
    (hi : get? m2 i = some x) :
    ((m1, m2) : M V × M V) ~l~>[SI] (delete m1 i, delete m2 i) := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_delete_eq rfl, get?_delete_eq rfl, hi]
    exact LocalUpdate.delete_option _ x
  · rw [get?_delete_ne hj, get?_delete_ne hj]

@[rocq_alias delete_singleton_local_update]
theorem delete_singleton_local_update {m : M V} {i : K} (x : V) [Exclusive SI x] :
    ((m, singleton i x) : M V × M V) ~l~>[SI] (delete m i, ∅) :=
  delete_singleton_eq (M := M) ▸
    delete_local_update x (get?_singleton_eq rfl)

open Classical in
@[rocq_alias delete_local_update_cancelable]
theorem delete_local_update_cancelable {m1 m2 : M V} {i : K} (mx : Option V)
    [Cancelable SI mx] (hi1 : get? m1 i = mx) (hi2 : get? m2 i = mx) :
    ((m1, m2) : M V × M V) ~l~>[SI] (delete m1 i, delete m2 i) := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_delete_eq rfl, get?_delete_eq rfl, hi1, hi2]
    exact LocalUpdate.delete_option_cancelable mx
  · rw [get?_delete_ne hj, get?_delete_ne hj]

@[rocq_alias delete_singleton_local_update_cancelable]
theorem delete_singleton_local_update_cancelable {m : M V} {i : K} {x : V}
    [Cancelable SI (some x)] (hi : get? m i = some x) :
    ((m, singleton i x) : M V × M V) ~l~>[SI] (delete m i, ∅) :=
  delete_singleton_eq (M := M) ▸
    delete_local_update_cancelable (some x) hi (get?_singleton_eq rfl)

end Heap

end Properties

section UnitalProperties

open ORA PartialMap LawfulPartialMap

variable [LawfulPartialMap M K] [URA V] [UORA SI V]

namespace Heap

open Classical in
@[rocq_alias insert_alloc_local_update]
theorem insert_alloc_local_update {m1 m2 : M V} {i : K} {x x' y' : V}
    (hi1 : get? m1 i = some x) (hi2 : get? m2 i = none) (h : (x, UnitOp.unit) ~l~>[SI] (x', y')) :
    ((m1, m2) : M V × M V) ~l~>[SI] (insert m1 i x', insert m2 i y') := by
  refine local_update fun j => ?_
  by_cases hj : i = j
  · subst hj
    rw [get?_insert_eq rfl, get?_insert_eq rfl, hi1, hi2]
    exact .option_none h
  · rw [get?_insert_ne hj, get?_insert_ne hj]

end Heap

end UnitalProperties

section HeapFunctor

variable {K} (H : Type _ → Type _) [LawfulPartialMap H K]

namespace PartialMap
open ORA

def map (f : α → β) : H α → H β := PartialMap.bindAlter (fun _ a => some <| f a)

@[rocq_alias map_fmap_ne, rocq_alias gmap_fmap_ne]
instance [OFE SI α] [OFE SI β] {f : α → β} [hne : OFE.NonExpansive SI f] : OFE.NonExpansive SI (map H f) where
  ne := by
    simp only [OFE.Dist, HasDist.dist, Option.Forall₂, map, get?_bindAlter, Option.bind]
    refine fun n m1 m2 => forall_imp fun k => ?_
    cases get? m1 k <;> cases get? m2 k <;> simp
    apply OFE.NonExpansive.ne

theorem map_id [OFE SI α] (a : H α) :
    PartialMap.map H id a = a := OFE.eq_dist_2 (SI := SI) <| by
  intro n x
  simp [PartialMap.map, get?_bindAlter, Option.bind]
  rcases get? a x <;> simp

@[rocq_alias gmapO_map]
def mapO [OFE SI α] [OFE SI β] (f : α -n>[SI] β) : OFE.Hom SI (H α) (H β) where
  f := map H f
  ne := inferInstance

@[rocq_alias gmap_fmap_ne_ext, rocq_alias gmapO_map_ne]
theorem map_ne {n : SI} [OFE SI β] (f g : α -> β) {heq : f ≡{n}≡ g} : map H f m ≡{n}≡ map H g m := by
  simp [OFE.Dist, HasDist.dist, Option.Forall₂, map, get?_bindAlter]
  intro k
  cases get? m k <;> simp
  exact heq _

theorem map_compose [OFE SI γ] (f : α -> β) (g : β -> γ) m :
    map H (g.comp f) m = map H g (map H f m) := OFE.eq_dist_2 (SI := SI) <| by
  intro n k
  simp [map, get?_bindAlter]
  cases get? m k <;> simp

theorem get?_map (f : α → β) (m : H α) (k : K) : get? (map H f m) k = (get? m k).map f := by
  simp only [map, get?_bindAlter]
  cases get? m k <;> rfl

@[rocq_alias gmap_fmap_cmra_morphism]
def mapC [RA α] [ORA SI α] [RA β] [ORA SI β] (f : α -C>[SI] β) : Hom SI (H α) (H β) where
  f := PartialMap.map H f
  ne := inferInstance
  validN {n : SI} {x} := by
    simp only [map, ValidN, Heap.validN, optionValidN]
    apply forall_imp
    intro k
    rw [get?_bindAlter]
    cases (get? x k) <;> simp
    apply f.validN
  pcore m := OFE.eq_dist_2 (SI := SI) <| by
    intro _ x
    simp [map, get?_bindAlter]
    rcases get? m x with _|v <;> simp
    have h : (pcore v).bind (fun a => some (f a)) = (pcore v).map f := by
      rw [Option.map_eq_bind]
      rfl
    rw [h]
    exact (f.pcore v).dist
  op m1 m2 := OFE.eq_dist_2 (SI := SI) <| by
    intro _ k
    simp [op, map, get?_bindAlter, get?_merge, Option.merge]
    cases get? m1 k <;> cases get? m2 k <;> simp
    exact (f.op _ _).dist
  monoN_ord h k := by rw [get?_map, get?_map]; exact (Option.mapC f).monoN_ord (h k)
  mono_ord h k := by rw [get?_map, get?_map]; exact (Option.mapC f).mono_ord (h k)
  increasing h := Heap.increasing_iff.mpr fun k => by
    rw [get?_map]; exact (Option.mapC f).increasing (Heap.increasing_get? h k)

abbrev PartialMapOF (F : COFE.OFunctorPre SI) : COFE.OFunctorPre SI :=
  fun A B _ _ => H (F A B)

@[rocq_alias gmapOF]
instance {F} [COFE.OFunctor SI F] : COFE.OFunctor SI (PartialMapOF H F) where
  ofe := inferInstance
  map f g := mapO H (COFE.OFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply map_ne
    apply COFE.OFunctor.map_ne.ne <;> simp_all
  map_id x := by
    refine .trans ?_ (map_id (SI := SI) H x)
    exact congrArg (map H · x) (funext fun a => COFE.OFunctor.map_id (F := F) a)
  map_comp f g f' g' m := OFE.eq_dist_2 (SI := SI) <| by
    simp [mapO, map]
    intro n x
    simp [get?_bindAlter]
    cases get? m x <;> simp
    exact (COFE.OFunctor.map_comp f g f' g' _).dist

@[rocq_alias gmapOF_contractive]
instance {F} [COFE.OFunctorContractive SI F] : COFE.OFunctorContractive SI (PartialMapOF H F) where
  map_contractive.1 h m := by
    apply map_ne _ _
    exact COFE.OFunctorContractive.map_contractive.1 h

@[rocq_alias gmapURF]
instance {F} [RFunctor SI F] : URFunctor SI (PartialMapOF H F) where
  map f g := mapC H (RFunctor.map f g)
  map_ne {_} _ _ _ _ _ _ _ := by
    constructor
    intros _ _ _ _ _ _ _ _
    apply map_ne
    apply RFunctor.map_ne.ne <;> simp_all
  map_id x := by
    refine .trans ?_ (map_id (SI := SI) H x)
    exact congrArg (map H · x) (funext fun a => RFunctor.map_id (F := F) a)
  map_comp f g f' g' m := OFE.eq_dist_2 (SI := SI) <| by
    simp [mapC, map]
    intro n x
    simp [get?_bindAlter]
    cases get? m x <;> simp
    exact (RFunctor.map_comp f g f' g' _).dist

instance instRFunctorAffine {F} [RFunctor SI F] [RFunctorAffine SI F] :
    RFunctorAffine SI (PartialMapOF H F) where
  affine := inferInstance

@[rocq_alias gmapURF_contractive]
instance {F} [RFunctorContractive SI F] : URFunctorContractive SI (PartialMapOF H F) where
  map_contractive.1 H m := by
    apply map_ne _ _
    exact (RFunctorContractive.map_contractive.1 H)

-- The unital functor instances above already give the non-unital ones, through
-- `URFunctor.toRFunctor` and `URFunctorContractive.toRFunctorContractive`.
#rocq_ignore gmapRF "Found by typeclass inference"
#rocq_ignore gmapRF_contractive "Found by typeclass inference"

end PartialMap
