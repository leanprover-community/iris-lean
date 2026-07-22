/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko, Zongyuan Liu
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Updates
public import Iris.Std.GenSets
public import Iris.Std.Infinite
public import Iris.Std.CoPset
meta import Iris.Std.RocqPorting

@[expose] public section

/-! ## Leibniz Set algebras
This file defines generic set algebras.
This generic construction specializes to both the union and disjoint-union set CMRAs.
All sets are given the discrete Leibniz OFE, and as a consequence, is not related to any
OFE/CMRA on the element type.
-/

open Iris Std CMRA OFE LawfulSet

inductive DisjointLeibnizSet (S : Type _) where
  | valid : S → DisjointLeibnizSet S
  | error : DisjointLeibnizSet S

instance : COFE (DisjointLeibnizSet S) := COFE.ofDiscrete _

instance inst_disjointLeibnizSet_DiscreteE {S : Type _} (x : DisjointLeibnizSet S) :
    DiscreteE x := ⟨fun h => h⟩

instance instEmptyCollectionDisjointLeibnizSet [LawfulSet S A] :
    EmptyCollection (DisjointLeibnizSet S) where
  emptyCollection := .valid ∅

instance instMembershowDisjointLeibnizSet [LawfulSet S A] :
    Membership A (DisjointLeibnizSet S) where
  mem s x :=
    match s with
    | .valid s   => x ∈ s
    | .error => False

theorem DisjointLeibnizSet.mem_empty [LawfulSet S A] (p : A) : ¬p ∈ (∅ : (DisjointLeibnizSet S)) :=
  Std.mem_empty

theorem DisjointLeibnizSet.exist_set_of_mem [LawfulSet S A] {x : DisjointLeibnizSet S} (h : p ∈ x) :
    ∃x', x = .valid x' :=
  match x with
  | .error => by simp [Membership.mem] at h
  | .valid x' => ⟨x', rfl⟩

theorem DisjointLeibnizSet.mem_of_eqv [LawfulSet S A] {a b : DisjointLeibnizSet S}
    (eqv : a ≡ b) (mx : x ∈ a) : x ∈ b :=
  match a, b with
  | .error, _ => False.elim mx
  | .valid _, .error => absurd eqv.to_eq (by simp)
  | .valid _, .valid _ => by simpa [← show _ = _ from eqv.to_eq]

namespace DisjointLeibnizSet

variable {S : Type _} [LawfulSet S A] [DecidableDisj S]

instance : CMRA (DisjointLeibnizSet S) where
  pcore _ := some (.valid ∅)
  op
    | valid x, valid y => if x ## y then valid (x ∪ y) else error
    | _, _ => error
  ValidN _ | valid _ => True | _ => False
  Valid | valid _ => True | _ => False
  op_ne.ne _ _ _ H := by rw [(H : _ = _)]
  pcore_ne {_ _ _ cx} _ H := ⟨cx, H, .rfl⟩
  validN_ne H G := (H : _ = _) ▸ G
  valid_iff_validN := ⟨(fun _ => ·), (· 0)⟩
  validN_succ := id
  validN_op_left {_ x y} := by rcases x <;> rcases y <;> simp
  assoc {x y z} := by
    rcases x with (x|_) <;> rcases y with (y|_) <;> rcases z with (z|_) <;> (try · simp)
    by_cases hyz : y ## z <;> by_cases hxy : x ## y <;>
      by_cases hxyzL : x ## y ∪ z <;> by_cases hxyzR : x ∪ y ## z <;>
    all_goals simp only [hyz, hxy, hxyzL, hxyzR, ↓reduceIte, valid.injEq]
    · exact union_assoc
    · have ⟨_, h⟩ := disjoint_union_right.mp hxyzL
      exact hxyzR (disjoint_union_left.mpr ⟨h, hyz⟩) |>.elim
    · have ⟨h, _⟩ := disjoint_union_left.mp hxyzR
      exact hxyzL (disjoint_union_right.mpr ⟨hxy, h⟩) |>.elim
    · have ⟨h, _⟩ := disjoint_union_right.mp hxyzL
      exact hxy h |>.elim
    · have ⟨h, _⟩ := disjoint_union_right.mp hxyzL
      exact hxy h |>.elim
    · have ⟨_, h⟩ := disjoint_union_left.mp hxyzR
      exact hyz h |>.elim
    · have ⟨_, h⟩ := disjoint_union_left.mp hxyzR
      exact hyz h |>.elim
  comm {x y} := by
    rcases x with (x|_) <;> rcases y with (y|_) <;> (try · simp)
    by_cases H : x ## y <;> grind only [Equiv.of_eq, disjoint_symm, union_comm]
  pcore_op_left {cx x} := by
    rcases x with (x|_) <;> rcases cx with (cx|_) <;> (try · simp)
    rintro ⟨⟩
    simp [disjoint_empty_left]
  pcore_idem {x cx} := by grind only [Equiv.of_eq]
  pcore_op_mono {_ x} := by
    rcases x with (x|_) <;> rintro ⟨⟩ y
    exists (.valid ∅)
    simp [disjoint_empty_left]
  extend {_ _ y₁ y₂} _ h := ⟨y₁, y₂, ⟨h, .rfl, .rfl⟩⟩

instance instDiscreteDisjointLeibnizSet : CMRA.Discrete (DisjointLeibnizSet S) where
  discrete_0 := fun h => h
  discrete_valid := id

instance instUCMRADisjointLeibnizSet : UCMRA (DisjointLeibnizSet S) where
  unit := .valid ∅
  unit_valid := by simp [Valid]
  unit_left_id {x} := by rcases x <;> simp [disjoint_empty_left, op]
  pcore_unit := by simp [pcore]

theorem valid_set {s : S} : ✓ valid s := ⟨⟩
theorem validN_set {s : S}: ✓{n} valid s := ⟨⟩

theorem not_valid_invalid : ¬ ✓ (error : DisjointLeibnizSet S) := False.elim
theorem not_validN_invalid : ¬ ✓{n} (error : DisjointLeibnizSet S) := False.elim

theorem mem_iff_of_valid_union {x y : DisjointLeibnizSet S} (v : ✓ x • y) (a : A) :
    a ∈ x • y ↔ a ∈ x ∨ a ∈ y := by
  match x, y with
  | error, _ => exact v.elim
  | _, error => simp only [op] at v; exact v.elim
  | valid x, valid y =>
    by_cases h : x ## y
    · simp only [op, h, ↓reduceIte]
      exact mem_union
    · simp only [op, h, ↓reduceIte] at v; exact v.elim

theorem mem_iff_of_validN_union {x y : DisjointLeibnizSet S} (v : ✓{n} x • y) (a : A) :
    a ∈ x • y ↔ a ∈ x ∨ a ∈ y := mem_iff_of_valid_union v a

@[rocq_alias coPset_disj_included, rocq_alias gset_disj_included]
theorem included_iff_subset {X Y : S} : valid X ≼ valid Y ↔ X ⊆ Y := by
  refine ⟨?_, ?_⟩
  · rintro ⟨(Z|_), HZ⟩
    · by_cases H : X ## Z
      · obtain rfl : Y = X ∪ Z := by have := HZ; simp_all [op]
        exact fun _ => (mem_union.mpr <| .inl ·)
      · exact absurd HZ (by simp [op, H])
    · exact absurd HZ (by simp [op])
  · intro Hsub
    exists valid (Y \ X)
    suffices h : Y = X ∪ Y \ X by
      have H : X ## (Y \ X) := fun _ H => (mem_diff.mp H.2).right H.1
      rw [show (valid X • valid (Y \ X) : DisjointLeibnizSet S) = valid (X ∪ Y \ X) by simp [op, H]]
      exact congrArg valid h
    ext p; rw [mem_union, mem_diff]
    refine ⟨by grind, (·.casesOn (Hsub _) (·.left))⟩

@[rocq_alias coPset_disj_union, rocq_alias gset_disj_union]
theorem disj_op_union {X Y : S} (Hdisj : X ## Y) :
    (valid X) • (valid Y) = valid (X ∪ Y) := by
  simp [op, Hdisj]

@[rocq_alias coPset_disj_valid_op, rocq_alias gset_disj_valid_op]
theorem valid_op_iff_disj {X Y : S} : ✓ ((valid X) • (valid Y)) ↔ X ## Y := by
  by_cases H : X ## Y <;> simp [H, op, Valid]

@[rocq_alias coPset_disj_valid_inv_l, rocq_alias gset_disj_valid_inv_l]
theorem valid_inv_l {X : S} {Y : DisjointLeibnizSet S} :
    ✓ (valid X) • Y → ∃ Y', Y = valid Y' ∧ X ## Y' := by
  simp only [op, Valid]
  rcases Y with (Y|_) <;> try (· simp)
  by_cases H : X ## Y <;> simp [H]

theorem not_mem_of_mem_and_valid_op_left {x y : DisjointLeibnizSet S} (v : ✓ x • y) {p : A} (m : p ∈ x)
    : ¬ p ∈ y := by
  intro h
  obtain ⟨x', hx⟩ := exist_set_of_mem m
  obtain ⟨y', hy⟩ := exist_set_of_mem h
  exact ((valid_op_iff_disj.mp (hx ▸ hy ▸ v)) p
    ⟨show p ∈ valid x' from hx ▸ m, show p ∈ valid y' from hy ▸ h⟩).elim

theorem not_mem_of_mem_and_valid_op_right {x y : DisjointLeibnizSet S}
  (v : ✓ x • y) {p : A} (m : p ∈ y)
    : ¬ p ∈ x := not_mem_of_mem_and_valid_op_left ((OFE.Equiv.valid CMRA.comm').mp v) m

@[rocq_alias gset_disj_dealloc_local_update]
theorem localUpdate_dealloc {X Y : S} : (valid X, valid Y) ~l~> (valid (X \ Y), valid ∅) := by
  refine LocalUpdate.total_valid fun vx vy inc => ?_
  refine (local_update_unital_discrete ..).mpr fun z hx heq => ⟨valid_mapN (fun _ _ => vx) vx, ?_⟩
  rcases z with (z|_)
  · by_cases Hdisj : Y ## z <;> simp only [Hdisj, ↓reduceIte, op] at heq
    · obtain rfl := valid.inj heq.to_eq
      simp only [op, disjoint_empty_left, ↓reduceIte, union_empty_left, valid.injEq]
      ext i
      grind [Hdisj i, mem_diff, mem_union]
    · exact absurd heq.to_eq (by simp)
  · exact absurd heq.to_eq (by simp [op])

@[rocq_alias gset_disj_dealloc_empty_local_update]
theorem localUpdate_dealloc_empty {X Z : S} :
    (valid Z • valid X, valid Z) ~l~> (valid X, valid ∅) := by
  refine LocalUpdate.total_valid fun Hdisj _ _ => ?_
  rw [valid_op_iff_disj] at Hdisj
  rw [disj_op_union Hdisj]
  have Heq : X = (Z ∪ X) \ Z := by
    ext a; rw [mem_diff, mem_union]
    exact ⟨fun H => ⟨.inr H, (Hdisj a ⟨·, H⟩)⟩, fun H => H.1.casesOn (H.2 · |>.elim) id⟩
  conv => rhs; rw [Heq]
  exact localUpdate_dealloc

@[rocq_alias gset_disj_dealloc_op_local_update]
theorem localUpdate_op_l {X Y Z : S} :
    (valid Z • valid X, valid Z • valid Y) ~l~> (valid X, valid Y) := by
  suffices (valid Z • valid X, valid Z • valid Y) ~l~> (valid X, unit • valid Y) by
    rwa [unit_left_id] at this
  exact LocalUpdate.op_frame _ _ _ _ _ localUpdate_dealloc_empty

@[rocq_alias gset_disj_alloc_op_local_update]
theorem localUpdate_op_r {X Y Z : S} (Hdisj : Z ## X) :
    (valid X, valid Y) ~l~> (valid Z • valid X, valid Z • valid Y) :=
  LocalUpdate.op_discrete _ _ _ fun _ => valid_op_iff_disj.mpr Hdisj

@[rocq_alias gset_disj_alloc_local_update]
theorem localUpdate_union_r_of_disj (X Y Z : S) (Hdisj : Z ## X) :
    (valid X, valid Y) ~l~> (valid (Z ∪ X), valid (Z ∪ Y)) := by
  refine LocalUpdate.total_valid fun vx vy inc => ?_
  have HdisjY : Z ## Y := fun a ⟨Hz, Hy⟩ => Hdisj a ⟨Hz, included_iff_subset.mp inc a Hy⟩
  rw [←disj_op_union Hdisj, ←disj_op_union HdisjY]
  exact localUpdate_op_r Hdisj

@[rocq_alias gset_disj_alloc_empty_local_update]
theorem localUpdate_alloc_empty_of_disj (X Z : S) (Hdisj : Z ## X) :
    (valid X, valid ∅) ~l~>
    (valid (Z ∪ X), valid Z) := by
  rw [(show valid Z ≡ valid (Z ∪ ∅) by simp [union_empty_right]).to_eq]
  exact localUpdate_union_r_of_disj X ∅ Z Hdisj

@[rocq_alias gset_disj_alloc_updateP_strong]
theorem alloc_updateP_strong {P : A → Prop} {Q : DisjointLeibnizSet S → Prop} {X : S}
    (Hfresh : ∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) (HQ : ∀ {i}, i ∉ X → P i → Q (valid ({i} ∪ X))) :
    valid X ~~>: Q := by
  refine UpdateP.discrete_total.mpr fun z H => ?_
  obtain ⟨Y, rfl, Hdisj⟩ := valid_inv_l H
  have ⟨y, Hnotin, HP⟩ := Hfresh (X ∪ Y) (fun _ => (mem_union.mpr <| .inl ·))
  exists valid ({y} ∪ X)
  refine ⟨HQ (Hnotin <| mem_union.mpr <| .inl ·) HP, ?_⟩
  refine valid_op_iff_disj.mpr fun i => ?_
  simp only [mem_union, mem_singleton, not_and]
  rintro (rfl | G)
  · exact (Hnotin <| mem_union.mpr <| .inr ·)
  · grind [Hdisj i]

@[rocq_alias gset_disj_alloc_updateP_strong']
theorem alloc_updateP_strong' {P : A → Prop} {X : S} (H : ∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) :
    valid X ~~>: fun Y => ∃ i, Y = valid ({i} ∪ X) ∧ i ∉ X ∧ P i :=
  alloc_updateP_strong H (by grind)

@[rocq_alias gset_disj_alloc_empty_updateP_strong]
theorem alloc_empty_updateP_strong {P : A → Prop} {Q : DisjointLeibnizSet S → Prop}
  (Hfresh : ∀ Y : S, ∃ j, j ∉ Y ∧ P j) (Hvalid : ∀ {i}, P i → Q (valid {i})) :
    valid ∅ ~~>: Q := by
  refine alloc_updateP_strong (fun _ => Hfresh ·) (fun _ HP => ?_)
  rw [union_empty_right]
  exact Hvalid HP

@[rocq_alias gset_disj_alloc_empty_updateP_strong']
theorem alloc_empty_updateP_strong' {P : A → Prop} (Hfresh : ∀ Y : S, ∃ j, j ∉ Y ∧ P j) :
    valid (∅ : S) ~~>: fun Y => ∃ i, Y = valid {i} ∧ P i := by
  refine alloc_updateP_strong (fun _ => Hfresh ·) ?_
  refine fun _ HP => ⟨_, ⟨?_, HP⟩⟩
  rw [union_empty_right]

end DisjointLeibnizSet

namespace DisjointLeibnizSet

variable {S : Type _} [LawfulFiniteSet S A] [DecidableDisj S] [InfiniteType A]

@[rocq_alias gset_disj_alloc_updateP]
theorem alloc_updateP {Q : DisjointLeibnizSet S → Prop} {X} (Hv : ∀ {i}, i ∉ X → Q (valid ({i} ∪ X))) :
    valid X ~~>: Q := by
  refine alloc_updateP_strong (P := fun _ => True) (fun Y H => ?_) (fun _ => Hv ·)
  obtain ⟨a, _⟩ := FiniteSet.fresh Y
  exists a

@[rocq_alias gset_disj_alloc_updateP']
theorem alloc_updateP' {X : S} : valid X ~~>: fun Y => ∃ i : A, Y = valid ({i} ∪ X) ∧ i ∉ X :=
  alloc_updateP (by grind)

@[rocq_alias gset_disj_alloc_empty_updateP]
theorem alloc_empty_updateP {Q : DisjointLeibnizSet S → Prop} (Hv : ∀ {i}, Q (valid {i})) :
    valid ∅ ~~>: Q := by
  refine alloc_updateP (fun i => ?_)
  rw [union_empty_right]
  exact Hv

@[rocq_alias gset_disj_alloc_empty_updateP']
theorem alloc_empty_updateP' : valid (∅ : S) ~~>: fun Y => ∃ i, Y = valid {i} :=
  alloc_empty_updateP (by grind)

end DisjointLeibnizSet

inductive LeibnizSet (S : Type _) where
  | valid (s : S)

instance : COFE (LeibnizSet S) := COFE.ofDiscrete _

namespace LeibnizSet

variable {S : Type _} [LawfulSet S A]

instance : CMRA (LeibnizSet S) where
  pcore := some
  op | .valid x, valid y => valid (x ∪ y)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ H := by rw [(H : _ = _)]
  pcore_ne {_ _ _} _ H1 H2 :=  ⟨_, rfl, .trans (.of_eq <| Option.some.injEq _ _ ▸ H2.symm) H1⟩
  validN_ne _ _ := by simp
  valid_iff_validN := by simp
  validN_succ _ := by simp
  validN_op_left _ := by simp
  assoc := by simp [union_assoc]
  comm := by simp [union_comm]
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; simp [union_idem]
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ y; exists y
  extend {_ _ _ _} _ h := ⟨_, _, h, .rfl, .rfl⟩

instance : UCMRA (LeibnizSet S) where
  unit := valid ∅
  unit_valid := by simp [Valid]
  unit_left_id := by simp [op, union_empty_left]
  pcore_unit := by simp [pcore, pcore]

instance instDiscreteLeibnizSet : CMRA.Discrete (LeibnizSet S) where
  discrete_0 := fun h => h
  discrete_valid := id

@[rocq_alias gset_core_id]
instance instCoreIdLeibnizSet (X : LeibnizSet S) : CMRA.CoreId X := ⟨rfl⟩

@[rocq_alias coPset_op, rocq_alias gset_op]
theorem op_union (X Y : S) : (valid X) • (valid Y) = valid (X ∪ Y) := by simp [op]

@[rocq_alias coPset_core, rocq_alias gset_core]
theorem core_equiv (X : LeibnizSet S) : core X = X := by
  change (pcore X).getD X = X
  simp [pcore]

@[rocq_alias coPset_included, rocq_alias gset_included]
theorem included_iff_subset (X Y : S) : valid X ≼ valid Y ↔ X ⊆ Y := by
  simp only [Included, op]
  refine ⟨fun ⟨_, H⟩ => ?_, fun Hsub => ?_⟩
  · obtain ⟨rfl⟩ := H
    exact fun _ Hp => mem_union.mpr (.inl Hp)
  · exists valid (Y \ X)
    congr 1; ext p
    rw [mem_union, mem_diff]
    refine ⟨fun H1 => ?_, (·.casesOn (Hsub _) (·.left))⟩
    by_cases H : (p ∈ X)
    · exact .inl H
    · exact .inr ⟨H1, H⟩

@[rocq_alias coPset_opM, rocq_alias gset_opM]
theorem opM_union (X : LeibnizSet S) (mY : Option (LeibnizSet S)) :
    X •? mY = X • mY.getD (valid ∅) := by
  cases mY <;> simp [op?, op, union_empty_right]

@[rocq_alias coPset_update, rocq_alias gset_update]
theorem update (X Y : S) : valid X ~~> valid Y :=
  fun _ _ _ => trivial

@[rocq_alias coPset_local_update, rocq_alias gset_local_update]
theorem localUpdate (X Y X' : S) (H : X ⊆ X') :
    (valid X, valid Y) ~l~> (valid X', valid X') := by
  refine (LocalUpdate.discrete ..).mpr fun mz _ e => ⟨trivial, ?_⟩
  match mz with
  | none => rfl
  | some (.valid Z) =>
    simp only [op?, op] at e ⊢
    have hZ : Z ⊆ X' := subset_trans union_subset_right (valid.inj e.to_eq ▸ H)
    rw [union_comm, union_subset_absorption hZ]

end LeibnizSet

/-! ## The CoPset CMRAs

The two resource algebras over `CoPset`, obtained as instances of the generic set-CMRA construction above. -/

/-- The union CMRA over `CoPset`: every element is valid and composition is set union. -/
@[rocq_alias coPsetO, rocq_alias coPsetR, rocq_alias coPsetUR]
abbrev CoPsetL := LeibnizSet CoPset

#rocq_ignore coPset_valid_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_unit_instance "Provided by the `UCMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_op_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_pcore_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_ra_mixin "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore coPset_cmra_discrete "Provided by the generic `CMRA.Discrete (LeibnizSet S)` instance."
#rocq_ignore coPset_ucmra_mixin "Provided by the `UCMRA (LeibnizSet S)` instance."

/-- The disjoint union CMRA over `CoPset`: composition of two sets is valid only when they are
disjoint, tracked through the `DisjointLeibnizSet` error element. -/
@[rocq_alias coPset_disj, rocq_alias coPset_disjO, rocq_alias coPset_disjR, rocq_alias coPset_disjUR]
abbrev CoPsetDisjL := DisjointLeibnizSet CoPset

#rocq_ignore coPset_disj_valid_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_unit_instance "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_op_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_pcore_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_ra_mixin "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore coPset_disj_cmra_discrete "Provided by `CMRA.Discrete (DisjointLeibnizSet S)`."
#rocq_ignore coPset_disj_ucmra_mixin "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."

/-! ## The Gset CMRAs

The `LeibnizSet`/`DisjointLeibnizSet` construction over an arbitrary `LawfulSet` also subsumes the
`gset` resource algebras: the OFE, RA, and UCMRA structures are aliased onto the generic types
below, and the `gset` typeclass instances / mixins are provided by the generic instances. -/

#rocq_ignore gsetO "Use `[LawfulSet S A] → LeibnizSet S` and its `COFE` instance."
#rocq_ignore gsetR "Use `[LawfulSet S A] → LeibnizSet S` and its `CMRA` instance."
#rocq_ignore gsetUR "Use `[LawfulSet S A] → LeibnizSet S` and its `UCMRA` instance."
#rocq_ignore gset_valid_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore gset_unit_instance "Provided by the `UCMRA (LeibnizSet S)` instance."
#rocq_ignore gset_op_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore gset_pcore_instance "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore gset_ra_mixin "Provided by the `CMRA (LeibnizSet S)` instance."
#rocq_ignore gset_cmra_discrete "Provided by the generic `CMRA.Discrete (LeibnizSet S)` instance."
#rocq_ignore gset_ucmra_mixin "Provided by the `UCMRA (LeibnizSet S)` instance."

#rocq_ignore gset_disj "Use `[LawfulSet S A] → DisjointLeibnizSet S`."
#rocq_ignore gset_disjO "Use `[LawfulSet S A] → DisjointLeibnizSet S` and its `COFE` instance."
#rocq_ignore gset_disjR "Use `[LawfulSet S A] → DisjointLeibnizSet S` and its `CMRA` instance."
#rocq_ignore gset_disjUR "Use `[LawfulSet S A] → DisjointLeibnizSet S` and its `UCMRA` instance."
#rocq_ignore gset_disj_valid_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore gset_disj_unit_instance "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore gset_disj_op_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore gset_disj_pcore_instance "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore gset_disj_ra_mixin "Provided by the `CMRA (DisjointLeibnizSet S)` instance."
#rocq_ignore gset_disj_cmra_discrete "Provided by `CMRA.Discrete (DisjointLeibnizSet S)`."
#rocq_ignore gset_disj_ucmra_mixin "Provided by the `UCMRA (DisjointLeibnizSet S)` instance."
