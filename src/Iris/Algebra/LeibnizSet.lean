/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.Updates
public import Iris.Std.GenSets
public import Iris.Std.Infinite

@[expose] public section

/-! ## Leibniz Set algebras
This file defines generic set algebras.
This subsumes both gset and copset from Iris-Rocq.
All sets are given the discrete Leibniz OFE, and as a consequence, is not related to any
OFE/CMRA on the element type.
-/

open Iris Std CMRA OFE LawfulSet

inductive DisjointLeibnizSet (S : Type _) where
  | valid : S → DisjointLeibnizSet S
  | error : DisjointLeibnizSet S

instance : COFE (DisjointLeibnizSet S) := COFE.ofDiscrete _ Eq_Equivalence
instance : Leibniz (DisjointLeibnizSet S) := ⟨id⟩

namespace DisjointLeibnizSet

variable {S : Type _} [LawfulSet S A] [DecidableDisj S]

instance : CMRA (DisjointLeibnizSet S) where
  pcore _ := some (.valid ∅)
  op
    | valid x, valid y => if x ## y then valid (x ∪ y) else error
    | _, _ => error
  ValidN _ | valid _ => True | _ => False
  Valid | valid _ => True | _ => False
  op_ne.ne _ _ _ H := by rw [H]
  pcore_ne {_ _ _ cx} _ H := ⟨cx, H, rfl⟩
  validN_ne H G := H ▸ G
  valid_iff_validN := ⟨(fun _ => ·), (· 0)⟩
  validN_succ := id
  validN_op_left {_ x y} := by rcases x <;> rcases y <;> simp
  assoc {x y z} := by
    rcases x with (x|_) <;> rcases y with (y|_) <;> rcases z with (z|_) <;> (try · simp)
    simp only [leibniz]
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
    by_cases H : x ## y
    · simp [H, disjoint_symm H, union_comm]
    · simpa [H] using (H <| disjoint_symm ·)
  pcore_op_left {cx x} := by
    rcases x with (x|_) <;> rcases cx with (cx|_) <;> (try · simp)
    rintro ⟨⟩
    simp [disjoint_empty_left]
  pcore_idem {x cx} := by rcases x with (x|_) <;> rcases cx with (cx|_) <;> simp
  pcore_op_mono {_ x} := by
    rcases x with (x|_) <;> rintro ⟨⟩ y
    exists (.valid ∅)
    simp [disjoint_empty_left]
  extend {_ _ y₁ y₂} _ h := ⟨y₁, y₂, ⟨h, rfl, rfl⟩⟩

instance : CMRA.Discrete (DisjointLeibnizSet S) where
  discrete_0 := id
  discrete_valid := id

instance : UCMRA (DisjointLeibnizSet S) where
  unit := .valid ∅
  unit_valid := by simp [Valid]
  unit_left_id {x} := by rcases x <;> simp [disjoint_empty_left, op]
  pcore_unit := by simp [pcore]

theorem included_iff_subset {X Y : S} : valid X ≼ valid Y ↔ X ⊆ Y := by
  refine ⟨?_, ?_⟩
  · rintro ⟨(Z|_), HZ⟩
    · by_cases H : X ## Z
      · obtain rfl : Y = X ∪ Z := by simp_all [op]
        exact fun _ => (mem_union.mpr <| .inl ·)
      · simp [op, H] at HZ
    · simp [op] at HZ
  · intro Hsub
    exists valid (Y \ X)
    suffices Y = X ∪ Y \ X by
      have H : X ## (Y \ X) := fun _ H => (mem_diff.mp H.2).right H.1
      simpa [op, H]
    ext p; rw [mem_union, mem_diff]
    refine ⟨by grind, (·.casesOn (Hsub _) (·.left))⟩

theorem disj_op_union {X Y : S} (Hdisj : X ## Y) :
    (valid X) • (valid Y) ≡ valid (X ∪ Y) := by
  simp [op, Hdisj]

theorem valid_op_iff_disj {X Y : S} : ✓ ((valid X) • (valid Y)) ↔ X ## Y := by
  by_cases H : X ## Y <;> simp [H, op, Valid]

theorem valid_inv_l {X : S} {Y : DisjointLeibnizSet S} :
    ✓ (valid X) • Y → ∃ Y', Y = valid Y' ∧ X ## Y' := by
  simp only [op, Valid]
  rcases Y with (Y|_) <;> try (· simp)
  by_cases H : X ## Y <;> simp [H]

theorem localUpdate_dealloc {X Y : S} : (valid X, valid Y) ~l~> (valid (X \ Y), valid ∅) := by
  refine LocalUpdate.total_valid fun vx vy inc => ?_
  refine (local_update_unital_discrete ..).mpr fun z hx heq => ⟨valid_mapN (fun _ _ => vx) vx, ?_⟩
  rcases z with (z|_) <;> try · cases heq
  by_cases Hdisj : Y ## z <;> simp only [Hdisj, ↓reduceIte, op, leibniz] at heq
  · obtain ⟨rfl⟩ := valid.injEq _ _ ▸ heq
    simp only [op, leibniz, disjoint_empty_left, ↓reduceIte, union_empty_left, valid.injEq] at ⊢
    ext i
    rw [mem_diff, mem_union]
    specialize (Hdisj i)
    grind
  · cases heq

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

theorem localUpdate_op_l {X Y Z : S} :
    (valid Z • valid X, valid Z • valid Y) ~l~> (valid X, valid Y) := by
  suffices (valid Z • valid X, valid Z • valid Y) ~l~> (valid X, unit • valid Y) by
    rwa [show UCMRA.unit • valid Y ≡ valid Y by apply unit_left_id] at this
  exact LocalUpdate.op_frame _ _ _ _ _ localUpdate_dealloc_empty

theorem localUpdate_op_r {X Y Z : S} (Hdisj : Z ## X) :
    (valid X, valid Y) ~l~> (valid Z • valid X, valid Z • valid Y) :=
  LocalUpdate.op_discrete _ _ _ fun _ => valid_op_iff_disj.mpr Hdisj

theorem localUpdate_union_r_of_disj (X Y Z : S) (Hdisj : Z ## X) :
    (valid X, valid Y) ~l~> (valid (Z ∪ X), valid (Z ∪ Y)) := by
  refine LocalUpdate.total_valid fun vx vy inc => ?_
  have HdisjY : Z ## Y := fun a ⟨Hz, Hy⟩ => Hdisj a ⟨Hz, included_iff_subset.mp inc a Hy⟩
  rw [←disj_op_union Hdisj, ←disj_op_union HdisjY]
  exact localUpdate_op_r Hdisj

theorem localUpdate_alloc_empty_of_disj (X Z : S) (Hdisj : Z ## X) :
    (valid X, valid ∅) ~l~>
    (valid (Z ∪ X), valid Z) := by
  rw [show valid Z ≡ valid (Z ∪ ∅) by simp [union_empty_right]]
  exact localUpdate_union_r_of_disj X ∅ Z Hdisj

theorem alloc_updateP_strong (P : A → Prop) (Q : DisjointLeibnizSet S → Prop) (X : S) :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    (∀ i, i ∉ X → P i → Q (valid ({i} ∪ X))) →
    valid X ~~>: Q := by
    intro Hfresh HQ
    apply UpdateP.discrete_total.mpr
    intro Z H
    have ⟨Y, Heq, Hdisj⟩ := valid_inv_l H
    have ⟨y, Hnotin, HP⟩ := (Hfresh (X ∪ Y) (fun i Hi => mem_union.mpr (.inl Hi)))
    exists (valid ({y} ∪ X)); constructor
    · apply HQ _ (fun Hc => Hnotin (mem_union.mpr (.inl Hc))) HP
    · rw [Heq]; apply valid_op_iff_disj.mpr
      intro i; simp only [mem_union, mem_singleton, not_and]
      rintro (G | G)
      · subst G; exact (fun Hc => Hnotin (mem_union.mpr (.inr Hc)))
      · specialize (Hdisj i); grind

theorem alloc_updateP_strong' (P : A → Prop) (X : S) :
  (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
  valid X ~~>: fun Y => ∃ i, Y = valid ({i} ∪ X) ∧ i ∉ X ∧ P i := by
  intro Hfresh; apply alloc_updateP_strong P _ X Hfresh; grind

theorem alloc_empty_updateP_strong (P : A → Prop) (Q : DisjointLeibnizSet S → Prop) :
  (∀ Y : S, ∃ j, j ∉ Y ∧ P j) →
  (∀ i : A, P i → Q (valid {i})) → valid ∅ ~~>: Q := by
  intro Hfresh Hvalid
  apply alloc_updateP_strong P Q _ (fun Y _ => Hfresh Y)
  intro i _ HP; rw [union_empty_right]; exact Hvalid i HP

theorem alloc_empty_updateP_strong' (P : A → Prop) :
  (∀ Y : S, ∃ j, j ∉ Y ∧ P j) →
  valid (∅ : S) ~~>: fun Y => ∃ i, Y = valid {i} ∧ P i := by
  intro Hfresh
  apply alloc_updateP_strong _ _ _ (fun Y _ => Hfresh Y)
  intro i _ HP; exists i; rw [union_empty_right]; simp [HP]

end DisjointLeibnizSet

namespace DisjointLeibnizSet

variable {S : Type _} [LawfulFiniteSet S A] [DecidableDisj S] [InfiniteType A]

theorem alloc_updateP (Q : DisjointLeibnizSet S → Prop) X :
  (∀ i, i ∉ X → Q (valid ({i} ∪ X))) → valid X ~~>: Q := by
  intro Hvalid
  apply alloc_updateP_strong (fun _ => True) _ X _ (fun i Hnotin _ => Hvalid i Hnotin)
  intro Y Hsub; simp only [and_true]
  exact FiniteSet.fresh Y

theorem alloc_updateP' (X : S) :
  valid X ~~>: fun Y => ∃ i : A, Y = valid ({i} ∪ X) ∧ i ∉ X := by
  apply alloc_updateP; grind

theorem alloc_empty_updateP (Q : DisjointLeibnizSet S → Prop) :
  (∀ i, Q (valid {i})) → valid ∅ ~~>: Q := by
  intro Hvalid; apply alloc_updateP Q ∅; intro i _; rw [union_empty_right]; apply Hvalid i

theorem alloc_empty_updateP' :
  valid (∅ : S) ~~>: fun Y => ∃ i, Y = valid {i} := by
  apply alloc_empty_updateP _ (fun i => ⟨i, rfl⟩)

end DisjointLeibnizSet

inductive LeibnizSet (S : Type _) where
  | valid (s : S)

instance : COFE (LeibnizSet S) := COFE.ofDiscrete _ Eq_Equivalence
instance : Leibniz (LeibnizSet S) := ⟨id⟩

namespace LeibnizSet

variable {S : Type _} [LawfulSet S A]

instance : CMRA (LeibnizSet S) where
  pcore := some
  op | .valid x, valid y => valid (x ∪ y)
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ H := by rw [H]
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
  extend {_ _ _ _} _ := (⟨_, _, ⟨·, rfl, rfl⟩⟩)

instance : UCMRA (LeibnizSet S) where
  unit := valid ∅
  unit_valid := by simp [Valid]
  unit_left_id := by simp [op, union_empty_left]
  pcore_unit := by simp [pcore, pcore]

theorem op_union (X Y : S) : (valid X) • (valid Y) ≡ valid (X ∪ Y) := by simp [op]

theorem core_equiv (X : LeibnizSet S) : core X ≡ X := by
  change (pcore X).getD X ≡ X
  simp [pcore]

theorem included_iff_subset (X Y : S) : valid X ≼ valid Y ↔ X ⊆ Y := by
  simp only [Included, op]
  refine ⟨fun ⟨_, H⟩ => ?_, fun Hsub => ?_⟩
  · rcases H with ⟨rfl⟩
    exact fun _ Hp => mem_union.mpr (.inl Hp)
  · exists valid (Y \ X)
    refine .of_eq ?_
    congr 1; ext p
    rw [mem_union, mem_diff]
    refine ⟨fun H1 => ?_, (·.casesOn (Hsub _) (·.left))⟩
    by_cases H : (p ∈ X)
    · exact .inl H
    · exact .inr ⟨H1, H⟩

end LeibnizSet
