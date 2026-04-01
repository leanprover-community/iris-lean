/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.LocalUpdates
public import Iris.Std.GenSets

@[expose] public section

/-! ## Set algebra

This file defines an set algebra.
In comparison to Rocq, we have a single algebra for both gset and copset.
The set should satisfy the usual set axioms, as in LawfulSet and have decidable disjointedness.
-/

open Iris Std

section OFE

open OFE LawfulSet

section Def

variable (S : Type _)

inductive GenSetDisj S where
  | set_valid : S → GenSetDisj S
  | set_invalid : GenSetDisj S

abbrev GenSetDisjO := LeibnizO (GenSetDisj S)

instance : OFE (GenSetDisjO S) := inferInstance

end Def

namespace GenSetDisj

abbrev gen_set_valid : S → GenSetDisjO S := fun X => ⟨.set_valid X⟩

section dec_disj

variable {S : Type _} [LawfulSet S A] [DecidableDisj S]

def unit : GenSetDisjO S := gen_set_valid ∅

def pcore : GenSetDisjO S → Option (GenSetDisjO S) := fun _ => some unit

def valid (x : GenSetDisjO S) : Prop :=
  match x.car with
  | .set_valid _ => True
  | _ => False

def validN : Nat → GenSetDisjO S → Prop := fun _ x => valid x

def op (x y : GenSetDisjO S) : GenSetDisjO S :=
  match x.car, y.car with
  | .set_valid x, .set_valid y => if (x ## y) then ⟨.set_valid (x ∪ y)⟩ else ⟨.set_invalid⟩
  | _, _ => ⟨.set_invalid⟩

instance op_ne {x : GenSetDisjO S} : OFE.NonExpansive (op x) where
  ne _ _ _ H := by rw [H]

theorem assoc {x y z : GenSetDisjO S} : op x (op y z) ≡ op (op x y) z := by
  rcases x, y, z with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩, ⟨⟨z⟩ | _⟩⟩ <;> simp [op]
  by_cases H : y ## z
  · simp only [H, ↓reduceIte]
    by_cases G : x ## y
    · simp [G, ↓reduceIte]
      by_cases J : x ## z
      · simp [↓reduceIte, union_assoc
          , show x ## y ∪ z by
              symm; rw [disjoint_union_left]; exact ⟨disjoint_symm G, disjoint_symm J⟩
          , show x ∪ y ## z by rw [disjoint_union_left]; exact ⟨J, H⟩]
      · simp [↓reduceIte
          , show ¬ x ## y ∪ z by
              intro C; rw [disjoint_comm, disjoint_union_left] at C; exact (J (disjoint_symm C.right))
          , show ¬ x ∪ y ## z by
              intro C; rw [disjoint_comm, disjoint_union_right] at C; exact (J (disjoint_symm C.left))]
    · simp only [G, ↓reduceIte, ite_eq_right_iff, LeibnizO.mk.injEq, reduceCtorEq, imp_false]
      intro C; symm at C; rw [disjoint_union_left] at C
      exact (G (disjoint_symm C.left))
  · simp only [H, ↓reduceIte]
    by_cases G : x ## y
    · simp only [G, ↓reduceIte, right_eq_ite_iff, LeibnizO.mk.injEq, reduceCtorEq, imp_false]
      intro C; rw [disjoint_union_left] at C; exact H C.right
    · simp [G]

theorem comm {x y : GenSetDisjO S} : op x y ≡ op y x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op]
  by_cases H : x ## y
  · simp [H, union_comm, show y ## x by symm; assumption]
  · simp [H]; intro c; exact H (disjoint_symm c)

instance : CMRA (GenSetDisjO S) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne {_ _ _ cx} _ H := ⟨cx, H, rfl⟩
  validN_ne H G := H ▸ G
  valid_iff_validN := ⟨(fun _ => ·), (· 0)⟩
  validN_succ := id
  validN_op_left {_ x y} := by rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op, validN, valid]
  assoc := assoc
  comm := comm
  pcore_op_left {cx x} := by
    rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [op, pcore, unit]
    rintro ⟨⟩; simp [disjoint_empty_left]
  pcore_idem {x cx} := by rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [pcore, unit]
  pcore_op_mono {_ x} := by
    rcases x with ⟨x | _⟩ <;> simp only [pcore, Option.some.injEq, leibniz] <;> rintro ⟨⟩ y
    <;> (exists unit; simp only [unit, op, disjoint_empty_left, ↓reduceIte, union_idem])
  extend {_ _ y₁ y₂} _ h := ⟨y₁, y₂, ⟨h, rfl, rfl⟩⟩

instance : CMRA.Discrete (GenSetDisjO S) where
  discrete_valid {_} := id

instance : UCMRA (GenSetDisjO S) where
  unit := unit
  unit_valid := by simp [unit, CMRA.Valid, valid]
  unit_left_id {x} := by rcases x with ⟨x | _⟩ <;> simp [op, unit, disjoint_empty_left, CMRA.op]
  pcore_unit := by simp [unit, CMRA.pcore, pcore]

theorem set_disj_included (X Y : S) :
   gen_set_valid X ≼ gen_set_valid Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  constructor
  · intro ⟨Z, HZ⟩
    rcases Z with ⟨Z | _⟩
    · by_cases H : X ## Z
      · simp [CMRA.op, op, H, ↓reduceIte] at HZ; rw [HZ]
        intro p Hp; rw [mem_union]; left; exact Hp
      · simp [CMRA.op, op, H] at HZ
    · simp [CMRA.op, op] at HZ
  · intro Hsub
    exists gen_set_valid (Y \ X)
    simp only [leibniz, LeibnizO.mk.injEq, ↓reduceIte, CMRA.op, op
      , show X ## (Y \ X) by intro p ⟨H1, H2⟩; rw [mem_diff] at H2; exact H2.right H1]
    rw [set_valid.injEq]
    ext p; rw [mem_union, mem_diff]
    constructor
    · intro G
      by_cases H : (p ∈ X)
      · left; exact H
      · right; exact ⟨G, H⟩
    · rintro (G|G)
      · exact Hsub _ G
      · exact G.left

theorem set_disj_union (X Y : S) (Hdisj : X ## Y) :
  (gen_set_valid X) • (gen_set_valid Y) ≡ gen_set_valid (X ∪ Y) := by
  simp only [CMRA.op, op, Hdisj, ↓reduceIte, gen_set_valid]; rfl

theorem set_disj_valid_op (X Y : S) :
    ✓ ((gen_set_valid X) • (gen_set_valid Y)) ↔ X ## Y := by
  simp only [CMRA.op, op, CMRA.Valid, valid]
  by_cases H : X ## Y <;> simp [H]

theorem set_disj_valid_inv_l (X : S) (Y : GenSetDisjO S) :
    ✓ ((gen_set_valid X) • Y) → ∃ Y', Y = gen_set_valid Y' ∧ X ## Y' := by
  simp only [CMRA.op, op, CMRA.Valid, valid]
  rcases Y with ⟨Y | _⟩ <;> simp <;> by_cases H : X ## Y <;> simp [H]

theorem set_disj_dealloc_local_update (X Y : S) :
    (gen_set_valid X, gen_set_valid Y) ~l~> (gen_set_valid (X \ Y), gen_set_valid ∅) := by
  apply LocalUpdate.total_valid
  intro vx vy inc
  apply (local_update_unital_discrete _ _ _ _).mpr
  intro z HX heq
  constructor
  · simp [CMRA.Valid, valid]
  · rcases z with ⟨z|_⟩
    · simp only [CMRA.op, op, leibniz, disjoint_empty_left, ↓reduceIte, union_empty_left,
      LeibnizO.mk.injEq, set_valid.injEq] at heq ⊢
      by_cases Hdisj : Y ## z <;> simp only [Hdisj, ↓reduceIte] at heq
      · simp only [LeibnizO.mk.injEq, set_valid.injEq] at heq
        ext i; rw [heq, mem_diff, mem_union]
        specialize (Hdisj i)
        grind
      · cases heq
    · simp only [CMRA.op, op, leibniz] at heq
      cases heq

theorem set_disj_dealloc_empty_local_update (X Z : S)  :
    (gen_set_valid Z • gen_set_valid X, gen_set_valid Z) ~l~>
    (gen_set_valid X, gen_set_valid ∅) := by
  apply LocalUpdate.total_valid
  intro Hdisj _ _; rw [set_disj_valid_op] at Hdisj
  have Heq : X = (Z ∪ X) \ Z := by
    ext a; rw [mem_diff, mem_union]
    constructor
    · intro Ha; constructor
      · right; exact Ha
      · intro Hz; exact Hdisj a ⟨Hz, Ha⟩
    · intro ⟨Ha, Ha'⟩
      rcases Ha with Ha | Ha
      · exact (Ha' Ha).elim
      · exact Ha
  rw [set_disj_union Z X Hdisj]
  conv => rhs; rw [Heq]
  exact set_disj_dealloc_local_update (Z ∪ X) Z

theorem set_disj_dealloc_op_local_update (X Y Z : S) :
    (gen_set_valid Z • gen_set_valid X, gen_set_valid Z • gen_set_valid Y) ~l~>
    (gen_set_valid X, gen_set_valid Y) := by
  conv => rhs; rw [show gen_set_valid Y ≡ UCMRA.unit • gen_set_valid Y by apply CMRA.unit_left_id.symm]
  apply LocalUpdate.op_frame
  exact set_disj_dealloc_empty_local_update X Z

theorem set_disj_alloc_op_local_update (X Y Z : S) (Hdisj : Z ## X) :
    (gen_set_valid X, gen_set_valid Y) ~l~>
    (gen_set_valid Z • gen_set_valid X, gen_set_valid Z • gen_set_valid Y) := by
  apply LocalUpdate.op_discrete
  intro vx
  simp [CMRA.Valid, valid, CMRA.op, op, Hdisj]

theorem set_disj_alloc_local_update (X Y Z : S) (Hdisj : Z ## X) :
    (gen_set_valid X, gen_set_valid Y) ~l~>
    (gen_set_valid (Z ∪ X), gen_set_valid (Z ∪ Y)) := by
  apply LocalUpdate.total_valid
  intro vx vy inc
  have HdisjY : Z ## Y := by
    have Hsub : Y ⊆ X := set_disj_included Y X |>.mp inc
    intro a ⟨Hz, Hy⟩
    exact Hdisj a ⟨Hz, Hsub _ Hy⟩
  rw [←set_disj_union Z X Hdisj, ←set_disj_union Z Y HdisjY]
  exact set_disj_alloc_op_local_update X Y Z Hdisj

theorem set_disj_alloc_empty_local_update (X Z : S) (Hdisj : Z ## X) :
    (gen_set_valid X, gen_set_valid ∅) ~l~>
    (gen_set_valid (Z ∪ X), gen_set_valid Z) := by
  rw [show gen_set_valid Z ≡ gen_set_valid (Z ∪ ∅) by simp [union_empty_right]]
  exact set_disj_alloc_local_update X ∅ Z Hdisj

end dec_disj

end GenSetDisj

section Def

variable (S : Type _)

abbrev GenSetO := LeibnizO S

instance : OFE (GenSetO S) := inferInstance

end Def

namespace GenSet

variable {S : Type _} [LawfulSet S A]

abbrev gen_set_valid : S → GenSetO S := fun X => ⟨X⟩

def unit : GenSetO S := gen_set_valid ∅

def pcore (x : GenSetO S) : Option (GenSetO S) := some x

def valid (_x : GenSetO S) : Prop := True

def validN (_n : Nat) (x : GenSetO S) : Prop := valid x

theorem pcore_ne {x y : GenSetO S} : x ≡{n}≡ y → pcore x = some cx →
  ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := by
  intro H1 H2
  exists y
  simp only [pcore, Option.some.injEq, true_and] at H2 ⊢
  rw [←H2]
  exact H1

def op (x y : GenSetO S) : GenSetO S := gen_set_valid (x.car ∪ y.car)

instance op_ne {x : GenSetO S} : OFE.NonExpansive (op x) where
  ne _ _ _ H := by simp only [op]; rw [H]

instance : CMRA (GenSetO S) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := pcore_ne
  validN_ne := by intro _ _; simp [validN, valid]
  valid_iff_validN := by simp [validN, valid]
  validN_succ := by intro _; simp [validN, valid]
  validN_op_left := by intro _; simp [validN, valid]
  assoc := by simp [op, union_assoc]
  comm := by simp [op, union_comm]
  pcore_op_left {_ x} := by
    simp only [pcore, Option.some.injEq, op, leibniz]; rintro ⟨⟩; simp [union_idem]
  pcore_idem := by simp [pcore]
  pcore_op_mono heq y := by simp only [pcore, Option.some.injEq] at heq; cases heq; exists y
  extend {_ _ y₁ y₂} _ h := ⟨y₁, y₂, ⟨h, rfl, rfl⟩⟩

instance : UCMRA (GenSetO S) where
  unit := unit
  unit_valid := by simp [CMRA.Valid, valid]
  unit_left_id := by simp [CMRA.op, op, unit, union_empty_left]
  pcore_unit := by simp [CMRA.pcore, pcore, unit]

theorem set_op (X Y : GenSetO S) : X • Y ≡ gen_set_valid (X.car ∪ Y.car) := by
  simp [CMRA.op, op]

theorem set_core (X : GenSetO S) : CMRA.core X ≡ X := by
  unfold CMRA.core
  change (pcore X).getD X ≡ X
  simp [pcore]

theorem set_included (X Y : S) : gen_set_valid X ≼ gen_set_valid Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  constructor
  · intro ⟨Z, HZ⟩
    simp only [CMRA.op, op, leibniz, LeibnizO.mk.injEq] at HZ
    rw [HZ]
    intro p Hp; rw [mem_union]; left; exact Hp
  · intro Hsub
    exists gen_set_valid (Y \ X)
    simp only [CMRA.op, op, leibniz, LeibnizO.mk.injEq]
    ext p; rw [mem_union, mem_diff]
    constructor
    · intro G
      by_cases H : (p ∈ X)
      · left; exact H
      · right; exact ⟨G, H⟩
    · rintro (G|G)
      · apply Hsub _ G
      · apply G.left

end GenSet

end OFE
