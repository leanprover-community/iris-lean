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

abbrev gen_set_valid : S → GenSetDisjO S := fun X => .mk (.set_valid X)

variable {S : Type _} [LawfulSet S A]

def unit : GenSetDisjO S := gen_set_valid ∅

def pcore : GenSetDisjO S → Option (GenSetDisjO S) := fun _ => some unit

def valid (x : GenSetDisjO S) : Prop :=
  match x.car with
  | .set_valid _ => True
  | _ => False

theorem unit_valid : valid (unit (S := S)) := by simp [unit, valid]

def validN : Nat → GenSetDisjO S → Prop := fun _ x => valid x

theorem pcore_ne {x y : GenSetDisjO S} : x ≡{n}≡ y → pcore x = some cx →
  ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := by
  intro H1 H2
  exists cx

theorem validN_ne : x ≡{n}≡ y → validN n x → validN n y := by
  intro H G; rw [<-H]; assumption

theorem valid_iff_validN : valid x ↔ ∀ n, validN n x := by
  apply Iff.intro
  · intro H n; apply H
  · intro H; apply H 0

theorem validN_succ : validN n.succ x → validN n x := by
  intro H; apply H

theorem pcore_idem {x : GenSetDisjO S} : pcore x = some cx → pcore cx ≡ some cx := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [pcore, unit]

theorem pcore_unit : pcore (unit : GenSetDisjO S) ≡ some unit := by
  simp [pcore, unit]

variable [∀ X₁ X₂ : S, Decidable (X₁ ## X₂)]

def op (x y : GenSetDisjO S) : GenSetDisjO S :=
  match x.car, y.car with
  | .set_valid x, .set_valid y => if (x ## y) then .mk (.set_valid (x ∪ y)) else .mk .set_invalid
  | _, _ => .mk .set_invalid

theorem validN_op_left {x y : GenSetDisjO S} : validN n (op x y) → validN n x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op, validN, valid]

instance op_ne {x : GenSetDisjO S} : OFE.NonExpansive (op x) where
  ne n y z H := by rw [H]

theorem assoc {x y z : GenSetDisjO S} : op x (op y z) ≡ op (op x y) z := by
  rcases x, y, z with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩, ⟨⟨z⟩ | _⟩⟩ <;> simp [op]
  if H : y ## z
  then
    simp [H]
    if G : x ## y
    then
      simp [G]
      if J : x ## z
      then
        have K1 : x ## y ∪ z := by
          symm
          rw [disjoint_union_left]; apply And.intro <;> (symm; assumption)
        have K2 : x ∪ y ## z := by
          rw [disjoint_union_left]; apply And.intro <;> assumption
        simp [K1, K2]
        rw [union_assoc]
      else
        have K1 : ¬ x ## y ∪ z := by
          intro C
          symm at C; rw [disjoint_union_left] at C
          apply J; symm; exact C.right
        have K2 : ¬ x ∪ y ## z := by
          rw [disjoint_union_left, not_and]
          intro C
          exfalso; apply J C
        simp [K1, K2]
    else
      simp [G]
      intro C; symm at C; rw [disjoint_union_left] at C
      apply (G (disjoint_symm C.left))
  else
    simp [H]
    if G : x ## y
    then
      simp [G]
      intro C; apply H
      rw [disjoint_union_left] at C
      apply C.right
    else
      simp [G]

theorem comm {x y : GenSetDisjO S} : op x y ≡ op y x := by
  rcases x, y with ⟨⟨⟨x⟩ | _⟩, ⟨⟨y⟩ | _⟩⟩ <;> simp [op]
  if H : x ## y
  then
    have H' : y ## x := by symm; assumption
    simp [H, H', union_comm]
  else
    simp [H]
    intro c; apply H (disjoint_symm c)

theorem pcore_op_left {x : GenSetDisjO S} : pcore x = some cx → op cx x ≡ x := by
  rcases x with ⟨x | _⟩ <;> rcases cx with ⟨cx | _⟩ <;> simp [op, pcore, unit]
  rintro ⟨⟩; simp [disjoint_empty_left]

theorem pcore_op_mono {x : GenSetDisjO S} : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) ≡ some (op cx cy) := by
  rcases x with ⟨x | _⟩ <;> simp only [pcore, Option.some.injEq, leibniz] <;> rintro ⟨⟩ y
  <;> (exists unit; simp only [unit, op, disjoint_empty_left, ↓reduceIte, union_idem])

def extend {x y₁ y₂ : GenSetDisjO S} (H : x ≡{n}≡ op y₁ y₂) :
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  exists y₁, y₂

theorem unit_left_id {x : GenSetDisjO S} : op unit x ≡ x := by
  rcases x with ⟨x | _⟩ <;> simp [op, unit, disjoint_empty_left]

instance : CMRA (GenSetDisjO S) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := pcore_ne
  validN_ne := validN_ne
  valid_iff_validN := valid_iff_validN
  validN_succ := validN_succ
  validN_op_left := validN_op_left
  assoc := assoc
  comm := comm
  pcore_op_left := pcore_op_left
  pcore_idem := pcore_idem
  pcore_op_mono := pcore_op_mono
  extend _ := extend

instance : CMRA.Discrete (GenSetDisjO S) where
  discrete_valid := by intro x Hx; apply Hx

instance : UCMRA (GenSetDisjO S) where
  unit := unit
  unit_valid := unit_valid
  unit_left_id := unit_left_id
  pcore_unit := pcore_unit

theorem set_disj_included (X Y : S) :
   gen_set_valid X ≼ gen_set_valid Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  apply Iff.intro
  · intro ⟨Z, HZ⟩
    rcases Z with ⟨Z | _⟩
    · if H : X ## Z
      then
        simp [CMRA.op, op, H] at HZ; rw [HZ]
        intro p Hp; rw [mem_union]; left; exact Hp
      else
        simp [CMRA.op, op, H] at HZ
    · simp [CMRA.op, op] at HZ
  · intro Hsub
    exists gen_set_valid (Y \ X)
    have H : X ## (Y \ X) := by
      intro p ⟨H1, H2⟩
      rw [mem_diff] at H2
      apply H2.right H1
    simp [CMRA.op, op, H]
    ext p; rw [mem_union, mem_diff]
    apply Iff.intro
    · intro G
      by_cases H : (p ∈ X)
      · left; exact H
      · right; exact ⟨G, H⟩
    · rintro (G|G)
      · apply Hsub _ G
      · apply G.left

theorem set_disj_union (X Y : S) (Hdisj : X ## Y) :
  (gen_set_valid X) • (gen_set_valid Y) ≡ gen_set_valid (X ∪ Y) := by
  simp [CMRA.op, op]
  exact Hdisj

theorem set_disj_valid_op (X Y : S) :
    ✓ ((gen_set_valid X) • (gen_set_valid Y)) ↔ X ## Y := by
  simp [CMRA.op, op, CMRA.Valid, valid]
  by_cases H : X ## Y <;> simp [H]

theorem set_disj_valid_inv_l (X : S) (Y : GenSetDisjO S) :
    ✓ ((gen_set_valid X) • Y) → ∃ Y', Y = gen_set_valid Y' ∧ X ## Y' := by
  simp [CMRA.op, op, CMRA.Valid, valid]
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
    <;> simp [CMRA.op, op, disjoint_empty_left] at *
    <;> if Hdisj : (Y ## z)
        then simp [Hdisj] at heq; rw [heq]; ext i;
             rw [mem_diff, mem_union];
             specialize (Hdisj i);
             grind only
        else simp [Hdisj] at heq

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
      · exfalso; exact Ha' Ha
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

end GenSetDisj

section Def

variable (S : Type _)

abbrev GenSetO := LeibnizO S

instance : OFE (GenSetO S) := inferInstance

end Def

namespace GenSet

variable {S : Type _} [LawfulSet S A]

abbrev gen_set_valid : S → GenSetO S := fun X => .mk X

def unit : GenSetO S := gen_set_valid ∅

def pcore (x : GenSetO S) : Option (GenSetO S) := some x

def valid (_x : GenSetO S) : Prop := True

theorem unit_valid : valid (unit (S := S)) := by simp [valid]

def validN (_n : Nat) (x : GenSetO S) : Prop := valid x

theorem pcore_ne {x y : GenSetO S} : x ≡{n}≡ y → pcore x = some cx →
  ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := by
  intro H1 H2
  exists y
  simp only [pcore, Option.some.injEq, true_and] at H2 ⊢
  rw [<-H2]
  exact H1

theorem validN_ne {x y : GenSetO S} : x ≡{n}≡ y → validN n x → validN n y := by
  intro _ _; simp [validN, valid]

theorem valid_iff_validN {x : GenSetO S} : valid x ↔ ∀ n, validN n x := by
  simp [validN, valid]

theorem validN_succ {x : GenSetO S} : validN n.succ x → validN n x := by
  intro _; simp [validN, valid]

theorem pcore_idem {x : GenSetO S} : pcore x = some cx → pcore cx ≡ some cx := by
  simp [pcore]

theorem pcore_unit : pcore (unit : GenSetO S) ≡ some unit := by
  simp [pcore, unit]

def op (x y : GenSetO S) : GenSetO S := gen_set_valid (x.car ∪ y.car)

theorem validN_op_left {x y : GenSetO S} : validN n (op x y) → validN n x := by
  intro _; simp [validN, valid]

instance op_ne {x : GenSetO S} : OFE.NonExpansive (op x) where
  ne n y z H := by simp [op]; rw [H]

theorem assoc {x y z : GenSetO S} : op x (op y z) ≡ op (op x y) z := by
  simp [op, union_assoc]

theorem comm {x y : GenSetO S} : op x y ≡ op y x := by
  simp [op, union_comm]

theorem pcore_op_left {x : GenSetO S} : pcore x = some cx → op cx x ≡ x := by
  simp only [pcore, Option.some.injEq, op, leibniz]
  rintro ⟨⟩; simp [union_idem]

theorem pcore_op_mono {x : GenSetO S} : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) ≡ some (op cx cy) := by
  simp only [pcore, Option.some.injEq, leibniz]
  rintro ⟨⟩ y
  exists y

def extend {x y₁ y₂ : GenSetO S} (H : x ≡{n}≡ op y₁ y₂) :
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ := by
  exists y₁, y₂

theorem unit_left_id {x : GenSetO S} : op unit x ≡ x := by
  simp [op, unit, union_empty_left]

instance : CMRA (GenSetO S) where
  pcore := pcore
  op := op
  ValidN := validN
  Valid := valid
  op_ne := op_ne
  pcore_ne := pcore_ne
  validN_ne := validN_ne
  valid_iff_validN := valid_iff_validN
  validN_succ := validN_succ
  validN_op_left := validN_op_left
  assoc := assoc
  comm := comm
  pcore_op_left := pcore_op_left
  pcore_idem := pcore_idem
  pcore_op_mono := pcore_op_mono
  extend _ := extend

instance : UCMRA (GenSetO S) where
  unit := unit
  unit_valid := unit_valid
  unit_left_id := unit_left_id
  pcore_unit := pcore_unit

theorem set_op (X Y : GenSetO S) : X • Y ≡ gen_set_valid (X.car ∪ Y.car) := by
  simp [CMRA.op, op]

theorem set_core (X : GenSetO S) : CMRA.core X ≡ X := by
  unfold CMRA.core
  change (pcore X).getD X ≡ X
  simp [pcore]

theorem set_included (X Y : S) : gen_set_valid X ≼ gen_set_valid Y ↔ X ⊆ Y := by
  simp only [CMRA.Included]
  apply Iff.intro
  · intro ⟨Z, HZ⟩
    simp [CMRA.op, op] at HZ
    rw [HZ]
    intro p Hp; rw [mem_union]; left; exact Hp
  · intro Hsub
    exists gen_set_valid (Y \ X)
    simp [CMRA.op, op]
    ext p; rw [mem_union, mem_diff]
    apply Iff.intro
    · intro G
      by_cases H : (p ∈ X)
      · left; exact H
      · right; exact ⟨G, H⟩
    · rintro (G|G)
      · apply Hsub _ G
      · apply G.left

end GenSet

end OFE
