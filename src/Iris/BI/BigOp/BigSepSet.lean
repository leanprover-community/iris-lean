/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.BigOp.BigSepList
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase

/-! # Big Separating Conjunction over Sets

- Rocq Iris: `iris/bi/big_op.v`, Section `sep_set` -/

variable {PROP : Type _} [BI PROP]
variable {S : Type _} {A : Type _}
variable [DecidableEq A] [FiniteSet S A] [FiniteSetLaws S A]

namespace BigSepS

/-! ## Monotonicity and Congruence -/

omit [DecidableEq A] in
private theorem mono_list {Φ Ψ : A → PROP} {l : List A}
    (h : ∀ x, List.Mem x l → Φ x ⊢ Ψ x) :
    bigOpL sep emp (fun _ x => Φ x) l ⊢ bigOpL sep emp (fun _ x => Ψ x) l := by
  induction l with
  | nil => exact Entails.rfl
  | cons x xs ih =>
    simp only [BigOpL.cons]
    apply sep_mono
    · exact h x (List.Mem.head xs)
    · apply ih
      intro y hy
      exact h y (List.Mem.tail x hy)

/-- Corresponds to `big_sepS_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, FiniteSet.mem x X = true → Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x := by
  unfold bigSepS
  apply mono_list
  intro x hx
  have := (FiniteSetLaws.mem_toList X x).mp hx
  exact h x this

/-- Corresponds to `big_sepS_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : A → PROP} {X : S} {n : Nat}
    (h : ∀ x, FiniteSet.mem x X = true → Φ x ≡{n}≡ Ψ x) :
    ([∗set] x ∈ X, Φ x) ≡{n}≡ ([∗set] x ∈ X, Ψ x) := by
  unfold bigSepS
  apply BigOpL.congr_ne
  intro i x hget
  have hmem : List.Mem x (toList X) := List.mem_of_getElem? hget
  have := (FiniteSetLaws.mem_toList X x).mp hmem
  exact h x this

/-- Corresponds to `big_sepS_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, FiniteSet.mem x X = true → Φ x ⊣⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊣⊢ ([∗set] x ∈ X, Ψ x) := by
  unfold bigSepS
  apply equiv_iff.mp
  apply BigOpL.congr
  intro i x hget
  have hmem_list : List.Mem x (toList X) := List.mem_of_getElem? hget
  have hmem := (FiniteSetLaws.mem_toList X x).mp hmem_list
  exact equiv_iff.mpr (h x hmem)

/-- Corresponds to `big_sepS_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x :=
  mono (fun x _ => h x)

/-- Corresponds to `big_sepS_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Ψ x ⊢ Φ x) :
    ([∗set] x ∈ X, Ψ x) ⊢ [∗set] x ∈ X, Φ x :=
  mono' h

/-! ## Basic Structural Lemmas -/

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_elements` in Rocq Iris. -/
theorem elements {Φ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊣⊢ [∗list] x ∈ toList X, Φ x := by
  unfold bigSepS bigSepL
  exact .rfl

/-- Corresponds to `big_sepS_empty` in Rocq Iris. -/
@[simp]
theorem empty {Φ : A → PROP} :
    ([∗set] x ∈ (∅ : S), Φ x) ⊣⊢ emp := by
  unfold bigSepS
  rw [FiniteSetLaws.toList_empty]
  simp only [BigOpL.nil]
  exact .rfl

/-- Corresponds to `big_sepS_empty'` in Rocq Iris. -/
theorem empty' {P : PROP} [Affine P] {Φ : A → PROP} :
    P ⊢ [∗set] x ∈ (∅ : S), Φ x :=
  Affine.affine.trans empty.2

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_emp` in Rocq Iris. -/
theorem emp' {X : S} :
    ([∗set] _x ∈ X, emp) ⊣⊢ (emp : PROP) := by
  unfold bigSepS
  have := @BigOpL.unit_const PROP _ _ sep emp _ (toList X)
  exact equiv_iff.mp this

/-- Corresponds to `big_sepS_singleton` in Rocq Iris. -/
theorem singleton {Φ : A → PROP} {x : A} :
    ([∗set] y ∈ (FiniteSet.singleton x : S), Φ y) ⊣⊢ Φ x := by
  unfold bigSepS
  have hperm := FiniteSetLaws.toList_singleton (S := S) (x : A)
  have hp := equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
  simp only [BigOpL.cons, BigOpL.nil] at hp
  exact hp.trans sep_emp

/-- Corresponds to `big_sepS_union` in Rocq Iris. -/
theorem union {Φ : A → PROP} {X Y : S}
    (h : FiniteSet.Disjoint X Y) :
    ([∗set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) := by
  unfold bigSepS
  obtain ⟨l', hperm, hperm'⟩ := FiniteSetLaws.toList_union (S := S) X Y h
  have hp1 := equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
  have happ := equiv_iff.mp (@BigOpL.append PROP _ _ sep emp _ (fun _ x => Φ x) (toList X) l')
  have hp2 : bigOpL sep emp (fun _ => Φ) (toList X) ∗ bigOpL sep emp (fun _ => Φ) l' ⊣⊢
             bigOpL sep emp (fun _ => Φ) (toList X) ∗ bigOpL sep emp (fun _ => Φ) (toList Y) :=
    sep_congr_r (equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm'.symm))
  exact hp1.trans (happ.trans hp2)

private theorem bigSepS_perm_of_mem_eq {Φ : A → PROP} {X Y : S}
    (hmem_eq : ∀ z, FiniteSet.mem z X = FiniteSet.mem z Y) :
    ([∗set] y ∈ X, Φ y) ⊣⊢ ([∗set] y ∈ Y, Φ y) := by
  have hsub1 : X ⊆ Y := fun z hz => by have := hmem_eq z; rwa [← this]
  have hsub2 : Y ⊆ X := fun z hz => by have := hmem_eq z; rwa [this]
  have ⟨l₁, hperm1⟩ := FiniteSetLaws.toList_subset Y X hsub1
  have ⟨l₂, hperm2⟩ := FiniteSetLaws.toList_subset X Y hsub2
  have hl1_nil : l₁ = [] := by
    have h1 := hperm1.length_eq
    have h2 := hperm2.length_eq
    simp only [List.length_append] at h1 h2
    have : l₁.length = 0 := by omega
    match l₁ with
    | [] => rfl
    | _ :: _ => simp at this
  rw [hl1_nil, List.append_nil] at hperm1
  unfold bigSepS
  exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm1)

/-- Corresponds to `big_sepS_delete` in Rocq Iris. -/
theorem delete {Φ : A → PROP} {X : S} {x : A}
    (h : FiniteSet.mem x X = true) :
    ([∗set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ FiniteSet.diff X (FiniteSet.singleton x), Φ y := by
  unfold bigSepS
  obtain ⟨l', hperm, hperm'⟩ := FiniteSetLaws.toList_sdiff (S := S) X x h
  have hp1 := equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
  simp only [BigOpL.cons] at hp1
  have hp2 : Φ x ∗ bigOpL sep emp (fun _ => Φ) l' ⊣⊢
             Φ x ∗ bigOpL sep emp (fun _ => Φ) (toList (diff X (FiniteSet.singleton x))) :=
    sep_congr_r (equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm'.symm))
  exact hp1.trans hp2

/-- Corresponds to `big_sepS_insert` in Rocq Iris. -/
theorem insert {Φ : A → PROP} {X : S} {x : A}
    (h : FiniteSet.mem x X = false) :
    ([∗set] y ∈ FiniteSet.singleton x ∪ X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X, Φ y := by
  have hdisj : FiniteSet.Disjoint (FiniteSet.singleton x : S) X := by
    intro y ⟨hmem1, hmem2⟩
    by_cases hyx : y = x
    · subst hyx; simp_all
    · rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_ne _ _ _ hyx] at hmem1
      rw [FiniteSetLaws.mem_empty] at hmem1
      exact Bool.noConfusion hmem1
  have hunion := union (Φ := Φ) hdisj
  exact hunion.trans (sep_congr_l singleton)

/-- Corresponds to `big_sepS_union_2` in Rocq Iris. -/
theorem union_2 {Φ : A → PROP} {X Y : S}
    [h : ∀ x, TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ Y, Φ y) -∗ ([∗set] y ∈ X ∪ Y, Φ y) := by
  have h_core : ∀ X : S, ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) ⊢ ([∗set] y ∈ X ∪ Y, Φ y) := by
    intro X
    refine FiniteSet.set_ind (P := fun X => ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) ⊢ ([∗set] y ∈ X ∪ Y, Φ y)) ?_ ?_ X
    · refine (sep_mono_l empty.1).trans ?_
      refine emp_sep.1.trans ?_
      have hmem_eq : ∀ z, FiniteSet.mem z (∅ ∪ Y) = FiniteSet.mem z Y := fun z => by
        have hunion := FiniteSetLaws.mem_union (∅ : S) Y z
        have hempty := FiniteSetLaws.mem_empty (S := S) (A := A) z
        cases hz : FiniteSet.mem z (∅ ∪ Y) <;> cases hy : FiniteSet.mem z Y
        · rfl
        · have := hunion.mpr (Or.inr hy); rw [hz] at this; exact Bool.noConfusion this
        · have := hunion.mp hz
          cases this with
          | inl hl => rw [hempty] at hl; exact Bool.noConfusion hl
          | inr hr => rw [hy] at hr; exact Bool.noConfusion hr
        · rfl
      exact (bigSepS_perm_of_mem_eq hmem_eq).2
    · intro x X' hnotin IH
      have hdisj : FiniteSet.Disjoint (FiniteSet.singleton x : S) X' := by
        intro y ⟨hmem1, hmem2⟩
        by_cases hyx : y = x
        · subst hyx; simp_all
        · rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_ne _ _ _ hyx] at hmem1
          rw [FiniteSetLaws.mem_empty] at hmem1
          exact Bool.noConfusion hmem1
      have hunion_x_X' := union (Φ := Φ) hdisj
      have hins : ([∗set] y ∈ FiniteSet.singleton x ∪ X', Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X', Φ y :=
        hunion_x_X'.trans (sep_congr_l singleton)
      refine (sep_mono_l hins.1).trans ?_
      have h_assoc := @sep_assoc PROP _ (Φ x) ([∗set] y ∈ X', Φ y) ([∗set] y ∈ Y, Φ y)
      refine h_assoc.1.trans ?_
      refine (sep_mono_r IH).trans ?_
      by_cases hx_in_Y : FiniteSet.mem x Y = true
      · have hx_in_union : FiniteSet.mem x (X' ∪ Y) = true :=
          (FiniteSetLaws.mem_union X' Y x).mpr (Or.inr hx_in_Y)
        have hmem_eq : ∀ w, FiniteSet.mem w (X' ∪ Y) =
                           FiniteSet.mem w ((FiniteSet.singleton x ∪ X') ∪ Y) := fun w => by
          by_cases hwx : w = x
          · rw [hwx]
            have lhs : FiniteSet.mem x (X' ∪ Y) = true :=
              (FiniteSetLaws.mem_union X' Y x).mpr (Or.inr hx_in_Y)
            have rhs_inner : FiniteSet.mem x (FiniteSet.singleton x ∪ X') = true := by
              rw [FiniteSetLaws.mem_union, FiniteSet.singleton, FiniteSetLaws.mem_insert_eq _ _ _ rfl]
              simp
            have rhs : FiniteSet.mem x ((FiniteSet.singleton x ∪ X') ∪ Y) = true :=
              (FiniteSetLaws.mem_union (FiniteSet.singleton x ∪ X') Y x).mpr (Or.inl rhs_inner)
            rw [lhs, rhs]
          · rw [Bool.eq_iff_iff]
            rw [FiniteSetLaws.mem_union X' Y w, FiniteSetLaws.mem_union (FiniteSet.singleton x ∪ X') Y w]
            rw [FiniteSetLaws.mem_union (FiniteSet.singleton x) X' w]
            rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_ne _ _ _ hwx, FiniteSetLaws.mem_empty]
            simp
        refine (sep_mono_r (delete hx_in_union).1).trans ?_
        refine sep_assoc.2.trans ?_
        refine (sep_mono_l sep_elim_l).trans ?_
        refine (delete hx_in_union).2.trans ?_
        exact (@bigSepS_perm_of_mem_eq PROP _ S A _ _ _ Φ _ _ hmem_eq).1
      · have hx_notin_union : FiniteSet.mem x (X' ∪ Y) = false := by
          have : ¬(FiniteSet.mem x (X' ∪ Y) = true) := by
            intro h
            have := (FiniteSetLaws.mem_union X' Y x).mp h
            cases this with
            | inl h' => simp [h'] at hnotin
            | inr h' => simp [h'] at hx_in_Y
          cases h : FiniteSet.mem x (X' ∪ Y)
          · rfl
          · contradiction
        have hmem_eq : ∀ w, FiniteSet.mem w (FiniteSet.singleton x ∪ (X' ∪ Y)) =
                           FiniteSet.mem w ((FiniteSet.singleton x ∪ X') ∪ Y) := fun w => by
          by_cases hwx : w = x
          · rw [hwx]
            have lhs_inner : FiniteSet.mem x (FiniteSet.singleton (S := S) x) = true := by
              rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_eq (S := S) _ _ _ rfl]
            have lhs : FiniteSet.mem x (FiniteSet.singleton x ∪ (X' ∪ Y)) = true :=
              (FiniteSetLaws.mem_union (S := S) (FiniteSet.singleton x) (X' ∪ Y) x).mpr (Or.inl lhs_inner)
            have rhs_inner : FiniteSet.mem x (FiniteSet.singleton x ∪ X') = true :=
              (FiniteSetLaws.mem_union (FiniteSet.singleton x) X' x).mpr (Or.inl lhs_inner)
            have rhs : FiniteSet.mem x ((FiniteSet.singleton x ∪ X') ∪ Y) = true :=
              (FiniteSetLaws.mem_union (FiniteSet.singleton x ∪ X') Y x).mpr (Or.inl rhs_inner)
            rw [lhs, rhs]
          · rw [Bool.eq_iff_iff]
            rw [FiniteSetLaws.mem_union (FiniteSet.singleton x) (X' ∪ Y) w]
            rw [FiniteSetLaws.mem_union (FiniteSet.singleton x ∪ X') Y w]
            rw [FiniteSetLaws.mem_union (FiniteSet.singleton x) X' w]
            rw [FiniteSetLaws.mem_union X' Y w]
            rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_ne _ _ _ hwx, FiniteSetLaws.mem_empty]
            simp
        refine (insert hx_notin_union).2.trans ?_
        exact (@bigSepS_perm_of_mem_eq PROP _ S A _ _ _ Φ _ _ hmem_eq).1
  have h1 : ([∗set] y ∈ X, Φ y) ⊢ ([∗set] y ∈ Y, Φ y) -∗ ([∗set] y ∈ X ∪ Y, Φ y) :=
    wand_intro' ((sep_comm (PROP := PROP)).1.trans (h_core X))
  exact entails_wand h1

/-- Corresponds to `big_sepS_insert_2` in Rocq Iris. -/
theorem insert_2 {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    Φ x ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ FiniteSet.singleton x ∪ X, Φ y) := by
  apply wand_intro
  by_cases hx : FiniteSet.mem x X = true
  · have hdel := (@delete PROP _ S A _ _ _ Φ X x hx).1
    refine (sep_mono_r hdel).trans ?_
    refine (sep_assoc (PROP := PROP)).2.trans ?_
    refine (sep_mono_l sep_elim_l).trans ?_
    have hunion_sub_X : (FiniteSet.singleton x ∪ X) ⊆ X := fun y hy => by
      rw [FiniteSetLaws.mem_union] at hy
      cases hy with
      | inl h =>
        by_cases hyx : y = x
        · subst hyx; exact hx
        · rw [FiniteSet.singleton, FiniteSetLaws.mem_insert_ne _ _ _ hyx, FiniteSetLaws.mem_empty] at h
          exact Bool.noConfusion h
      | inr h => exact h
    have hX_sub_union : X ⊆ (FiniteSet.singleton x ∪ X) := fun y hy => by
      rw [FiniteSetLaws.mem_union]
      right; exact hy
    have ⟨l₁, hperm1⟩ := FiniteSetLaws.toList_subset X (FiniteSet.singleton x ∪ X) hunion_sub_X
    have ⟨l₂, hperm2⟩ := FiniteSetLaws.toList_subset (FiniteSet.singleton x ∪ X) X hX_sub_union
    have hl1_nil : l₁ = [] := by
      have h := hperm1.length_eq
      have h2 := hperm2.length_eq
      simp only [List.length_append] at h h2
      have : l₁.length = 0 := by omega
      match l₁ with
      | [] => rfl
      | _ :: _ => simp at this
    rw [hl1_nil, List.append_nil] at hperm1
    have heq : ([∗set] y ∈ FiniteSet.singleton x ∪ X, Φ y) ⊣⊢ ([∗set] y ∈ X, Φ y) := by
      unfold bigSepS
      exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm1)
    exact (@delete PROP _ S A _ _ _ Φ X x hx).2.trans heq.2
  · have hx' : FiniteSet.mem x X = false := eq_false_of_ne_true hx
    have hinsert := (@insert PROP _ S A _ _ _ Φ X x hx').2
    exact hinsert

/-- Corresponds to `big_sepS_insert_2'` in Rocq Iris. -/
theorem insert_2' {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    ⊢ Φ x -∗ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ X ∪ FiniteSet.singleton x, Φ y) := by
  have heq : ([∗set] y ∈ X ∪ FiniteSet.singleton x, Φ y) ⊣⊢
             ([∗set] y ∈ FiniteSet.singleton x ∪ X, Φ y) := by
    unfold bigSepS
    have hperm := FiniteSetLaws.toList_union_comm (S := S) (A := A) X (FiniteSet.singleton x)
    exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
  have h1 : ⊢ Φ x -∗ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ FiniteSet.singleton x ∪ X, Φ y) :=
    entails_wand insert_2
  exact h1.trans (wand_mono_r (wand_mono_r heq.2))

/-! ## Function Insertion -/

/-- Function update: returns `b` if `k = i`, otherwise `f k`. -/
def fnInsert {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) : B :=
  if k = i then b else f k

theorem fnInsert_same {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) :
    fnInsert f i b i = b := by simp [fnInsert]

theorem fnInsert_ne {K B : Type _} [DecidableEq K] (f : K → B) (i : K) (b : B) (k : K) (h : k ≠ i) :
    fnInsert f i b k = f k := by simp [fnInsert, h]

/-- Corresponds to `big_sepS_fn_insert` in Rocq Iris. -/
theorem fn_insert {B : Type _} {Ψ : A → B → PROP} {f : A → B} {X : S} {x : A} {b : B}
    (h : FiniteSet.mem x X = false) :
    ([∗set] y ∈ FiniteSet.singleton x ∪ X, Ψ y (fnInsert f x b y)) ⊣⊢
      Ψ x b ∗ [∗set] y ∈ X, Ψ y (f y) := by
  have hins := insert (Φ := fun y => Ψ y (fnInsert f x b y)) h
  have hhead : Ψ x (fnInsert f x b x) ⊣⊢ Ψ x b := by
    simp only [fnInsert_same]
    exact .rfl
  have htail : ([∗set] y ∈ X, Ψ y (fnInsert f x b y)) ⊣⊢
      [∗set] y ∈ X, Ψ y (f y) := by
    apply proper
    intro y hy
    have hne : y ≠ x := by
      intro heq
      rw [←heq] at h
      rw [hy] at h
      cases h
    simp only [fnInsert_ne f x b y hne]
    exact .rfl
  exact hins.trans ⟨(sep_mono hhead.1 htail.1), (sep_mono hhead.2 htail.2)⟩

/-- Corresponds to `big_sepS_fn_insert'` in Rocq Iris. -/
theorem fn_insert' {Φ : A → PROP} {X : S} {x : A} {P : PROP}
    (h : FiniteSet.mem x X = false) :
    ([∗set] y ∈ FiniteSet.singleton x ∪ X, fnInsert Φ x P y) ⊣⊢
      P ∗ [∗set] y ∈ X, Φ y :=
  fn_insert (Ψ := fun _ P => P) (f := Φ) (b := P) h

/-- Corresponds to `big_sepS_delete_2` in Rocq Iris. -/
theorem delete_2 {Φ : A → PROP} {X : S} {x : A}
    [hAff : Affine (Φ x)] :
    Φ x ⊢ ([∗set] y ∈ FiniteSet.diff X (FiniteSet.singleton x), Φ y) -∗ [∗set] y ∈ X, Φ y := by
  apply wand_intro
  by_cases hx : FiniteSet.mem x X = true
  · exact (delete (Φ := Φ) hx).2
  · have hdiff_sub : ∀ y, FiniteSet.mem y (FiniteSet.diff X (FiniteSet.singleton x)) = true →
        FiniteSet.mem y X = true := fun y hy =>
      ((FiniteSetLaws.mem_diff_singleton X x y).mp hy).1
    have hX_sub : ∀ y, FiniteSet.mem y X = true →
        FiniteSet.mem y (FiniteSet.diff X (FiniteSet.singleton x)) = true := by
      intro y hy
      rw [FiniteSetLaws.mem_diff_singleton]
      constructor
      · exact hy
      · intro heq
        subst heq
        exact hx hy
    refine (sep_mono_l hAff.affine).trans emp_sep.1 |>.trans ?_
    have hX_sub_diff : X ⊆ FiniteSet.diff X (FiniteSet.singleton x) := fun y hy => hX_sub y hy
    have hdiff_sub_X : FiniteSet.diff X (FiniteSet.singleton x) ⊆ X := fun y hy => hdiff_sub y hy
    have ⟨l₁, hperm1⟩ := FiniteSetLaws.toList_subset (FiniteSet.diff X (FiniteSet.singleton x)) X hX_sub_diff
    have ⟨l₂, hperm2⟩ := FiniteSetLaws.toList_subset X (FiniteSet.diff X (FiniteSet.singleton x)) hdiff_sub_X
    have hlen_eq : (toList (FiniteSet.diff X (FiniteSet.singleton x))).length =
        (toList X).length := by
      have h1 := hperm1.length_eq
      have h2 := hperm2.length_eq
      simp only [List.length_append] at h1 h2
      omega
    have hl1_nil : l₁ = [] := by
      have h := hperm1.length_eq
      simp only [List.length_append] at h
      have : l₁.length = 0 := by omega
      match l₁ with
      | [] => rfl
      | _ :: _ => simp at this
    rw [hl1_nil, List.append_nil] at hperm1
    unfold bigSepS
    exact (equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm1.symm)).1

/-! ## Lookup and Access -/

/-- Corresponds to `big_sepS_elem_of` in Rocq Iris. -/
theorem elem_of {Φ : A → PROP} {X : S} {x : A}
    (hmem : x ∈ X) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] →
    ([∗set] y ∈ X, Φ y) ⊢ Φ x
  | TCOr.l => by
    have hdel := delete (Φ := Φ) (S := S) hmem
    refine hdel.1.trans ?_
    exact sep_elim_l
  | TCOr.r => by
    have hdel := delete (Φ := Φ) (S := S) hmem
    refine hdel.1.trans ?_
    exact sep_elim_l

/-- Corresponds to `big_sepS_elem_of_acc` in Rocq Iris. -/
theorem elem_of_acc {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗set] y ∈ X, Φ y)) := by
  have hdel := delete (Φ := Φ) (S := S) h
  refine hdel.1.trans ?_
  apply sep_mono_r
  exact wand_intro' hdel.2

/-! ## Typeclass Instances -/

/-- Corresponds to `big_sepS_empty_persistent` in Rocq Iris. -/
instance empty_persistent {Φ : A → PROP} :
    Persistent ([∗set] x ∈ (∅ : S), Φ x) where
  persistent := by
    unfold bigSepS
    rw [FiniteSetLaws.toList_empty]
    simp only [BigOpL.nil]
    exact persistently_emp_intro (PROP := PROP) (P := emp)

omit [DecidableEq A] in
private theorem persistent_list {Φ : A → PROP} {l : List A}
    (h : ∀ x, List.Mem x l → Persistent (Φ x)) :
    bigOpL sep emp (fun _ => Φ) l ⊢ <pers> bigOpL sep emp (fun _ => Φ) l := by
  induction l with
  | nil => exact persistently_emp_intro
  | cons x xs ih =>
    simp only [BigOpL.cons]
    have h1 : Φ x ⊢ <pers> Φ x := (h x (List.Mem.head xs)).persistent
    have h2 : bigOpL sep emp (fun _ y => Φ y) xs ⊢ <pers> bigOpL sep emp (fun _ y => Φ y) xs :=
      ih (fun y hy => h y (List.Mem.tail x hy))
    exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepS_persistent` in Rocq Iris. -/
theorem persistent_cond {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Persistent (Φ x)) :
    Persistent ([∗set] x ∈ X, Φ x) where
  persistent := by
    unfold bigSepS
    apply persistent_list
    intro x hmem_list
    have hmem := (FiniteSetLaws.mem_toList X x).mp hmem_list
    exact h x hmem

/-- Corresponds to `big_sepS_persistent'` in Rocq Iris. -/
instance persistent {Φ : A → PROP} {X : S}
    [h : ∀ x, Persistent (Φ x)] :
    Persistent ([∗set] x ∈ X, Φ x) :=
  persistent_cond (Φ := Φ) (X := X) (fun _ _ => h _)

/-- Corresponds to `big_sepS_empty_affine` in Rocq Iris. -/
instance empty_affine {Φ : A → PROP} :
    Affine ([∗set] x ∈ (∅ : S), Φ x) where
  affine := by
    have h := empty (Φ := Φ) (S := S)
    exact h.1

omit [DecidableEq A] in
private theorem affine_list {Φ : A → PROP} {l : List A}
    (h : ∀ x, List.Mem x l → Affine (Φ x)) :
    bigOpL sep emp (fun _ => Φ) l ⊢ emp := by
  induction l with
  | nil => exact Entails.rfl
  | cons x xs ih =>
    simp only [BigOpL.cons]
    have h1 : Φ x ⊢ emp := (h x (List.Mem.head xs)).affine
    have h2 : bigOpL sep emp (fun _ y => Φ y) xs ⊢ emp :=
      ih (fun y hy => h y (List.Mem.tail x hy))
    exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepS_affine` in Rocq Iris. -/
theorem affine_cond {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Affine (Φ x)) :
    Affine ([∗set] x ∈ X, Φ x) where
  affine := by
    unfold bigSepS
    apply affine_list
    intro x hmem_list
    have hmem := (FiniteSetLaws.mem_toList X x).mp hmem_list
    exact h x hmem

/-- Corresponds to `big_sepS_affine'` in Rocq Iris. -/
instance affine {Φ : A → PROP} {X : S}
    [h : ∀ x, Affine (Φ x)] :
    Affine ([∗set] x ∈ X, Φ x) :=
  affine_cond (fun _ _ => h _)

/-! ## List/Set Conversion -/

/-- Corresponds to `big_sepS_list_to_set` in Rocq Iris. -/
theorem list_to_set {Φ : A → PROP} {l : List A}
    (h : l.Nodup) :
    ([∗set] x ∈ (ofList l : S), Φ x) ⊣⊢ [∗list] x ∈ l, Φ x := by
  unfold bigSepS bigSepL
  have hperm := FiniteSetLaws.toList_ofList l (ofList l : S) h rfl
  exact equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)

/-! ## Filter -/

/-- Corresponds to `big_sepS_filter'` in Rocq Iris. -/
theorem filter' (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) X, Φ y) ⊣⊢
    ([∗set] y ∈ X, if φ y then Φ y else emp) := by
  unfold bigSepS
  have hperm := FiniteSetLaws.toList_filter (S := S) X (fun x => decide (φ x))
  have h1 := equiv_iff.mp (@BigOpL.perm PROP _ _ sep emp _ Φ _ _ hperm)
  refine h1.trans ?_
  have h2 : ∀ l : List A,
      bigOpL sep emp (fun _ => Φ) (l.filter (fun x => decide (φ x))) ⊣⊢
      bigOpL sep emp (fun _ x => if φ x then Φ x else emp) l := by
    intro l
    induction l with
    | nil =>
      simp only [List.filter, BigOpL.nil]
      exact .rfl
    | cons y ys ih =>
      simp only [BigOpL.cons]
      by_cases hy : φ y
      · have hdec : decide (φ y) = true := by simp [hy]
        have hfilt : List.filter (fun x => decide (φ x)) (y :: ys) =
            y :: List.filter (fun x => decide (φ x)) ys := by
          simp [List.filter, hdec]
        rw [hfilt]
        simp only [BigOpL.cons, hy, ↓reduceIte]
        exact sep_congr_r ih
      · have hdec : decide (φ y) = false := by simp [hy]
        have hfilt : List.filter (fun x => decide (φ x)) (y :: ys) =
            List.filter (fun x => decide (φ x)) ys := by
          simp [List.filter, hdec]
        rw [hfilt]
        simp only [hy, ↓reduceIte]
        exact ih.trans (emp_sep (PROP := PROP)).symm
  exact h2 (toList X)

/-- Corresponds to `big_sepS_filter` in Rocq Iris. -/
theorem filter [BIAffine PROP] (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) X, Φ y) ⊣⊢
    ([∗set] y ∈ X, ⌜φ y⌝ → Φ y) := by
  refine (filter' φ).trans (proper fun y _ => ?_)
  by_cases hy : φ y
  · simp only [hy, ↓reduceIte]
    exact true_imp (PROP := PROP).symm
  · simp only [hy, ↓reduceIte]
    constructor
    · apply imp_intro'
      apply pure_elim_l (R := Φ y)
      intro hf
      exact hf.elim
    · exact Affine.affine (self := BIAffine.affine _)

/-- Corresponds to `big_sepS_filter_acc'` in Rocq Iris. -/
theorem filter_acc' (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X Y : S}
    (h : ∀ y, FiniteSet.mem y Y = true → φ y → FiniteSet.mem y X = true) :
    ([∗set] y ∈ X, Φ y) ⊢
      ([∗set] y ∈ Y, if φ y then Φ y else emp) ∗
      (([∗set] y ∈ Y, if φ y then Φ y else emp) -∗ [∗set] y ∈ X, Φ y) := by
  -- First, show that filter φ Y ⊆ X
  have hfilter_sub : FiniteSet.filter (fun x => decide (φ x)) Y ⊆ X := by
    intro z hz
    have ⟨hz_Y, hz_φ⟩ := FiniteSetLaws.mem_filter Y (fun x => decide (φ x)) z |>.mp hz
    have : φ z := of_decide_eq_true hz_φ
    exact h z hz_Y this
  -- Use union_diff to decompose X
  have ⟨hdisj, hmem_decomp⟩ := FiniteSetLaws.union_diff X (FiniteSet.filter (fun x => decide (φ x)) Y) hfilter_sub
  -- X = filterY ∪ (X \ filterY), and they are disjoint
  have hX_decomp : X = FiniteSet.filter (fun x => decide (φ x)) Y ∪
      FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y) := by
    apply @FiniteSetLaws.ext S A _ _
    intro z
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hz; rw [FiniteSetLaws.mem_union]; exact (hmem_decomp z).mp hz
    · intro hz; rw [FiniteSetLaws.mem_union] at hz; exact (hmem_decomp z).mpr hz
  -- Apply union: [∗set] X = [∗set] filterY ∗ [∗set] (X \ filterY)
  have hunion := @union PROP _ S A _ _ _ Φ (FiniteSet.filter (fun x => decide (φ x)) Y)
      (FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y)) hdisj
  have hX_split : ([∗set] y ∈ X, Φ y) ⊣⊢
      ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) Y, Φ y) ∗
      ([∗set] y ∈ FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) := by
    -- Convert equality to equivalence, then compose with hunion
    have heq : ([∗set] y ∈ X, Φ y) = ([∗set] y ∈ FiniteSet.filter (fun x => decide (φ x)) Y ∪
        FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) :=
      congrArg (fun s => bigSepS Φ s) hX_decomp
    exact BIBase.BiEntails.of_eq heq |>.trans hunion
  -- Apply filter': [∗set] filterY = [∗set] y ∈ Y, if φ y then Φ y else emp
  have hfilter := @filter' PROP _ S A _ _ _ φ _ Φ Y
  -- Combine: [∗set] X ⊣⊢ A ∗ Z where A = [∗set] Y with filter, Z = [∗set] (X \ filterY)
  have hcombined : ([∗set] y ∈ X, Φ y) ⊣⊢
      ([∗set] y ∈ Y, if φ y then Φ y else emp) ∗
      ([∗set] y ∈ FiniteSet.diff X (FiniteSet.filter (fun x => decide (φ x)) Y), Φ y) :=
    hX_split.trans (sep_congr_l hfilter)
  -- Now prove the goal: X ⊢ A ∗ (A -∗ X)
  -- From X ⊣⊢ A ∗ Z, we have X ⊢ A ∗ Z
  refine hcombined.1.trans ?_
  -- Need: A ∗ Z ⊢ A ∗ (A -∗ X)
  apply sep_mono
  · -- Prove: A ⊢ A
    exact BIBase.Entails.rfl
  · -- Prove: Z ⊢ A -∗ X
    apply wand_intro'
    -- Goal becomes: A ∗ Z ⊢ X
    -- This is exactly hcombined.2
    exact hcombined.2

/-- Corresponds to `big_sepS_filter_acc` in Rocq Iris. -/
theorem filter_acc [BIAffine PROP] (φ : A → Prop) [DecidablePred φ] {Φ : A → PROP} {X Y : S}
    (h : ∀ y, FiniteSet.mem y Y = true → φ y → FiniteSet.mem y X = true) :
    ([∗set] y ∈ X, Φ y) ⊢
      ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) ∗
      (([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) -∗ [∗set] y ∈ X, Φ y) := by
  have h1 := @filter_acc' PROP _ S A _ _ _ φ _ Φ X Y h
  have h_equiv : ([∗set] y ∈ Y, if φ y then Φ y else emp) ⊣⊢ ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) := by
    apply proper
    intro y _
    by_cases hy : φ y
    · simp only [hy, ↓reduceIte]
      exact true_imp (PROP := PROP).symm
    · simp only [hy, ↓reduceIte]
      constructor
      · apply imp_intro'
        apply pure_elim_l (R := Φ y)
        intro hf
        exact hf.elim
      · exact Affine.affine (self := BIAffine.affine _)
  refine h1.trans ?_
  apply sep_mono
  · exact h_equiv.1
  · apply wand_mono h_equiv.2
    exact BIBase.Entails.rfl

/-! ## Separation Logic Combinators -/

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ X, Ψ y) := by
  unfold bigSepS
  have := @BigOpL.op_distr PROP _ _ sep emp _ (fun _ x => Φ x) (fun _ x => Ψ x) (toList X)
  exact equiv_iff.mp this

/-- Corresponds to `big_sepS_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y) ⊢
    ([∗set] y ∈ X, Ψ y) -∗
    ([∗set] y ∈ X, Φ y ∗ Ψ y) := by
  apply wand_intro (PROP := PROP)
  refine sep_comm (PROP := PROP).1.trans ?_
  have h := @sep' PROP _ S A _ Ψ Φ X
  refine h.2.trans ?_
  apply mono
  intro x _
  exact sep_comm (PROP := PROP).1

/-- Corresponds to `big_sepS_and` in Rocq Iris. -/
theorem and' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗set] y ∈ X, Φ y) ∧ ([∗set] y ∈ X, Ψ y) := by
  apply and_intro
  · exact mono (fun _ _ => and_elim_l)
  · exact mono (fun _ _ => and_elim_r)

/-! ## Pure Propositions -/

/-- Corresponds to `big_sepS_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) := by
  refine elements.1.trans ?_
  refine BigSepL.pure_1.trans (pure_mono ?_)
  intro h y hmem
  have hlist : List.Mem y (toList X) := (FiniteSetLaws.mem_toList X y).mpr hmem
  have ⟨i, hget⟩ := List.getElem?_of_mem hlist
  exact h i y hget

/-- Corresponds to `big_sepS_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : A → Prop} {X : S} :
    (<affine> (⌜∀ y, y ∈ X → φ y⌝ : PROP)) ⊢ ([∗set] y ∈ X, <affine> ⌜φ y⌝) := by
  have hlist : (<affine> ⌜∀ k x, (toList X)[k]? = some x → φ x⌝ : PROP) ⊢
      ([∗list] _k ↦ x ∈ toList X, <affine> ⌜φ x⌝) :=
    BigSepL.affinely_pure_2
  refine (affinely_mono (pure_mono ?_)).trans hlist
  intro h k x hget
  have hmem : List.Mem x (toList X) := List.mem_of_getElem? hget
  have hset_mem := (FiniteSetLaws.mem_toList X x).mp hmem
  exact h x hset_mem

/-- Corresponds to `big_sepS_pure` in Rocq Iris. -/
theorem pure [BIAffine PROP] {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊣⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono fun _ _ => affinely_elim)⟩

/-- Corresponds to `big_sepS_forall` in Rocq Iris. -/
theorem forall' [BIAffine PROP] {Φ : A → PROP} {X : S}
    [hPers : ∀ x, Persistent (Φ x)] :
    ([∗set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x) := by
  constructor
  · apply forall_intro
    intro x
    apply imp_intro'
    apply pure_elim_l
    intro hmem
    haveI hAff : ∀ y, Affine (Φ y) := fun y => BIAffine.affine (Φ y)
    exact @elem_of PROP _ S A _ _ _ Φ X x hmem (@TCOr.l _ _ (hAff))
  · unfold bigSepS
    have hmem_all : ∀ x, List.Mem x (toList X) → FiniteSet.mem x X = true :=
      fun x hmem => (FiniteSetLaws.mem_toList X x).mp hmem
    have helper : ∀ l, (∀ x, List.Mem x l → FiniteSet.mem x X = true) →
        (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ bigOpL sep emp (fun _ => Φ) l := by
      intro l hl
      induction l with
      | nil =>
        simp only [BigOpL.nil]
        exact Affine.affine (self := BIAffine.affine _)
      | cons y ys ih =>
        simp only [BigOpL.cons]
        have hy_mem : FiniteSet.mem y X = true := hl y (List.Mem.head ys)
        have hhead : (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ Φ y :=
          (forall_elim y).trans ((and_intro (pure_intro hy_mem) .rfl).trans imp_elim_r)
        refine and_self.2.trans (and_mono_l hhead) |>.trans ?_
        refine (persistent_and_sep_1 (P := Φ y)).trans ?_
        exact sep_mono_r (ih (fun x hx => hl x (List.Mem.tail y hx)))
    exact helper (toList X) hmem_all

/-! ## Modal Operators -/

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_persistently` in Rocq Iris. -/
theorem persistently [BIAffine PROP] {Φ : A → PROP} {X : S} :
    (<pers> ([∗set] y ∈ X, Φ y)) ⊣⊢ [∗set] y ∈ X, <pers> (Φ y) :=
  (persistently_congr elements).trans (BigSepL.persistently.trans elements.symm)

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_dup` in Rocq Iris. -/
theorem dup {P : PROP} [hAff : Affine P] {X : S} :
    ⊢ □ (P -∗ P ∗ P) -∗ P -∗ [∗set] _x ∈ X, P := by
  unfold bigSepS
  apply wand_intro
  apply wand_intro
  refine (sep_mono_l emp_sep.1).trans ?_
  induction toList X with
  | nil =>
    simp only [BigOpL.nil]
    exact sep_elim_r.trans hAff.affine
  | cons y ys ih =>
    simp only [BigOpL.cons]
    refine (sep_mono_l (intuitionistically_sep_idem (PROP := PROP)).2).trans ?_
    refine sep_assoc (PROP := PROP).1.trans ?_
    refine (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans ?_
    refine sep_assoc (PROP := PROP).2.trans ?_
    refine (sep_mono_l ih).trans ?_
    exact sep_comm (PROP := PROP).1

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_later` in Rocq Iris. -/
theorem later [BIAffine PROP] {Φ : A → PROP} {X : S} :
    iprop(▷ [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷ Φ y :=
  (later_congr elements).trans (BigSepL.later.trans elements.symm)

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_later_2` in Rocq Iris. -/
theorem later_2 {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ X, ▷ Φ y) ⊢ iprop(▷ [∗set] y ∈ X, Φ y) :=
  elements.1.trans (BigSepL.later_2.trans (later_mono elements.2))

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_laterN` in Rocq Iris. -/
theorem laterN [BIAffine PROP] {Φ : A → PROP} {n : Nat} {X : S} :
    iprop(▷^[n] [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷^[n] Φ y := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans later

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : A → PROP} {n : Nat} {X : S} :
    ([∗set] y ∈ X, ▷^[n] Φ y) ⊢ iprop(▷^[n] [∗set] y ∈ X, Φ y) := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact later_2.trans (later_mono ih)

/-! ## Introduction and Elimination -/

omit [DecidableEq A] [FiniteSetLaws S A] in
private theorem intro_list {Φ : A → PROP} {X : S} {l : List A}
    (hmem : ∀ x, List.Mem x l → FiniteSet.mem x X = true) :
    (□ (∀ x, ⌜FiniteSet.mem x X = true⌝ → Φ x)) ⊢ bigOpL sep emp (fun _ => Φ) l := by
  induction l with
  | nil => exact Affine.affine (self := intuitionistically_affine (PROP := PROP) _)
  | cons y ys ih =>
    have hy := hmem y (List.Mem.head ys)
    refine intuitionistically_sep_idem.2.trans (sep_mono ?_ (ih (fun x hx => hmem x (List.Mem.tail y hx))))
    exact intuitionistically_elim.trans <|
      (forall_elim y).trans <| (and_intro (pure_intro hy) .rfl).trans imp_elim_r

/-- Corresponds to `big_sepS_intro` in Rocq Iris. -/
theorem intro {Φ : A → PROP} {X : S} :
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x)) ⊢ [∗set] x ∈ X, Φ x := by
  unfold bigSepS
  apply intro_list (X := X)
  intro x hmem_list
  exact (FiniteSetLaws.mem_toList X x).mp hmem_list

/-- Corresponds to `big_sepS_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) -∗
    [∗set] x ∈ X, Ψ x := by
  apply BI.wand_intro
  have h1 : iprop(□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) ⊢ [∗set] x ∈ X, (Φ x -∗ Ψ x) := intro
  refine (sep_mono_r h1).trans ?_
  refine sep'.2.trans ?_
  apply mono
  intro _ _
  exact wand_elim_r (PROP := PROP)

/-- Corresponds to `big_sepS_wand` in Rocq Iris. -/
theorem wand' {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    ([∗set] x ∈ X, Φ x -∗ Ψ x) -∗
    [∗set] x ∈ X, Ψ x := by
  apply BI.wand_intro (PROP := PROP)
  refine sep_comm (PROP := PROP).1.trans ?_
  refine sep'.2.trans ?_
  apply mono
  intro _ _
  exact wand_elim_l (PROP := PROP)

/-- Corresponds to `big_sepS_elem_of_acc_impl` in Rocq Iris. -/
theorem elem_of_acc_impl {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢
    Φ x ∗
    (∀ (Ψ : A → PROP),
       (□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)) -∗
     Ψ x -∗
     ([∗set] y ∈ X, Ψ y)) := by
  have hdel := (delete (Φ := Φ) h).1
  refine hdel.trans (sep_mono_r ?_)
  apply forall_intro
  intro Ψ
  apply BI.wand_intro
  apply BI.wand_intro
  have hdel_Ψ := (delete (Φ := Ψ) (S := S) h).2
  have h1 : iprop(□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)) ⊢
      iprop(□ (∀ y, ⌜FiniteSet.mem y (FiniteSet.diff X (FiniteSet.singleton x)) = true⌝ → Φ y -∗ Ψ y)) := by
    apply intuitionistically_mono
    apply forall_intro
    intro y
    apply imp_intro'
    apply pure_elim_l
    intro hy_diff
    have ⟨hy_X, hy_ne⟩ := (FiniteSetLaws.mem_diff_singleton X x y).mp hy_diff
    exact (forall_elim y).trans <|
      (imp_mono_l (pure_mono fun _ => hy_X)).trans true_imp.1 |>.trans <|
      (imp_mono_l (pure_mono fun _ => hy_ne.symm)).trans true_imp.1
  refine sep_assoc.1.trans ?_
  refine (sep_mono_r (sep_comm (PROP := PROP).1)).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  refine sep_assoc.1.trans ?_
  refine (sep_mono_r ?_).trans hdel_Ψ
  refine (sep_mono_l h1).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  have h_impl := @impl PROP _ S A _ _ _ Φ Ψ (FiniteSet.diff X (FiniteSet.singleton x))
  refine (sep_mono_l h_impl).trans ?_
  refine (sep_comm (PROP := PROP).1).trans ?_
  exact wand_elim_r (PROP := PROP)

/-! ## Subsumption -/

/-- Corresponds to `big_sepS_subseteq` in Rocq Iris. -/
theorem subseteq {Φ : A → PROP} {X Y : S}
    [h : ∀ x, Affine (Φ x)]
    (hsub : Y ⊆ X) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ Y, Φ x := by
  unfold bigSepS
  have ⟨l, hperm⟩ := FiniteSetLaws.toList_subset X Y hsub
  exact BigSepL.submseteq hperm

/-! ## Commuting Lemmas -/

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_sepL` in Rocq Iris. -/
theorem sepL {B : Type _} (Φ : A → Nat → B → PROP) (X : S) (l : List B) :
    ([∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y) ⊣⊢
      ([∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y) := by
  calc [∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y
      _ ⊣⊢ [∗list] x ∈ toList X, [∗list] k↦y ∈ l, Φ x k y := elements (Φ := fun x => [∗list] k↦y ∈ l, Φ x k y)
      _ ⊣⊢ [∗list] k↦y ∈ l, [∗list] x ∈ toList X, Φ x k y :=
          @BigSepL.sepL PROP _ A B (fun _ x k y => Φ x k y) (toList X) l
      _ ⊣⊢ [∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y :=
          equiv_iff.mp <| BigSepL.congr (fun k y => equiv_iff.mpr <| elements (Φ := fun x => Φ x k y).symm)

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_sepS` in Rocq Iris. -/
theorem sepS {B : Type _} {T : Type _} [DecidableEq B] [FiniteSet T B] [FiniteSetLaws T B]
    (Φ : A → B → PROP) (X : S) (Y : T) :
    ([∗set] x ∈ X, [∗set] y ∈ Y, Φ x y) ⊣⊢
      ([∗set] y ∈ Y, [∗set] x ∈ X, Φ x y) := by
  calc [∗set] x ∈ X, [∗set] y ∈ Y, Φ x y
      _ ⊣⊢ [∗list] x ∈ toList X, [∗set] y ∈ Y, Φ x y := elements (Φ := fun x => [∗set] y ∈ Y, Φ x y)
      _ ⊣⊢ [∗list] x ∈ toList X, [∗list] y ∈ toList Y, Φ x y :=
          equiv_iff.mp <| BigSepL.congr (fun _ x => equiv_iff.mpr <| elements (Φ := Φ x))
      _ ⊣⊢ [∗list] y ∈ toList Y, [∗list] x ∈ toList X, Φ x y :=
          @BigSepL.sepL PROP _ A B (fun _ x _ y => Φ x y) (toList X) (toList Y)
      _ ⊣⊢ [∗list] y ∈ toList Y, [∗set] x ∈ X, Φ x y :=
          equiv_iff.mp <| BigSepL.congr (fun _ y => equiv_iff.mpr <| elements (Φ := fun x => Φ x y).symm)
      _ ⊣⊢ [∗set] y ∈ Y, [∗set] x ∈ X, Φ x y := elements (Φ := fun y => [∗set] x ∈ X, Φ x y).symm

omit [DecidableEq A] [FiniteSetLaws S A] in
/-- Corresponds to `big_sepS_sepM` in Rocq Iris. -/
theorem sepM {B : Type _} {M : Type _ → Type _} {K : Type _}
    [DecidableEq K] [FiniteMap K M] [FiniteMapLaws K M]
    (Φ : A → K → B → PROP) (X : S) (m : M B) :
    ([∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y) ⊣⊢
      ([∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y) := by
  calc [∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y
      _ ⊣⊢ [∗list] x ∈ toList X, [∗map] k↦y ∈ m, Φ x k y :=
          elements (Φ := fun x => [∗map] k↦y ∈ m, Φ x k y)
      _ ⊣⊢ [∗list] x ∈ toList X, [∗list] kv ∈ toList m, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply BigSepL.congr
          intro _ x; unfold bigSepM; exact equiv_iff.mpr .rfl
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗list] x ∈ toList X, Φ x kv.1 kv.2 :=
          @BigSepL.sepL PROP _ A (K × B) (fun _ x _ kv => Φ x kv.1 kv.2) (toList X) (toList m)
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗set] x ∈ X, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply BigSepL.congr
          intro _ kv; exact equiv_iff.mpr (elements (Φ := fun x => Φ x kv.1 kv.2)).symm
      _ ⊣⊢ [∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y :=
          equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl

end BigSepS

end Iris.BI
