/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.DerivedLawsLater
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra BigOpL
open Iris.Std
open BIBase

/-! # Big Separating Conjunction over Lists -/

private theorem list_split {A : Type _} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    l = l.take i ++ x :: l.drop (i + 1) := by
  have ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  have := List.take_append_drop (i + 1) l
  rw [List.take_succ_eq_append_getElem hi, hx, List.append_assoc] at this; exact this.symm

namespace BigSepL
variable {PROP : Type _} [BI PROP] {A : Type _}

@[simp]
theorem bigSepL_nil {Φ : Nat → A → PROP} :
    ([∗list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ emp := .rfl

theorem bigSepL_nil_affine {P : PROP} [Affine P] {Φ : Nat → A → PROP} :
    P ⊢ [∗list] k ↦ x ∈ ([] : List A), Φ k x := Affine.affine.trans bigSepL_nil.2

theorem bigSepL_cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∗list] k ↦ y ∈ x :: xs, Φ k y) ⊣⊢ Φ 0 x ∗ [∗list] k ↦ y ∈ xs, Φ (k + 1) y := .rfl

theorem bigSepL_singleton {Φ : Nat → A → PROP} {x : A} :
    ([∗list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x := equiv_iff.mp (bigOpL_singleton_equiv Φ x)

theorem bigSepL_app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∗list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l₁, Φ k x) ∗ [∗list] k ↦ x ∈ l₂, Φ (k + l₁.length) x :=
  equiv_iff.mp (bigOpL_append_equiv Φ l₁ l₂)

theorem bigSepL_snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∗list] k ↦ y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗list] k ↦ y ∈ l, Φ k y) ∗ Φ l.length x :=
  equiv_iff.mp (bigOpL_snoc_equiv Φ l x)

theorem bigSepL_mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_gen_proper (· ⊢ ·) .rfl sep_mono (h ·)

theorem bigSepL_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv h

theorem bigSepL_equiv_of_forall_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv_of_forall_equiv h

theorem bigSepL_dist {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∗list] k ↦ x ∈ l, Ψ k x := bigOpL_dist h

theorem bigSepL_mono_of_forall {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x := bigSepL_mono (fun _ => h)

theorem bigSepL_flip_mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Ψ k x ⊢ Φ k x) :
    ([∗list] k ↦ x ∈ l, Ψ k x) ⊢ [∗list] k ↦ x ∈ l, Φ k x := bigSepL_mono (fun _ => h)

theorem bigSepL_id_mono {Ps Qs : List PROP} (hlen : Ps.length = Qs.length)
    (h : ∀ (i : Nat) (P Q : PROP), Ps[i]? = some P → Qs[i]? = some Q → P ⊢ Q) :
    ([∗list] P ∈ Ps, P) ⊢ [∗list] Q ∈ Qs, Q :=
  bigOpL_gen_proper_2 (· ⊢ ·) .rfl sep_mono hlen (h _ _ _ · ·)

instance bigSepL_persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2) (fun _ => Persistent.persistent)

instance bigSepL_affine {Φ : Nat → A → PROP} {l : List A} [∀ k x, Affine (Φ k x)] :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (fun _ => Affine.affine)

theorem bigSepL_persistent_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Persistent P) :
    Persistent ([∗list] P ∈ Ps, P) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2)
    (fun hget => (hPs _ (List.mem_iff_getElem?.mpr ⟨_, hget⟩)).persistent)

theorem bigSepL_affine_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Affine P) :
    Affine ([∗list] P ∈ Ps, P) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1)
    (fun hget => (hPs _ (List.mem_iff_getElem?.mpr ⟨_, hget⟩)).affine)

theorem bigSepL_persistent_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2) (fun hget => (h _ _ hget).persistent)

theorem bigSepL_affine_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ {k x}, l[k]? = some x → Affine (Φ k x)) :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (fun hget => (h hget).affine)

instance bigSepL_nil_timeless [Timeless (emp : PROP)] {Φ : Nat → A → PROP} :
    Timeless ([∗list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by simp only [bigOpL]; exact Timeless.timeless

theorem bigSepL_emp_l {l : List A} :
    ([∗list] _x ∈ l, (emp : PROP)) ⊣⊢ emp := equiv_iff.mp (bigOpL_const_unit_equiv)

theorem bigSepL_sep_equiv {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x) ⊣⊢ ([∗list] k ↦ x ∈ l, Φ k x) ∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  equiv_iff.mp (bigOpL_op_equiv Φ Ψ l)

theorem bigSepL_sep_equiv_symm {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ∗ ([∗list] k ↦ x ∈ l, Ψ k x) ⊣⊢ [∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x :=
  bigSepL_sep_equiv.symm

theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∧ Ψ k x) ⊢ ([∗list] k ↦ x ∈ l, Φ k x) ∧ [∗list] k ↦ x ∈ l, Ψ k x :=
  and_intro (bigSepL_mono fun _ => and_elim_l) (bigSepL_mono fun _ => and_elim_r)

theorem wand {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ([∗list] k ↦ x ∈ l, Φ k x -∗ Ψ k x) -∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  wand_intro <| bigSepL_sep_equiv_symm.1.trans (bigSepL_mono fun _ => wand_elim_r)

theorem bigSepL_pure_intro {φ : Nat → A → Prop} {l : List A} :
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact BI.pure_intro fun _ _ h => nomatch h
  | cons y ys ih =>
    refine (sep_mono_r ih).trans <| sep_and.trans <| pure_and.1.trans <| pure_mono ?_
    intro ⟨hy, hys⟩ k x hget
    match k with
    | 0 => exact Option.some.inj hget ▸ hy
    | k + 1 => exact hys k x hget

theorem bigSepL_affinely_pure_elim {φ : Nat → A → Prop} {l : List A} :
    (<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) ⊢
      ([∗list] k ↦ x ∈ l, <affine> ⌜φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact affinely_elim_emp
  | cons y ys ih =>
    refine (affinely_mono <| pure_mono fun h => ⟨h 0 y rfl, fun k x hget => h (k + 1) x hget⟩).trans <|
      (affinely_mono pure_and.2).trans <| affinely_and.1.trans <| persistent_and_sep_1.trans (sep_mono_r ih)

theorem pure' [BIAffine PROP] {φ : Nat → A → Prop} {l : List A} :
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊣⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨bigSepL_pure_intro, (affine_affinely _).2.trans <| bigSepL_affinely_pure_elim.trans (bigSepL_mono fun _ => affinely_elim)⟩

theorem bigSepL_take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l.take n, Φ k x) ∗ [∗list] k ↦ x ∈ l.drop n, Φ (n + k) x :=
  equiv_iff.mp (bigOpL_take_drop_equiv Φ l n)

theorem bigSepL_map {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∗list] k ↦ y ∈ l.map f, Φ k y) ≡ [∗list] k ↦ x ∈ l, Φ k (f x) :=
  bigOpL_map_equiv f Φ l

theorem bigSepL_filterMap {B : Type _} (f : A → Option B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.filterMap f, Φ y) ≡ [∗list] x ∈ l, (f x).elim emp Φ :=
  bigOpL_filterMap_equiv f Φ l

theorem bigSepL_bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.flatMap f, Φ y) ≡ [∗list] x ∈ l, [∗list] y ∈ f x, Φ y :=
  bigOpL_flatMap_equiv f Φ l

theorem bigSepL_lookup_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) := by
  induction l generalizing i Φ x with
  | nil => simp at h
  | cons z zs ih => cases i with
    | zero => exact Option.some.inj (List.getElem?_cons_zero ▸ h) ▸
        ⟨sep_mono_r (forall_intro fun y => wand_intro sep_comm.1),
         (sep_mono_r (forall_elim z)).trans wand_elim_r⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have ih := ih (Φ := fun n => Φ (n + 1)) h
      refine ⟨(sep_mono_r ih.1).trans <| sep_assoc.2.trans <| (sep_mono_l sep_comm.1).trans <|
        sep_assoc.1.trans <| sep_mono_r <| forall_intro fun y => wand_intro <|
        sep_assoc.1.trans <| sep_mono_r <| (sep_mono_l (forall_elim y)).trans <|
          sep_comm.1.trans wand_elim_r, ?_⟩
      have := (List.getElem?_eq_some_iff.mp h).2 ▸ List.set_getElem_self (List.getElem?_eq_some_iff.mp h).1
      conv => rhs; rw [← this]
      exact (sep_mono_r (forall_elim x)).trans wand_elim_r

theorem bigSepL_lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    [TCOr (∀ k y, Affine (Φ k y)) (Absorbing (Φ i x))] → ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x
  | TCOr.l => by
    rw [list_split h]; refine bigSepL_app.1.trans <| sep_elim_r.trans ?_
    simp only [bigOpL, Nat.zero_add,
      List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp h).1)]
    exact sep_elim_l
  | TCOr.r => (bigSepL_lookup_acc h).1.trans sep_elim_l

theorem bigSepL_insert_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) :=
  (bigSepL_lookup_acc h).1

theorem bigSepL_elem_of_acc {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    ([∗list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗list] y ∈ l, Φ y) := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  conv => rhs; rw [← show l.set i x = l from hget ▸ List.set_getElem_self hi]
  exact (bigSepL_lookup_acc (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)).1.trans (sep_mono_r (forall_elim x))

theorem bigSepL_elem_of {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] → ([∗list] y ∈ l, Φ y) ⊢ Φ x
  | TCOr.l | TCOr.r =>
    let ⟨_, hi, hget⟩ := List.mem_iff_getElem.mp h
    bigSepL_lookup (Φ := fun _ y => Φ y) (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)

theorem bigSepL_delete_cond {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ [∗list] k ↦ y ∈ l, if k = i then emp else Φ k y := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons z zs ih => cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp only [bigOpL, ↓reduceIte]
      exact sep_congr_r ((equiv_iff.mp (bigSepL_equiv fun _ => equiv_iff.mpr .rfl)).trans emp_sep.symm)
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact (sep_congr_r (ih h)).trans sep_left_comm |>.trans
        (sep_congr_r (sep_congr_r (equiv_iff.mp (bigSepL_equiv fun _ =>
          equiv_iff.mpr (by simp [Nat.add_right_cancel_iff])))))

theorem bigSepL_delete_impl [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y := by
  have hmono : ∀ {k y}, (if k = i then emp else Φ k y) ⊣⊢ iprop(⌜k ≠ i⌝ → Φ k y) := fun {k y} => by
    by_cases hki : k = i <;> simp only [hki, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
    · exact ⟨imp_intro' <| (pure_elim_l (R := Φ i y) fun hf => hf.elim), Affine.affine⟩
    · exact true_imp.symm
  exact (bigSepL_delete_cond h).trans <| sep_congr_r <| equiv_iff.mp <| bigSepL_equiv fun _ => equiv_iff.mpr hmono

theorem bigSepL_intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} [Intuitionistic P]
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact intuitionistic.trans affinely_elim_emp
  | cons y ys ih =>
    exact intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
      sep_mono (intuitionistically_elim.trans (h 0 y rfl))
               (intuitionistically_elim.trans (ih fun k x hget => h (k + 1) x hget))

theorem bigSepL_forall_intro {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  BI.forall_intro fun _ => BI.forall_intro fun _ => imp_intro' <| pure_elim_l fun hget =>
    (bigSepL_lookup_acc hget).1.trans <| (sep_mono_l Persistent.persistent).trans <|
      sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

theorem bigSepL_forall_elim {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x)) ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Affine.affine
  | cons y ys ih =>
    have head_step : (∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x) ⊢ Φ 0 y :=
      (BI.forall_elim 0).trans (BI.forall_elim y) |>.trans <|
        (and_intro (BI.pure_intro rfl) .rfl).trans imp_elim_r
    have tail_step : (∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x)
        ⊢ iprop(∀ k x, ⌜ys[k]? = some x⌝ → Φ (k + 1) x) :=
      BI.forall_intro fun k => BI.forall_intro fun z =>
        (BI.forall_elim (k + 1)).trans (BI.forall_elim z)
    exact and_self.2.trans (and_mono_l head_step) |>.trans persistent_and_sep_1 |>.trans <|
      sep_mono_r (tail_step.trans ih)

theorem bigSepL_forall_equiv {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
    ⟨bigSepL_forall_intro, bigSepL_forall_elim⟩

theorem bigSepL_impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢
      □ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) -∗ [∗list] k ↦ x ∈ l, Ψ k x := by
  apply wand_intro
  have h1 : (□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) ⊢ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l := by
    haveI : Intuitionistic iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) :=
      intuitionistically_intuitionistic _
    exact bigSepL_intro fun k x hget => intuitionistically_elim.trans <|
      (BI.forall_elim k).trans (BI.forall_elim x) |>.trans <|
        (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1
  exact (sep_mono_r h1).trans <| bigSepL_sep_equiv_symm.1.trans (bigSepL_mono fun _ => wand_elim_r)

theorem bigSepL_lookup_acc_impl {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    iprop([∗list] k ↦ x ∈ l, Φ k x) ⊢
      Φ i x ∗ ∀ (Ψ: Nat → A → PROP), □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
        Ψ i x -∗  ([∗list] k ↦ x ∈ l, Ψ k x) := by
  refine (bigSepL_delete_cond h).1.trans <| sep_mono_r <| BI.forall_intro fun Ψ => wand_intro <| wand_intro ?_
  refine sep_comm.1.trans <| (sep_mono_r ?_).trans (bigSepL_delete_cond (Φ := Ψ) h).2
  have hwand : (□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
      ⊢ bigSepL (fun k y => if k = i then emp else iprop(Φ k y -∗ Ψ k y)) l := by
    haveI : Intuitionistic iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) :=
      intuitionistically_intuitionistic _
    exact bigSepL_intro fun k y hget => by
      by_cases hki : k = i
      · subst hki; simp only []
        exact Intuitionistic.intuitionistic.trans (affinely_elim_emp (PROP := PROP))
      · simp only [hki]
        exact intuitionistically_elim.trans <| (BI.forall_elim k).trans (BI.forall_elim y) |>.trans <|
          ((and_intro (BI.pure_intro hget) .rfl).trans imp_elim_r).trans <|
          ((and_intro (BI.pure_intro hki) .rfl).trans imp_elim_r)
  exact (sep_mono_r hwand).trans <| bigSepL_sep_equiv_symm.1.trans <| bigSepL_mono fun {k _} hget => by
    by_cases hki : k = i <;> simp only [hki]
    · exact emp_sep.1
    · exact wand_elim_r

theorem bigSepL_persistently {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    (<pers> [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, <pers> Φ k x :=
  equiv_iff.mp <| bigOpL_hom (H := MonoidHomomorphism.ofEquiv persistently_ne
    (equiv_iff.mpr persistently_sep) (equiv_iff.mpr persistently_emp')) Φ l

theorem bigSepL_later [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} :
    (▷ [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷ Φ k x :=
  equiv_iff.mp <| bigOpL_hom (H := MonoidHomomorphism.ofEquiv later_ne
    (equiv_iff.mpr later_sep) (equiv_iff.mpr later_emp)) Φ l

theorem bigSepL_later_2 {Φ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, ▷ Φ k x) ⊢ iprop(▷ [∗list] k ↦ x ∈ l, Φ k x) :=
  bigOpL_gen_proper (fun a b => a ⊢ ▷ b) later_intro
    (fun h1 h2 => (sep_mono h1 h2).trans later_sep.2) (fun _ => .rfl)

theorem bigSepL_laterN [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    (▷^[n] [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷^[n] Φ k x :=
  match n with | 0 => .rfl | _ + 1 => (later_congr bigSepL_laterN).trans bigSepL_later

theorem bigSepL_laterN_2 {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, ▷^[n] Φ k x) ⊢ (▷^[n] [∗list] k ↦ x ∈ l, Φ k x) :=
  match n with | 0 => .rfl | _ + 1 => bigSepL_later_2.trans (later_mono bigSepL_laterN_2)

theorem bigSepL_perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∗list] x ∈ l₁, Φ x) ⊣⊢ [∗list] x ∈ l₂, Φ x := equiv_iff.mp (bigOpL_equiv_of_perm Φ hp)

theorem bigSepL_submseteq {Φ : A → PROP} [∀ x, Affine (Φ x)] {l₁ l₂ l : List A} (h : (l₁ ++ l).Perm l₂) :
    ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₁, Φ x :=
    (bigSepL_perm (Φ := Φ) h).2.trans (bigSepL_app.1.trans sep_elim_l)

theorem bigSepL_dup {P : PROP} [Affine P] {l : List A} : □ (P -∗ P ∗ P) ∗ P ⊢ ([∗list] _x ∈ l, P) :=
  match l with
  | [] => sep_elim_r.trans Affine.affine
  | _ :: _ =>
    (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      sep_assoc.2.trans <| (sep_mono_l bigSepL_dup).trans sep_comm.1

theorem bigSepL_replicate {P : PROP} {l : List A} :
    ([∗list] _x ∈ List.replicate l.length P, P) ⊣⊢ [∗list] _x ∈ l, P :=
  match l with | [] => .rfl | _ :: _ => ⟨sep_mono_r bigSepL_replicate.1, sep_mono_r bigSepL_replicate.2⟩

theorem bigSepL_zip_seq {Φ : A × Nat → PROP} {n : Nat} {l : List A} :
    ([∗list] xy ∈ l.zipIdx n, Φ xy) ⊣⊢ [∗list] i ↦ x ∈ l, Φ (x, n + i) :=
  equiv_iff.mp (bigOpL_zipIdx_equiv Φ n l)

theorem bigSepL_sep_zip {B : Type _} {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP}
    {l₁ : List A} {l₂ : List B} (hlen : l₁.length = l₂.length) :
    ([∗list] i ↦ xy ∈ l₁.zip l₂, Φ i xy.1 ∗ Ψ i xy.2) ⊣⊢
      ([∗list] i ↦ x ∈ l₁, Φ i x) ∗ [∗list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil => cases l₂ with | nil => exact emp_sep.symm | cons => simp at hlen
  | cons _ _ ih => cases l₂ with
    | nil => simp at hlen
    | cons _ _ => exact (sep_congr_r (ih (by simpa using hlen))).trans sep_sep_sep_comm

theorem bigSepL_sep_zip_with {B C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP} {l₁ : List A} {l₂ : List B}
    (hg1 : ∀ x y, g1 (f x y) = x) (hg2 : ∀ x y, g2 (f x y) = y)
    (hlen : l₁.length = l₂.length) :
    ([∗list] i ↦ c ∈ List.zipWith f l₁ l₂, Φ i (g1 c) ∗ Ψ i (g2 c)) ⊣⊢
      ([∗list] i ↦ x ∈ l₁, Φ i x) ∗ [∗list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil => cases l₂ with | nil => exact emp_sep.symm | cons => simp at hlen
  | cons _ _ ih => cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, bigOpL, hg1, hg2]
      exact (sep_congr_r (ih hlen)).trans sep_sep_sep_comm

theorem bigSepL_zip_with {B C : Type _} (f : A → B → C) {Φ : Nat → C → PROP}
    {l₁ : List A} {l₂ : List B} :
    ([∗list] k ↦ c ∈ List.zipWith f l₁ l₂, Φ k c) ⊣⊢
      [∗list] k ↦ x ∈ l₁, match l₂[k]? with | some y => Φ k (f x y) | none => emp := by
  induction l₁ generalizing l₂ Φ with
  | nil => exact .rfl
  | cons _ _ ih => cases l₂ with
    | nil => exact emp_sep.symm.trans (sep_congr_r bigSepL_emp_l.symm)
    | cons _ _ => exact sep_congr_r ih

theorem bigSepL_comm {B : Type _} (Φ : Nat → A → Nat → B → PROP) (l₁ : List A) (l₂ : List B) :
    ([∗list] k1↦x1 ∈ l₁, [∗list] k2↦x2 ∈ l₂, Φ k1 x1 k2 x2) ⊣⊢
      ([∗list] k2↦x2 ∈ l₂, [∗list] k1↦x1 ∈ l₁, Φ k1 x1 k2 x2) :=
  match l₁ with
  | [] => ⟨(equiv_iff.mp bigOpL_const_unit_equiv).2, (equiv_iff.mp bigOpL_const_unit_equiv).1⟩
  | _ :: _ =>
    let ih := bigSepL_comm (fun i a j b => Φ (i + 1) a j b) _ l₂
    ⟨(sep_mono_r ih.1).trans (equiv_iff.mp (bigOpL_op_equiv _ _ _)).2,
     (equiv_iff.mp (bigOpL_op_equiv _ _ _)).1.trans (sep_mono_r ih.2)⟩

end BigSepL

-- # Big Separating Conjunction over Two Lists
namespace BigSepL2

variable {PROP : Type _} [BI PROP] {A B : Type _}

def bigSepL2 [BI PROP] {A B : Type _} (Φ : Nat → A → B → PROP)
    (l1 : List A) (l2 : List B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: xs1, x2 :: xs2 => sep (Φ 0 x1 x2) (bigSepL2 (fun n => Φ (n + 1)) xs1 xs2)
  | _, _ => iprop(False)

macro_rules
  | `([∗list] $x1:ident;$x2:ident ∈ $l1;$l2, $P) =>
      `(bigSepL2 (fun _ $x1 $x2 => $P) $l1 $l2)
  | `([∗list] $k:ident ↦ $x1:ident;$x2:ident ∈ $l1;$l2, $P) =>
      `(bigSepL2 (fun $k $x1 $x2 => $P) $l1 $l2)

macro_rules
  | `(iprop([∗list] $x1:ident;$x2:ident ∈ $l1;$l2, $P)) =>
      `(bigSepL2 (fun _ $x1 $x2 => iprop($P)) $l1 $l2)
  | `(iprop([∗list] $k:ident ↦ $x1:ident;$x2:ident ∈ $l1;$l2, $P)) =>
      `(bigSepL2 (fun $k $x1 $x2 => iprop($P)) $l1 $l2)

@[simp]
theorem bigSepL2_nil {Φ : Nat → A → B → PROP} :
    ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') ⊣⊢ emp := .rfl

theorem bigSepL2_nil_affine {P : PROP} [Affine P] {Φ : Nat → A → B → PROP} :
    P ⊢ ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') :=
  Affine.affine.trans bigSepL2_nil.2

theorem bigSepL2_nil_inv_l {Φ : Nat → A → B → PROP} {l2 : List B} :
   ([∗list] k ↦ x;x' ∈ [];l2, Φ k x x')  ⊢ ⌜l2 = []⌝ :=
  match l2 with | .nil => pure_intro rfl | .cons _ _ => false_elim

theorem bigSepL2_nil_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} :
    ([∗list] k ↦ x;x' ∈ l1;[], Φ k x x') ⊢ ⌜l1 = []⌝ :=
  match l1 with | .nil => pure_intro rfl | .cons _ _ => false_elim

theorem bigSepL2_cons {Φ : Nat → A → B → PROP} {x1 : A} {x2 : B} {xs1 : List A} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2 := .rfl

theorem bigSepL2_cons_inv_l {Φ : Nat → A → B → PROP} {x1 : A} {xs1 : List A} {l2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;l2, Φ k y1 y2) ⊣⊢
      ∃ x2 xs2, ⌜l2 = x2 :: xs2⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) :=
  match l2 with
  | [] => ⟨false_elim, exists_elim fun _ => exists_elim fun _ =>
      and_elim_l.trans (pure_elim' (nomatch ·))⟩
  | _ :: _ =>
    ⟨(and_intro (pure_intro rfl) .rfl).trans (exists_intro' _ (exists_intro' _ .rfl)),
     exists_elim fun _ => exists_elim fun _ => pure_elim_l fun h => by cases h; exact .rfl⟩

theorem bigSepL2_cons_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {x2 : B} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ l1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      ∃ x1 xs1, ⌜l1 = x1 :: xs1⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) :=
  match l1 with
  | [] => ⟨false_elim, exists_elim fun _ => exists_elim fun _ =>
      and_elim_l.trans (pure_elim' (nomatch ·))⟩
  | _ :: _ =>
    ⟨(and_intro (pure_intro rfl) .rfl).trans (exists_intro' _ (exists_intro' _ .rfl)),
     exists_elim fun _ => exists_elim fun _ => pure_elim_l fun h => by cases h; exact .rfl⟩

theorem bigSepL2_singleton {Φ : Nat → A → B → PROP} {x : A} {y : B} :
    ([∗list] k ↦ x1;x2 ∈ [x];[y], Φ k x1 x2) ⊣⊢ Φ 0 x y := sep_emp

private theorem bigSepL2_alt_len {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ⌜l1.length = l2.length⌝ := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 <;> simp only [bigSepL2] <;> first | exact pure_intro rfl | exact false_elim
  | cons _ _ ih => cases l2 with
    | nil => exact false_elim
    | cons _ _ => exact (sep_mono true_intro ih).trans (true_sep.1.trans (pure_mono (congrArg (· + 1))))

private theorem bigSepL2_alt_fwd {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2) := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 <;> simp only [bigSepL2, List.zip_nil_left, bigOpL] <;>
           first | exact .rfl | exact false_elim
  | cons _ _ ih => cases l2 with
    | nil => exact false_elim
    | cons _ _ => exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)))

private theorem bigSepL2_alt_bwd {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2) ⊢
      [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 <;> first | exact .rfl | simp at hlen
  | cons _ _ ih => cases l2 with
    | nil => simp at hlen
    | cons _ _ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) hlen)

theorem bigSepL2_alt {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
  ⟨and_intro bigSepL2_alt_len bigSepL2_alt_fwd, pure_elim_l bigSepL2_alt_bwd⟩

theorem bigSepL2_length {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ iprop(⌜l1.length = l2.length⌝) :=
  bigSepL2_alt.1.trans and_elim_l

theorem bigSepL2_mono {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_mono (h rfl rfl) (bigSepL2_mono fun {k} => @h (k + 1))

theorem bigSepL2_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  ⟨bigSepL2_mono fun h1 h2 => (h h1 h2).1, bigSepL2_mono fun h1 h2 => (h h1 h2).2⟩

theorem bigSepL2_equiv_of_forall_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  bigSepL2_equiv fun _ _ => h

theorem bigSepL2_dist {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ≡{n}≡ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_ne.ne (h rfl rfl) (bigSepL2_dist fun {k} => @h (k + 1))

theorem bigSepL2_mono_of_forall {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  bigSepL2_mono (fun _ _ => h)

instance bigSepL2_persistent {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  persistent := match l1, l2 with
    | [], [] => persistently_emp_2
    | [], _ :: _ | _ :: _, [] => false_elim.trans (persistently_mono false_elim)
    | _ :: _, _ :: _ =>
      (sep_mono Persistent.persistent bigSepL2_persistent.persistent).trans persistently_sep_2

instance bigSepL2_affine {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  affine := match l1, l2 with
    | [], [] => .rfl
    | [], _ :: _ | _ :: _, [] => false_elim
    | _ :: _, _ :: _ => (sep_mono Affine.affine bigSepL2_affine.affine).trans sep_emp.1

theorem bigSepL2_sep_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 <;> simp only [bigSepL2] <;> first | exact emp_sep.symm
                                                       | exact ⟨false_elim, sep_elim_l.trans false_elim⟩
  | cons _ _ ih => cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, sep_elim_l.trans false_elim⟩
    | cons _ _ => exact (sep_congr .rfl ih).trans sep_sep_sep_comm

theorem bigSepL2_sep_equiv_symm {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) := bigSepL2_sep_equiv.symm

theorem bigSepL2_and {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∧ Ψ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∧ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
   and_intro (bigSepL2_mono fun _ _ => and_elim_l) (bigSepL2_mono fun _ _ => and_elim_r)

theorem bigSepL2_pure_intro {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊢
      iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  (and_mono .rfl BigSepL.bigSepL_pure_intro |>.trans pure_and.1 |>.trans
  <| pure_mono fun ⟨_, h⟩ k x1 x2 h1 h2 =>
    h k (x1, x2) (List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩)) |> bigSepL2_alt.1.trans

theorem bigSepL2_affinely_pure_elim {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    iprop(<affine> ⌜l1.length = l2.length ∧
      ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) :=
  (affinely_mono pure_and.2).trans affinely_and.1 |>.trans
    (and_mono .rfl <| (affinely_mono <| pure_mono fun h k (p : A × B) hp =>
        h k p.1 p.2 (List.getElem?_zip_eq_some.mp hp).1 (List.getElem?_zip_eq_some.mp hp).2).trans
      BigSepL.bigSepL_affinely_pure_elim) |>.trans (and_mono affinely_elim .rfl) |>.trans
    (bigSepL2_alt (Φ := fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝))).2

theorem bigSepL2_pure [BIAffine PROP] {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊣⊢
      iprop(⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  ⟨(and_intro bigSepL2_length bigSepL2_pure_intro).trans pure_and.1,
   (affine_affinely _).2.trans bigSepL2_affinely_pure_elim |>.trans (bigSepL2_mono fun _ _ => affinely_elim)⟩

theorem bigSepL2_emp_l [BIAffine PROP] {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ _x1;_x2 ∈ l1;l2, (emp : PROP)) ⊣⊢ iprop(⌜l1.length = l2.length⌝) := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => simp only [bigSepL2]; exact (true_emp).symm.trans (pure_true rfl).symm
    | cons => exact ⟨false_elim, pure_elim' (nomatch ·)⟩
  | cons _ _ ih => cases l2 with
    | nil => exact ⟨false_elim, pure_elim' (nomatch ·)⟩
    | cons _ _ =>
      simp only [bigSepL2, List.length_cons]
      exact emp_sep.trans (ih.trans ⟨pure_mono (congrArg (· + 1)), pure_mono Nat.succ.inj⟩)

theorem bigSepL2_app_wand {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) -∗
      ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) := by
  apply wand_intro'
  induction l1a generalizing l2a Φ with
  | nil => cases l2a with
    | nil => simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]; exact sep_emp.1
    | cons => simp only [bigSepL2, List.nil_append]; exact sep_elim_r.trans false_elim
  | cons _ _ ih => cases l2a with
    | nil => simp only [bigSepL2, List.nil_append]; exact sep_elim_r.trans false_elim
    | cons _ _ =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      exact (sep_mono_l (bigSepL2_equiv_of_forall_equiv (by simp [Nat.add_assoc])).1).trans sep_symm |>.trans
        sep_assoc.1 |>.trans (sep_mono_r sep_symm) |>.trans
        (sep_mono_r (ih (Φ := fun n => Φ (n + 1))))

private theorem bigSepL2_app_inv_core {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
        ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  induction l1a generalizing l2a Φ with
  | nil => cases l2a with
    | nil => simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]; exact emp_sep.2
    | cons y ys => cases hlen with
      | inl h => simp at h
      | inr h =>
        simp only [bigSepL2, List.nil_append]
        exact bigSepL2_alt_len.trans (pure_elim' (by simp; omega))
  | cons x1 xs1 ih => cases l2a with
    | nil => cases hlen with
      | inl h => simp at h
      | inr h =>
        exact bigSepL2_alt_len.trans (pure_elim' (by simp; omega))
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      exact (sep_mono_r (ih (l2a := xs2) (hlen.imp (by simp_all) id))).trans sep_assoc.2

theorem bigSepL2_app {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
        ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) :=
  ⟨ bigSepL2_app_inv_core hlen, sep_symm.trans (wand_elim'  bigSepL2_app_wand)⟩

theorem bigSepL2_snoc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {x : A} {y : B} :
    ([∗list] k ↦ x1;x2 ∈ l1 ++ [x];l2 ++ [y], Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ Φ l1.length x y := by
  have h := bigSepL2_app (Φ := Φ) (l1a := l1) (l2a := l2) (l1b := [x]) (l2b := [y]) (Or.inr rfl)
  simp only [bigSepL2, Nat.zero_add] at h
  exact h.trans (sep_congr .rfl sep_emp)

theorem bigSepL2_map_left {C : Type _} (f : C → A) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) y) := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil | cons => exact .rfl
  | cons _ _ ih => cases l2 with
    | nil => exact .rfl
    | cons _ _ => exact sep_congr .rfl ih

theorem bigSepL2_map_right {C : Type _} (f : C → B) {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List C} :
    ([∗list] k ↦ x;y ∈ l1;l2.map f, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x (f y)) := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil | cons => simp only [List.map_nil, List.map_cons]; exact .rfl
  | cons _ _ ih => cases l2 with
    | nil => exact .rfl
    | cons _ _ => exact sep_congr .rfl ih

theorem bigSepL2_map {C D : Type _} (f : C → A) (g : D → B) {Φ : Nat → A → B → PROP} {l1 : List C} {l2 : List D} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2.map g, Φ k x y) ⊣⊢
      ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) (g y)) := (bigSepL2_map_left f).trans (bigSepL2_map_right g)

theorem bigSepL2_flip {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l2;l1, Φ k y x) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_congr .rfl bigSepL2_flip

theorem bigSepL2_fst_snd {Φ : Nat → A → B → PROP} {l : List (A × B)} :
    ([∗list] k ↦ x;y ∈ l.map Prod.fst;l.map Prod.snd, Φ k x y) ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) l := by
  have h : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with | nil => rfl | cons _ _ ih => simp [ih]
  exact bigSepL2_alt.trans (by simp only [List.length_map, h]; exact true_and)

theorem bigSepL2_app_inv_l {Φ : Nat → A → B → PROP} {l1' l1'' : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1' ++ l1'';l2, Φ k x1 x2) ⊢
      (∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧
        (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l1'.length) x1 x2))) := by
  refine (exists_intro' (l2.take l1'.length) (exists_intro' (l2.drop l1'.length)
    (and_intro (BI.pure_intro (List.take_append_drop l1'.length l2).symm) ?_)))
  induction l1' generalizing l2 Φ with
  | nil => exact emp_sep.symm.1.trans (sep_mono_l bigSepL2_nil.symm.1)
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => exact false_elim
    | cons x2 xs2 =>
      exact (sep_mono_r ih).trans (sep_assoc.symm.1.trans (sep_mono_r (bigSepL2_mono_of_forall .rfl)))

theorem bigSepL2_app_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {l2' l2'' : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2' ++ l2'', Φ k x1 x2) ⊢
      iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
        (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l2'.length) x1 x2))) :=
  bigSepL2_flip.symm.1.trans bigSepL2_app_inv_l |>.trans <|
    exists_mono fun _ => exists_mono fun _ => and_mono .rfl (sep_mono bigSepL2_flip.1 bigSepL2_flip.1)

private theorem bigSepL2_zip_set {C D : Type _} {l1 : List C} {l2 : List D} {i : Nat}
    (hi1 : i < l1.length) (hi2 : i < l2.length) (y1 : C) (y2 : D) :
    (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2) := by
  apply List.ext_getElem?; intro k; simp only [List.getElem?_set]
  by_cases hik : i = k
  · subst hik; simp only [show i < (l1.zip l2).length from by simp only [List.length_zip]; omega, ↓reduceIte]
    exact (List.getElem?_zip_eq_some.mpr ⟨List.getElem?_set_self hi1, List.getElem?_set_self hi2⟩).symm
  · simp [List.zip_eq_zipWith, List.getElem?_zipWith, hik]

theorem bigSepL2_insert_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗
        [∗list] k ↦ z1;z2 ∈ l1.set i y1;l2.set i y2, Φ k z1 z2)) := by
  have hi1 := (List.getElem?_eq_some_iff.mp h1).1
  have hi2 := (List.getElem?_eq_some_iff.mp h2).1
  refine bigSepL2_alt.1.trans (pure_elim_l fun hlen => ?_)
  have hzip : (l1.zip l2)[i]? = some (x1, x2) := List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩
  refine (BigSepL.bigSepL_insert_acc hzip).trans (sep_mono_r ?_)
  refine BI.forall_intro fun y1 => BI.forall_intro fun y2 =>
    (BI.forall_elim (y1, y2)).trans (wand_mono_r ?_)
  rw [bigSepL2_zip_set hi1 hi2]; exact (and_intro (BI.pure_intro (by simp [hlen])) .rfl).trans bigSepL2_alt.2

theorem bigSepL2_lookup_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)) :=
  let ⟨hi1, hx1⟩ := List.getElem?_eq_some_iff.mp h1
  let ⟨hi2, hx2⟩ := List.getElem?_eq_some_iff.mp h2
  (bigSepL2_insert_acc h1 h2).trans (sep_mono_r ((forall_elim x1).trans ((forall_elim x2).trans
    ((hx1 ▸ List.set_getElem_self hi1).symm ▸ (hx2 ▸ List.set_getElem_self hi2).symm ▸ .rfl))))

theorem bigSepL2_lookup {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))] →
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2
  | TCOr.l => by
    have hi1 := (List.getElem?_eq_some_iff.mp h1).1
    have hi2 := (List.getElem?_eq_some_iff.mp h2).1
    have hlen := List.length_take_of_le (Nat.le_of_lt hi1) |>.trans
      (List.length_take_of_le (Nat.le_of_lt hi2)).symm
    rw [list_split h1, list_split h2]
    exact (bigSepL2_app (Or.inl hlen)).1.trans <| sep_elim_r.trans <| by
      simp only [List.length_take_of_le (Nat.le_of_lt hi1), bigSepL2, Nat.zero_add]; exact sep_elim_l
  | TCOr.r => (bigSepL2_lookup_acc h1 h2).trans sep_elim_l

/-! ## Higher-Order Lemmas -/

private abbrev bigSepL2_forall_elim2 {Φ : Nat → A → B → PROP} {y1 : A} {y2 : B}
    {ys1 : List A} {ys2 : List B} :
    (∀ k x1 x2, iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
      ⊢ Φ 0 y1 y2 :=
  (BI.forall_elim 0).trans ((BI.forall_elim y1).trans ((BI.forall_elim y2).trans
    (((and_intro (BI.pure_intro rfl) .rfl).trans imp_elim_r).trans
      ((and_intro (BI.pure_intro rfl) .rfl).trans imp_elim_r))))

private abbrev bigSepL2_forall_shift {Φ : Nat → A → B → PROP} {y1 : A} {y2 : B}
    {ys1 : List A} {ys2 : List B} :
    (∀ k x1 x2, iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
      ⊢ (∀ k x1 x2, iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2)) :=
  BI.forall_intro fun k => BI.forall_intro fun z1 => BI.forall_intro fun z2 =>
    (BI.forall_elim (k + 1)).trans ((BI.forall_elim z1).trans (BI.forall_elim z2))

theorem bigSepL2_intro {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧
      □ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  refine pure_elim_l fun hlen => ?_
  suffices h : iprop(□ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      bigSepL2 Φ l1 l2 from h
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil => exact Affine.affine | cons => simp at hlen
  | cons y1 ys1 ih => cases l2 with
    | nil => simp at hlen
    | cons y2 ys2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; simp only [bigSepL2]
      exact intuitionistically_sep_idem.symm.1.trans (sep_mono
        (intuitionistically_elim.trans bigSepL2_forall_elim2)
        ((intuitionistically_mono bigSepL2_forall_shift).trans (ih hlen)))

theorem bigSepL2_wand {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 -∗ Ψ k x1 x2) -∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  wand_intro <| bigSepL2_sep_equiv_symm.1.trans (bigSepL2_mono fun _ _ => wand_elim_r)

theorem bigSepL2_impl {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      iprop(□ (∀ k, ∀ x1, ∀ x2,
        iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
   wand_intro <| (sep_mono_l (and_self.2.trans (and_mono_l bigSepL2_length))).trans <|
    (sep_mono_l persistent_and_affinely_sep_l.1).trans <|
    sep_assoc.1.trans <| persistent_and_affinely_sep_l.symm.1.trans <|
    pure_elim_l fun hlen =>
    (sep_mono_r ((and_intro (BI.pure_intro hlen) .rfl).trans
      (bigSepL2_intro (Φ := fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2))))).trans
    (bigSepL2_sep_equiv_symm.1.trans (bigSepL2_mono fun _ _ => wand_elim_r))

theorem forall' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hPersistent : ∀ k x1 x2, Persistent (Φ k x1 x2)) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) := by
  refine ⟨and_intro bigSepL2_length (BI.forall_intro fun _ => BI.forall_intro fun _ =>
      BI.forall_intro fun _ =>
      imp_intro' (pure_elim_l fun h1 => imp_intro' (pure_elim_l fun h2 => bigSepL2_lookup h1 h2))),
    pure_elim_l fun hlen => ?_⟩
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil => exact Affine.affine | cons => simp at hlen
  | cons y1 ys1 ih => cases l2 with
    | nil => simp at hlen
    | cons y2 ys2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; simp only [bigSepL2]
      exact (and_self.2.trans (and_mono_l bigSepL2_forall_elim2)).trans (persistent_and_sep_1.trans
        (sep_mono_r (bigSepL2_forall_shift.trans (ih (fun k => hPersistent (k + 1)) hlen))))

/-! ## Modality Interaction -/

theorem persistently [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(<pers> [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, <pers> Φ k x1 x2) :=
  (persistently_congr bigSepL2_alt).trans persistently_and |>.trans (and_congr persistently_pure .rfl) |>.trans
    (and_congr .rfl BigSepL.bigSepL_persistently) |>.trans
    (bigSepL2_alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2))).symm

theorem bigSepL2_later_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) ⊢
      iprop(▷ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  (bigSepL2_alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2))).1.trans
  (and_mono later_intro BigSepL.bigSepL_later_2) |>.trans
    later_and.2 |>.trans (later_mono bigSepL2_alt.2)

theorem bigSepL2_laterN_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷^[n] Φ k x1 x2) ⊢
      iprop(▷^[n] [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  match n with | 0 => .rfl | _ + 1 => bigSepL2_later_2.trans (later_mono bigSepL2_laterN_2)

theorem sepL {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) := by
  have h hlen := BigSepL.bigSepL_sep_zip (Φ := Φ1) (Ψ := Φ2) (l₁ := l1) (l₂ := l2) hlen
  refine bigSepL2_alt.trans ⟨pure_elim_l fun hlen => and_intro (BI.pure_intro hlen) (h hlen).1,
                    pure_elim_l fun hlen => and_intro (BI.pure_intro hlen) (h hlen).2⟩

theorem bigSepL2_sepL_2 {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ⊢ bigSepL Φ2 l2 -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) :=
  wand_intro <| (sep_mono_l persistent_and_affinely_sep_l.1).trans sep_assoc.1
    |>.trans persistent_and_affinely_sep_l.symm.1 |>.trans sepL.2

theorem bigSepL2_reverse_2 {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) ⊢
      ([∗list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) := by
  refine (and_self.2.trans (and_mono_l bigSepL2_length)).trans (pure_elim_l fun hlen => ?_)
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp only [bigSepL2, List.reverse_nil] <;> first | exact .rfl | simp at hlen
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons x2 xs2 =>
      simp only [List.length_cons] at hlen
      simp only [bigSepL2, List.reverse_cons]
      exact sep_comm.1.trans (sep_mono_l (ih (Nat.succ.inj hlen))) |>.trans bigSepL2_snoc.2

theorem reverse {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) ⊣⊢
      ([∗list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) := by
  refine ⟨?_, bigSepL2_reverse_2⟩; have := bigSepL2_reverse_2 (Φ := Φ) (l1 := l1.reverse) (l2 := l2.reverse)
  simp only [List.reverse_reverse] at this; exact this

theorem bigSepL2_replicate_left {Φ : Nat → A → B → PROP} {l : List B} {x : A} :
    ([∗list] k ↦ x1;x2 ∈ List.replicate l.length x;l, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x2 => Φ k x x2) l :=
  match l with | [] => .rfl | _ :: _ => sep_congr .rfl bigSepL2_replicate_left

theorem bigSepL2_replicate_right {Φ : Nat → A → B → PROP} {l : List A} {x : B} :
    ([∗list] k ↦ x1;x2 ∈ l;List.replicate l.length x, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x1 => Φ k x1 x) l :=
  match l with | [] => .rfl | _ :: _ => sep_congr .rfl bigSepL2_replicate_right

theorem bigSepL2_app_same_length {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      (([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
         [∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (l1a.length + k) x1 x2) :=
  (bigSepL2_app hlen).trans (sep_congr .rfl
  (bigSepL2_equiv_of_forall_equiv (by simp only [Nat.add_comm]; exact .rfl)))

theorem bigSepL2_const_sepL_left {Φ : Nat → A → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;_x2 ∈ l1;l2, Φ k x1) ⊣⊢ (⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
  have fst_zip : ∀ hlen : l1.length = l2.length, (l1.zip l2).map Prod.fst = l1 := by
    intro hlen; induction l1 generalizing l2 with
    | nil => cases l2 <;> first | rfl | simp at hlen
    | cons _ _ ih => cases l2 with
      | nil => simp at hlen
      | cons _ _ => simp [ih (by simpa using hlen)]
  refine bigSepL2_alt.trans ⟨pure_elim_l fun hlen => and_intro (BI.pure_intro hlen) ?_,
                    pure_elim_l fun hlen => and_intro (BI.pure_intro hlen) ?_⟩ <;> {
    have h : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
      equiv_iff.mp (BigSepL.bigSepL_map Prod.fst)
    rw [fst_zip hlen] at h; first | exact h.1 | exact h.2 }

theorem bigSepL2_const_sepL_right {Φ : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ _x1;x2 ∈ l1;l2, Φ k x2) ⊣⊢ (⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) :=
  bigSepL2_flip.trans bigSepL2_const_sepL_left |>.trans
  ⟨and_mono (pure_mono Eq.symm) .rfl, and_mono (pure_mono Eq.symm) .rfl⟩

theorem bigSepL2_sep_sepL_left [BIAffine PROP] {Φ : Nat → A → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2) ⊣⊢
      (bigSepL Φ l1 ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  refine bigSepL2_sep_equiv.trans (sep_congr_l bigSepL2_const_sepL_left) |>.trans ⟨sep_mono and_elim_r .rfl, ?bwd⟩
  refine (sep_mono_r <| (and_intro bigSepL2_length .rfl).trans persistent_and_affinely_sep_l.1 |>.trans
    (sep_mono_l affinely_elim)).trans sep_assoc.2 |>.trans (sep_mono_l ?_)
  exact and_intro (sep_comm.1.trans (sep_mono_l persistently_intro) |>.trans
    persistently_absorb_l |>.trans persistently_elim) sep_elim_l

theorem bigSepL2_sep_sepL_right [BIAffine PROP] {Φ : Nat → B → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x2 ∗ Ψ k x1 x2) ⊣⊢ (bigSepL Φ l2 ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  (bigSepL2_equiv_of_forall_equiv sep_comm).trans bigSepL2_flip |>.trans
    ((bigSepL2_equiv_of_forall_equiv sep_comm).trans bigSepL2_sep_sepL_left) |>.trans (sep_congr_r bigSepL2_flip)

theorem bigSepL2_delete_cond {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      (Φ i x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ l1;l2, if k = i then emp else Φ k y1 y2) := by
  induction l1 generalizing l2 i Φ with
  | nil => simp at h1
  | cons z1 zs1 ih => cases l2 with
    | nil => simp at h2
    | cons z2 zs2 => cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1; subst h2
        exact sep_congr_r <| (bigSepL2_equiv fun _ _ => .rfl).trans emp_sep.symm
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact (sep_congr_r (ih h1 h2)).trans sep_left_comm |>.trans
          (sep_congr_r (sep_congr_r (bigSepL2_equiv fun _ _ =>
            by simp only [Nat.add_right_cancel_iff]; exact .rfl)))

theorem bigSepL2_delete [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ l1;l2, ⌜k ≠ i⌝ → Φ k y1 y2) :=
  (bigSepL2_delete_cond h1 h2).trans <| sep_congr .rfl <| bigSepL2_equiv_of_forall_equiv fun {k y1 y2} => by
    by_cases hki : k = i
    · subst hki; simp only [↓reduceIte, ne_eq, not_true_eq_false]
      exact ⟨imp_intro' ((pure_elim_l (fun hf => False.elim hf)).trans .rfl), Affine.affine⟩
    · simp only [hki, ↓reduceIte, ne_eq, not_false_eq_true]; exact true_imp.symm

theorem bigSepL2_lookup_acc_impl {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      (Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
        (⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
          Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
  refine (bigSepL2_delete_cond h1 h2).1.trans (sep_mono_r <| BI.forall_intro fun Ψ => wand_intro <| wand_intro ?_)
  refine sep_comm.1.trans (sep_mono_r ?_) |>.trans (bigSepL2_delete_cond h1 h2).2
  have himpl := bigSepL2_impl (Φ := fun k y1 y2 => if k = i then emp else Φ k y1 y2)
                     (Ψ := fun k y1 y2 => if k = i then emp else Ψ k y1 y2) (l1 := l1) (l2 := l2)
  refine (sep_mono_r ?_).trans (wand_elim himpl)
  refine intuitionistically_intro' <| BI.forall_intro fun k => BI.forall_intro fun y1 =>
    BI.forall_intro fun y2 =>
    imp_intro' <| pure_elim_l fun hk1 => imp_intro' <| pure_elim_l fun hk2 => ?_
  by_cases hki : k = i
  · subst hki; simp only []
    exact wand_intro (sep_emp.1.trans Affine.affine)
  · simp only [hki]
    exact intuitionistically_elim.trans <|
      (BI.forall_elim k).trans ((BI.forall_elim y1).trans (BI.forall_elim y2))
      |>.trans ((and_intro (BI.pure_intro hk1) .rfl).trans imp_elim_r)
      |>.trans ((and_intro (BI.pure_intro hk2) .rfl).trans imp_elim_r)
      |>.trans ((and_intro (BI.pure_intro hki) .rfl).trans imp_elim_r)

theorem bigSepL2_sepL2_diag {Φ : Nat → A → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x x) ⊢ ([∗list] k ↦ x1; x2 ∈ l;l, Φ k x1 x2) := by
  have hzip : l.zip l = l.map (fun x => (x, x)) := by
    induction l with | nil => rfl | cons _ _ ih => simp [ih]
  have : bigSepL (fun k x => Φ k x x) l ⊣⊢ bigSepL (fun k p => Φ k p.1 p.2) (l.zip l) := by
    rw [hzip]
    exact (equiv_iff.mp (BigSepL.bigSepL_map (PROP := PROP) (Φ := fun k p => Φ k p.1 p.2)
      (fun x => (x, x)) (l := l))).symm
  exact (and_intro (pure_intro rfl) .rfl).trans (and_mono .rfl this.1) |>.trans BigSepL2.bigSepL2_alt.2

end BigSepL2

end BI
