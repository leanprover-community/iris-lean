/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.BigOp.BigOp
import Iris.BI.DerivedLawsLater
import Iris.BI.Instances
import Iris.Std.TC
meta import Iris.Std.RocqAlias

public section

namespace Iris.BI

open Iris.Algebra BigOpL Iris.Std BIBase

/-! # Big Separating Conjunction over Lists -/

private theorem list_split {A : Type _} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    l = l.take i ++ x :: l.drop (i + 1) := by
  have ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  have := List.take_append_drop (i + 1) l
  rw [List.take_succ_eq_append_getElem hi, hx, List.append_assoc] at this; exact this.symm

namespace BigSepL
variable {PROP : Type _} [BI PROP] {A : Type _}

@[simp, rocq_alias big_sepL_nil]
theorem bigSepL_nil {Φ : Nat → A → PROP} :
    ([∗list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ emp :=
  .rfl

@[rocq_alias big_sepL_nil']
theorem bigSepL_nil_intro {P : PROP} [Affine P] {Φ : Nat → A → PROP} :
    P ⊢ [∗list] k ↦ x ∈ ([] : List A), Φ k x :=
  Affine.affine.trans bigSepL_nil.2

@[rocq_alias big_sepL_cons]
theorem bigSepL_cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∗list] k ↦ y ∈ x :: xs, Φ k y) ⊣⊢ Φ 0 x ∗ [∗list] k ↦ y ∈ xs, Φ (k + 1) y :=
  .rfl

@[rocq_alias big_sepL_singleton]
theorem bigSepL_singleton {Φ : Nat → A → PROP} {x : A} :
    ([∗list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp <| bigOpL_singleton_equiv Φ x

@[rocq_alias big_sepL_app]
theorem bigSepL_append {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∗list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l₁, Φ k x) ∗ [∗list] k ↦ x ∈ l₂, Φ (k + l₁.length) x :=
  equiv_iff.mp <| bigOpL_append_equiv Φ l₁ l₂

@[rocq_alias big_sepL_snoc]
theorem bigSepL_snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∗list] k ↦ y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗list] k ↦ y ∈ l, Φ k y) ∗ Φ l.length x :=
  equiv_iff.mp <| bigOpL_snoc_equiv Φ l x

@[rocq_alias big_sepL_mono]
theorem bigSepL_mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_gen_proper (· ⊢ ·) .rfl sep_mono (h ·)

@[rocq_alias big_sepL_proper]
theorem bigSepL_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_equiv h

theorem bigSepL_equiv_of_forall_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_equiv_of_forall_equiv h

@[rocq_alias big_sepL_ne]
theorem bigSepL_dist {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat}
    (h : ∀ {k x}, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_dist h

theorem bigSepL_mono_of_forall {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x :=
  bigSepL_mono fun _ => h

@[rocq_alias big_sepL_flip_mono]
theorem bigSepL_flip_mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Ψ k x ⊢ Φ k x) :
    ([∗list] k ↦ x ∈ l, Ψ k x) ⊢ [∗list] k ↦ x ∈ l, Φ k x :=
  bigSepL_mono fun _ => h

@[rocq_alias big_sepL_id_mono]
theorem bigSepL_id_mono {Ps Qs : List PROP} (hlen : Ps.length = Qs.length)
    (h : ∀ (i : Nat) (P Q : PROP), Ps[i]? = some P → Qs[i]? = some Q → P ⊢ Q) :
    ([∗list] P ∈ Ps, P) ⊢ [∗list] Q ∈ Qs, Q :=
  bigOpL_gen_proper_2 (· ⊢ ·) .rfl sep_mono hlen (h _ _ _ · ·)

@[rocq_alias big_sepL_persistent_id]
theorem bigSepL_persistent_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Persistent P) :
    Persistent ([∗list] P ∈ Ps, P) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2)
    (fun hget => (hPs _ (List.mem_iff_getElem?.mpr ⟨_, hget⟩)).persistent)

@[rocq_alias big_sepL_persistent]
theorem bigSepL_persistent {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2)
    (fun hget => (h _ _ hget).persistent)

@[rocq_alias big_sepL_nil_persistent]
instance bigSepL_nil_persistent {Φ : Nat → A → PROP} :
    Persistent ([∗list] k ↦ x ∈ ([] : List A), Φ k x) where
  persistent := by simpa only [bigOpL] using Persistent.persistent

@[rocq_alias big_sepL_persistent']
instance bigSepL_persistent_inst {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) :=
  bigSepL_persistent fun _ => inferInstance

@[rocq_alias big_sepL_affine_id]
theorem bigSepL_affine_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Affine P) :
    Affine ([∗list] P ∈ Ps, P) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1)
    (fun hget => (hPs _ (List.mem_iff_getElem?.mpr ⟨_, hget⟩)).affine)

@[rocq_alias big_sepL_nil_affine]
instance bigSepL_nil_affine_inst {Φ : Nat → A → PROP} :
    Affine ([∗list] k ↦ x ∈ ([] : List A), Φ k x) where
  affine := by simpa only [bigOpL] using Affine.affine

@[rocq_alias big_sepL_affine]
theorem bigSepL_affine {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ {k x}, l[k]? = some x → Affine (Φ k x)) :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (fun hget => (h hget).affine)

@[rocq_alias big_sepL_affine']
instance bigSepL_affine_inst {Φ : Nat → A → PROP} {l : List A} [∀ k x, Affine (Φ k x)] :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) :=
  bigSepL_affine fun _ => inferInstance

@[rocq_alias big_sepL_timeless_id]
theorem bigSepL_timeless_id [Timeless (emp : PROP)] {Ps : List PROP}
    (hPs : ∀ {P}, P ∈ Ps → Timeless P) :
    Timeless ([∗list] P ∈ Ps, P) where
  timeless := bigOpL_closed (P := fun Q => ▷ Q ⊢ ◇ Q) Timeless.timeless
    (fun hx hy => later_sep.1.trans ((sep_mono hx hy).trans except0_sep.2))
    (fun hget => hPs (List.mem_iff_getElem?.mpr ⟨_, hget⟩) |>.timeless)

@[rocq_alias big_sepL_timeless]
theorem bigSepL_timeless [Timeless (emp : PROP)] {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ {k x}, l[k]? = some x → Timeless (Φ k x)) :
    Timeless ([∗list] k ↦ x ∈ l, Φ k x) where
  timeless := bigOpL_closed (P := fun Q => ▷ Q ⊢ ◇ Q) Timeless.timeless
    (fun hx hy => later_sep.1.trans ((sep_mono hx hy).trans except0_sep.2))
    (h ·|>.timeless)

@[rocq_alias big_sepL_nil_timeless]
instance bigSepL_nil_timeless_inst [Timeless (emp : PROP)] {Φ : Nat → A → PROP} :
    Timeless ([∗list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by simpa only [bigOpL] using Timeless.timeless

@[rocq_alias big_sepL_timeless']
instance bigSepL_timeless_inst [Timeless (emp : PROP)] {Φ : Nat → A → PROP} {l : List A}
    [∀ {k x}, Timeless (Φ k x)] :
    Timeless ([∗list] k ↦ x ∈ l, Φ k x) :=
  bigSepL_timeless fun _ => inferInstance

@[rocq_alias big_sepL_emp]
theorem bigSepL_emp {l : List A} :
    ([∗list] _x ∈ l, (emp : PROP)) ⊣⊢ emp :=
  equiv_iff.mp <| bigOpL_const_unit_equiv

@[rocq_alias big_sepL_sep]
theorem bigSepL_sep_equiv {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x) ⊣⊢ ([∗list] k ↦ x ∈ l, Φ k x) ∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  equiv_iff.mp <| bigOpL_op_equiv Φ Ψ l

@[deprecated "bigSepL_sep_equiv.symm" (since := "26/03/30"), rocq_alias big_sepL_sep_2]
theorem bigSepL_sep_equiv_symm {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ∗ ([∗list] k ↦ x ∈ l, Ψ k x) ⊣⊢ [∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x :=
  bigSepL_sep_equiv.symm

@[rocq_alias big_sepL_and]
theorem bigSepL_and {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∧ Ψ k x) ⊢ ([∗list] k ↦ x ∈ l, Φ k x) ∧ [∗list] k ↦ x ∈ l, Ψ k x :=
  and_intro (bigSepL_mono fun _ => and_elim_l) (bigSepL_mono fun _ => and_elim_r)

@[rocq_alias big_sepL_wand]
theorem bigSepL_wand {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ([∗list] k ↦ x ∈ l, Φ k x -∗ Ψ k x) -∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  wand_intro <| bigSepL_sep_equiv.symm.1.trans <| bigSepL_mono fun _ => wand_elim_r

@[rocq_alias big_sepL_pure_1]
theorem bigSepL_pure_intro {φ : Nat → A → Prop} {l : List A}:
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  match l with
  | [] => pure_intro fun _ _ h => nomatch h
  | _ :: _ =>
    (sep_mono_r bigSepL_pure_intro).trans <| sep_and.trans <| pure_and.1.trans <| pure_mono
      fun ⟨hy, hys⟩ k x hget => match k with
        | 0 => Option.some.inj hget ▸ hy
        | k + 1 => hys k x hget

@[rocq_alias big_sepL_affinely_pure_2]
theorem bigSepL_affinely_pure_elim {φ : Nat → A → Prop} {l : List A} :
    (<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) ⊢
      ([∗list] k ↦ x ∈ l, <affine> ⌜φ k x⌝ : PROP) :=
  match l with
  | [] => affinely_elim_emp
  | _ :: _ =>
    (affinely_mono <| pure_mono fun h => ⟨h 0 _ rfl, fun k x hget => h (k + 1) x hget⟩).trans <|
    (affinely_mono pure_and.2).trans <| affinely_and.1.trans <|
    persistent_and_sep_1.trans <| sep_mono_r bigSepL_affinely_pure_elim

@[rocq_alias big_sepL_pure]
theorem bigSepL_pure [BIAffine PROP] {φ : Nat → A → Prop} {l : List A} :
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊣⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨bigSepL_pure_intro,
   (affine_affinely _).2.trans <|
    bigSepL_affinely_pure_elim.trans (bigSepL_mono fun _ => affinely_elim)⟩

@[rocq_alias big_sepL_take_drop]
theorem bigSepL_take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l.take n, Φ k x) ∗ [∗list] k ↦ x ∈ l.drop n, Φ (n + k) x :=
  equiv_iff.mp (bigOpL_take_drop_equiv Φ l n)

@[rocq_alias big_sepL_fmap]
theorem bigSepL_map {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∗list] k ↦ y ∈ l.map f, Φ k y) ≡ [∗list] k ↦ x ∈ l, Φ k (f x) :=
  bigOpL_map_equiv f Φ l

@[rocq_alias big_sepL_omap]
theorem bigSepL_filterMap {B : Type _} (f : A → Option B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.filterMap f, Φ y) ≡ [∗list] x ∈ l, (f x).elim emp Φ :=
  bigOpL_filterMap_equiv f Φ l

@[rocq_alias big_sepL_bind]
theorem bigSepL_flatMap {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.flatMap f, Φ y) ≡ [∗list] x ∈ l, [∗list] y ∈ f x, Φ y :=
  bigOpL_flatMap_equiv f Φ l

@[rocq_alias big_sepL_lookup_acc]
theorem bigSepL_lookup_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) :=
  match l, i, h with
  | _ :: _, 0, h => Option.some.inj (List.getElem?_cons_zero ▸ h) ▸
      ⟨sep_mono_r (forall_intro fun y => wand_intro sep_comm.1),
       (sep_mono_r (forall_elim _)).trans wand_elim_r⟩
  | _ :: _, _ + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    refine ⟨?_, ?_⟩
    · refine (sep_mono_r (bigSepL_lookup_acc h).1).trans <| sep_assoc.2.trans <|
      (sep_mono_l sep_comm.1).trans <| sep_assoc.1.trans <| sep_mono_r ?_
      refine forall_intro fun y => wand_intro <| sep_assoc.1.trans <| sep_mono_r <|
      (sep_mono_l (forall_elim y)).trans <| sep_comm.1.trans wand_elim_r
    · refine (sep_mono_r (forall_elim x)).trans <| ?_
      have hset := (List.getElem?_eq_some_iff.mp h).2 ▸
        List.set_getElem_self (List.getElem?_eq_some_iff.mp h).1
      simpa only [List.set_cons_succ, hset, bigOpL_cons] using wand_elim_r

@[rocq_alias big_sepL_lookup]
theorem bigSepL_lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    [TCOr (∀ k y, Affine (Φ k y)) (Absorbing (Φ i x))] → ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x
  | TCOr.l => by
    rw [list_split h]
    refine bigSepL_append.1.trans <| sep_elim_r.trans ?_
    simpa [List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp h).1)] using sep_elim_l
  | TCOr.r => (bigSepL_lookup_acc h).1.trans sep_elim_l

@[rocq_alias big_sepL_insert_acc]
theorem bigSepL_insert_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) :=
  (bigSepL_lookup_acc h).1

@[rocq_alias big_sepL_elem_of_acc]
theorem bigSepL_mem_acc {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    ([∗list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗list] y ∈ l, Φ y) := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h ; subst hget
  refine (bigSepL_lookup_acc <| List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩).1.trans <|
   sep_mono_r <| (forall_elim l[i]).trans <| wand_mono .rfl ?_
  simp [List.set_getElem_self hi]

@[rocq_alias big_sepL_elem_of]
theorem bigSepL_mem {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] → ([∗list] y ∈ l, Φ y) ⊢ Φ x
  | TCOr.l | TCOr.r =>
    let ⟨_, hi, hget⟩ := List.mem_iff_getElem.mp h
    bigSepL_lookup <| List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩

@[rocq_alias big_sepL_delete]
theorem bigSepL_delete_cond {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ [∗list] k ↦ y ∈ l, if k = i then emp else Φ k y := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons z zs ih => cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      exact sep_congr_r <| (equiv_iff.mp (bigSepL_equiv fun _ => equiv_iff.mpr .rfl)).trans emp_sep.symm
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact ((sep_congr_r <| ih h).trans sep_left_comm).trans <|
        sep_congr_r <| sep_congr_r <| equiv_iff.mp <|
        bigSepL_equiv fun _ => equiv_iff.mpr <| by simp [Nat.add_right_cancel_iff]

@[rocq_alias big_sepL_delete']
theorem bigSepL_delete [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y := by
  refine (bigSepL_delete_cond h).trans <|
    sep_congr_r <| equiv_iff.mp <| bigSepL_equiv fun {k _} _ => equiv_iff.mpr ?_
  by_cases hki : k = i <;> simp only [hki, ne_eq, not_true_eq_false, not_false_eq_true]
  · exact ⟨imp_intro' <| pure_elim_l fun hf => hf.elim, Affine.affine⟩
  · exact true_imp.symm

@[rocq_alias big_sepL_intro]
theorem bigSepL_intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} [Intuitionistic P]
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact intuitionistic.trans affinely_elim_emp
  | cons y ys ih =>
    exact intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
      sep_mono (intuitionistically_elim.trans <| h 0 y rfl)
               (intuitionistically_elim.trans <| ih fun k x hget => h (k + 1) x hget)

theorem bigSepL_forall_intro {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  forall_intro fun _ => forall_intro fun _ => imp_intro' <| pure_elim_l fun hget =>
    (bigSepL_lookup_acc hget).1.trans <| (sep_mono_l Persistent.persistent).trans <|
      sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

theorem bigSepL_forall_elim {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x)) ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Affine.affine
  | cons y ys ih =>
    refine (and_self.2.trans <| and_mono_l ?_).trans persistent_and_sep_1 |>.trans <| sep_mono_r <| ?_
    exact ((forall_elim 0).trans <| forall_elim y).trans <| (and_intro (pure_intro rfl) .rfl).trans imp_elim_r
    exact (forall_intro fun k => forall_intro fun z => (forall_elim (k + 1)).trans (forall_elim z)).trans ih

@[rocq_alias big_sepL_forall]
theorem bigSepL_forall_equiv {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  ⟨bigSepL_forall_intro, bigSepL_forall_elim⟩

@[rocq_alias big_sepL_impl]
theorem bigSepL_impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢
      □ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) -∗ [∗list] k ↦ x ∈ l, Ψ k x := by
  refine wand_intro <| (sep_mono_r ?_).trans <| bigSepL_sep_equiv.symm.1.trans <|
    bigSepL_mono fun _ => wand_elim_r
  exact bigSepL_intro fun k x hget => intuitionistically_elim.trans <|
    ((forall_elim k).trans <| forall_elim x).trans <| (imp_mono_l <| pure_mono fun _ => hget).trans true_imp.1

@[rocq_alias big_sepL_lookup_acc_impl]
theorem bigSepL_lookup_acc_impl {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    iprop([∗list] k ↦ x ∈ l, Φ k x) ⊢
      Φ i x ∗ ∀ (Ψ: Nat → A → PROP), □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
        Ψ i x -∗  ([∗list] k ↦ x ∈ l, Ψ k x) := by
  refine (bigSepL_delete_cond h).1.trans <| sep_mono_r <| forall_intro fun Ψ => wand_intro <| wand_intro ?_
  refine sep_comm.1.trans <| (sep_mono_r ?_).trans (bigSepL_delete_cond h).2
  refine (sep_mono_r <| bigSepL_intro (Φ := fun k y => if k = i then emp else iprop(Φ k y -∗ Ψ k y))
    fun k y hget => ?_).trans <| bigSepL_sep_equiv.symm.1.trans <| bigSepL_mono fun {k _} hget => by
    by_cases hki : k = i <;> simp only [hki, ite_true, ite_false]
    · exact emp_sep.1
    · exact wand_elim_r
  by_cases hki : k = i
  · subst hki; simp only [ite_true]
    exact Intuitionistic.intuitionistic.trans affinely_elim_emp
  · simp only [show (k = i) = False from eq_false hki, ite_false]
    exact intuitionistically_elim.trans <| ((forall_elim k).trans <| forall_elim y).trans <|
          ((and_intro (pure_intro hget) .rfl).trans imp_elim_r).trans <|
          ((and_intro (pure_intro hki) .rfl).trans imp_elim_r)

@[rocq_alias big_sepL_persistently]
theorem bigSepL_persistently {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    (<pers> [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, <pers> Φ k x :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) persistently_ne
    (equiv_iff.mpr persistently_sep) (equiv_iff.mpr persistently_emp')
  equiv_iff.mp <| bigOpL_hom  Φ l

@[rocq_alias big_sepL_later]
theorem bigSepL_later [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} :
    (▷ [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷ Φ k x :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) later_ne
    (equiv_iff.mpr later_sep) (equiv_iff.mpr later_emp)
  equiv_iff.mp <| bigOpL_hom  Φ l

@[rocq_alias big_sepL_later_2]
theorem bigSepL_later_2 {Φ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, ▷ Φ k x) ⊢ iprop(▷ [∗list] k ↦ x ∈ l, Φ k x) :=
  bigOpL_gen_proper (fun a b => a ⊢ ▷ b) later_intro
    (fun h1 h2 => (sep_mono h1 h2).trans later_sep.2) (fun _ => .rfl)

@[rocq_alias big_sepL_laterN]
theorem bigSepL_laterN [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    (▷^[n] [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷^[n] Φ k x :=
  match n with | 0 => .rfl | _ + 1 => (later_congr bigSepL_laterN).trans bigSepL_later

@[rocq_alias big_sepL_laterN_2]
theorem bigSepL_laterN_2 {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, ▷^[n] Φ k x) ⊢ (▷^[n] [∗list] k ↦ x ∈ l, Φ k x) :=
  match n with | 0 => .rfl | _ + 1 => bigSepL_later_2.trans <| later_mono bigSepL_laterN_2

theorem bigSepL_perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∗list] x ∈ l₁, Φ x) ⊣⊢ [∗list] x ∈ l₂, Φ x :=
  equiv_iff.mp <| bigOpL_equiv_of_perm Φ hp

@[rocq_alias big_sepL_submseteq]
theorem bigSepL_submseteq {Φ : A → PROP} [∀ x, Affine (Φ x)] {l₁ l₂ l : List A} (h : (l₁ ++ l).Perm l₂) :
    ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₁, Φ x :=
  (bigSepL_perm h).2.trans <| bigSepL_append.1.trans sep_elim_l

@[rocq_alias big_sepL_dup]
theorem bigSepL_dup {P : PROP} [Affine P] {l : List A} : □ (P -∗ P ∗ P) ∗ P ⊢ ([∗list] _x ∈ l, P) :=
  match l with
  | [] => sep_elim_r.trans Affine.affine
  | _ :: _ =>
    (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      sep_assoc.2.trans <| (sep_mono_l bigSepL_dup).trans sep_comm.1

@[rocq_alias big_sepL_replicate]
theorem bigSepL_replicate {P : PROP} {l : List A} :
    ([∗list] _x ∈ List.replicate l.length P, P) ⊣⊢ [∗list] _x ∈ l, P :=
  match l with | [] => .rfl | _ :: _ => ⟨sep_mono_r bigSepL_replicate.1, sep_mono_r bigSepL_replicate.2⟩

@[rocq_alias big_sepL_zip_seq]
theorem bigSepL_zip_seq {Φ : A × Nat → PROP} {n : Nat} {l : List A} :
    ([∗list] xy ∈ l.zipIdx n, Φ xy) ⊣⊢ [∗list] i ↦ x ∈ l, Φ (x, n + i) :=
  equiv_iff.mp <| bigOpL_zipIdx_equiv Φ n l

@[rocq_alias big_sepL_sep_zip]
theorem bigSepL_sep_zip {B : Type _} {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP}
    {l₁ : List A} {l₂ : List B} (hlen : l₁.length = l₂.length) :
    ([∗list] i ↦ xy ∈ l₁.zip l₂, Φ i xy.1 ∗ Ψ i xy.2) ⊣⊢
      ([∗list] i ↦ x ∈ l₁, Φ i x) ∗ [∗list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil => cases l₂ with | nil => exact emp_sep.symm | cons => simp at hlen
  | cons _ _ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons _ _ => exact (sep_congr_r <| ih (by simpa using hlen)).trans sep_sep_sep_comm

@[rocq_alias big_sepL_sep_zip_with]
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
      exact (sep_congr_r <| ih hlen).trans sep_sep_sep_comm

@[rocq_alias big_sepL_zip_with]
theorem bigSepL_zip_with {B C : Type _} (f : A → B → C) {Φ : Nat → C → PROP}
    {l₁ : List A} {l₂ : List B} :
    ([∗list] k ↦ c ∈ List.zipWith f l₁ l₂, Φ k c) ⊣⊢
      [∗list] k ↦ x ∈ l₁, match l₂[k]? with | some y => Φ k (f x y) | none => emp := by
  induction l₁ generalizing l₂ Φ with
  | nil => exact .rfl
  | cons _ _ ih =>
    cases l₂ with
    | nil => exact emp_sep.symm.trans <| sep_congr_r bigSepL_emp.symm
    | cons _ _ => exact sep_congr_r ih

@[rocq_alias big_sepL_sepL]
theorem bigSepL_comm {B : Type _} (Φ : Nat → A → Nat → B → PROP) (l₁ : List A) (l₂ : List B) :
    ([∗list] k1↦x1 ∈ l₁, [∗list] k2↦x2 ∈ l₂, Φ k1 x1 k2 x2) ⊣⊢
      ([∗list] k2↦x2 ∈ l₂, [∗list] k1↦x1 ∈ l₁, Φ k1 x1 k2 x2) :=
  match l₁ with
  | [] => ⟨(equiv_iff.mp bigOpL_const_unit_equiv).2, (equiv_iff.mp bigOpL_const_unit_equiv).1⟩
  | _ :: _ =>
    let ih := bigSepL_comm (fun i a j b => Φ (i + 1) a j b) _ l₂
    ⟨(sep_mono_r ih.1).trans (equiv_iff.mp (bigOpL_op_equiv _ _ _)).2,
     (equiv_iff.mp (bigOpL_op_equiv _ _ _)).1.trans (sep_mono_r ih.2)⟩

-- TODO: missing and blocked: big_sepL_sepM, big_sepL_sepMS, big_sepL_sepS

end BigSepL

/-! # Big Separating Conjunction over Two Lists -/
namespace BigSepL2

variable {PROP : Type _} [BI PROP] {A B : Type _}

@[simp, rocq_alias big_sepL2_nil]
theorem bigSepL2_nil {Φ : Nat → A → B → PROP} :
    ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') ⊣⊢ emp := .rfl

@[rocq_alias big_sepL2_nil']
theorem bigSepL2_nil_affine {P : PROP} [Affine P] {Φ : Nat → A → B → PROP} :
    P ⊢ ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') :=
  Affine.affine.trans bigSepL2_nil.2

@[rocq_alias big_sepL2_nil_inv_l]
theorem bigSepL2_nil_inv_left {Φ : Nat → A → B → PROP} {l2 : List B} :
   ([∗list] k ↦ x;x' ∈ [];l2, Φ k x x')  ⊢ ⌜l2 = []⌝ :=
  match l2 with | .nil => pure_intro rfl | .cons _ _ => false_elim

@[rocq_alias big_sepL2_nil_inv_r]
theorem bigSepL2_nil_inv_right {Φ : Nat → A → B → PROP} {l1 : List A} :
    ([∗list] k ↦ x;x' ∈ l1;[], Φ k x x') ⊢ ⌜l1 = []⌝ :=
  match l1 with | .nil => pure_intro rfl | .cons _ _ => false_elim

@[rocq_alias big_sepL2_cons]
theorem bigSepL2_cons {Φ : Nat → A → B → PROP} {x1 : A} {x2 : B} {xs1 : List A} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2 := .rfl

@[rocq_alias big_sepL2_cons_inv_l]
theorem bigSepL2_cons_inv_left {Φ : Nat → A → B → PROP} {x1 : A} {xs1 : List A} {l2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;l2, Φ k y1 y2) ⊣⊢
      ∃ x2 xs2, ⌜l2 = x2 :: xs2⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) :=
  match l2 with
  | [] => ⟨false_elim, exists_elim fun _ => exists_elim fun _ =>
      and_elim_l.trans (pure_elim' (nomatch ·))⟩
  | _ :: _ =>
    ⟨(and_intro (pure_intro rfl) .rfl).trans (exists_intro' _ (exists_intro' _ .rfl)),
     exists_elim fun _ => exists_elim fun _ => pure_elim_l fun h => by cases h; exact .rfl⟩

@[rocq_alias big_sepL2_cons_inv_r]
theorem bigSepL2_cons_inv_right {Φ : Nat → A → B → PROP} {l1 : List A} {x2 : B} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ l1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      ∃ x1 xs1, ⌜l1 = x1 :: xs1⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) :=
  match l1 with
  | [] => ⟨false_elim, exists_elim fun _ => exists_elim fun _ =>
      and_elim_l.trans (pure_elim' (nomatch ·))⟩
  | _ :: _ =>
    ⟨(and_intro (pure_intro rfl) .rfl).trans (exists_intro' _ (exists_intro' _ .rfl)),
     exists_elim fun _ => exists_elim fun _ => pure_elim_l fun h => by cases h; exact .rfl⟩

@[rocq_alias big_sepL2_singleton]
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
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ [∗list] k ↦ p ∈ (l1.zip l2), Φ k p.1 p.2  := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 <;> simp only [bigSepL2, List.zip_nil_left, bigOpL] <;>
           first | exact .rfl | exact false_elim
  | cons _ _ ih => cases l2 with
    | nil => exact false_elim
    | cons _ _ => exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)))

private theorem bigSepL2_alt_bwd {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hlen : l1.length = l2.length) :
    ([∗list] k ↦ p ∈ (l1.zip l2), Φ k p.1 p.2) ⊢ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 <;> first | exact .rfl | simp at hlen
  | cons _ _ ih => cases l2 with
    | nil => simp at hlen
    | cons _ _ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) hlen)

@[rocq_alias big_sepL2_alt]
theorem bigSepL2_alt {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) :=
  ⟨and_intro bigSepL2_alt_len bigSepL2_alt_fwd, pure_elim_l bigSepL2_alt_bwd⟩

@[rocq_alias big_sepL2_length]
theorem bigSepL2_length {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ iprop(⌜l1.length = l2.length⌝) :=
  bigSepL2_alt.1.trans and_elim_l

@[rocq_alias big_sepL2_mono]
theorem bigSepL2_mono {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_mono (h rfl rfl) (bigSepL2_mono fun {k} => @h (k + 1))

@[rocq_alias big_sepL2_proper]
theorem bigSepL2_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  ⟨bigSepL2_mono fun h1 h2 => (h h1 h2).1, bigSepL2_mono fun h1 h2 => (h h1 h2).2⟩

theorem bigSepL2_equiv_of_forall_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  bigSepL2_equiv fun _ _ => h

@[rocq_alias big_sepL2_ne]
theorem bigSepL2_dist {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ≡{n}≡ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_ne.ne (h rfl rfl) (bigSepL2_dist fun {k} => @h (k + 1))

@[rocq_alias big_sepL2_flip_mono]
theorem bigSepL2_mono_of_forall {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  bigSepL2_mono (fun _ _ => h)

@[rocq_alias big_sepL2_closed]
theorem bigSepL2_closed {P : PROP → Prop} {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hemp : P emp) (hfalse : P iprop(False))
    (hsep : ∀ {Q1 Q2}, P Q1 → P Q2 → P (sep Q1 Q2))
    (hf : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → P (Φ k x1 x2)) :
    P ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  match l1, l2 with
  | [], [] => hemp
  | [], _ :: _ | _ :: _, [] => hfalse
  | _ :: _, _ :: _ => hsep (hf (List.getElem?_cons_zero .. ▸ rfl) (List.getElem?_cons_zero .. ▸ rfl))
      (bigSepL2_closed hemp hfalse hsep fun h1 h2 => hf h1 h2)

@[rocq_alias big_sepL2_nil_persistent]
instance bigSepL2_nil_persistent_inst {Φ : Nat → A → B → PROP} :
    Persistent ([∗list] k ↦ x1;x2 ∈ ([] : List A);([] : List B), Φ k x1 x2) where
  persistent := by simp only [bigSepL2]; exact Persistent.persistent

@[rocq_alias big_sepL2_persistent]
theorem bigSepL2_persistent {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Persistent (Φ k x1 x2)) :
    Persistent ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  persistent := bigSepL2_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (false_elim.trans (persistently_mono false_elim))
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2)
    (fun h1 h2 => (h _ _ _ h1 h2).persistent)

@[rocq_alias big_sepL2_persistent']
instance bigSepL2_persistent_inst {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  bigSepL2_persistent (fun _ _ => inferInstance)

@[rocq_alias big_sepL2_nil_affine]
instance bigSepL2_nil_affine_inst {Φ : Nat → A → B → PROP} :
    Affine ([∗list] k ↦ x1;x2 ∈ ([] : List A);([] : List B), Φ k x1 x2) where
  affine := by simp only [bigSepL2]; exact Affine.affine

@[rocq_alias big_sepL2_affine]
theorem bigSepL2_affine {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ {k x1 x2}, l1[k]? = some x1 → l2[k]? = some x2 → Affine (Φ k x1 x2)) :
    Affine ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  affine := bigSepL2_closed (P := fun Q => Q ⊢ emp) .rfl false_elim
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1)
    (fun h1 h2 => (h h1 h2).affine)

@[rocq_alias big_sepL2_affine']
instance bigSepL2_affine_inst {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
    bigSepL2_affine (fun _ _ => inferInstance)

@[rocq_alias big_sepL2_nil_timeless]
instance bigSepL2_nil_timeless [Timeless (emp : PROP)] {Φ : Nat → A → B → PROP} :
    Timeless ([∗list] k ↦ x1;x2 ∈ ([] : List A);([] : List B), Φ k x1 x2) where
  timeless := by simp only [bigSepL2]; exact Timeless.timeless

@[rocq_alias big_sepL2_timeless]
theorem bigSepL2_timeless [Timeless (emp : PROP)] {Φ : Nat → A → B → PROP} {l1 : List A}
    {l2 : List B} (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Timeless (Φ k x1 x2)) :
    Timeless ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  timeless := bigSepL2_closed (P := fun Q => ▷ Q ⊢ ◇ Q) Timeless.timeless
    (or_intro_l (P := iprop(▷ False)).trans (or_mono (later_mono false_elim) false_elim))
    (fun hx hy => later_sep.1.trans ((sep_mono hx hy).trans except0_sep.2))
    (fun h1 h2 => (h _ _ _ h1 h2).timeless)

@[rocq_alias big_sepL2_timeless']
instance bigSepL2_timeless' [Timeless (emp : PROP)] {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List B} [∀ k x1 x2, Timeless (Φ k x1 x2)] :
    Timeless ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  bigSepL2_timeless fun _ _ _ _ _ => inferInstance

@[rocq_alias big_sepL2_sep]
theorem bigSepL2_sep_equiv {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 <;> simp only [bigSepL2] <;>
    first | exact emp_sep.symm | exact ⟨false_elim, sep_elim_l.trans false_elim⟩
  | cons _ _ ih => cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, sep_elim_l.trans false_elim⟩
    | cons _ _ => exact (sep_congr .rfl ih).trans sep_sep_sep_comm

@[rocq_alias big_sepL2_sep_2]
theorem bigSepL2_sep_equiv_symm {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) := bigSepL2_sep_equiv.symm

@[rocq_alias big_sepL2_and]
theorem bigSepL2_and {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∧ Ψ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∧ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  and_intro (bigSepL2_mono fun _ _ => and_elim_l) (bigSepL2_mono fun _ _ => and_elim_r)

@[rocq_alias big_sepL2_pure_1]
theorem bigSepL2_pure_intro {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊢
      iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  bigSepL2_alt.1.trans <| (and_mono .rfl BigSepL.bigSepL_pure_intro).trans <| pure_and.1.trans <|
  pure_mono fun ⟨_, h⟩ k x1 x2 h1 h2 => h k (x1, x2) (List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩)

@[rocq_alias big_sepL2_affinely_pure_2]
theorem bigSepL2_affinely_pure_elim {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    iprop(<affine> ⌜l1.length = l2.length ∧
      ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) := by
  refine (affinely_mono pure_and.2).trans <| affinely_and.1.trans <|
  (and_mono .rfl ?_).trans <| (and_mono affinely_elim .rfl).trans <|
  bigSepL2_alt.2
  exact (affinely_mono <| pure_mono fun h k (p : A × B) hp =>
          h k p.1 p.2 (List.getElem?_zip_eq_some.mp hp).1
        (List.getElem?_zip_eq_some.mp hp).2).trans BigSepL.bigSepL_affinely_pure_elim

@[rocq_alias big_sepL2_pure]
theorem bigSepL2_pure [BIAffine PROP] {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊣⊢
      iprop(⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  ⟨(and_intro bigSepL2_length bigSepL2_pure_intro).trans pure_and.1,
   ((affine_affinely _).2.trans bigSepL2_affinely_pure_elim).trans <|
   bigSepL2_mono fun _ _ => affinely_elim⟩

@[rocq_alias big_sepL2_app]
theorem bigSepL2_app_wand {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) -∗
      ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) := by
  refine wand_intro' ?_
  induction l1a generalizing l2a Φ with
  | nil => cases l2a with
    | nil => apply sep_emp.1
    | cons => apply sep_elim_r.trans false_elim
  | cons _ _ ih => cases l2a with
    | nil => apply sep_elim_r.trans false_elim
    | cons _ _ =>
      exact (sep_mono_l (bigSepL2_equiv_of_forall_equiv (by simp [Nat.add_assoc])).1).trans <|
      sep_symm.trans <| sep_assoc.1.trans <| (sep_mono_r sep_symm).trans <| sep_mono_r <|
      ih (Φ := fun n => Φ (n + 1))

private theorem bigSepL2_app_inv_core {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
        ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  induction l1a generalizing l2a Φ with
  | nil => cases l2a with
    | nil => apply emp_sep.2
    | cons y ys => cases hlen with
      | inl h => simp at h
      | inr h =>
        exact bigSepL2_alt_len.trans <| pure_elim' (by simp; omega)
  | cons x1 xs1 ih => cases l2a with
    | nil => cases hlen with
      | inl h => simp at h
      | inr h =>
        exact bigSepL2_alt_len.trans <| pure_elim' (by simp; omega)
    | cons x2 xs2 =>
      exact (sep_mono_r <| ih <| hlen.imp (by simp_all) id).trans sep_assoc.2

@[rocq_alias big_sepL2_app_inv]
theorem bigSepL2_append {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
        ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) :=
  ⟨bigSepL2_app_inv_core hlen, sep_symm.trans <| wand_elim' bigSepL2_app_wand⟩

@[rocq_alias big_sepL2_snoc]
theorem bigSepL2_snoc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {x : A} {y : B} :
    ([∗list] k ↦ x1;x2 ∈ l1 ++ [x];l2 ++ [y], Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ Φ l1.length x y :=
  Nat.zero_add l1.length ▸
  ((bigSepL2_append (l1b := [x]) (l2b := [y]) (Or.inr rfl)).trans <|
   sep_congr .rfl bigSepL2_singleton)

@[rocq_alias big_sepL2_fmap_l]
theorem bigSepL2_map_left {C : Type _} (f : C → A) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) y) := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil | cons => exact .rfl
  | cons _ _ ih => cases l2 with
    | nil => exact .rfl
    | cons _ _ => exact sep_congr .rfl ih

@[rocq_alias big_sepL2_fmap_r]
theorem bigSepL2_map_right {C : Type _} (f : C → B) {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List C} :
    ([∗list] k ↦ x;y ∈ l1;l2.map f, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x (f y)) := by
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil | cons => simp only [List.map_nil, List.map_cons]; exact .rfl
  | cons _ _ ih => cases l2 with
    | nil => exact .rfl
    | cons _ _ => exact sep_congr .rfl ih

theorem bigSepL2_map {C D : Type _} (f : C → A) (g : D → B)
    {Φ : Nat → A → B → PROP} {l1 : List C} {l2 : List D} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2.map g, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) (g y)) :=
    (bigSepL2_map_left f).trans <| bigSepL2_map_right g

@[rocq_alias big_sepL2_flip]
theorem bigSepL2_flip {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l2;l1, Φ k y x) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) :=
  match l1, l2 with
  | [], [] | [], _ :: _ | _ :: _, [] => .rfl
  | _ :: _, _ :: _ => sep_congr .rfl bigSepL2_flip

@[rocq_alias big_sepL2_fst_snd]
theorem bigSepL2_fst_snd {Φ : Nat → A → B → PROP} {l : List (A × B)} :
    ([∗list] k ↦ x;y ∈ l.map Prod.fst;l.map Prod.snd, Φ k x y) ⊣⊢
      [∗list] k ↦ p ∈ l, Φ k p.1 p.2 := by
  have h : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with | nil => rfl | cons _ _ ih => simp [ih]
  exact bigSepL2_alt.trans <| by simp only [List.length_map, h]; exact true_and

@[rocq_alias big_sepL2_app_inv_l]
theorem bigSepL2_app_inv_left {Φ : Nat → A → B → PROP} {l1' l1'' : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1' ++ l1'';l2, Φ k x1 x2) ⊢
      (∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧ (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l1'.length) x1 x2))) := by
  refine exists_intro' (l2.take l1'.length) <| exists_intro' (l2.drop l1'.length) <|
    and_intro (pure_intro (List.take_append_drop l1'.length l2).symm) ?_
  induction l1' generalizing l2 Φ with
  | nil => exact emp_sep.symm.1.trans <| sep_mono_l bigSepL2_nil.symm.1
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => exact false_elim
    | cons x2 xs2 =>
      exact (sep_mono_r ih).trans <| sep_assoc.symm.1.trans <|
        sep_mono_r <| bigSepL2_mono_of_forall .rfl

@[rocq_alias big_sepL2_app_inv_r]
theorem bigSepL2_app_inv_right {Φ : Nat → A → B → PROP} {l1 : List A} {l2' l2'' : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2' ++ l2'', Φ k x1 x2) ⊢
      (∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧ (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l2'.length) x1 x2))) :=
  bigSepL2_flip.symm.1.trans <| bigSepL2_app_inv_left.trans <|
  exists_mono fun _ => exists_mono fun _ => and_mono .rfl <|
  sep_mono bigSepL2_flip.1 bigSepL2_flip.1

private theorem zip_set {C D : Type _} {l1 : List C} {l2 : List D} {i : Nat}
    (hi1 : i < l1.length) (hi2 : i < l2.length) (y1 : C) (y2 : D) :
    (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2) := by
  apply List.ext_getElem?; intro k; simp only [List.getElem?_set]
  by_cases hik : i = k
  · subst hik; simp only [show i < (l1.zip l2).length from by simp only [List.length_zip]; omega]
    exact (List.getElem?_zip_eq_some.mpr ⟨List.getElem?_set_self hi1, List.getElem?_set_self hi2⟩).symm
  · simp [List.zip_eq_zipWith, List.getElem?_zipWith, hik]

@[rocq_alias big_sepL2_insert_acc]
theorem bigSepL2_insert_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ (Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗
        [∗list] k ↦ z1;z2 ∈ l1.set i y1;l2.set i y2, Φ k z1 z2)) := by
  have hi1 := (List.getElem?_eq_some_iff.mp h1).1
  have hi2 := (List.getElem?_eq_some_iff.mp h2).1
  refine bigSepL2_alt.1.trans <| pure_elim_l fun hlen => ?_
  have hzip : (l1.zip l2)[i]? = some (x1, x2) := List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩
  refine (BigSepL.bigSepL_insert_acc hzip).trans <| sep_mono_r <| forall_intro fun y1 =>
    forall_intro fun y2 => (forall_elim (y1, y2)).trans <| wand_mono_r ?_
  rw [zip_set hi1 hi2]; exact (and_intro (pure_intro (by simp [hlen])) .rfl).trans bigSepL2_alt.2

@[rocq_alias big_sepL2_lookup_acc]
theorem bigSepL2_lookup_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)) :=
  let ⟨hi1, hx1⟩ := List.getElem?_eq_some_iff.mp h1
  let ⟨hi2, hx2⟩ := List.getElem?_eq_some_iff.mp h2
  (bigSepL2_insert_acc h1 h2).trans <| sep_mono_r <| (forall_elim x1).trans <| (forall_elim x2).trans <|
    (hx1 ▸ List.set_getElem_self hi1).symm ▸ (hx2 ▸ List.set_getElem_self hi2).symm ▸ .rfl

@[rocq_alias big_sepL2_lookup]
theorem bigSepL2_lookup {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))] →
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2
  | TCOr.l => by
    have hi1 := (List.getElem?_eq_some_iff.mp h1).1
    rw [list_split h1, list_split h2]
    refine (bigSepL2_append (Or.inl ?_)).1.trans <| sep_elim_r.trans <| by
      simp only [List.length_take_of_le (Nat.le_of_lt hi1), bigSepL2, Nat.zero_add]; exact sep_elim_l
    exact (List.length_take_of_le (Nat.le_of_lt hi1)).trans <|
      (List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp h2).1)).symm
  | TCOr.r => (bigSepL2_lookup_acc h1 h2).trans sep_elim_l

@[rocq_alias big_sepL2_lookup_l]
theorem bigSepL2_lookup_left {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A}
    (h1 : l1[i]? = some x1) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x2, Absorbing (Φ i x1 x2))] →
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ∃ x2, iprop(⌜l2[i]? = some x2⌝ ∧ Φ i x1 x2)
  | TCOr.l | TCOr.r  => by
    match h2 : l2[i]? with
    | some x2 =>
      exact (bigSepL2_lookup h1 h2).trans <| exists_intro' x2 <| and_intro (pure_intro rfl) .rfl
    | none => exact bigSepL2_length.trans <| pure_elim' fun hlen =>
        absurd (List.getElem?_eq_none_iff.mp h2) (by have := (List.getElem?_eq_some_iff.mp h1).1; omega)

@[rocq_alias big_sepL2_lookup_r]
theorem bigSepL2_lookup_right {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x2 : B}
    (h2 : l2[i]? = some x2) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x1, Absorbing (Φ i x1 x2))] →
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ∃ x1, iprop(⌜l1[i]? = some x1⌝ ∧ Φ i x1 x2)
  | TCOr.l | TCOr.r =>
    match h1 : l1[i]? with
    | some x1 =>
      (bigSepL2_lookup h1 h2).trans <| exists_intro' x1 <| and_intro (pure_intro rfl) .rfl
    | none => bigSepL2_length.trans <| pure_elim' fun hlen =>
        absurd (List.getElem?_eq_none_iff.mp h1) (by have := (List.getElem?_eq_some_iff.mp h2).1; omega)

private abbrev bigSepL2_forall_elim {Φ : Nat → A → B → PROP} {y1 : A} {y2 : B}
    {ys1 : List A} {ys2 : List B} :
    (∀ k x1 x2, (⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
      ⊢ Φ 0 y1 y2 :=
  (forall_elim 0).trans <| (forall_elim y1).trans <| (forall_elim y2).trans <|
  ((and_intro (pure_intro rfl) .rfl).trans imp_elim_r).trans <|
  (and_intro (pure_intro rfl) .rfl).trans imp_elim_r

private abbrev bigSepL2_forall_shift {Φ : Nat → A → B → PROP} {y1 : A} {y2 : B}
    {ys1 : List A} {ys2 : List B} :
    (∀ k x1 x2, iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))
      ⊢ (∀ k x1 x2, iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2)) :=
  forall_intro fun k => forall_intro fun z1 => forall_intro fun z2 =>
  (forall_elim (k + 1)).trans <| (forall_elim z1).trans <| forall_elim z2

@[rocq_alias big_sepL2_intro]
theorem bigSepL2_intro {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    (⌜l1.length = l2.length⌝ ∧
      □ (∀ k, ∀ x1, ∀ x2, (⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
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
      exact intuitionistically_sep_idem.symm.1.trans <|
        sep_mono (intuitionistically_elim.trans bigSepL2_forall_elim) <|
        (intuitionistically_mono bigSepL2_forall_shift).trans <| ih hlen

@[rocq_alias big_sepL2_wand]
theorem bigSepL2_wand {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 -∗ Ψ k x1 x2) -∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  wand_intro <| bigSepL2_sep_equiv_symm.1.trans <| bigSepL2_mono fun _ _ => wand_elim_r

@[rocq_alias big_sepL2_impl]
theorem bigSepL2_impl {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      (□ (∀ k, ∀ x1, ∀ x2, (⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  wand_intro <| (sep_mono_l (and_self.2.trans <| and_mono_l bigSepL2_length)).trans <|
  (sep_mono_l persistent_and_affinely_sep_l.1).trans <|
  sep_assoc.1.trans <| persistent_and_affinely_sep_l.symm.1.trans <|
  pure_elim_l fun hlen =>
    (sep_mono_r <| (and_intro (pure_intro hlen) .rfl).trans <| bigSepL2_intro).trans <|
    bigSepL2_sep_equiv_symm.1.trans <| bigSepL2_mono fun _ _ => wand_elim_r

@[rocq_alias big_sepL2_forall]
theorem bigSepL2_forall [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hPersistent : ∀ k x1 x2, Persistent (Φ k x1 x2)) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      (⌜l1.length = l2.length⌝ ∧
        (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) := by
  refine ⟨and_intro bigSepL2_length <|
      forall_intro fun _ => forall_intro fun _ => forall_intro fun _ =>
      imp_intro' <| pure_elim_l fun h1 => imp_intro' <| pure_elim_l fun h2 => bigSepL2_lookup h1 h2,
    pure_elim_l fun hlen => ?_⟩
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with | nil => exact Affine.affine | cons => simp at hlen
  | cons y1 ys1 ih => cases l2 with
    | nil => simp at hlen
    | cons y2 ys2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen; simp only [bigSepL2]
      exact (and_self.2.trans (and_mono_l bigSepL2_forall_elim)).trans <| persistent_and_sep_1.trans <|
        sep_mono_r <| bigSepL2_forall_shift.trans <| ih (fun k => hPersistent (k + 1)) hlen

@[rocq_alias big_sepL2_persistently]
theorem bigSepL2_persistently [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    (<pers> [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, <pers> Φ k x1 x2) :=
  (persistently_congr bigSepL2_alt).trans <| persistently_and.trans <|
  (and_congr persistently_pure .rfl).trans <| (and_congr .rfl BigSepL.bigSepL_persistently).trans <|
  (bigSepL2_alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2))).symm

private theorem later_pure_except0 {φ : Prop} : (▷ ⌜φ⌝ : PROP) ⊢ ◇ ⌜φ⌝ :=
  (later_mono <| (pure_mono (fun h => ⟨h, trivial⟩)).trans <| pure_exists.2.trans <|
    exists_mono fun _ => (pure_true trivial).1).trans <|
  later_exists_false.trans <| or_mono .rfl <|
  (exists_mono fun _ => later_true.1.trans <| (pure_true trivial).2).trans <|
  pure_exists.1.trans <| pure_mono fun ⟨h, _⟩ => h

@[rocq_alias big_sepL2_later_2]
theorem bigSepL2_later_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) ⊢ (▷ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  (bigSepL2_alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2))).1.trans <|
  (and_mono later_intro BigSepL.bigSepL_later_2).trans <|
  later_and.2.trans <| later_mono bigSepL2_alt.2

@[rocq_alias big_sepL2_laterN_2]
theorem bigSepL2_laterN_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷^[n] Φ k x1 x2) ⊢ (▷^[n] [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  match n with | 0 => .rfl | _ + 1 => bigSepL2_later_2.trans <| later_mono bigSepL2_laterN_2

@[rocq_alias big_sepL2_later_1]
theorem bigSepL2_later_1 [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    (▷ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ (◇ [∗list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) :=
  (later_mono bigSepL2_alt.1).trans <| later_and.1.trans <|
  (and_mono later_pure_except0 BigSepL.bigSepL_later.1).trans <|
  (and_mono .rfl except0_intro).trans <| except0_and.2.trans <|
  except0_mono (bigSepL2_alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2))).2

@[rocq_alias big_sepL2_later]
theorem bigSepL2_later [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    (▷ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ (◇ [∗list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) :=
  ⟨bigSepL2_later_1, (except0_mono bigSepL2_later_2).trans except0_later⟩

@[rocq_alias big_sepL2_sepL]
theorem bigSepL2_sepL {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) :=
  bigSepL2_alt.trans <|
  ⟨pure_elim_l fun hlen => and_intro (pure_intro hlen) (BigSepL.bigSepL_sep_zip hlen).1,
   pure_elim_l fun hlen => and_intro (pure_intro hlen) (BigSepL.bigSepL_sep_zip hlen).2⟩

@[rocq_alias big_sepL2_sepL_2]
theorem bigSepL2_sepL_2 {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ⊢ bigSepL Φ2 l2 -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) :=
  wand_intro <| (sep_mono_l persistent_and_affinely_sep_l.1).trans <| sep_assoc.1.trans <|
  persistent_and_affinely_sep_l.symm.1.trans <| bigSepL2_sepL.2

@[rocq_alias big_sepL2_reverse_2]
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
      simp only [List.length_cons] at hlen; simp only [bigSepL2, List.reverse_cons]
      exact sep_comm.1.trans <| (sep_mono_l (ih (Nat.succ.inj hlen))).trans <| bigSepL2_snoc.2

@[rocq_alias big_sepL2_reverse]
theorem bigSepL2_reverse {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) ⊣⊢
      ([∗list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) := by
  refine ⟨?_, bigSepL2_reverse_2⟩
  have := bigSepL2_reverse_2 (Φ := Φ) (l1 := l1.reverse) (l2 := l2.reverse)
  simp only [List.reverse_reverse] at this; exact this

@[rocq_alias big_sepL2_replicate_l]
theorem bigSepL2_replicate_left {Φ : Nat → A → B → PROP} {l : List B} {x : A} :
    ([∗list] k ↦ x1;x2 ∈ List.replicate l.length x;l, Φ k x1 x2) ⊣⊢
      [∗list] k ↦ x2 ∈ l, Φ k x x2 :=
  match l with | [] => .rfl | _ :: _ => sep_congr .rfl bigSepL2_replicate_left

@[rocq_alias big_sepL2_replicate_r]
theorem bigSepL2_replicate_right {Φ : Nat → A → B → PROP} {l : List A} {x : B} :
    ([∗list] k ↦ x1;x2 ∈ l;List.replicate l.length x, Φ k x1 x2) ⊣⊢
      [∗list] k ↦ x1 ∈ l, Φ k x1 x :=
  match l with | [] => .rfl | _ :: _ => sep_congr .rfl bigSepL2_replicate_right

@[rocq_alias big_sepL2_app_same_length]
theorem bigSepL2_app_same_length {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
         [∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (l1a.length + k) x1 x2 :=
  (bigSepL2_append hlen).trans <| sep_congr .rfl <|
  bigSepL2_equiv_of_forall_equiv <| by simp only [Nat.add_comm]; exact .rfl

@[rocq_alias big_sepL2_const_sepL_l]
theorem bigSepL2_const_sepL_left {Φ : Nat → A → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;_x2 ∈ l1;l2, Φ k x1) ⊣⊢ ⌜l1.length = l2.length⌝ ∧ [∗list] k ↦ x ∈ l1, Φ k x := by
  have fst_zip : ∀ hlen : l1.length = l2.length, (l1.zip l2).map Prod.fst = l1 := by
    intro hlen; induction l1 generalizing l2 with
    | nil => cases l2 <;> first | rfl | simp at hlen
    | cons _ _ ih => cases l2 with
      | nil => simp at hlen
      | cons _ _ => simp [ih (by simpa using hlen)]
  refine bigSepL2_alt.trans <|
        ⟨pure_elim_l fun hlen => and_intro (pure_intro hlen) ?_,
         pure_elim_l fun hlen => and_intro (pure_intro hlen) ?_⟩ <;>
  { have h : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
      equiv_iff.mp (BigSepL.bigSepL_map Prod.fst)
    rw [fst_zip hlen] at h; first | exact h.1 | exact h.2 }

@[rocq_alias big_sepL2_const_sepL_r]
theorem bigSepL2_const_sepL_right {Φ : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ _x1;x2 ∈ l1;l2, Φ k x2) ⊣⊢ ⌜l1.length = l2.length⌝ ∧ [∗list] k ↦ x ∈ l2, Φ k x :=
  bigSepL2_flip.trans <| bigSepL2_const_sepL_left.trans <|
  ⟨and_mono (pure_mono Eq.symm) .rfl, and_mono (pure_mono Eq.symm) .rfl⟩

@[rocq_alias big_sepL2_sep_sepL_l]
theorem bigSepL2_sep_sepL_left [BIAffine PROP] {Φ : Nat → A → PROP} {Ψ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x ∈ l1, Φ k x) ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2 := by
  refine bigSepL2_sep_equiv.trans <| (sep_congr_l bigSepL2_const_sepL_left).trans
    ⟨sep_mono and_elim_r .rfl, ?_⟩
  exact (sep_mono_r <| (and_intro bigSepL2_length .rfl).trans <|
    persistent_and_affinely_sep_l.1.trans <| sep_mono_l affinely_elim).trans <|
    sep_assoc.2.trans <| sep_mono_l <|
    and_intro (sep_comm.1.trans <| (sep_mono_l persistently_intro).trans <|
      persistently_absorb_l.trans persistently_elim) sep_elim_l

@[rocq_alias big_sepL2_sep_sepL_r]
theorem bigSepL2_sep_sepL_right [BIAffine PROP] {Φ : Nat → B → PROP} {Ψ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x2 ∗ Ψ k x1 x2) ⊣⊢
      (bigSepL Φ l2 ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  (bigSepL2_equiv_of_forall_equiv sep_comm).trans <| bigSepL2_flip.trans <|
  (bigSepL2_equiv_of_forall_equiv sep_comm).trans <| bigSepL2_sep_sepL_left.trans <|
  sep_congr_r bigSepL2_flip

@[rocq_alias big_sepL2_delete]
theorem bigSepL2_delete_cond {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B} (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
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
        exact (sep_congr_r (ih h1 h2)).trans <| sep_left_comm.trans <| sep_congr_r <|
        sep_congr_r <| bigSepL2_equiv fun _ _ => by simp only [Nat.add_right_cancel_iff]; exact .rfl

@[rocq_alias big_sepL2_delete']
theorem bigSepL2_delete [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B} (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ l1;l2, ⌜k ≠ i⌝ → Φ k y1 y2) :=
  (bigSepL2_delete_cond h1 h2).trans <| sep_congr .rfl <| bigSepL2_equiv_of_forall_equiv fun {k y1 y2} => by
    by_cases hki : k = i
    · subst hki; simp only [ne_eq, not_true_eq_false]
      exact ⟨imp_intro' <| (pure_elim_l fun hf => False.elim hf).trans .rfl, Affine.affine⟩
    · simp only [hki, ne_eq, not_false_eq_true]; exact true_imp.symm

@[rocq_alias big_sepL2_lookup_acc_impl]
theorem bigSepL2_lookup_acc_impl {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B} (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      (Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
        (⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
          Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
  refine (bigSepL2_delete_cond h1 h2).1.trans
    (sep_mono_r <| forall_intro fun Ψ => wand_intro <| wand_intro ?_)
  refine sep_comm.1.trans (sep_mono_r ?_) |>.trans (bigSepL2_delete_cond h1 h2).2
  refine (sep_mono_r ?_).trans (wand_elim <|
      bigSepL2_impl (Φ := fun k y1 y2 => if k = i then emp else Φ k y1 y2)
      (Ψ := fun k y1 y2 => if k = i then emp else Ψ k y1 y2))
  refine intuitionistically_intro' <| forall_intro fun k => forall_intro fun y1 =>
    forall_intro fun y2 =>
    imp_intro' <| pure_elim_l fun hk1 => imp_intro' <| pure_elim_l fun hk2 => ?_
  by_cases hki : k = i
  · subst hki; simp only []; exact wand_intro (sep_emp.1.trans Affine.affine)
  · simp only [hki]
    exact intuitionistically_elim.trans <|
      (forall_elim k).trans <| (forall_elim y1).trans <| (forall_elim y2).trans <|
      ((and_intro (pure_intro hk1) .rfl).trans imp_elim_r).trans <|
      ((and_intro (pure_intro hk2) .rfl).trans imp_elim_r).trans <|
      (and_intro (pure_intro hki) .rfl).trans imp_elim_r

@[rocq_alias big_sepL2_ne_2]
theorem bigSepL2_dist_2 [OFE A] [OFE B]
    {Φ Ψ : Nat → A → B → PROP} {l1 l1' : List A} {l2 l2' : List B} {n : Nat}
    (hl1 : l1.length = l1'.length) (hl2 : l2.length = l2'.length)
    (hel1 : ∀ {k : Nat} {x x' : A}, l1[k]? = some x → l1'[k]? = some x' → x ≡{n}≡ x')
    (hel2 : ∀ {k : Nat} {y y' : B}, l2[k]? = some y → l2'[k]? = some y' → y ≡{n}≡ y')
    (hf : ∀ {k y1 y1' y2 y2'}, l1[k]? = some y1 → l1'[k]? = some y1' → y1 ≡{n}≡ y1' →
      l2[k]? = some y2 → l2'[k]? = some y2' → y2 ≡{n}≡ y2' →
      Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ≡{n}≡
      ([∗list] k ↦ x1;x2 ∈ l1';l2', Ψ k x1 x2) := by
  cases l1 <;> cases l1' <;> cases l2 <;> cases l2'
  all_goals (first | · exact .rfl | · simp at hl2 | · simp at hl1 | skip)
  exact sep_ne.ne (hf rfl rfl (@hel1 0 _ _ rfl rfl) rfl rfl (@hel2 0 _ _ rfl rfl)) <|
    bigSepL2_dist_2 (by simpa using hl1) (by simpa using hl2)
    (fun {k} => @hel1 (k + 1)) (fun {k} => @hel2 (k + 1)) (fun {k} => @hf (k + 1))

@[rocq_alias big_sepL2_proper_2]
theorem bigSepL2_proper_2 [OFE A] [OFE B]
    {Φ Ψ : Nat → A → B → PROP} {l1 l1' : List A} {l2 l2' : List B}
    (hl1 : l1.length = l1'.length) (hl2 : l2.length = l2'.length)
    (hel1 : ∀ {k : Nat} {x x' : A}, l1[k]? = some x → l1'[k]? = some x' → x ≡ x')
    (hel2 : ∀ {k : Nat} {y y' : B}, l2[k]? = some y → l2'[k]? = some y' → y ≡ y')
    (hf : ∀ {k y1 y1' y2 y2'}, l1[k]? = some y1 → l1'[k]? = some y1' → y1 ≡ y1' →
      l2[k]? = some y2 → l2'[k]? = some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1';l2', Ψ k x1 x2) :=
  equiv_iff.mp <| OFE.equiv_dist.mpr fun _ =>
    bigSepL2_dist_2 hl1 hl2 (fun h1 h2 => (hel1 h1 h2).dist) (fun h1 h2 => (hel2 h1 h2).dist)
      (fun h1 h2 _ h3 h4 _ => (equiv_iff.mpr (hf h1 h2 (hel1 h1 h2) h3 h4 (hel2 h3 h4))).dist)

@[rocq_alias big_sepL_sepL2_diag]
theorem bigSepL_sepL2_diag {Φ : Nat → A → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x x) ⊢ ([∗list] k ↦ x1; x2 ∈ l;l, Φ k x1 x2) := by
  refine (and_intro (pure_intro rfl) .rfl).trans (and_mono .rfl ?_) |>.trans BigSepL2.bigSepL2_alt.2
  have hzip : l.zip l = l.map (fun x => (x, x)) := by
    induction l with | nil => rfl | cons _ _ ih => simp [ih]
  rw [hzip]
  exact (equiv_iff.mp <| BigSepL.bigSepL_map (Φ := fun k p => Φ k p.1 p.2) (fun x => (x, x))).symm.1

end BigSepL2

end BI
