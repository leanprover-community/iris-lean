/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.Instances
import Iris.Std.TC

namespace Iris.BI

open Iris.Algebra
open Iris.Std
open BIBase


/-! # Big Separating Conjunction over Lists -/

namespace BigSepL
variable {PROP : Type _} [BI PROP] {A : Type _}

/-- Corresponds to `big_sepL_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∗list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ emp := by
  simp only [bigSepL, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepL_nil'` in Rocq Iris. -/
theorem nil' {Φ : Nat → A → PROP} {l : List A} (h : l = []) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ emp := by
  subst h; exact nil

/-- Corresponds to second `big_sepL_nil'` in Rocq Iris. -/
theorem nil'_affine {P : PROP} [Affine P] {Φ : Nat → A → PROP} :
    P ⊢ [∗list] k ↦ x ∈ ([] : List A), Φ k x :=
  Affine.affine.trans nil.2

/-- Corresponds to `big_sepL_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∗list] k ↦ y ∈ x :: xs, Φ k y) ⊣⊢ Φ 0 x ∗ [∗list] k ↦ y ∈ xs, Φ (k + 1) y := by
  simp only [bigSepL, bigOpL]
  exact .rfl

/-- Corresponds to `big_sepL_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∗list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x :=
  equiv_iff.mp (BigOpL.singleton Φ x)

/-- Corresponds to `big_sepL_app` in Rocq Iris. -/
theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∗list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l₁, Φ k x) ∗ [∗list] k ↦ x ∈ l₂, Φ (k + l₁.length) x :=
  equiv_iff.mp (BigOpL.append Φ l₁ l₂)

/-- Corresponds to `big_sepL_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∗list] k ↦ y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗list] k ↦ y ∈ l, Φ k y) ∗ Φ l.length x :=
  equiv_iff.mp (BigOpL.snoc Φ l x)

/-- Corresponds to `big_sepL_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x := by
  induction l generalizing Φ Ψ with
  | nil => exact Entails.rfl
  | cons y ys ih =>
    simp only [bigSepL, bigOpL]
    apply sep_mono
    · exact h 0 y rfl
    · apply ih
      intro k x hget
      exact h (k + 1) x hget

/-- Corresponds to `big_sepL_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr h

/-- Unconditional version of `proper`. No direct Rocq equivalent. -/
theorem congr {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr' h

/-- Corresponds to `big_sepL_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat}
    (h : ∀ k x, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∗list] k ↦ x ∈ l, Ψ k x :=
  BigOpL.congr_ne h

/-- Corresponds to `big_sepL_mono'` in Rocq Iris. -/
theorem mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ [∗list] k ↦ x ∈ l, Ψ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_flip_mono'` in Rocq Iris. -/
theorem flip_mono' {Φ Ψ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, Ψ k x ⊢ Φ k x) :
    ([∗list] k ↦ x ∈ l, Ψ k x) ⊢ [∗list] k ↦ x ∈ l, Φ k x :=
  mono (fun k x _ => h k x)

/-- Corresponds to `big_sepL_id_mono'` in Rocq Iris. -/
theorem id_mono' {Ps Qs : List PROP}
    (hlen : Ps.length = Qs.length)
    (h : ∀ (i : Nat) (P Q : PROP), Ps[i]? = some P → Qs[i]? = some Q → P ⊢ Q) :
    ([∗list] P ∈ Ps, P) ⊢ [∗list] Q ∈ Qs, Q := by
  induction Ps generalizing Qs with
  | nil =>
    cases Qs with
    | nil => exact Entails.rfl
    | cons _ _ => simp at hlen
  | cons P Ps' ih =>
    cases Qs with
    | nil => simp at hlen
    | cons Q Qs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigSepL, bigOpL]
      apply sep_mono
      · exact h 0 P Q rfl rfl
      · apply ih hlen
        intro i P' Q' hP' hQ'
        exact h (i + 1) P' Q' hP' hQ'

/-- Corresponds to `big_sepL_persistent'` in Rocq Iris. -/
instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons x xs ih =>
      simp only [bigSepL, bigOpL]
      have h1 : Φ 0 x ⊢ <pers> Φ 0 x := Persistent.persistent
      have h2 : bigSepL (fun n => Φ (n + 1)) xs ⊢ <pers> bigSepL (fun n => Φ (n + 1)) xs := ih
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine'` in Rocq Iris. -/
instance affine {Φ : Nat → A → PROP} {l : List A} [∀ k x, Affine (Φ k x)] :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons x xs ih =>
      simp only [bigSepL, bigOpL]
      have h1 : Φ 0 x ⊢ emp := Affine.affine
      have h2 : bigSepL (fun n => Φ (n + 1)) xs ⊢ emp := ih
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_persistent_id` in Rocq Iris. -/
theorem persistent_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Persistent P) :
    Persistent ([∗list] P ∈ Ps, P) where
  persistent := by
    induction Ps with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons P Ps' ih =>
      simp only [bigSepL, bigOpL]
      have hP : Persistent P := hPs P List.mem_cons_self
      have hPs' : ∀ Q, Q ∈ Ps' → Persistent Q := fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)
      have : Persistent (bigSepL (fun _ (P : PROP) => P) Ps') := ⟨ih hPs'⟩
      have h1 : P ⊢ <pers> P := hP.persistent
      have h2 : bigSepL (fun _ (P : PROP) => P) Ps' ⊢ <pers> bigSepL (fun _ (P : PROP) => P) Ps' :=
        this.persistent
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine_id` in Rocq Iris. -/
theorem affine_id {Ps : List PROP} (hPs : ∀ P, P ∈ Ps → Affine P) :
    Affine ([∗list] P ∈ Ps, P) where
  affine := by
    induction Ps with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons P Ps' ih =>
      simp only [bigSepL, bigOpL]
      have hP : Affine P := hPs P List.mem_cons_self
      have hPs' : ∀ Q, Q ∈ Ps' → Affine Q := fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)
      have : Affine (bigSepL (fun _ (P : PROP) => P) Ps') := ⟨ih hPs'⟩
      have h1 : P ⊢ emp := hP.affine
      have h2 : bigSepL (fun _ (P : PROP) => P) Ps' ⊢ emp := this.affine
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_persistent` in Rocq Iris. -/
theorem persistent_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∗list] k ↦ x ∈ l, Φ k x) where
  persistent := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact persistently_emp_2
    | cons y ys ih =>
      simp only [bigSepL, bigOpL]
      have h0 : Persistent (Φ 0 y) := h 0 y rfl
      have hrest : ∀ k x, ys[k]? = some x → Persistent (Φ (k + 1) x) :=
        fun k x hget => h (k + 1) x hget
      have h1 : Φ 0 y ⊢ <pers> Φ 0 y := h0.persistent
      have hPers : Persistent (bigSepL (fun n => Φ (n + 1)) ys) := ⟨ih hrest⟩
      have h2 : bigSepL (fun n => Φ (n + 1)) ys ⊢ <pers> bigSepL (fun n => Φ (n + 1)) ys :=
        hPers.persistent
      exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL_affine` in Rocq Iris. -/
theorem affine_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Affine (Φ k x)) :
    Affine ([∗list] k ↦ x ∈ l, Φ k x) where
  affine := by
    induction l generalizing Φ with
    | nil =>
      simp only [bigSepL, bigOpL]
      exact Entails.rfl
    | cons y ys ih =>
      simp only [bigSepL, bigOpL]
      have h0 : Affine (Φ 0 y) := h 0 y rfl
      have hrest : ∀ k x, ys[k]? = some x → Affine (Φ (k + 1) x) :=
        fun k x hget => h (k + 1) x hget
      have h1 : Φ 0 y ⊢ emp := h0.affine
      have hAff : Affine (bigSepL (fun n => Φ (n + 1)) ys) := ⟨ih hrest⟩
      have h2 : bigSepL (fun n => Φ (n + 1)) ys ⊢ emp := hAff.affine
      exact (sep_mono h1 h2).trans sep_emp.1

/-- Corresponds to `big_sepL_nil_timeless` in Rocq Iris. -/
instance nil_timeless [Timeless (emp : PROP)] {Φ : Nat → A → PROP} :
    Timeless ([∗list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by
    simp only [bigSepL, bigOpL]
    exact Timeless.timeless

/-- Corresponds to `big_sepL_emp` in Rocq Iris. -/
theorem emp_l {l : List A} :
    ([∗list] _x ∈ l, (emp : PROP)) ⊣⊢ emp :=
  equiv_iff.mp (BigOpL.unit_const l)

/-- Corresponds to `big_sepL_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x) ⊣⊢ ([∗list] k ↦ x ∈ l, Φ k x) ∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  equiv_iff.mp (BigOpL.op_distr Φ Ψ l)

/-- Corresponds to `big_sepL_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ∗ ([∗list] k ↦ x ∈ l, Ψ k x) ⊣⊢ [∗list] k ↦ x ∈ l, Φ k x ∗ Ψ k x :=
  sep'.symm

/-- Corresponds to `big_sepL_and` in Rocq Iris (one direction only). -/
theorem and' {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x ∧ Ψ k x) ⊢
      ([∗list] k ↦ x ∈ l, Φ k x) ∧ [∗list] k ↦ x ∈ l, Ψ k x :=
  and_intro (mono fun _ _ _ => and_elim_l) (mono fun _ _ _ => and_elim_r)

/-- Corresponds to `big_sepL_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ([∗list] k ↦ x ∈ l, Φ k x -∗ Ψ k x) -∗ [∗list] k ↦ x ∈ l, Ψ k x :=
  wand_intro <| sep_2.1.trans (mono fun _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → Prop} {l : List A} :
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact pure_intro fun _ _ h => nomatch h
  | cons y ys ih =>
    refine (sep_mono_r ih).trans <| sep_and.trans <| pure_and.1.trans <| pure_mono ?_
    intro ⟨hy, hys⟩ k x hget
    match k with
    | 0 => exact Option.some.inj hget ▸ hy
    | k + 1 => exact hys k x hget

/-- Corresponds to `big_sepL_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : Nat → A → Prop} {l : List A} :
    iprop(<affine> ⌜∀ k x, l[k]? = some x → φ k x⌝) ⊢
      ([∗list] k ↦ x ∈ l, <affine> ⌜φ k x⌝ : PROP) := by
  induction l generalizing φ with
  | nil => exact affinely_elim_emp
  | cons y ys ih =>
    refine (affinely_mono <| pure_mono fun h => ⟨h 0 y rfl, fun k x hget => h (k + 1) x hget⟩).trans <|
      (affinely_mono pure_and.2).trans <| affinely_and.1.trans <| persistent_and_sep_1.trans (sep_mono_r ih)

/-- Corresponds to `big_sepL_pure` in Rocq Iris. Requires `BIAffine`. -/
theorem pure' [BIAffine PROP] {φ : Nat → A → Prop} {l : List A} :
    ([∗list] k ↦ x ∈ l, ⌜φ k x⌝) ⊣⊢ (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) :=
  ⟨pure_1, (affine_affinely _).2.trans <| affinely_pure_2.trans (mono fun _ _ _ => affinely_elim)⟩

/-- Corresponds to `big_sepL_take_drop` in Rocq Iris. -/
theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢
      ([∗list] k ↦ x ∈ l.take n, Φ k x) ∗ [∗list] k ↦ x ∈ l.drop n, Φ (n + k) x :=
  equiv_iff.mp (BigOpL.take_drop Φ l n)

/-- Corresponds to `big_sepL_fmap` in Rocq Iris. -/
theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∗list] k ↦ y ∈ l.map f, Φ k y) ≡ [∗list] k ↦ x ∈ l, Φ k (f x) := by
  induction l generalizing Φ with
  | nil => simp only [List.map_nil]; exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.map_cons, bigSepL, bigOpL]
    exact Monoid.op_proper OFE.Equiv.rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL_omap` in Rocq Iris. -/
theorem omap {B : Type _} (f : A → Option B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.filterMap f, Φ y) ≡
      [∗list] x ∈ l, (f x).elim emp Φ := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, bigSepL, bigOpL]
    cases hx : f x <;> simp only [Option.elim]
    · exact OFE.Equiv.trans ih (OFE.Equiv.symm (equiv_iff.mpr emp_sep))
    · exact Monoid.op_proper OFE.Equiv.rfl ih

/-- Corresponds to `big_sepL_bind` in Rocq Iris. -/
theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∗list] y ∈ l.flatMap f, Φ y) ≡
      [∗list] x ∈ l, [∗list] y ∈ f x, Φ y := by
  induction l with
  | nil => exact OFE.Equiv.rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, bigSepL, bigOpL]
    exact OFE.Equiv.trans (equiv_iff.mpr app) (Monoid.op_proper OFE.Equiv.rfl ih)

/-- Corresponds to `big_sepL_lookup_acc` in Rocq Iris. -/
theorem lookup_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) := by
  induction l generalizing i Φ x with
  | nil => simp at h
  | cons z zs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [bigSepL, bigOpL, List.set_cons_zero]
      exact ⟨sep_mono_r (forall_intro fun y => wand_intro sep_comm.1),
             (sep_mono_r (forall_elim z)).trans wand_elim_r⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL, List.set_cons_succ]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      have hset_eq : zs.set j x = zs := by
        apply List.ext_getElem?; intro k
        simp only [List.getElem?_set]
        by_cases hjk : j = k
        · subst hjk; simp only [(List.getElem?_eq_some_iff.mp h).1, ↓reduceIte, h]
        · simp only [hjk, ↓reduceIte]
      constructor
      · refine (sep_mono_r ih'.1).trans <| sep_assoc.2.trans <| (sep_mono_l sep_comm.1).trans <|
          sep_assoc.1.trans <| sep_mono_r <| forall_intro fun y => wand_intro ?_
        exact sep_assoc.1.trans <| (sep_mono_r <| (sep_mono_l (forall_elim y)).trans <|
          sep_comm.1.trans wand_elim_r)
      · conv => rhs; rw [← hset_eq]
        exact (sep_mono_r (forall_elim x)).trans wand_elim_r

/-- Corresponds to `big_sepL_lookup` in Rocq Iris. -/
theorem lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    [TCOr (∀ k y, Affine (Φ k y)) (Absorbing (Φ i x))] →
    ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x
  | TCOr.l => by
    have hi : i < l.length := List.getElem?_eq_some_iff.mp h |>.1
    have hx : l[i] = x := List.getElem?_eq_some_iff.mp h |>.2
    have hlen : (l.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
    have hmiddle : l = l.take i ++ x :: l.drop (i + 1) := by
      have htake : l.take (i + 1) = l.take i ++ [x] := by rw [List.take_succ_eq_append_getElem hi, hx]
      calc l = l.take (i + 1) ++ l.drop (i + 1) := (List.take_append_drop (i + 1) l).symm
        _ = (l.take i ++ [x]) ++ l.drop (i + 1) := by rw [htake]
        _ = l.take i ++ ([x] ++ l.drop (i + 1)) := List.append_assoc ..
        _ = l.take i ++ (x :: l.drop (i + 1)) := rfl
    rw [hmiddle]
    refine app.1.trans <| sep_elim_r.trans ?_
    simp only [bigSepL, bigOpL, Nat.zero_add, hlen]
    exact sep_elim_l
  | TCOr.r => (lookup_acc h).1.trans sep_elim_l

/-- Corresponds to `big_sepL_insert_acc` in Rocq Iris. -/
theorem insert_acc {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ [∗list] k ↦ z ∈ l.set i y, Φ k z) :=
  (lookup_acc h).1

/-- Corresponds to `big_sepL_elem_of_acc` in Rocq Iris. -/
theorem elem_of_acc {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    ([∗list] y ∈ l, Φ y) ⊢ Φ x ∗ (Φ x -∗ [∗list] y ∈ l, Φ y) := by
  have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hset : l.set i x = l := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_set]
    by_cases hik : i = k
    · subst hik; simp only [hi, ↓reduceIte, hlookup]
    · simp only [hik, ↓reduceIte]
  conv => rhs; rw [← hset]
  exact (lookup_acc hlookup).1.trans (sep_mono_r (forall_elim x))

/-- Corresponds to `big_sepL_elem_of` in Rocq Iris. -/
theorem elem_of {Φ : A → PROP} {l : List A} {x : A}
    (h : x ∈ l) :
    [TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))] →
    ([∗list] y ∈ l, Φ y) ⊢ Φ x
  | TCOr.l => by
    have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    haveI : ∀ (k : Nat) (y : A), Affine ((fun _ y => Φ y) k y) := fun _ y => inferInstance
    exact lookup (Φ := fun _ y => Φ y) hlookup
  | TCOr.r => by
    have ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    have hlookup : l[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    haveI : Absorbing ((fun _ y => Φ y) i x) := inferInstance
    exact lookup (Φ := fun _ y => Φ y) hlookup

/-- Corresponds to `big_sepL_delete` in Rocq Iris. -/
theorem delete {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢
      Φ i x ∗ [∗list] k ↦ y ∈ l, if k = i then emp else Φ k y := by
  induction l generalizing i Φ with
  | nil => simp at h
  | cons z zs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [bigSepL, bigOpL, ↓reduceIte]
      have hmono : ∀ k y, (Φ (k + 1) y) ⊣⊢ (if k + 1 = 0 then emp else Φ (k + 1) y) := fun k _ => by
        simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact .rfl
      exact ⟨sep_mono_r <| (mono fun k y _ => (hmono k y).1).trans emp_sep.2,
             sep_mono_r <| emp_sep.1.trans (mono fun k y _ => (hmono k y).2)⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simp only [bigSepL, bigOpL]
      have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h
      have hne0 : (0 : Nat) ≠ j + 1 := Nat.zero_ne_add_one j
      have hmono : ∀ k y, (if k = j then emp else Φ (k + 1) y) ⊣⊢
          (if k + 1 = j + 1 then emp else Φ (k + 1) y) := fun k _ => by
        simp only [Nat.add_right_cancel_iff]; exact .rfl
      refine (sep_congr_r ih').trans <| sep_left_comm.trans <| sep_congr_r ?_
      simp only [bigSepL, hne0, ↓reduceIte]
      exact sep_congr_r (equiv_iff.mp (proper fun k y _ => equiv_iff.mpr (hmono k y)))

/-- Corresponds to `big_sepL_delete'` in Rocq Iris. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    ([∗list] k ↦ y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗list] k ↦ y ∈ l, ⌜k ≠ i⌝ → Φ k y := by
  have hmono : ∀ k y, (if k = i then emp else Φ k y) ⊣⊢ iprop(⌜k ≠ i⌝ → Φ k y) := fun k y => by
    by_cases hki : k = i <;> simp only [hki, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true]
    · exact ⟨imp_intro' <| (pure_elim_l (R := Φ i y) fun hf => hf.elim), Affine.affine⟩
    · exact true_imp.symm
  exact (delete h).trans <| sep_congr_r <| equiv_iff.mp <| proper fun k y _ => equiv_iff.mpr (hmono k y)

/-- Corresponds to `big_sepL_intro` in Rocq Iris. -/
theorem intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} [Intuitionistic P]
    (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Intuitionistic.intuitionistic.trans affinely_elim_emp
  | cons y ys ih =>
    exact Intuitionistic.intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
      sep_mono (intuitionistically_elim.trans (h 0 y rfl))
               (intuitionistically_elim.trans (ih fun k x hget => h (k + 1) x hget))

/-- Forward direction of `big_sepL_forall` in Rocq Iris. -/
theorem forall_1' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) := by
  refine forall_intro fun k => forall_intro fun x => imp_intro' <| pure_elim_l fun hget => ?_
  exact (lookup_acc hget).1.trans <| (sep_mono_l Persistent.persistent).trans <|
    sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

/-- Backward direction of `big_sepL_forall` in Rocq Iris. -/
theorem forall_2' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x)) ⊢ [∗list] k ↦ x ∈ l, Φ k x := by
  induction l generalizing Φ with
  | nil => exact Affine.affine
  | cons y ys ih =>
    have head_step : iprop(∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x) ⊢ Φ 0 y :=
      (forall_elim 0).trans (forall_elim y) |>.trans <|
        (and_intro (pure_intro rfl) .rfl).trans imp_elim_r
    have tail_step : iprop(∀ k x, ⌜(y :: ys)[k]? = some x⌝ → Φ k x)
        ⊢ iprop(∀ k x, ⌜ys[k]? = some x⌝ → Φ (k + 1) x) :=
      forall_intro fun k => forall_intro fun z => (forall_elim (k + 1)).trans (forall_elim z)
    exact and_self.2.trans (and_mono_l head_step) |>.trans persistent_and_sep_1 |>.trans <|
      sep_mono_r (tail_step.trans ih)

/-- Corresponds to `big_sepL_forall` in Rocq Iris. -/
theorem forall' {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP]
    [∀ k x, Persistent (Φ k x)] :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  ⟨forall_1', forall_2'⟩

/-- Corresponds to `big_sepL_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ □ (∀ k x, iprop(⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) -∗ [∗list] k ↦ x ∈ l, Ψ k x := by
  apply wand_intro
  have h1 : iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) ⊢ bigSepL (fun k x => iprop(Φ k x -∗ Ψ k x)) l := by
    haveI : Intuitionistic iprop(□ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x -∗ Ψ k x)) :=
      intuitionistically_intuitionistic _
    exact intro fun k x hget => intuitionistically_elim.trans <|
      (forall_elim k).trans (forall_elim x) |>.trans <| (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1
  exact (sep_mono_r h1).trans <| sep_2.1.trans (mono fun _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL_lookup_acc_impl` in Rocq Iris. -/
theorem lookup_acc_impl {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A}
    (h : l[i]? = some x) :
    iprop([∗list] k ↦ x ∈ l, Φ k x) ⊢
      Φ i x ∗ ∀ (Ψ: Nat → A → PROP), □ (∀ k y, iprop(⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) -∗
        Ψ i x -∗  ([∗list] k ↦ x ∈ l, Ψ k x) := by
  refine (delete h).1.trans <| sep_mono_r <| forall_intro fun Ψ => wand_intro <| wand_intro ?_
  have hdel_psi := (delete (Φ := Ψ) h).2
  refine sep_comm.1.trans <| (sep_mono_r ?_).trans hdel_psi
  have htrans : iprop(bigSepL (fun k y => if k = i then emp else Φ k y) l ∗
        □ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
      ⊢ bigSepL (fun k y => if k = i then emp else Ψ k y) l := by
    have hwand : iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y))
        ⊢ bigSepL (fun k y => if k = i then emp else iprop(Φ k y -∗ Ψ k y)) l := by
      haveI : Intuitionistic iprop(□ (∀ k y, ⌜l[k]? = some y⌝ → ⌜k ≠ i⌝ → Φ k y -∗ Ψ k y)) :=
        intuitionistically_intuitionistic _
      exact intro fun k y hget => by
        by_cases hki : k = i
        · subst hki; simp only [↓reduceIte]
          exact Intuitionistic.intuitionistic.trans (affinely_elim_emp (PROP := PROP))
        · simp only [hki, ↓reduceIte]
          exact intuitionistically_elim.trans <| (forall_elim k).trans (forall_elim y) |>.trans <|
            (imp_mono_l (pure_mono fun _ => hget)).trans true_imp.1 |>.trans <|
            (imp_mono_l (pure_mono fun _ => hki)).trans true_imp.1
    refine (sep_mono_r hwand).trans <| sep_2.1.trans <| mono fun k y _ => by
      by_cases hki : k = i
      · subst hki; simp only [↓reduceIte]; exact emp_sep.1
      · simp only [hki, ↓reduceIte]; exact wand_elim_r
  exact htrans

/-- Corresponds to `big_sepL_persistently` in Rocq Iris. Requires `BIAffine`. -/
theorem persistently {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    iprop(<pers> [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, <pers> Φ k x := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact persistently_emp' (PROP := PROP)
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact persistently_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_later` in Rocq Iris. -/
theorem later [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} :
    iprop(▷ [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷ Φ k x := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact later_emp
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact later_sep.trans ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_later_2` in Rocq Iris. -/
theorem later_2 {Φ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l, ▷ Φ k x) ⊢ iprop(▷ [∗list] k ↦ x ∈ l, Φ k x) := by
  induction l generalizing Φ with
  | nil => simp only [bigSepL, bigOpL]; exact later_intro
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    exact (sep_mono_r ih).trans later_sep.2

/-- Corresponds to `big_sepL_laterN` in Rocq Iris. -/
theorem laterN [BIAffine PROP] {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    iprop(▷^[n] [∗list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗list] k ↦ x ∈ l, ▷^[n] Φ k x := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans later

/-- Corresponds to `big_sepL_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∗list] k ↦ x ∈ l, ▷^[n] Φ k x) ⊢ iprop(▷^[n] [∗list] k ↦ x ∈ l, Φ k x) := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact later_2.trans (later_mono ih)

/-- Corresponds to `big_sepL_Permutation` in Rocq Iris. -/
theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∗list] x ∈ l₁, Φ x) ⊣⊢ [∗list] x ∈ l₂, Φ x :=
  equiv_iff.mp (BigOpL.perm Φ hp)

/-- Corresponds to `big_sepL_submseteq` in Rocq Iris. -/
theorem submseteq {Φ : A → PROP} [∀ x, Affine (Φ x)] {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∗list] x ∈ l₂, Φ x) ⊢ [∗list] x ∈ l₁, Φ x := by
  have hperm := (perm (Φ := Φ) h).2
  have happ := (app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).1
  exact hperm.trans (happ.trans sep_elim_l)

/-- Corresponds to `big_sepL_dup` in Rocq Iris. -/
theorem dup {P : PROP} [Affine P] {l : List A} :
     □ (P -∗ P ∗ P) ∗ P ⊢ ([∗list] _x ∈ l, P) := by
  induction l with
  | nil => exact sep_elim_r.trans Affine.affine
  | cons _ _ ih =>
    refine (sep_mono_l intuitionistically_sep_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r <| (sep_mono_l intuitionistically_elim).trans wand_elim_l).trans <|
      sep_assoc.2.trans <| (sep_mono_l ih).trans sep_comm.1

/-- Corresponds to `big_sepL_replicate` in Rocq Iris. -/
theorem replicate {P : PROP} {l : List A} :
    ([∗list] _x ∈ List.replicate l.length P, P) ⊣⊢ [∗list] _x ∈ l, P := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.replicate]
    exact .rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate, bigSepL, BigOpL.cons]
    exact ⟨sep_mono_r ih.1, sep_mono_r ih.2⟩

/-- Corresponds to `big_sepL_zip_seq` in Rocq Iris. -/
theorem zip_seq {Φ : Nat × A → PROP} {n : Nat} {l : List A} :
    ([∗list] p ∈ (List.range' n l.length).zip l, Φ p) ⊣⊢
      [∗list] i ↦ x ∈ l, Φ (n + i, x) :=
  equiv_iff.mp (BigOpL.zip_seq Φ n l)

/-- Lean-only: Big sep over zip with a sequence starting at 0.
    No direct Rocq equivalent (uses zero-indexed range). -/
theorem zip_with_range {Φ : Nat × A → PROP} {l : List A} :
    ([∗list] p ∈ (List.range l.length).zip l, Φ p) ⊣⊢
      [∗list] i ↦ x ∈ l, Φ (i, x) :=
  equiv_iff.mp (BigOpL.zip_with_range Φ l)

/-- Corresponds to `big_sepL_sep_zip` in Rocq Iris. -/
theorem sep_zip {B : Type _} {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP}
    {l₁ : List A} {l₂ : List B} (hlen : l₁.length = l₂.length) :
    ([∗list] i ↦ xy ∈ l₁.zip l₂, Φ i xy.1 ∗ Ψ i xy.2) ⊣⊢
      ([∗list] i ↦ x ∈ l₁, Φ i x) ∗ [∗list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zip_nil_left, bigSepL, bigOpL]; exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, bigSepL, bigOpL]
      have ih' := ih (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      exact (sep_congr_r ih').trans sep_sep_sep_comm

/-- Corresponds to `big_sepL_sep_zip_with` in Rocq Iris. -/
theorem sep_zip_with {B C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    {Φ : Nat → A → PROP} {Ψ : Nat → B → PROP} {l₁ : List A} {l₂ : List B}
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hlen : l₁.length = l₂.length) :
    ([∗list] i ↦ c ∈ List.zipWith f l₁ l₂, Φ i (g1 c) ∗ Ψ i (g2 c)) ⊣⊢
      ([∗list] i ↦ x ∈ l₁, Φ i x) ∗ [∗list] i ↦ y ∈ l₂, Ψ i y := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simp only [List.zipWith_nil_left, bigSepL, bigOpL]; exact emp_sep.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, bigSepL, bigOpL, hg1, hg2]
      have ih' := ih (l₂ := ys) (Φ := fun n => Φ (n + 1)) (Ψ := fun n => Ψ (n + 1)) hlen
      exact (sep_congr_r ih').trans sep_sep_sep_comm

/-- Corresponds to `big_sepL_zip_with` in Rocq Iris. -/
theorem zip_with {B C : Type _} (f : A → B → C) {Φ : Nat → C → PROP}
    {l₁ : List A} {l₂ : List B} :
    ([∗list] k ↦ c ∈ List.zipWith f l₁ l₂, Φ k c) ⊣⊢
      [∗list] k ↦ x ∈ l₁, match l₂[k]? with | some y => Φ k (f x y) | none => emp := by
  induction l₁ generalizing l₂ Φ with
  | nil => simp only [List.zipWith_nil_left, bigSepL, bigOpL]; exact .rfl
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      simp only [List.zipWith_nil_right, List.getElem?_nil, bigSepL, bigOpL]
      exact emp_sep.symm.trans (sep_congr_r (emp_l (l := xs)).symm)
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
                 bigSepL, bigOpL]
      exact sep_congr_r (ih (l₂ := ys) (Φ := fun n => Φ (n + 1)))

/-! ## Commuting Lemmas -/

/-- Corresponds to `big_sepL_sepL` in Rocq Iris. -/
theorem sepL {B : Type _} (Φ : Nat → A → Nat → B → PROP) (l₁ : List A) (l₂ : List B) :
    ([∗list] k1↦x1 ∈ l₁, [∗list] k2↦x2 ∈ l₂, Φ k1 x1 k2 x2) ⊣⊢
      ([∗list] k2↦x2 ∈ l₂, [∗list] k1↦x1 ∈ l₁, Φ k1 x1 k2 x2) := by
  induction l₁ generalizing Φ with
  | nil =>
    simp only [bigSepL, bigOpL]
    constructor
    · exact Entails.rfl.trans (equiv_iff.mp (BigOpL.unit_const l₂)).2
    · exact (equiv_iff.mp (BigOpL.unit_const l₂)).1
  | cons x xs ih =>
    simp only [bigSepL, bigOpL]
    have ih' := ih (fun i a j b => Φ (i + 1) a j b)
    constructor
    · refine (sep_mono_r ih'.1).trans ?_
      exact equiv_iff.mp (BigOpL.op_distr _ _ _) |>.2
    · refine equiv_iff.mp (BigOpL.op_distr _ _ _) |>.1.trans ?_
      exact sep_mono_r ih'.2

/-- Corresponds to `big_sepL_sepM` in Rocq Iris. -/
theorem sepM {B : Type _} {M : Type _} {K : Type _} [FiniteMap M K B]
    (Φ : Nat → A → K → B → PROP) (l : List A) (m : M) :
    ([∗list] k↦x ∈ l, [∗map] k'↦y ∈ m, Φ k x k' y) ⊣⊢
      ([∗map] k'↦y ∈ m, [∗list] k↦x ∈ l, Φ k x k' y) := by
  calc [∗list] k↦x ∈ l, [∗map] k'↦y ∈ m, Φ k x k' y
      _ ⊣⊢ [∗list] k↦x ∈ l, [∗list] kv ∈ toList m, Φ k x kv.1 kv.2 :=
          equiv_iff.mp <| BigSepL.congr fun k x => .rfl
      _ ⊣⊢ [∗list] kv ∈ toList m, [∗list] k↦x ∈ l, Φ k x kv.1 kv.2 :=
          @sepL PROP _ A (K × B) (fun k x _ kv => Φ k x kv.1 kv.2) l (toList m)
      _ ⊣⊢ [∗map] k'↦y ∈ m, [∗list] k↦x ∈ l, Φ k x k' y :=
          equiv_iff.mp <| BigSepL.congr fun _ kv => .rfl

/-- Corresponds to `big_sepL_sepS` in Rocq Iris. -/
theorem sepS {B : Type _} {S : Type _} [DecidableEq B] [FiniteSet S B] [FiniteSetLaws S B]
    (Φ : Nat → A → B → PROP) (l : List A) (X : S) :
    ([∗list] k↦x ∈ l, [∗set] y ∈ X, Φ k x y) ⊣⊢
      ([∗set] y ∈ X, [∗list] k↦x ∈ l, Φ k x y) := by
  calc [∗list] k↦x ∈ l, [∗set] y ∈ X, Φ k x y
      _ ⊣⊢ [∗list] k↦x ∈ l, [∗list] y ∈ toList X, Φ k x y :=
          equiv_iff.mp <| BigSepL.congr fun k x => .rfl
      _ ⊣⊢ [∗list] y ∈ toList X, [∗list] k↦x ∈ l, Φ k x y :=
          @sepL PROP _ A B (fun k x _ y => Φ k x y) l (toList X)
      _ ⊣⊢ [∗set] y ∈ X, [∗list] k↦x ∈ l, Φ k x y :=
          equiv_iff.mp <| BigSepL.congr fun _ y => .rfl

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_sepL_timeless`, `big_sepL_timeless'`, `big_sepL_timeless_id`: Requires `sep_timeless` infrastructure
- `big_sepL_zip_seqZ`: Uses Z (integers); only Nat version available
-/

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

syntax "[∗ " "list" "] " ident ";" ident " ∈ " term ";" term ", " term : term
syntax "[∗ " "list" "] " ident " ↦ " ident ";" ident " ∈ " term ";" term ", " term : term

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

namespace BigSepL2

/-- Corresponds to `big_sepL2_nil` in Rocq Iris. -/
@[simp]
theorem nil {Φ : Nat → A → B → PROP} :
    ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') ⊣⊢ emp := by
  simp only [bigSepL2]
  exact .rfl

/-- Corresponds to `big_sepL2_nil'` in Rocq Iris. -/
theorem nil' {P : PROP} [Affine P] {Φ : Nat → A → B → PROP} :
    P ⊢ ([∗list] k ↦ x;x' ∈ ([] : List A);([] : List B), Φ k x x') :=
  Affine.affine.trans nil.2

/-- Corresponds to `big_sepL2_nil_inv_l` in Rocq Iris. -/
theorem nil_inv_l {Φ : Nat → A → B → PROP} {l2 : List B} :
   ([∗list] k ↦ x;x' ∈ [];l2, Φ k x x')  ⊢ ⌜l2 = []⌝ := by
  cases l2 with
  | nil => exact pure_intro rfl
  | cons y ys => simp only [bigSepL2]; exact false_elim

/-- Corresponds to `big_sepL2_nil_inv_r` in Rocq Iris. -/
theorem nil_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} :
    ([∗list] k ↦ x;x' ∈ l1;[], Φ k x x') ⊢ ⌜l1 = []⌝ := by
  cases l1 with
  | nil => exact pure_intro rfl
  | cons x xs => simp only [bigSepL2]; exact false_elim

/-- Corresponds to `big_sepL2_cons` in Rocq Iris. -/
theorem cons {Φ : Nat → A → B → PROP} {x1 : A} {x2 : B} {xs1 : List A} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2 := by
  simp only [bigSepL2]
  exact .rfl

/-- Corresponds to `big_sepL2_cons_inv_l` in Rocq Iris. -/
theorem cons_inv_l {Φ : Nat → A → B → PROP} {x1 : A} {xs1 : List A} {l2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ x1 :: xs1;l2, Φ k y1 y2) ⊣⊢
      ∃ x2 xs2, ⌜l2 = x2 :: xs2⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) := by
  cases l2 with
  | nil =>
    simp only [bigSepL2]
    constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons y ys =>
    simp only [bigSepL2]
    constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs2 => iprop(⌜y :: ys = y :: xs2⌝ ∧
          (Φ 0 x1 y ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) ys).trans
        (exists_intro (Ψ := fun x2 => iprop(∃ xs2, ⌜y :: ys = x2 :: xs2⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) y))
    · exact exists_elim fun x2 => exists_elim fun xs2 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

/-- Corresponds to `big_sepL2_cons_inv_r` in Rocq Iris. -/
theorem cons_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {x2 : B} {xs2 : List B} :
    ([∗list] k ↦ y1;y2 ∈ l1;x2 :: xs2, Φ k y1 y2) ⊣⊢
      ∃ x1 xs1, ⌜l1 = x1 :: xs1⌝ ∧ (Φ 0 x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ xs1;xs2, Φ (k + 1) y1 y2) := by
  cases l1 with
  | nil =>
    simp only [bigSepL2]
    constructor
    · exact false_elim
    · exact exists_elim fun _ => exists_elim fun _ =>
        and_elim_l.trans (pure_elim' (fun h => nomatch h))
  | cons x xs =>
    simp only [bigSepL2]
    constructor
    · exact (and_intro (pure_intro rfl) Entails.rfl).trans
        ((exists_intro (Ψ := fun xs1 => iprop(⌜x :: xs = x :: xs1⌝ ∧
          (Φ 0 x x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) xs).trans
        (exists_intro (Ψ := fun x1 => iprop(∃ xs1, ⌜x :: xs = x1 :: xs1⌝ ∧
          (Φ 0 x1 x2 ∗ bigSepL2 (fun n => Φ (n + 1)) xs1 xs2))) x))
    · exact exists_elim fun x1 => exists_elim fun xs1 =>
        pure_elim_l fun h => by cases h; exact Entails.rfl

/-- Corresponds to `big_sepL2_singleton` in Rocq Iris. -/
theorem singleton {Φ : Nat → A → B → PROP} {x : A} {y : B} :
    ([∗list] k ↦ x1;x2 ∈ [x];[y], Φ k x1 x2) ⊣⊢ Φ 0 x y := by
  simp only [bigSepL2]
  exact sep_emp

/-! ## Alternative Characterization via Zip -/

/-- Corresponds to `big_sepL2_alt` in Rocq Iris. -/
theorem alt {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL (fun k p => Φ k p.1 p.2) (l1.zip l2)) := by
  refine ⟨and_intro ?fwd_len ?fwd_sep, pure_elim_l fun hlen => ?bwd⟩
  case fwd_len =>
    induction l1 generalizing l2 Φ with
    | nil => cases l2 <;> simp only [bigSepL2] <;> first | exact pure_intro rfl | exact false_elim
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim
      | cons x2 xs2 =>
        simp only [bigSepL2, List.length_cons]
        refine (sep_mono true_intro ih).trans ?_
        refine (true_sep (PROP := PROP)).1.trans ?_
        exact pure_mono (congrArg (· + 1))
  case fwd_sep =>
    induction l1 generalizing l2 Φ with
    | nil => cases l2 <;> simp only [bigSepL2, List.zip_nil_left, bigSepL, bigOpL] <;>
             first | exact .rfl | exact false_elim
    | cons x xs ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim
      | cons y ys => simp only [bigSepL2, List.zip_cons_cons, bigSepL, bigOpL]
                     exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)))
  case bwd =>
    induction l1 generalizing l2 Φ with
    | nil => cases l2 <;> first | simp only [bigSepL2, List.zip_nil_left, bigSepL, bigOpL]; exact .rfl
                                | simp at hlen
    | cons x xs ih =>
      cases l2 with
      | nil => simp at hlen
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [bigSepL2, List.zip_cons_cons, bigSepL, bigOpL]
        exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) hlen)

/-! ## Length Lemma -/

/-- Corresponds to `big_sepL2_length` in Rocq Iris. -/
theorem length {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ iprop(⌜l1.length = l2.length⌝) :=
  alt.1.trans and_elim_l

/-! ## Monotonicity and Congruence -/

/-- Corresponds to `big_sepL2_mono` in Rocq Iris. -/
theorem mono {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 <;> simp only [bigSepL2] <;> exact .rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact .rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      exact sep_mono (h 0 x1 x2 rfl rfl) (ih fun k y1 y2 => h (k + 1) y1 y2)

/-- Corresponds to `big_sepL2_proper` in Rocq Iris. -/
theorem proper {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  constructor
  · apply mono; intro k x1 x2 h1 h2; exact ( (h k x1 x2 h1 h2)).1
  · apply mono; intro k x1 x2 h1 h2; exact ( (h k x1 x2 h1 h2)).2

/-- No direct Rocq equivalent; simplified version of `proper` that doesn't require lookup hypotheses.
    Useful when the predicate transformation is unconditional. -/
theorem congr {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  apply proper
  intro k x1 x2 _ _
  exact h k x1 x2

/-- Corresponds to `big_sepL2_ne` in Rocq Iris. -/
theorem ne {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat}
    (h : ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ≡{n}≡ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 <;> simp only [bigSepL2] <;> exact .rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact .rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      exact sep_ne.ne (h 0 x1 x2 rfl rfl) (ih fun k y1 y2 => h (k + 1) y1 y2)

/-- No direct Rocq equivalent; monotonicity without lookup condition. -/
theorem mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-- No direct Rocq equivalent; flip version of mono'. -/
theorem flip_mono' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (h : ∀ k x1 x2, Ψ k x1 x2 ⊢ Φ k x1 x2) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊢ ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  mono (fun k x1 x2 _ _ => h k x1 x2)

/-- Corresponds to `big_sepL2_persistent'` in Rocq Iris. -/
instance persistent {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  persistent := by
    induction l1 generalizing l2 Φ with
    | nil =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact persistently_emp_2
      | cons => simp only [bigSepL2]; exact false_elim.trans (persistently_mono false_elim)
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim.trans (persistently_mono false_elim)
      | cons x2 xs2 =>
        simp only [bigSepL2]
        have h1 : Φ 0 x1 x2 ⊢ <pers> Φ 0 x1 x2 := Persistent.persistent
        have h2 : ([∗list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ⊢
            iprop(<pers> [∗list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) := ih
        exact (sep_mono h1 h2).trans persistently_sep_2

/-- Corresponds to `big_sepL2_affine'` in Rocq Iris. -/
instance affine {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    [∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) where
  affine := by
    induction l1 generalizing l2 Φ with
    | nil =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact Entails.rfl
      | cons => simp only [bigSepL2]; exact false_elim
    | cons x1 xs1 ih =>
      cases l2 with
      | nil => simp only [bigSepL2]; exact false_elim
      | cons x2 xs2 =>
        simp only [bigSepL2]
        have h1 : Φ 0 x1 x2 ⊢ emp := Affine.affine
        have h2 : ([∗list] n ↦ y1;y2 ∈ xs1;xs2, Φ (n + 1) y1 y2) ⊢ emp := ih
        exact (sep_mono h1 h2).trans ( sep_emp).1

/-- Corresponds to `big_sepL2_sep` in Rocq Iris. -/
theorem sep' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  induction l1 generalizing l2 Φ Ψ with
  | nil => cases l2 <;> simp only [bigSepL2] <;> first | exact emp_sep.symm
                                                       | exact ⟨false_elim, sep_elim_l.trans false_elim⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, sep_elim_l.trans false_elim⟩
    | cons x2 xs2 => simp only [bigSepL2]; exact (sep_congr .rfl ih).trans sep_sep_sep_comm

/-- Corresponds to `big_sepL2_sep_2` in Rocq Iris. -/
theorem sep_2 {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∗ Ψ k x1 x2) :=
  sep'.symm

/-- Corresponds to `big_sepL2_and` in Rocq Iris. -/
theorem and' {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 ∧ Ψ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∧ ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  apply and_intro
  · exact mono fun k x1 x2 _ _ => and_elim_l
  · exact mono fun k x1 x2 _ _ => and_elim_r

/-- Corresponds to `big_sepL2_pure_1` in Rocq Iris. -/
theorem pure_1 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊢
      iprop(⌜∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  (and_mono .rfl BigSepL.pure_1 |>.trans pure_and.1 |>.trans <| pure_mono fun ⟨_, h⟩ k x1 x2 h1 h2 =>
    h k (x1, x2) (List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩)) |> alt.1.trans

/-- Corresponds to `big_sepL2_affinely_pure_2` in Rocq Iris. -/
theorem affinely_pure_2 {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    iprop(<affine> ⌜l1.length = l2.length ∧
      ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, (<affine> ⌜φ k x1 x2⌝ : PROP)) :=
  (affinely_mono pure_and.2).trans affinely_and.1 |>.trans
    (and_mono .rfl <| (affinely_mono <| pure_mono fun h k (p : A × B) hp =>
        h k p.1 p.2 (List.getElem?_zip_eq_some.mp hp).1 (List.getElem?_zip_eq_some.mp hp).2).trans
      BigSepL.affinely_pure_2) |>.trans (and_mono affinely_elim .rfl) |>.trans
    (alt (Φ := fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝))).2

/-- Corresponds to `big_sepL2_pure` in Rocq Iris. -/
theorem pure [BIAffine PROP] {φ : Nat → A → B → Prop} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, (⌜φ k x1 x2⌝ : PROP)) ⊣⊢
      iprop(⌜l1.length = l2.length ∧
        ∀ k x1 x2, l1[k]? = some x1 → l2[k]? = some x2 → φ k x1 x2⌝ : PROP) :=
  ⟨(and_intro length pure_1).trans pure_and.1,
   (affine_affinely _).2.trans affinely_pure_2 |>.trans (mono fun _ _ _ _ _ => affinely_elim)⟩

/-- When the predicate is constantly emp, bigSepL2 reduces to a length equality check. -/
theorem emp_l [BIAffine PROP] {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ _x1;_x2 ∈ l1;l2, (emp : PROP)) ⊣⊢ iprop(⌜l1.length = l2.length⌝) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil =>
      simp only [bigSepL2]
      exact (true_emp (PROP := PROP)).symm.trans (pure_true (PROP := PROP) rfl).symm
    | cons => simp only [bigSepL2]; exact ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact ⟨false_elim, pure_elim' (fun h => nomatch h)⟩
    | cons x2 xs2 =>
      simp only [bigSepL2, List.length_cons]
      exact emp_sep.trans <| ih.trans ⟨pure_mono (congrArg (· + 1)), pure_mono Nat.succ.inj⟩

/-- Corresponds to Rocq's `big_sepL2_app`. -/
theorem app' {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) -∗
      ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) := by
  apply wand_intro'
  induction l1a generalizing l2a Φ with
  | nil =>
    cases l2a with
    | nil => simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]; exact sep_emp.1
    | cons => simp only [bigSepL2, List.nil_append]; exact sep_elim_r.trans false_elim
  | cons x1 xs1 ih =>
    cases l2a with
    | nil => simp only [bigSepL2, List.nil_append]; exact sep_elim_r.trans false_elim
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      -- Rocq: by rewrite -assoc IH
      -- Pattern: A ∗ (B ∗ C) where we need B ∗ (A ∗ C) to apply IH, then reassoc to (B ∗ result)
      have hcongr : ([∗list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) ⊣⊢
                   ([∗list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) :=
        congr fun n _ _ => by simp only [Nat.add_assoc]; exact BiEntails.rfl
      refine (sep_mono_l hcongr.1).trans ?_
      refine sep_symm.trans ?_
      refine sep_assoc.1.trans ?_
      refine (sep_mono_r sep_symm).trans ?_
      exact sep_mono_r (ih (Φ := fun n => Φ (n + 1)) (l2a := xs2))

/-- Inverse direction of app -/
private theorem app_inv_core {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  induction l1a generalizing l2a Φ with
  | nil =>
    cases l2a with
    | nil =>
      simp only [bigSepL2, List.nil_append, List.length_nil, Nat.add_zero]
      exact emp_sep.2
    | cons y ys =>
      cases hlen with
      | inl h => exact absurd h (by simp only [List.length_nil, List.length_cons]; omega)
      | inr h =>
        simp only [bigSepL2, List.nil_append]
        have hne : l1b.length ≠ (y :: ys ++ l2b).length := by
          simp only [List.length_cons, List.length_append]; omega
        exact length.trans (pure_elim' fun heq => absurd heq hne)
  | cons x1 xs1 ih =>
    cases l2a with
    | nil =>
      cases hlen with
      | inl h => exact absurd h (by simp only [List.length_nil, List.length_cons]; omega)
      | inr h =>
        simp only [bigSepL2, List.nil_append]
        have hne : (x1 :: xs1 ++ l1b).length ≠ l2b.length := by
          simp only [List.length_cons, List.length_append]; omega
        exact length.trans (pure_elim' fun heq => absurd heq hne)
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons]
      have hlen' : xs1.length = xs2.length ∨ l1b.length = l2b.length := by
        cases hlen with
        | inl h => left; simp only [List.length_cons] at h; omega
        | inr h => right; exact h
      have ihspec := ih (Φ := fun n => Φ (n + 1)) (l2a := xs2) hlen'
      have hcongr : ([∗list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + xs1.length + 1) y1 y2) ⊣⊢
                   ([∗list] n ↦ y1;y2 ∈ l1b;l2b, Φ (n + (xs1.length + 1)) y1 y2) :=
        congr fun n _ _ => by simp only [Nat.add_assoc]; exact BiEntails.rfl
      -- Rocq: by rewrite -assoc IH
      refine (sep_mono_r ihspec).trans ?_
      refine (sep_mono_r (sep_mono_r hcongr.2)).trans ?_
      exact sep_assoc.2

/-- bi-entailment version when we know one pair of lengths match. -/
theorem app {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) :=
  ⟨app_inv_core hlen, sep_symm.trans (wand_elim' app')⟩

theorem app_inv {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
      ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (k + l1a.length) x1 x2) := by
  exact app hlen

/-- Corresponds to `big_sepL2_snoc` in Rocq Iris. -/
theorem snoc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {x : A} {y : B} :
    ([∗list] k ↦ x1;x2 ∈ l1 ++ [x];l2 ++ [y], Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ∗ Φ l1.length x y := by
  have h := app (Φ := Φ) (l1a := l1) (l2a := l2) (l1b := [x]) (l2b := [y]) (Or.inr rfl)
  simp only [bigSepL2, Nat.zero_add] at h
  exact h.trans (sep_congr .rfl sep_emp)

/-- Corresponds to `big_sepL2_fmap_l` in Rocq Iris. -/
theorem fmap_l {C : Type _} (f : C → A) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) y) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_cons, bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_fmap_r` in Rocq Iris. -/
theorem fmap_r {C : Type _} (f : C → B) {Φ : Nat → A → B → PROP}
    {l1 : List A} {l2 : List C} :
    ([∗list] k ↦ x;y ∈ l1;l2.map f, Φ k x y) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x (f y)) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons => simp only [List.map_cons, bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [List.map_nil, bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [List.map_cons, bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- No direct Rocq equivalent; combined fmap_l and fmap_r. -/
theorem fmap {C D : Type _} (f : C → A) (g : D → B) {Φ : Nat → A → B → PROP}
    {l1 : List C} {l2 : List D} :
    ([∗list] k ↦ x;y ∈ l1.map f;l2.map g, Φ k x y) ⊣⊢
      ([∗list] k ↦ x;y ∈ l1;l2, Φ k (f x) (g y)) :=
  (fmap_l f).trans (fmap_r g)

/-- Corresponds to `big_sepL2_flip` in Rocq Iris. -/
theorem flip {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x;y ∈ l2;l1, Φ k y x) ⊣⊢ ([∗list] k ↦ x;y ∈ l1;l2, Φ k x y) := by
  induction l1 generalizing l2 Φ with
  | nil =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BiEntails.rfl
    | cons => simp only [bigSepL2]; exact BiEntails.rfl
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2]; exact BiEntails.rfl
    | cons x2 xs2 =>
      simp only [bigSepL2]
      exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_fst_snd` in Rocq Iris. -/
theorem fst_snd {Φ : Nat → A → B → PROP} {l : List (A × B)} :
    ([∗list] k ↦ x;y ∈ l.map Prod.fst;l.map Prod.snd, Φ k x y) ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) l := by
  have zip_fst_snd : (l.map Prod.fst).zip (l.map Prod.snd) = l := by
    induction l with
    | nil => rfl
    | cons hd tl ih => simp only [List.map_cons, List.zip_cons_cons, ih, Prod.eta]
  refine alt.trans ?_
  simp only [List.length_map, zip_fst_snd]
  exact true_and

/-- When we have bigSepL2 of l1' ++ l1'' with some l2, we can split l2 to match. -/
theorem app_inv_l {Φ : Nat → A → B → PROP} {l1' l1'' : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1' ++ l1'';l2, Φ k x1 x2) ⊢
      iprop(∃ l2' l2'', ⌜l2 = l2' ++ l2''⌝ ∧
        (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l1'.length) x1 x2))) := by
  refine (exists_intro' (l2.take l1'.length) (exists_intro' (l2.drop l1'.length)
    (and_intro (pure_intro (List.take_append_drop l1'.length l2).symm) ?_)))
  induction l1' generalizing l2 Φ with
  | nil =>
    simp only [List.nil_append, List.length_nil, List.take_zero, List.drop_zero, Nat.add_zero]
    exact emp_sep.symm.1.trans (sep_mono_l nil.symm.1)
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp only [bigSepL2, List.cons_append]; exact false_elim
    | cons x2 xs2 =>
      simp only [bigSepL2, List.cons_append, List.length_cons, List.take_succ_cons, List.drop_succ_cons]
      exact (sep_mono_r ih).trans (sep_assoc.symm.1.trans
        (sep_mono_r (mono' fun k _ _ => by simp only [Nat.add_assoc]; exact .rfl)))

/-- When we have bigSepL2 of l1 with l2' ++ l2'', we can split l1 to match. -/
theorem app_inv_r {Φ : Nat → A → B → PROP} {l1 : List A} {l2' l2'' : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2' ++ l2'', Φ k x1 x2) ⊢
      iprop(∃ l1' l1'', ⌜l1 = l1' ++ l1''⌝ ∧
        (([∗list] k ↦ x1;x2 ∈ l1';l2', Φ k x1 x2) ∗
         ([∗list] k ↦ x1;x2 ∈ l1'';l2'', Φ (k + l2'.length) x1 x2))) :=
  flip.symm.1.trans app_inv_l |>.trans <|
    exists_mono fun _ => exists_mono fun _ => and_mono .rfl (sep_mono flip.1 flip.1)

/-- Corresponds to `big_sepL2_insert_acc` in Rocq. -/
theorem insert_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (∀ y1, ∀ y2, Φ i y1 y2 -∗
        [∗list] k ↦ z1;z2 ∈ l1.set i y1;l2.set i y2, Φ k z1 z2)) := by
  refine alt.1.trans (pure_elim_l fun hlen => ?_)
  have hzip : (l1.zip l2)[i]? = some (x1, x2) := List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩
  refine (BigSepL.insert_acc hzip).trans (sep_mono_r ?_)
  refine forall_intro fun y1 => forall_intro fun y2 => (forall_elim (y1, y2)).trans (wand_mono_r ?_)
  have hi1 : i < l1.length := List.getElem?_eq_some_iff.mp h1 |>.1
  have hi2 : i < l2.length := List.getElem?_eq_some_iff.mp h2 |>.1
  have hizip : i < (l1.zip l2).length := by simp only [List.length_zip, Nat.min_def]; split <;> omega
  have hzip_set : (l1.zip l2).set i (y1, y2) = (l1.set i y1).zip (l2.set i y2) := by
    apply List.ext_getElem?; intro k; simp only [List.getElem?_set]
    by_cases hik : i = k
    · subst hik; simp only [hizip, ↓reduceIte]
      exact (List.getElem?_zip_eq_some.mpr ⟨List.getElem?_set_self hi1, List.getElem?_set_self hi2⟩).symm
    · simp only [List.zip_eq_zipWith, List.getElem?_zipWith, List.getElem?_set, hik, ↓reduceIte]
  have hlen1 : (l1.set i y1).length = (l2.set i y2).length := by simp only [List.length_set]; exact hlen
  rw [hzip_set]; exact (and_intro (pure_intro hlen1) .rfl).trans alt.2

theorem lookup_acc {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)) := by
  have hi1 : i < l1.length := List.getElem?_eq_some_iff.mp h1 |>.1
  have hi2 : i < l2.length := List.getElem?_eq_some_iff.mp h2 |>.1
  have hx1 : l1[i] = x1 := List.getElem?_eq_some_iff.mp h1 |>.2
  have hx2 : l2[i] = x2 := List.getElem?_eq_some_iff.mp h2 |>.2
  have hset1 : l1.set i x1 = l1 := hx1 ▸ List.set_getElem_self hi1
  have hset2 : l2.set i x2 = l2 := hx2 ▸ List.set_getElem_self hi2
  exact (insert_acc h1 h2).trans (sep_mono_r ((forall_elim x1).trans
    ((forall_elim x2).trans (hset1.symm ▸ hset2.symm ▸ .rfl))))

/-- Corresponds to `big_sepL2_lookup` in Rocq Iris. -/
theorem lookup {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    [TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))] →
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2
  | TCOr.l => by
    have hi1 : i < l1.length := List.getElem?_eq_some_iff.mp h1 |>.1
    have hi2 : i < l2.length := List.getElem?_eq_some_iff.mp h2 |>.1
    have hx1 : l1[i] = x1 := List.getElem?_eq_some_iff.mp h1 |>.2
    have hx2 : l2[i] = x2 := List.getElem?_eq_some_iff.mp h2 |>.2
    have hlen1 : (l1.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi1)
    have hmiddle1 : l1 = l1.take i ++ x1 :: l1.drop (i + 1) := by
      have htake : l1.take (i + 1) = l1.take i ++ [x1] := by rw [List.take_succ_eq_append_getElem hi1, hx1]
      exact (List.take_append_drop (i + 1) l1).symm.trans (htake ▸ List.append_assoc ..)
    have hmiddle2 : l2 = l2.take i ++ x2 :: l2.drop (i + 1) := by
      have htake : l2.take (i + 1) = l2.take i ++ [x2] := by rw [List.take_succ_eq_append_getElem hi2, hx2]
      exact (List.take_append_drop (i + 1) l2).symm.trans (htake ▸ List.append_assoc ..)
    rw [hmiddle1, hmiddle2]
    have hlen2 : (l2.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi2)
    have happ := app (Φ := Φ) (l1a := l1.take i) (l1b := x1 :: l1.drop (i + 1))
      (l2a := l2.take i) (l2b := x2 :: l2.drop (i + 1)) (Or.inl (hlen1.trans hlen2.symm))
    simp only [hlen1, bigSepL2, Nat.zero_add] at happ
    exact happ.1.trans (sep_elim_r.trans sep_elim_l)
  | TCOr.r => (lookup_acc h1 h2).trans sep_elim_l

/-! ## Higher-Order Lemmas -/

/-- Corresponds to `big_sepL2_intro` in Rocq Iris. -/
theorem intro {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧
      □ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  refine pure_elim_l fun hlen => ?_
  suffices h : iprop(□ (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) ⊢
      bigSepL2 Φ l1 l2 from h
  induction l1 generalizing l2 Φ with
  | nil => cases l2 with
    | nil => simp only [bigSepL2]; exact Affine.affine
    | cons => simp at hlen
  | cons y1 ys1 ih => cases l2 with
    | nil => simp at hlen
    | cons y2 ys2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bigSepL2]
      have head_step : iprop(□ (∀ k, ∀ x1, ∀ x2,
          iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) ⊢ Φ 0 y1 y2 :=
        intuitionistically_elim.trans ((forall_elim 0).trans ((forall_elim y1).trans ((forall_elim y2).trans
          (((and_intro (pure_intro rfl) .rfl).trans imp_elim_r).trans
            ((and_intro (pure_intro rfl) .rfl).trans imp_elim_r)))))
      have tail_step : iprop(□ (∀ k, ∀ x1, ∀ x2,
          iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2))) ⊢
          iprop(□ (∀ k, ∀ x1, ∀ x2, iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2))) :=
        intuitionistically_mono (forall_intro fun k => forall_intro fun z1 => forall_intro fun z2 =>
          ((forall_elim (k + 1)).trans ((forall_elim z1).trans (forall_elim z2))).trans
            (by simp only [List.getElem?_cons_succ]; exact .rfl))
      exact intuitionistically_sep_idem.symm.1.trans (sep_mono head_step (tail_step.trans (ih hlen)))

/-- Corresponds to `big_sepL2_wand` in Rocq Iris. -/
theorem wand {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2 -∗ Ψ k x1 x2) -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  wand_intro <| sep_2.1.trans (mono fun _ _ _ _ _ => wand_elim_r)

/-- Corresponds to `big_sepL2_impl` in Rocq Iris. -/
theorem impl {Φ Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      iprop(□ (∀ k, ∀ x1, ∀ x2,
        iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2))) -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  refine wand_intro ?_
  have hlen_extract : ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL2 Φ l1 l2) := and_self.2.trans (and_mono_l length)
  refine (sep_mono_l hlen_extract).trans ((sep_mono_l persistent_and_affinely_sep_l.1).trans
    (sep_assoc.1.trans (persistent_and_affinely_sep_l.symm.1.trans ?_)))
  refine pure_elim_l fun hlen => ?_
  have hwands := (and_intro (pure_intro hlen) Entails.rfl).trans
    (intro (Φ := fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)))
  exact (sep_mono_r hwands).trans (sep_2.1.trans (mono fun _ _ _ _ _ => wand_elim_r))

/-- Corresponds to `big_sepL2_forall` in Rocq Iris. -/
theorem forall' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}
    (hPersistent : ∀ k x1 x2, Persistent (Φ k x1 x2)) :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧
        (∀ k, ∀ x1, ∀ x2, iprop(⌜l1[k]? = some x1⌝ → ⌜l2[k]? = some x2⌝ → Φ k x1 x2))) := by
  haveI : ∀ k x1 x2, Persistent (Φ k x1 x2) := hPersistent
  constructor
  · exact and_intro length (forall_intro fun k => forall_intro fun x1 => forall_intro fun x2 =>
      imp_intro' (pure_elim_l fun h1 => imp_intro' (pure_elim_l fun h2 => lookup h1 h2)))
  · refine pure_elim_l fun hlen => ?_
    induction l1 generalizing l2 Φ hPersistent with
    | nil => cases l2 with
      | nil => simp only [bigSepL2]; exact Affine.affine
      | cons => simp at hlen
    | cons y1 ys1 ih => cases l2 with
      | nil => simp at hlen
      | cons y2 ys2 =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [bigSepL2]
        haveI : ∀ k x1 x2, Persistent (Φ k x1 x2) := hPersistent
        have head_step : iprop(∀ k, ∀ x1, ∀ x2,
            iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)) ⊢ Φ 0 y1 y2 :=
          ((forall_elim 0).trans ((forall_elim y1).trans ((forall_elim y2).trans
            (((and_intro (pure_intro rfl) .rfl).trans imp_elim_r).trans
              ((and_intro (pure_intro rfl) .rfl).trans imp_elim_r)))))
        have tail_step : iprop(∀ k, ∀ x1, ∀ x2,
            iprop(⌜(y1 :: ys1)[k]? = some x1⌝ → ⌜(y2 :: ys2)[k]? = some x2⌝ → Φ k x1 x2)) ⊢
            iprop(∀ k, ∀ x1, ∀ x2, iprop(⌜ys1[k]? = some x1⌝ → ⌜ys2[k]? = some x2⌝ → Φ (k + 1) x1 x2)) :=
          forall_intro fun k => forall_intro fun z1 => forall_intro fun z2 =>
            ((forall_elim (k + 1)).trans ((forall_elim z1).trans (forall_elim z2))).trans
              (by simp only [List.getElem?_cons_succ]; exact .rfl)
        have hP' : ∀ k x1 x2, Persistent (Φ (k + 1) x1 x2) := fun k x1 x2 => hPersistent (k + 1) x1 x2
        exact (and_self.2.trans (and_mono_l head_step)).trans (persistent_and_sep_1.trans
          (sep_mono_r (tail_step.trans (ih hP' hP' hlen))))

/-! ## Modality Interaction -/

/-- Corresponds to `big_sepL2_persistently` in Rocq Iris. -/
theorem persistently [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(<pers> [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ([∗list] k ↦ x1;x2 ∈ l1;l2, <pers> Φ k x1 x2) :=
  (persistently_congr alt).trans persistently_and |>.trans (and_congr persistently_pure .rfl) |>.trans
    (and_congr .rfl BigSepL.persistently) |>.trans (alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2))).symm

/-- Corresponds to `big_sepL2_later_2` in Rocq Iris. -/
theorem later_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷ Φ k x1 x2) ⊢
      iprop(▷ [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) :=
  (alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2))).1.trans (and_mono later_intro BigSepL.later_2) |>.trans
    later_and.2 |>.trans (later_mono alt.2)

/-- Corresponds to `big_sepL2_laterN_2` in Rocq Iris. -/
theorem laterN_2 {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {n : Nat} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, ▷^[n] Φ k x1 x2) ⊢
      iprop(▷^[n] [∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 x2) := by
  induction n with
  | zero => exact Entails.rfl
  | succ m ih => exact later_2.trans (later_mono ih)

/-- Corresponds to `big_sepL2_sepL` in Rocq Iris. -/
theorem sepL {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ (bigSepL Φ1 l1 ∗ bigSepL Φ2 l2)) := by
  have h hlen := BigSepL.sep_zip (Φ := Φ1) (Ψ := Φ2) (l₁ := l1) (l₂ := l2) hlen
  refine alt.trans ⟨pure_elim_l fun hlen => and_intro (pure_intro hlen) (h hlen).1,
                    pure_elim_l fun hlen => and_intro (pure_intro hlen) (h hlen).2⟩

/-- Corresponds to `big_sepL2_sepL_2` in Rocq Iris. -/
theorem sepL_2 {Φ1 : Nat → A → PROP} {Φ2 : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ1 l1) ⊢ bigSepL Φ2 l2 -∗
      ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ1 k x1 ∗ Φ2 k x2) := by
  refine wand_intro ?_
  -- Rearrange: (⌜len⌝ ∧ Φ1s) ∗ Φ2s ⊢ ⌜len⌝ ∧ (Φ1s ∗ Φ2s)
  exact (sep_mono_l persistent_and_affinely_sep_l.1).trans sep_assoc.1
    |>.trans persistent_and_affinely_sep_l.symm.1 |>.trans sepL.2

/-- Corresponds to `big_sepL2_reverse_2` in Rocq Iris. -/
theorem reverse_2 {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) ⊢
      ([∗list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) := by
  refine (and_self.2.trans (and_mono_l length)).trans (pure_elim_l fun hlen => ?_)
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp only [bigSepL2, List.reverse_nil] <;> first | exact .rfl | simp at hlen
  | cons x1 xs1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons x2 xs2 =>
      simp only [List.length_cons] at hlen
      simp only [bigSepL2, List.reverse_cons]
      exact sep_comm.1.trans (sep_mono_l (ih (Nat.succ.inj hlen))) |>.trans
        (snoc (Φ := fun _ => Φ)).2

/-- Corresponds to `big_sepL2_reverse` in Rocq Iris. -/
theorem reverse {Φ : A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] _k ↦ x1;x2 ∈ l1.reverse;l2.reverse, Φ x1 x2) ⊣⊢
      ([∗list] _k ↦ x1;x2 ∈ l1;l2, Φ x1 x2) := by
  constructor
  · have h1 := reverse_2 (Φ := Φ) (l1 := l1.reverse) (l2 := l2.reverse)
    simp only [List.reverse_reverse] at h1
    exact h1
  · exact reverse_2

/-! ## Replicate Lemmas -/

/-- Corresponds to `big_sepL2_replicate_l` in Rocq Iris. -/
theorem replicate_l {Φ : Nat → A → B → PROP} {l : List B} {x : A} :
    ([∗list] k ↦ x1;x2 ∈ List.replicate l.length x;l, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x2 => Φ k x x2) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact BiEntails.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_replicate_r` in Rocq Iris. -/
theorem replicate_r {Φ : Nat → A → B → PROP} {l : List A} {x : B} :
    ([∗list] k ↦ x1;x2 ∈ l;List.replicate l.length x, Φ k x1 x2) ⊣⊢
      bigSepL (fun k x1 => Φ k x1 x) l := by
  induction l generalizing Φ with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, bigSepL2, bigSepL, bigOpL]
    exact BiEntails.rfl
  | cons y ys ih =>
    simp only [List.length_cons, List.replicate_succ, bigSepL2, bigSepL, bigOpL]
    exact sep_congr .rfl (ih (Φ := fun n => Φ (n + 1)))

/-- Corresponds to `big_sepL2_app_same_length` in Rocq Iris. -/
theorem app_same_length {Φ : Nat → A → B → PROP} {l1a l1b : List A} {l2a l2b : List B}
    (hlen : l1a.length = l2a.length ∨ l1b.length = l2b.length) :
    ([∗list] k ↦ x1;x2 ∈ l1a ++ l1b;l2a ++ l2b, Φ k x1 x2) ⊣⊢
      iprop(([∗list] k ↦ x1;x2 ∈ l1a;l2a, Φ k x1 x2) ∗
            ([∗list] k ↦ x1;x2 ∈ l1b;l2b, Φ (l1a.length + k) x1 x2)) :=
  (app hlen).trans (sep_congr .rfl (congr fun k _ _ => by simp only [Nat.add_comm]; exact .rfl))

/-- No direct Rocq equivalent; when Φ doesn't depend on second argument. -/
theorem const_sepL_l {Φ : Nat → A → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;_x2 ∈ l1;l2, Φ k x1) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l1) := by
  have fst_zip : ∀ hlen : l1.length = l2.length, (l1.zip l2).map Prod.fst = l1 := by
    intro hlen; clear Φ
    induction l1 generalizing l2 with
    | nil => cases l2 <;> first | rfl | simp at hlen
    | cons x xs ih =>
      cases l2 with
      | nil => simp at hlen
      | cons y ys => simp only [List.length_cons] at hlen; simp [ih (Nat.succ.inj hlen)]
  have hfmap : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL (fun k p => Φ k p.1) (l1.zip l2) :=
    equiv_iff.mp (BigSepL.fmap Prod.fst)
  refine alt.trans ⟨pure_elim_l fun hlen => and_intro (pure_intro hlen) ?_,
                    pure_elim_l fun hlen => and_intro (pure_intro hlen) ?_⟩
  · have : bigSepL Φ ((l1.zip l2).map Prod.fst) ⊣⊢ bigSepL Φ l1 := by rw [fst_zip hlen]; exact .rfl
    exact (hfmap.symm.trans this).1
  · have : bigSepL Φ l1 ⊣⊢ bigSepL Φ ((l1.zip l2).map Prod.fst) := by rw [fst_zip hlen]; exact .rfl
    exact (this.trans hfmap).1

/-- No direct Rocq equivalent; when Φ doesn't depend on first argument. -/
theorem const_sepL_r {Φ : Nat → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ _x1;x2 ∈ l1;l2, Φ k x2) ⊣⊢
      iprop(⌜l1.length = l2.length⌝ ∧ bigSepL Φ l2) :=
  flip.trans const_sepL_l |>.trans ⟨and_mono (pure_mono Eq.symm) .rfl, and_mono (pure_mono Eq.symm) .rfl⟩

/-- Corresponds to `big_sepL2_sep_sepL_l` in Rocq Iris. -/
theorem sep_sepL_l [BIAffine PROP] {Φ : Nat → A → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x1 ∗ Ψ k x1 x2) ⊣⊢
      iprop(bigSepL Φ l1 ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) := by
  refine sep'.trans (sep_congr_l const_sepL_l) |>.trans ⟨sep_mono and_elim_r .rfl, ?bwd⟩
  refine (sep_mono_r <| (and_intro length .rfl).trans persistent_and_affinely_sep_l.1 |>.trans
    (sep_mono_l affinely_elim)).trans sep_assoc.2 |>.trans (sep_mono_l ?_)
  exact and_intro (sep_comm.1.trans (sep_mono_l persistently_intro) |>.trans
    persistently_absorb_l |>.trans persistently_elim) sep_elim_l

/-- Corresponds to `big_sepL2_sep_sepL_r` in Rocq Iris. -/
theorem sep_sepL_r [BIAffine PROP] {Φ : Nat → B → PROP} {Ψ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} :
    ([∗list] k ↦ x1;x2 ∈ l1;l2, Φ k x2 ∗ Ψ k x1 x2) ⊣⊢
      iprop(bigSepL Φ l2 ∗ [∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2) :=
  (congr fun _ _ _ => sep_comm).trans flip |>.trans
    ((congr fun _ _ _ => sep_comm).trans sep_sepL_l) |>.trans (sep_congr_r flip)

/-- Corresponds to `big_sepL2_delete` in Rocq Iris. -/
theorem delete {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ l1;l2,
        if k = i then emp else Φ k y1 y2) := by
  induction l1 generalizing l2 i Φ with
  | nil => simp at h1
  | cons z1 zs1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons z2 zs2 =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        simp only [bigSepL2, ↓reduceIte]
        exact sep_congr_r <| (proper fun k _ _ _ _ => by simp).trans emp_sep.symm
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        simp only [bigSepL2]
        have ih' := ih (i := j) (Φ := fun n => Φ (n + 1)) h1 h2
        refine (sep_congr_r ih').trans sep_left_comm |>.trans (sep_congr_r ?_)
        simp only [Nat.zero_ne_add_one, ↓reduceIte]
        exact sep_congr_r <| proper fun k _ _ _ _ => by
          simp only [Nat.add_right_cancel_iff]; exact .rfl

/-- Corresponds to `big_sepL2_delete'` in Rocq Iris. -/
theorem delete' [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat}
    {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
      iprop(Φ i x1 x2 ∗ [∗list] k ↦ y1;y2 ∈ l1;l2, ⌜k ≠ i⌝ → Φ k y1 y2) :=
  (delete h1 h2).trans <| sep_congr .rfl <| congr fun k y1 y2 => by
    by_cases hki : k = i
    · subst hki; simp only [↓reduceIte, ne_eq, not_true_eq_false]
      exact ⟨imp_intro' ((pure_elim_l (fun hf => False.elim hf)).trans .rfl), Affine.affine⟩
    · simp only [hki, ↓reduceIte, ne_eq, not_false_eq_true]; exact true_imp.symm


/-- Corresponds to `big_sepL2_lookup_acc_impl` in Rocq Iris. -/
theorem lookup_acc_impl {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B} {i : Nat} {x1 : A} {x2 : B}
    (h1 : l1[i]? = some x1) (h2 : l2[i]? = some x2) :
    ([∗list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
      iprop(Φ i x1 x2 ∗ ∀ Ψ, □ (∀ k, ∀ y1, ∀ y2,
        iprop(⌜l1[k]? = some y1⌝ → ⌜l2[k]? = some y2⌝ → ⌜k ≠ i⌝ →
          Φ k y1 y2 -∗ Ψ k y1 y2)) -∗
        Ψ i x1 x2 -∗ bigSepL2 Ψ l1 l2) := by
  refine (delete h1 h2).1.trans (sep_mono_r <| forall_intro fun Ψ => wand_intro <| wand_intro ?_)
  refine sep_comm.1.trans (sep_mono_r ?_) |>.trans (delete h1 h2).2
  have himpl := impl (Φ := fun k y1 y2 => if k = i then emp else Φ k y1 y2)
                     (Ψ := fun k y1 y2 => if k = i then emp else Ψ k y1 y2) (l1 := l1) (l2 := l2)
  refine (sep_mono_r ?_).trans (wand_elim himpl)
  refine intuitionistically_intro' <| forall_intro fun k => forall_intro fun y1 => forall_intro fun y2 =>
    imp_intro' <| pure_elim_l fun hk1 => imp_intro' <| pure_elim_l fun hk2 => ?_
  by_cases hki : k = i
  · subst hki; simp only [↓reduceIte]
    exact wand_intro (sep_emp.1.trans Affine.affine)
  · simp only [hki, ↓reduceIte]
    exact intuitionistically_elim.trans <| (forall_elim k).trans ((forall_elim y1).trans (forall_elim y2))
      |>.trans ((and_intro (pure_intro hk1) .rfl).trans imp_elim_r)
      |>.trans ((and_intro (pure_intro hk2) .rfl).trans imp_elim_r)
      |>.trans ((and_intro (pure_intro hki) .rfl).trans imp_elim_r)

end BigSepL2

namespace BigSepL

/-- No direct Rocq equivalent; diagonal BigSepL to BigSepL2. -/
theorem sepL2_diag {Φ : Nat → A → A → PROP} {l : List A} :
    bigSepL (fun k x => Φ k x x) l ⊢ bigSepL2 Φ l l := by
  have hzip : l.zip l = l.map (fun x => (x, x)) := by
    induction l with
    | nil => simp
    | cons hd tl ih => simp [ih]
  have inner_eq : bigSepL (fun k x => Φ k x x) l ⊣⊢
      bigSepL (fun k p => Φ k p.1 p.2) (l.zip l) := by
    rw [hzip]
    exact (equiv_iff.mp (BigSepL.fmap (PROP := PROP) (Φ := fun k p => Φ k p.1 p.2)
        (fun x => (x, x)) (l := l))).symm
  exact (and_intro (pure_intro rfl) .rfl).trans (and_mono .rfl inner_eq.1) |>.trans BigSepL2.alt.2

end BigSepL

/-! ## Missing Lemmas from Rocq Iris

The following lemmas from Rocq Iris are not ported:
- `big_sepL2_proper_2`: Uses OFE structure on A, B (list element types)
- `big_sepL2_closed`: Meta-lemma (direct inductive proofs used instead)
- `big_sepL2_timeless`, `big_sepL2_timeless'`: Requires `sep_timeless` infrastructure
- `big_sepL2_later_1`, `big_sepL2_later`, `big_sepL2_laterN_1`, `big_sepL2_laterN`: Requires except-0 infrastructure
-/

end BigSepL2

end Iris.BI
