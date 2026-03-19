/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.BigOp.BigOp
import Iris.BI.DerivedLawsLater
meta import Iris.Std.RocqAlias

public section

namespace Iris.BI

open Iris.Algebra BigOpL BIBase

/-! # Big Conjunction over Lists -/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigAndL

@[simp, rocq_alias big_andL_nil]
theorem bigAndL_nil {Φ : Nat → A → PROP} :
    ([∧list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(True) := .rfl

@[rocq_alias big_andL_nil']
theorem bigAndL_nil' {P} {Φ : Nat → A → PROP} :
   P ⊢ ([∧list] k ↦ x ∈ ([] : List A), Φ k x) := true_intro

@[rocq_alias big_andL_cons]
theorem bigAndL_cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∧list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∧ [∧list] n ↦ y ∈ xs, Φ (n + 1) y := .rfl

@[rocq_alias big_andL_singleton]
theorem bigAndL_singleton {Φ : Nat → A → PROP} {x : A} :
    ([∧list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x := equiv_iff.mp (bigOpL_singleton_equiv Φ x)

@[rocq_alias big_andL_app]
theorem bigAndL_app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∧list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∧list] k ↦ x ∈ l₁, Φ k x) ∧ [∧list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (bigOpL_append_equiv Φ l₁ l₂)

@[rocq_alias big_andL_snoc]
theorem bigAndL_snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∧list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∧list] k ↦ y ∈ l, Φ k y) ∧ Φ l.length x :=
  equiv_iff.mp (bigOpL_snoc_equiv Φ l x)

@[rocq_alias big_andL_mono]
theorem bigAndL_mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊢ [∧list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_gen_proper (· ⊢ ·) .rfl and_mono (h _ _ ·)

@[rocq_alias big_andL_proper]
theorem bigAndL_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv h

theorem bigAndL_equiv_of_forall_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡ [∧list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv_of_forall_equiv h

@[rocq_alias big_andL_persistent']
instance bigAndL_persistent_inst {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∧list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_true.2
    (fun hx hy => (and_mono hx hy).trans persistently_and.2) (fun _ => Persistent.persistent)

instance bigAndL_affine_inst {Φ : Nat → A → PROP} {l : List A} [BIAffine PROP] :
    Affine ([∧list] k ↦ x ∈ l, Φ k x) where
  affine := bigOpL_closed (P := fun Q => Q ⊢ emp) true_emp.1
    (fun hx _ => and_elim_l.trans hx) (fun _ => Affine.affine)

@[rocq_alias big_andL_and]
theorem bigAndL_and_equiv {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x)) ≡
      iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) := bigOpL_op_equiv Φ Ψ l

theorem bigAndL_and_equiv_symm {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∧list] k ↦ x ∈ l, Φ k x) ∧ [∧list] k ↦ x ∈ l, Ψ k x) ≡
      [∧list] k ↦ x ∈ l, iprop(Φ k x ∧ Ψ k x) := bigAndL_and_equiv.symm

@[rocq_alias big_andL_fmap]
theorem bigAndL_map {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∧list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∧list] k ↦ x ∈ l, Φ k (f x) := bigOpL_map_equiv f Φ l

@[rocq_alias big_andL_lookup]
theorem bigAndL_lookup {Φ : Nat → A → PROP} {l : List A} {i : Nat} {x : A} (h : l[i]? = some x) :
    ([∧list] k ↦ y ∈ l, Φ k y) ⊢ Φ i x :=
  match l, i, h with
  | _ :: _, 0, h => Option.some.inj h ▸ and_elim_l
  | _ :: _, _ + 1, h => and_elim_r.trans (bigAndL_lookup h)

@[rocq_alias big_andL_intro]
theorem bigAndL_intro {P : PROP} {Φ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → P ⊢ Φ k x) :
    P ⊢ [∧list] k ↦ x ∈ l, Φ k x :=
  bigOpL_closed (P := (P ⊢ ·)) true_intro and_intro (h _ _ ·)

@[rocq_alias big_andL_forall]
theorem bigAndL_forall {Φ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∀ k, ∀ x, iprop(⌜l[k]? = some x⌝ → Φ k x) :=
  ⟨forall_intro fun _ => forall_intro fun _ =>
      imp_intro <| and_comm.1.trans <| pure_elim_l (bigAndL_lookup ·),
   bigAndL_intro fun k x hget =>
      (forall_elim k).trans <| (forall_elim x).trans <|
        (imp_congr_l (pure_true hget)).1.trans true_imp.1⟩

@[rocq_alias big_andL_impl]
theorem bigAndL_impl {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∧list] k ↦ x ∈ l, Φ k x) ∧ (∀ k x, ⌜l[k]? = some x⌝ → Φ k x → Ψ k x) ⊢
      [∧list] k ↦ x ∈ l, Ψ k x :=
  bigAndL_intro fun k x hget =>
    (and_mono (bigAndL_lookup hget) ((forall_elim k).trans (forall_elim x))).trans <|
      (and_mono .rfl ((and_intro (pure_intro hget) .rfl).trans imp_elim_r)).trans imp_elim_r

@[rocq_alias big_andL_persistently]
theorem bigAndL_persistently {Φ : Nat → A → PROP} {l : List A} :
    (<pers> [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, <pers> Φ k x :=
  equiv_iff.mp <| bigOpL_hom (H := MonoidHomomorphism.ofEquiv persistently_ne
    (equiv_iff.mpr persistently_and) (equiv_iff.mpr persistently_true)) Φ l

@[rocq_alias big_andL_pure_1]
theorem bigAndL_pure_intro {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊢ ⌜∀ k x, l[k]? = some x → φ k x⌝ :=
  bigAndL_forall.1.trans <| (forall_mono fun _ => forall_mono fun _ => pure_imp.1).trans <|
    (forall_mono fun _ => pure_forall.1).trans pure_forall.1

@[rocq_alias big_andL_pure_2]
theorem bigAndL_pure_elim {φ : Nat → A → Prop} {l : List A} :
    (⌜∀ k x, l[k]? = some x → φ k x⌝ : PROP) ⊢ [∧list] k ↦ x ∈ l, ⌜φ k x⌝ :=
  pure_forall_2.trans <| (forall_mono fun _ => pure_forall_2).trans <|
    (forall_mono fun _ => forall_mono fun _ => pure_imp_2).trans bigAndL_forall.2

@[rocq_alias big_andL_pure]
theorem bigAndL_pure {φ : Nat → A → Prop} {l : List A} :
    ([∧list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊣⊢ ⌜∀ k x, l[k]? = some x → φ k x⌝ :=
    ⟨bigAndL_pure_intro, bigAndL_pure_elim⟩

@[rocq_alias big_andL_elem_of]
theorem bigAndL_elem_of {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    ([∧list] y ∈ l, Φ y) ⊢ Φ x :=
  let ⟨_, hi, hget⟩ := List.mem_iff_getElem.mp h
  bigAndL_lookup (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)

@[rocq_alias big_andL_zip_seq]
theorem bigAndL_zip_seq {Φ : A × Nat → PROP} {n : Nat} {l : List A} :
    ([∧list] xy ∈ l.zipIdx n, Φ xy) ≡ [∧list] i ↦ x ∈ l, Φ (x, n + i) :=
  bigOpL_zipIdx_equiv Φ n l

@[rocq_alias big_andL_bind]
theorem bigAndL_bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∧list] y ∈ (l.flatMap f), Φ y) ⊣⊢ [∧list] x ∈ l, [∧list] y ∈ (f x), Φ y :=
  equiv_iff.mp (bigOpL_flatMap_equiv f Φ l)

@[rocq_alias big_andL_later]
theorem bigAndL_later {Φ : Nat → A → PROP} {l : List A} :
    (▷ [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, (▷ Φ k x) :=
  equiv_iff.mp <| bigOpL_hom (H := MonoidHomomorphism.ofEquiv later_ne
    (equiv_iff.mpr later_and) (equiv_iff.mpr later_true)) Φ l

@[rocq_alias big_andL_laterN]
theorem bigAndL_laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    (▷^[n] [∧list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∧list] k ↦ x ∈ l, ▷^[n] Φ k x :=
  match n with
  | 0 => .rfl
  | _ + 1 => (later_congr bigAndL_laterN).trans bigAndL_later

theorem bigAndL_perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∧list] x ∈ l₁, Φ x) ≡ [∧list] x ∈ l₂, Φ x := bigOpL_equiv_of_perm Φ hp

@[rocq_alias big_andL_submseteq]
theorem bigAndL_submseteq {Φ : A → PROP} {l₁ l₂ l : List A} (h : (l₁ ++ l).Perm l₂) :
    ([∧list] x ∈ l₂, Φ x) ⊢ [∧list] x ∈ l₁, Φ x :=
  (equiv_iff.mp (bigAndL_perm (Φ := Φ) h)).2.trans <|
    (bigAndL_app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).1.trans and_elim_l

@[rocq_alias big_andL_ne]
theorem bigAndL_dist {Φ Ψ : Nat → A → PROP} {l : List A} {n : Nat}
    (h : ∀ {k x}, l[k]? = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ≡{n}≡ [∧list] k ↦ x ∈ l, Ψ k x := bigOpL_dist h

@[rocq_alias big_andL_mono']
theorem bigAndL_mono_of_forall {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∧list] k ↦ x ∈ l, Φ k x) ⊢ [∧list] k ↦ x ∈ l, Ψ k x := bigAndL_mono fun k x _ => h k x

@[rocq_alias big_andL_id_mono']
theorem bigAndL_id_mono' {l₁ l₂ : List PROP} (hlen : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (P Q : PROP), l₁[i]? = some P → l₂[i]? = some Q → P ⊢ Q) :
    ([∧list] P ∈ l₁, P) ⊢ [∧list] P ∈ l₂, P :=
  bigOpL_gen_proper_2 (· ⊢ ·) .rfl and_mono hlen (h _ _ _ · ·)

@[rocq_alias big_andL_nil_absorbing]
instance bigAndL_nil_absorbing {Φ : Nat → A → PROP} :
    Absorbing ([∧list] k ↦ x ∈ ([] : List A), Φ k x) where
  absorbing := by simp only [bigOpL]; exact Absorbing.absorbing

@[rocq_alias big_andL_absorbing]
theorem bigAndL_absorbing {Φ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Absorbing (Φ k x)) :
    Absorbing ([∧list] k ↦ x ∈ l, Φ k x) where
  absorbing := bigOpL_closed (P := fun Q => <absorb> Q ⊢ Q) true_intro
    (fun hx hy => absorbingly_and_1.trans (and_mono hx hy))
    (fun hget => (h _ _ hget).absorbing)

@[rocq_alias big_andL_absorbing']
instance bigAndL_absorbing' {Φ : Nat → A → PROP} {l : List A} [∀ k x, Absorbing (Φ k x)] :
    Absorbing ([∧list] k ↦ x ∈ l, Φ k x) :=
  bigAndL_absorbing fun _ _ _ => inferInstance

@[rocq_alias big_andL_nil_persistent]
instance bigAndL_nil_persistent {Φ : Nat → A → PROP} :
    Persistent ([∧list] k ↦ x ∈ ([] : List A), Φ k x) where
  persistent := by simp only [bigOpL]; exact Persistent.persistent

@[rocq_alias big_andL_persistent]
theorem bigAndL_persistent {Φ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∧list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) persistently_true.2
    (fun hx hy => (and_mono hx hy).trans persistently_and.2)
    (fun hget => (h _ _ hget).persistent)

@[rocq_alias big_andL_nil_timeless]
instance bigAndL_nil_timeless {Φ : Nat → A → PROP} :
    Timeless ([∧list] k ↦ x ∈ ([] : List A), Φ k x) where
  timeless := by simp only [bigOpL]; exact (later_true.1.trans except0_true.2)

@[rocq_alias big_andL_timeless]
theorem bigAndL_timeless {Φ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Timeless (Φ k x)) :
    Timeless ([∧list] k ↦ x ∈ l, Φ k x) where
  timeless := bigOpL_closed (P := fun Q => ▷ Q ⊢ ◇ Q)
    (later_true.1.trans except0_true.2)
    (fun hx hy => later_and.1.trans ((and_mono hx hy).trans except0_and.2))
    (fun hget => (h _ _ hget).timeless)

@[rocq_alias big_andL_timeless']
instance bigAndL_timeless' {Φ : Nat → A → PROP} {l : List A} [∀ k x, Timeless (Φ k x)] :
    Timeless ([∧list] k ↦ x ∈ l, Φ k x) :=
  bigAndL_timeless fun _ _ _ => inferInstance

end BigAndL

end Iris.BI
