/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.DerivedLawsLater

namespace Iris.BI

open Iris.Algebra BigOpL
open BIBase

/-! # Big Disjunction over Lists -/

variable {PROP : Type _} [BI PROP] {A : Type _}

namespace BigOrL

@[simp]
theorem nil {Φ : Nat → A → PROP} :
    ([∨list] k ↦ x ∈ ([] : List A), Φ k x) ⊣⊢ iprop(False) := .rfl

theorem cons {Φ : Nat → A → PROP} {x : A} {xs : List A} :
    ([∨list] k ↦ y ∈ (x :: xs), Φ k y) ⊣⊢ Φ 0 x ∨ [∨list] n ↦ y ∈ xs, Φ (n + 1) y := .rfl

theorem singleton {Φ : Nat → A → PROP} {x : A} :
    ([∨list] k ↦ y ∈ [x], Φ k y) ⊣⊢ Φ 0 x := equiv_iff.mp (bigOpL_singleton_equiv Φ x)

theorem app {Φ : Nat → A → PROP} {l₁ l₂ : List A} :
    ([∨list] k ↦ x ∈ (l₁ ++ l₂), Φ k x) ⊣⊢
      ([∨list] k ↦ x ∈ l₁, Φ k x) ∨ [∨list] n ↦ x ∈ l₂, Φ (n + l₁.length) x :=
  equiv_iff.mp (bigOpL_append_equiv Φ l₁ l₂)

theorem snoc {Φ : Nat → A → PROP} {l : List A} {x : A} :
    ([∨list] k ↦ y ∈ (l ++ [x]), Φ k y) ⊣⊢ ([∨list] k ↦ y ∈ l, Φ k y) ∨ Φ l.length x :=
  equiv_iff.mp (bigOpL_snoc_equiv Φ l x)

theorem mono {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ k x, l[k]? = some x → Φ k x ⊢ Ψ k x) :
    ([∨list] k ↦ x ∈ l, Φ k x) ⊢ [∨list] k ↦ x ∈ l, Ψ k x :=
  bigOpL_gen_proper (· ⊢ ·) .rfl or_mono (h _ _ ·)

theorem equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, l[k]? = some x → Φ k x ≡ Ψ k x) :
    ([∨list] k ↦ x ∈ l, Φ k x) ≡ [∨list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv h

theorem equiv_of_forall_equiv {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∨list] k ↦ x ∈ l, Φ k x) ≡ [∨list] k ↦ x ∈ l, Ψ k x := bigOpL_equiv_of_forall_equiv h

theorem false_l {l : List A} :
    ([∨list] _k ∈ l, iprop(False : PROP)) ≡ iprop(False) := bigOpL_const_unit_equiv

theorem or_equiv {Φ Ψ : Nat → A → PROP} {l : List A} :
    ([∨list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x)) ≡
      iprop(([∨list] k ↦ x ∈ l, Φ k x) ∨ [∨list] k ↦ x ∈ l, Ψ k x) := bigOpL_op_equiv Φ Ψ l

theorem or_equiv_symm {Φ Ψ : Nat → A → PROP} {l : List A} :
    iprop(([∨list] k ↦ x ∈ l, Φ k x) ∨ [∨list] k ↦ x ∈ l, Ψ k x) ≡
      [∨list] k ↦ x ∈ l, iprop(Φ k x ∨ Ψ k x) := or_equiv.symm

theorem take_drop {Φ : Nat → A → PROP} {l : List A} {n : Nat} :
    ([∨list] k ↦ x ∈ l, Φ k x) ≡
      iprop(([∨list] k ↦ x ∈ (l.take n), Φ k x) ∨ [∨list] k ↦ x ∈ (l.drop n), Φ (n + k) x) :=
  bigOpL_take_drop_equiv Φ l n

theorem fmap {B : Type _} (f : A → B) {Φ : Nat → B → PROP} {l : List A} :
    ([∨list] k ↦ y ∈ (l.map f), Φ k y) ≡ [∨list] k ↦ x ∈ l, Φ k (f x) := bigOpL_map_equiv f Φ l

theorem intro {Φ : Nat → A → PROP} {l : List A} {k : Nat} {x : A}
    (h : l[k]? = some x) :
    Φ k x ⊢ [∨list] i ↦ y ∈ l, Φ i y := by
  induction l generalizing k Φ with
  | nil => simp at h
  | cons _ _ ih => cases k with
    | zero => simp at h; subst h; exact or_intro_l
    | succ => simp at h; exact (ih (Φ := fun n => Φ (n + 1)) h).trans or_intro_r

private theorem exist_fwd {Φ : Nat → A → PROP} {l : List A} :
    ([∨list] k ↦ x ∈ l, Φ k x) ⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x) :=
  match l with
  | [] => false_elim
  | _ :: _ => or_elim
      (exists_intro' 0 (exists_intro' _ (and_intro (pure_intro rfl) .rfl)))
      (exist_fwd.trans (exists_elim fun k => exists_intro' (k + 1) .rfl))

theorem exist {Φ : Nat → A → PROP} {l : List A} :
    ([∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ ∃ k, ∃ x, iprop(⌜l[k]? = some x⌝ ∧ Φ k x) :=
  ⟨exist_fwd, exists_elim fun _ => exists_elim fun _ => pure_elim_l (intro ·)⟩

theorem pure {φ : Nat → A → Prop} {l : List A} :
    ([∨list] k ↦ x ∈ l, (⌜φ k x⌝ : PROP)) ⊣⊢ (⌜∃ k x, l[k]? = some x ∧ φ k x⌝ : PROP) :=
  exist.trans <| (exists_congr fun _ => (exists_congr fun _ => pure_and).trans pure_exists).trans pure_exists

theorem sep_l {P : PROP} {Φ : Nat → A → PROP} {l : List A} :
    (P ∗ [∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨list] k ↦ x ∈ l, (P ∗ Φ k x) :=
  (sep_congr .rfl exist).trans <| sep_exists_l.trans <| (exists_congr fun _ =>
    sep_exists_l.trans <| exists_congr fun _ =>
      (sep_congr .rfl persistent_and_affinely_sep_l).trans <|
        sep_assoc.symm.trans <| (sep_congr sep_comm .rfl).trans <|
          sep_assoc.trans persistent_and_affinely_sep_l.symm).trans exist.symm

theorem sep_r {Φ : Nat → A → PROP} {P : PROP} {l : List A} :
    (([∨list] k ↦ x ∈ l, Φ k x) ∗ P) ⊣⊢ [∨list] k ↦ x ∈ l, (Φ k x ∗ P) :=
  sep_comm.trans <| sep_l.trans (equiv_iff.mp (equiv_of_forall_equiv (equiv_iff.mpr sep_comm)))

theorem elem_of {Φ : A → PROP} {l : List A} {x : A} (h : x ∈ l) :
    Φ x ⊢ [∨list] y ∈ l, Φ y :=
  match l, h with
  | _ :: _, .head .. => or_intro_l
  | _ :: _, .tail _ hmem => (elem_of hmem).trans or_intro_r

theorem bind {B : Type _} (f : A → List B) {Φ : B → PROP} {l : List A} :
    ([∨list] y ∈ (l.flatMap f), Φ y) ⊣⊢ [∨list] x ∈ l, [∨list] y ∈ (f x), Φ y :=
  equiv_iff.mp (bigOpL_flatMap_equiv f Φ l)

theorem persistently {Φ : Nat → A → PROP} {l : List A} :
    (<pers> [∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨list] k ↦ x ∈ l, <pers> Φ k x :=
  equiv_iff.mp <| bigOpL_hom (H := MonoidHomomorphism.ofEquiv persistently_ne
    (equiv_iff.mpr persistently_or) (equiv_iff.mpr ⟨persistently_elim, false_elim⟩)) Φ l

theorem later {Φ : Nat → A → PROP} {l : List A} (hne : l ≠ []) :
    (▷ [∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨list] k ↦ x ∈ l, ▷ Φ k x :=
  equiv_iff.mp <| bigOpL_hom_weak (H := WeakMonoidHomomorphism.ofEquiv later_ne
    (equiv_iff.mpr later_or)) Φ hne

theorem laterN {Φ : Nat → A → PROP} {l : List A} {n : Nat} (hne : l ≠ []) :
    (▷^[n] [∨list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∨list] k ↦ x ∈ l, ▷^[n] Φ k x :=
  match n with
  | 0 => .rfl
  | _ + 1 => (later_congr (laterN hne)).trans (later hne)

theorem perm {Φ : A → PROP} {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([∨list] x ∈ l₁, Φ x) ≡ [∨list] x ∈ l₂, Φ x := bigOpL_equiv_of_perm Φ hp

theorem submseteq {Φ : A → PROP} {l₁ l₂ l : List A} (h : (l₁ ++ l).Perm l₂) :
    ([∨list] x ∈ l₁, Φ x) ⊢ [∨list] x ∈ l₂, Φ x :=
  (or_intro_l (Q := [∨list] x ∈ l, Φ x)).trans <|
    ((app (Φ := fun _ => Φ) (l₁ := l₁) (l₂ := l)).2).trans
      (equiv_iff.mp (perm (Φ := Φ) h)).1

theorem mono_of_forall {Φ Ψ : Nat → A → PROP} {l : List A} (h : ∀ k x, Φ k x ⊢ Ψ k x) :
    ([∨list] k ↦ x ∈ l, Φ k x) ⊢ [∨list] k ↦ x ∈ l, Ψ k x := mono fun k x _ => h k x

theorem id_mono' {l₁ l₂ : List PROP}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (P Q : PROP), l₁[i]? = some P → l₂[i]? = some Q → P ⊢ Q) :
    ([∨list] P ∈ l₁, P) ⊢ [∨list] P ∈ l₂, P :=
  bigOpL_gen_proper_2 (· ⊢ ·) .rfl or_mono hlen (h _ _ _ · ·)

instance nil_persistent {Φ : Nat → A → PROP} :
    Persistent ([∨list] k ↦ x ∈ ([] : List A), Φ k x) where
  persistent := false_elim

theorem persistent_cond {Φ : Nat → A → PROP} {l : List A}
    (h : ∀ k x, l[k]? = some x → Persistent (Φ k x)) :
    Persistent ([∨list] k ↦ x ∈ l, Φ k x) where
  persistent := bigOpL_closed (P := fun Q => Q ⊢ <pers> Q) false_elim
    (fun hx hy => or_elim (hx.trans (persistently_mono or_intro_l))
      (hy.trans (persistently_mono or_intro_r))) (fun hget => (h _ _ hget).persistent)

instance persistent {Φ : Nat → A → PROP} {l : List A} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∨list] k ↦ x ∈ l, Φ k x) := persistent_cond fun _ _ _ => inferInstance

theorem zip_seq {Φ : A × Nat → PROP} {n : Nat} {l : List A} :
    ([∨list] xy ∈ l.zipIdx n, Φ xy) ≡ [∨list] i ↦ x ∈ l, Φ (x, n + i) := bigOpL_zipIdx_equiv Φ n l

end BigOrL

end Iris.BI
