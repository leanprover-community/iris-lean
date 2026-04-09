/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.BigOp.BigOp
import Iris.BI.BigOp.BigSepList
import Iris.BI.DerivedLawsLater
import Iris.BI.Instances
import Iris.Std.TC
meta import Iris.Std.RocqAlias

public section

namespace Iris.BI

open Iris.Algebra BigOpL BigOpS BIBase Iris.Std BigSepL LawfulSet

/-! # Big Separating Conjunction over Sets -/

variable {PROP : Type _} [BI PROP]
variable {S : Type _} {A : Type _} [LawfulFiniteSet S A]

namespace BigSepS

@[rocq_alias big_sepS_mono]
theorem bigSepS_mono {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x :=
  bigOpS_gen_proper (· ⊢ ·) .rfl sep_mono fun hy => h _ hy

@[rocq_alias big_sepS_ne]
theorem bigSepS_ne {Φ Ψ : A → PROP} {X : S} {n : Nat}
    (h : ∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) :
    ([∗set] x ∈ X, Φ x) ≡{n}≡ ([∗set] x ∈ X, Ψ x) :=
  bigOpS_dist fun hy => h _ hy

@[rocq_alias big_sepS_proper]
theorem bigSepS_proper {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Φ x ≡ Ψ x) :
    ([∗set] x ∈ X, Φ x) ≡ ([∗set] x ∈ X, Ψ x) :=
  bigOpS_gen_proper (· ≡ ·) .rfl MonoidOps.op_proper fun hy => h _ hy

theorem bigSepS_equiv {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊣⊢ ([∗set] x ∈ X, Ψ x) :=
  equiv_iff.mp <| bigSepS_proper fun x hx => equiv_iff.mpr (h x hx)

@[rocq_alias big_sepS_mono']
theorem bigSepS_mono_of_forall {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x :=
  bigSepS_mono fun x _ => h x

@[rocq_alias big_sepS_flip_mono']
theorem bigSepS_flip_mono {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Ψ x ⊢ Φ x) :
    ([∗set] x ∈ X, Ψ x) ⊢ [∗set] x ∈ X, Φ x :=
  bigSepS_mono_of_forall h

@[rocq_alias big_sepS_elements]
theorem bigSepS_elements {Φ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊣⊢ [∗list] x ∈ FiniteSet.toList X, Φ x :=
  equiv_iff.mp bigOpS_bigOpL

@[simp, rocq_alias big_sepS_empty]
theorem bigSepS_empty {Φ : A → PROP} :
    ([∗set] x ∈ (∅ : S), Φ x) ⊣⊢ emp := by
  simp [bigSepS, bigOpS_empty]

@[rocq_alias big_sepS_empty']
theorem bigSepS_empty_intro {P : PROP} [Affine P] {Φ : A → PROP} :
    P ⊢ [∗set] x ∈ (∅ : S), Φ x :=
  Affine.affine.trans bigSepS_empty.2

@[rocq_alias big_sepS_emp]
theorem bigSepS_emp {X : S} :
    ([∗set] _x ∈ X, (emp : PROP)) ⊣⊢ emp :=
  bigSepS_elements.trans bigSepL_emp

@[rocq_alias big_sepS_singleton]
theorem bigSepS_singleton {Φ : A → PROP} {x : A} :
    ([∗set] y ∈ ({x} : S), Φ y) ⊣⊢ Φ x :=
  equiv_iff.mp bigOpS_singleton

@[rocq_alias big_sepS_insert]
theorem bigSepS_insert {Φ : A → PROP} {X : S} {x : A}
    (h : x ∉ X) :
    ([∗set] y ∈ insert x X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X, Φ y := by
  rw [insert_union]; exact equiv_iff.mp <| bigOpS_insert h

@[rocq_alias big_sepS_union]
theorem bigSepS_union {Φ : A → PROP} {X Y : S}
    (h : X ## Y) :
    ([∗set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ Y, Φ y) :=
  equiv_iff.mp <| bigOpS_union h

@[rocq_alias big_sepS_delete]
theorem bigSepS_delete {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗set] y ∈ X \ {x}, Φ y := by
  have hnotin : x ∉ X \ {x} := by rw [← delete_diff]; exact not_mem_delete
  have heq : X = insert x (X \ {x}) := by rw [← delete_diff]; exact (insert_delete h).symm
  rw (config := { occs := .pos [1] }) [heq]
  exact bigSepS_insert hnotin

private theorem mem_of_getElem? {i : Nat} {x : A} {X : S}
    (hget : (FiniteSet.toList X)[i]? = some x) : x ∈ X :=
  LawfulFiniteSet.mem_toList.mp (List.mem_of_getElem? hget)

@[rocq_alias big_sepS_persistent]
theorem bigSepS_persistent {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Persistent (Φ x)) :
    Persistent ([∗set] x ∈ X, Φ x) := by
  rw [show ([∗set] x ∈ X, Φ x) = bigSepS Φ X from rfl]
  unfold bigSepS bigOpS
  exact bigSepL_persistent fun {_ _} hget => h _ (mem_of_getElem? hget)

instance bigSepS_persistent_inst {Φ : A → PROP} {X : S}
    [h : ∀ x, Persistent (Φ x)] :
    Persistent ([∗set] x ∈ X, Φ x) :=
  bigSepS_persistent fun _ _ => h _

@[rocq_alias big_sepS_affine]
theorem bigSepS_affine {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Affine (Φ x)) :
    Affine ([∗set] x ∈ X, Φ x) := by
  rw [show ([∗set] x ∈ X, Φ x) = bigSepS Φ X from rfl]
  unfold bigSepS bigOpS
  exact bigSepL_affine fun {_ _} hget => h _ (mem_of_getElem? hget)

instance bigSepS_affine_inst {Φ : A → PROP} {X : S}
    [h : ∀ x, Affine (Φ x)] :
    Affine ([∗set] x ∈ X, Φ x) :=
  bigSepS_affine fun _ _ => h _

@[rocq_alias big_sepS_empty_persistent]
instance bigSepS_empty_persistent_inst {Φ : A → PROP} :
    Persistent ([∗set] x ∈ (∅ : S), Φ x) := by
  simp only [bigSepS, bigOpS_empty]; infer_instance

@[rocq_alias big_sepS_empty_affine]
instance bigSepS_empty_affine_inst {Φ : A → PROP} :
    Affine ([∗set] x ∈ (∅ : S), Φ x) := by
  simp only [bigSepS, bigOpS_empty]; infer_instance

@[rocq_alias big_sepS_empty_timeless]
instance bigSepS_empty_timeless_inst [Timeless (emp : PROP)] {Φ : A → PROP} :
    Timeless ([∗set] x ∈ (∅ : S), Φ x) := by
  simp only [bigSepS, bigOpS_empty]; infer_instance

@[rocq_alias big_sepS_timeless]
theorem bigSepS_timeless [Timeless (emp : PROP)] {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Timeless (Φ x)) :
    Timeless ([∗set] x ∈ X, Φ x) := by
  exact bigSepL_timeless fun {_ _} hget => h _ (mem_of_getElem? hget)

@[rocq_alias big_sepS_timeless']
instance bigSepS_timeless_inst [Timeless (emp : PROP)] {Φ : A → PROP} {X : S}
    [h : ∀ x, Timeless (Φ x)] :
    Timeless ([∗set] x ∈ X, Φ x) :=
  bigSepS_timeless fun _ _ => h _

@[rocq_alias big_sepS_sep]
theorem bigSepS_sep {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ X, Ψ y) :=
  equiv_iff.mp bigOpS_op_equiv

@[deprecated "bigSepS_sep.symm" (since := "26/04/07"), rocq_alias big_sepS_sep_2]
theorem bigSepS_sep_symm {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ X, Ψ y) ⊣⊢ [∗set] y ∈ X, Φ y ∗ Ψ y :=
  bigSepS_sep.symm

@[rocq_alias big_sepS_and]
theorem bigSepS_and {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗set] y ∈ X, Φ y) ∧ ([∗set] y ∈ X, Ψ y) :=
  and_intro (bigSepS_mono fun _ _ => and_elim_l) (bigSepS_mono fun _ _ => and_elim_r)

@[rocq_alias big_sepS_wand]
theorem bigSepS_wand {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢ ([∗set] x ∈ X, Φ x -∗ Ψ x) -∗ [∗set] x ∈ X, Ψ x :=
  wand_intro <| sep_comm.1.trans <| bigSepS_sep.symm.1.trans <|
    bigSepS_mono fun _ _ => wand_elim_l

@[rocq_alias big_sepS_elem_of]
theorem bigSepS_elem_of {Φ : A → PROP} {X : S} {x : A}
    (hmem : x ∈ X) [∀ y, Affine (Φ y)] :
    ([∗set] y ∈ X, Φ y) ⊢ Φ x :=
  (bigSepS_delete hmem).1.trans sep_elim_l

@[rocq_alias big_sepS_elem_of_acc]
theorem bigSepS_elem_of_acc {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗set] y ∈ X, Φ y)) :=
  (bigSepS_delete h).1.trans <| sep_mono_r <| wand_intro' (bigSepS_delete h).2

/-! ## Pure Propositions -/

@[rocq_alias big_sepS_pure_1]
theorem bigSepS_pure_intro {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  bigSepS_elements.1.trans <| bigSepL_pure_intro.trans <| pure_mono fun h _ hy =>
    h _ _ (List.getElem?_of_mem (LawfulFiniteSet.mem_toList.mpr hy)).choose_spec

@[rocq_alias big_sepS_affinely_pure_2]
theorem bigSepS_affinely_pure_elim {φ : A → Prop} {X : S} :
    (<affine> (⌜∀ y, y ∈ X → φ y⌝ : PROP)) ⊢ ([∗set] y ∈ X, <affine> ⌜φ y⌝) :=
  (affinely_mono <| pure_mono fun h _ x hget => h x (mem_of_getElem? hget)).trans <|
  bigSepL_affinely_pure_elim.trans bigSepS_elements.2

@[rocq_alias big_sepS_pure]
theorem bigSepS_pure [BIAffine PROP] {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊣⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  ⟨bigSepS_pure_intro, (affine_affinely _).2.trans <|
    bigSepS_affinely_pure_elim.trans (bigSepS_mono fun _ _ => affinely_elim)⟩

@[rocq_alias big_sepS_intro]
theorem bigSepS_intro {P : PROP} {Φ : A → PROP} {X : S} [Intuitionistic P]
    (h : ∀ x, x ∈ X → P ⊢ Φ x) :
    P ⊢ [∗set] x ∈ X, Φ x :=
  (bigSepL_intro fun _ x hget => h x (mem_of_getElem? hget)).trans bigSepS_elements.2

@[rocq_alias big_sepS_impl]
theorem bigSepS_impl {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) -∗
    [∗set] x ∈ X, Ψ x :=
  wand_intro <|
    (sep_mono_r <| bigSepS_intro (P := iprop(□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)))
      fun x hx => intuitionistically_elim.trans <|
        (forall_elim x).trans <| (imp_mono_l <| pure_mono fun _ => hx).trans true_imp.1).trans <|
    bigSepS_sep.symm.1.trans <| bigSepS_mono fun _ _ => wand_elim_r

@[rocq_alias big_sepS_forall]
theorem bigSepS_forall [BIAffine PROP] {Φ : A → PROP} {X : S}
    [hPers : ∀ x, Persistent (Φ x)] :
    ([∗set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x) := by
  constructor
  · exact forall_intro fun x => imp_intro' <| pure_elim_l fun hmem =>
      (bigSepS_elem_of_acc hmem).trans <|
        (sep_mono_l Persistent.persistent).trans <|
        sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim
  · induction X using FiniteSet.set_ind with
    | hemp => exact bigSepS_empty_intro
    | hadd a s hnin ih =>
      haveI : Persistent (Φ a) := hPers a
      apply Entails.trans _ (bigSepS_insert hnin).2
      apply Entails.trans _ persistent_and_sep_1
      apply BI.and_intro
      · exact (forall_elim a).trans
            ((and_intro (pure_intro (mem_insert.mpr (.inl rfl))) .rfl).trans imp_elim_r)
      · exact (forall_mono (fun (x : A) => imp_mono_l
            (pure_mono (fun (hx : x ∈ s) => mem_insert.mpr (.inr hx))
            : (⌜x ∈ s⌝ : PROP) ⊢ ⌜x ∈ Insert.insert a s⌝))).trans ih

@[rocq_alias big_sepS_elem_of_acc_impl]
theorem bigSepS_elem_of_acc_impl {Φ : A → PROP} {X : S} {x : A}
    (h : x ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢
    Φ x ∗
    (∀ (Ψ : A → PROP),
       (□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)) -∗
     Ψ x -∗
     ([∗set] y ∈ X, Ψ y)) := by
  refine (bigSepS_delete h).1.trans <| sep_mono_r ?_
  apply forall_intro; intro Ψ; apply wand_intro; apply wand_intro
  refine sep_comm.1.trans <| (sep_mono_r <|
    (sep_mono_r <| bigSepS_intro (Φ := fun y => iprop(Φ y -∗ Ψ y))
      (P := iprop(□ (∀ y, ⌜y ∈ X⌝ → ⌜x ≠ y⌝ → Φ y -∗ Ψ y)))
      fun y hy => by
        have hne : x ≠ y := fun heq => (mem_diff.mp hy).2 (mem_singleton.mpr heq.symm)
        exact intuitionistically_elim.trans <| (forall_elim y).trans <|
          ((and_intro (pure_intro (mem_diff.mp hy).1) .rfl).trans imp_elim_r).trans <|
          ((and_intro (pure_intro hne) .rfl).trans imp_elim_r)).trans <|
    (bigSepS_sep (Φ := Φ) (Ψ := fun y => iprop(Φ y -∗ Ψ y))).symm.1.trans <|
    bigSepS_mono fun _ _ => wand_elim_r).trans (bigSepS_delete (Φ := Ψ) h).2

@[rocq_alias big_sepS_persistently]
theorem bigSepS_persistently [BIAffine PROP] {Φ : A → PROP} {X : S} :
    (<pers> ([∗set] y ∈ X, Φ y)) ⊣⊢ [∗set] y ∈ X, <pers> (Φ y) :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) persistently_ne
    (equiv_iff.mpr persistently_sep) (equiv_iff.mpr persistently_emp')
  equiv_iff.mp <| BigOpS.hom this Φ X

@[rocq_alias big_sepS_later]
theorem bigSepS_later [BIAffine PROP] {Φ : A → PROP} {X : S} :
    iprop(▷ [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷ Φ y :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) later_ne
    (equiv_iff.mpr later_sep) (equiv_iff.mpr later_emp)
  equiv_iff.mp <| BigOpS.hom this Φ X

@[rocq_alias big_sepS_later_2]
theorem bigSepS_later_2 {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ X, ▷ Φ y) ⊢ iprop(▷ [∗set] y ∈ X, Φ y) :=
  bigSepS_elements.1.trans <| bigSepL_later_2.trans <| later_mono bigSepS_elements.2

@[rocq_alias big_sepS_laterN]
theorem bigSepS_laterN [BIAffine PROP] {Φ : A → PROP} {n : Nat} {X : S} :
    iprop(▷^[n] [∗set] y ∈ X, Φ y) ⊣⊢ [∗set] y ∈ X, ▷^[n] Φ y := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact (later_congr ih).trans bigSepS_later

@[rocq_alias big_sepS_laterN_2]
theorem bigSepS_laterN_2 {Φ : A → PROP} {n : Nat} {X : S} :
    ([∗set] y ∈ X, ▷^[n] Φ y) ⊢ iprop(▷^[n] [∗set] y ∈ X, Φ y) := by
  induction n with
  | zero => exact .rfl
  | succ m ih => exact bigSepS_later_2.trans (later_mono ih)

@[rocq_alias big_sepS_subseteq]
theorem bigSepS_subseteq {Φ : A → PROP} {X Y : S}
    [∀ x, Affine (Φ x)] (hsub : Y ⊆ X) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ Y, Φ x := by
  rw [show X = Y ∪ X \ Y from (diff_subset_decomp hsub).trans union_comm]
  exact (bigSepS_union (fun x hx => (mem_diff.mp hx.2).2 hx.1)).1.trans sep_elim_l

@[rocq_alias big_sepS_sepL]
theorem bigSepS_sepL {B : Type _} (Φ : A → Nat → B → PROP) (X : S) (l : List B) :
    ([∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y) ⊣⊢
      ([∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y) :=
  bigSepS_elements.trans <|
    (bigSepL_comm _ (FiniteSet.toList X) l).trans <|
    equiv_iff.mp <| bigOpL_equiv fun _ => equiv_iff.mpr bigSepS_elements.symm

@[rocq_alias big_sepS_sepS]
theorem bigSepS_sepS {B : Type _} {T : Type _} [LawfulFiniteSet T B]
    (Φ : A → B → PROP) (X : S) (Y : T) :
    ([∗set] x ∈ X, [∗set] y ∈ Y, Φ x y) ⊣⊢
      ([∗set] y ∈ Y, [∗set] x ∈ X, Φ x y) :=
  bigSepS_elements.trans <|
    (equiv_iff.mp <| bigOpL_equiv fun _ => equiv_iff.mpr bigSepS_elements).trans <|
    (bigSepL_comm _ (FiniteSet.toList X) (FiniteSet.toList Y)).trans <|
    (equiv_iff.mp <| bigOpL_equiv fun _ => equiv_iff.mpr bigSepS_elements.symm).trans <|
    bigSepS_elements.symm

@[rocq_alias big_sepS_sepM]
theorem bigSepS_sepM {B : Type _} {M : Type _ → Type _} {K : Type _}
    [LawfulFiniteMap M K]
    (Φ : A → K → B → PROP) (X : S) (m : M B) :
    ([∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y) ⊣⊢
      ([∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y) :=
  by
  calc [∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗map] k↦y ∈ m, Φ x k y := bigSepS_elements
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X,
            [∗list] kv ∈ LawfulFiniteMap.toList m, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply bigOpL_equiv; intro _ _ _; exact equiv_iff.mpr .rfl
      _ ⊣⊢ [∗list] kv ∈ LawfulFiniteMap.toList m,
            [∗list] x ∈ FiniteSet.toList X, Φ x kv.1 kv.2 :=
          bigSepL_comm _ (FiniteSet.toList X) (LawfulFiniteMap.toList m)
      _ ⊣⊢ [∗list] kv ∈ LawfulFiniteMap.toList m,
            [∗set] x ∈ X, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply bigOpL_equiv; intro _ _ _
          exact equiv_iff.mpr bigSepS_elements.symm
      _ ⊣⊢ [∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y :=
          equiv_iff.mp <| bigOpL_equiv fun _ => .rfl

@[rocq_alias big_sepS_list_to_set]
theorem bigSepS_list_to_set {Φ : A → PROP} {l : List A}
    (h : l.Nodup) :
    ([∗set] x ∈ (ofList l : S), Φ x) ⊣⊢ [∗list] x ∈ l, Φ x :=
  bigSepS_elements.trans <| bigSepL_perm (FiniteSet.toList_ofList h).symm

/-! ## Filter -/

@[rocq_alias big_sepS_filter']
theorem bigSepS_filter_cond (φ : A → Bool) {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ FiniteSet.filter φ X, Φ y) ⊣⊢
    ([∗set] y ∈ X, if φ y then Φ y else emp) :=
  bigSepS_elements.trans <|
    (bigSepL_perm (Iris.Std.FiniteSet.toList_filter_perm φ X)).trans <|
    (equiv_iff.mp (bigOpL_filter_equiv φ Φ (FiniteSet.toList X))).trans <|
    bigSepS_elements.symm

@[rocq_alias big_sepS_filter]
theorem bigSepS_filter [BIAffine PROP] (φ : A → Bool) {Φ : A → PROP} {X : S} :
    ([∗set] y ∈ FiniteSet.filter φ X, Φ y) ⊣⊢
    ([∗set] y ∈ X, ⌜φ y⌝ → Φ y) :=
  (bigSepS_filter_cond φ).trans <| bigSepS_equiv fun y _ => by
    cases hp : φ y <;> simp
    · exact ⟨imp_intro' <| pure_elim_l (fun hf => nomatch hf), Affine.affine⟩
    · exact true_imp.symm

@[rocq_alias big_sepS_filter_acc']
theorem bigSepS_filter_acc_cond (φ : A → Bool) {Φ : A → PROP} {X Y : S}
    (h : ∀ y, y ∈ Y → φ y → y ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢
      ([∗set] y ∈ Y, if φ y then Φ y else emp) ∗
      (([∗set] y ∈ Y, if φ y then Φ y else emp) -∗ [∗set] y ∈ X, Φ y) := by
  have hfilter_sub : FiniteSet.filter φ Y ⊆ X := fun z hz =>
    let ⟨hz_Y, hz_φ⟩ := FiniteSet.mem_filter φ Y z |>.mp hz; h z hz_Y hz_φ
  have hdisj : FiniteSet.filter φ Y ## (X \ FiniteSet.filter φ Y) :=
    fun a ha => (mem_diff.mp ha.2).2 ha.1
  rw [(diff_subset_decomp hfilter_sub).trans union_comm]
  have hfilt := bigSepS_filter_cond φ (Φ := Φ) (X := Y)
  exact (bigSepS_union hdisj).1.trans <|
    sep_mono hfilt.1 (wand_intro' <| (sep_mono_l hfilt.2).trans (bigSepS_union hdisj).2)

@[rocq_alias big_sepS_filter_acc]
theorem bigSepS_filter_acc [BIAffine PROP] (φ : A → Bool) {Φ : A → PROP} {X Y : S}
    (h : ∀ y, y ∈ Y → φ y → y ∈ X) :
    ([∗set] y ∈ X, Φ y) ⊢
      ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) ∗
      (([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) -∗ [∗set] y ∈ X, Φ y) := by
  have hequiv : ([∗set] y ∈ Y, if φ y then Φ y else emp) ⊣⊢
      ([∗set] y ∈ Y, ⌜φ y⌝ → Φ y) := bigSepS_equiv fun y _ => by
    cases hp : φ y <;> simp
    · exact ⟨imp_intro' <| pure_elim_l (fun hf => nomatch hf), Affine.affine⟩
    · exact true_imp.symm
  exact (bigSepS_filter_acc_cond φ h).trans <| sep_mono hequiv.1 (wand_mono hequiv.2 .rfl)

@[rocq_alias big_sepS_union_2]
theorem bigSepS_union_elim {Φ : A → PROP} {X Y : S}
    [∀ x, TCOr (Affine (Φ x)) (Absorbing (Φ x))] :
    ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ Y, Φ y) -∗ ([∗set] y ∈ X ∪ Y, Φ y) := by
  apply entails_wand; apply wand_intro'
  induction X using FiniteSet.set_ind with
  | hemp => simp only [union_empty_left]; exact (sep_mono_r bigSepS_empty.1).trans sep_emp.1
  | hadd a s hnin ih =>
    rw [show insert a s ∪ Y = insert a (s ∪ Y) from by
      ext w; rw [mem_union, mem_insert, mem_insert, mem_union]; grind]
    refine (sep_mono_r (bigSepS_insert hnin).1).trans <|
      sep_left_comm.1.trans <| (sep_mono_r ih).trans ?_
    by_cases ha : a ∈ Y
    · have hmem := mem_union.mpr (.inr ha : a ∈ s ∨ a ∈ Y)
      have heq : (s ∪ Y) \ {a} = insert a (s ∪ Y) \ {a} := by
        ext w; simp only [mem_diff, mem_union, mem_insert, mem_singleton]; grind
      refine (sep_mono_r (bigSepS_delete hmem).1).trans <| sep_assoc.2.trans <|
        (sep_mono_l sep_elim_l).trans ?_
      rw [heq]; exact (bigSepS_delete (mem_insert.mpr (.inl rfl))).2
    · exact (bigSepS_insert (fun hmem => (mem_union.mp hmem).elim hnin ha)).2

@[rocq_alias big_sepS_insert_2]
theorem bigSepS_insert_elim {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))]
    [∀ y, TCOr (Affine (Φ y)) (Absorbing (Φ y))] :
    Φ x ⊢ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ insert x X, Φ y) := by
  rw [insert_union]; exact bigSepS_singleton.2.trans (wand_entails bigSepS_union_elim)

@[rocq_alias big_sepS_insert_2']
theorem bigSepS_insert_elim_wand {Φ : A → PROP} {X : S} {x : A}
    [TCOr (Affine (Φ x)) (Absorbing (Φ x))]
    [∀ y, TCOr (Affine (Φ y)) (Absorbing (Φ y))] :
    ⊢ Φ x -∗ ([∗set] y ∈ X, Φ y) -∗ ([∗set] y ∈ X ∪ {x}, Φ y) := by
  rw [union_comm]; exact entails_wand bigSepS_insert_elim

@[rocq_alias big_sepS_delete_2]
theorem bigSepS_delete_elim {Φ : A → PROP} {X : S} {x : A}
    [Affine (Φ x)] :
    Φ x ⊢ ([∗set] y ∈ X \ {x}, Φ y) -∗ [∗set] y ∈ X, Φ y := by
  apply wand_intro
  by_cases hx : x ∈ X
  · exact (bigSepS_delete hx).2
  · have heq : X \ {x} = X := by
      ext y; rw [mem_diff, mem_singleton]
      exact ⟨And.left, fun hy => ⟨hy, fun heq => hx (heq ▸ hy)⟩⟩
    rw [heq]; exact (sep_mono_l Affine.affine).trans emp_sep.1

@[rocq_alias big_sepS_fn_insert]
theorem bigSepS_fn_insert [DecidableEq A] {B : Type _} {Ψ : A → B → PROP} {f : A → B}
    {X : S} {x : A} {b : B} (h : x ∉ X) :
    ([∗set] y ∈ insert x X, Ψ y (if y = x then b else f y)) ⊣⊢
      Ψ x b ∗ [∗set] y ∈ X, Ψ y (f y) :=
  (bigSepS_insert h).trans <| by
    simp only [ite_true]
    exact sep_congr_r <| bigSepS_equiv fun y hy => by simp [show y ≠ x from fun heq => h (heq ▸ hy)]

@[rocq_alias big_sepS_fn_insert']
theorem bigSepS_fn_insert_key [DecidableEq A] {Φ : A → PROP} {X : S} {x : A} {P : PROP}
    (h : x ∉ X) :
    ([∗set] y ∈ insert x X, if y = x then P else Φ y) ⊣⊢
      P ∗ [∗set] y ∈ X, Φ y :=
  bigSepS_fn_insert (Ψ := fun _ P => P) (f := Φ) (b := P) h

@[rocq_alias big_sepS_dup]
theorem bigSepS_dup {P : PROP} [Affine P] {X : S} :
    ⊢ □ (P -∗ P ∗ P) -∗ P -∗ [∗set] _x ∈ X, P :=
  entails_wand <| wand_intro' <| sep_comm.1.trans <| bigSepL_dup.trans bigSepS_elements.2

-- TODO: `big_sepS_sepMS` requires multiset infrastructure (`gmultiset`)

end BigSepS

end Iris.BI
