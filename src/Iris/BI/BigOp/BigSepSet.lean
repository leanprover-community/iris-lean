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

/-! # Big Separating Conjunction over Sets

- Rocq Iris: `iris/bi/big_op.v`, Section `sep_set` -/

variable {PROP : Type _} [BI PROP]
variable {S : Type _} {A : Type _} [LawfulFiniteSet S A]

namespace BigSepS

/-! ## Monotonicity and Congruence -/

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
theorem bigSepS_mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Φ x ⊢ Ψ x) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ X, Ψ x :=
  bigSepS_mono fun x _ => h x

@[rocq_alias big_sepS_flip_mono']
theorem bigSepS_flip_mono' {Φ Ψ : A → PROP} {X : S}
    (h : ∀ x, Ψ x ⊢ Φ x) :
    ([∗set] x ∈ X, Ψ x) ⊢ [∗set] x ∈ X, Φ x :=
  bigSepS_mono' h

/-! ## Basic Structural Lemmas -/

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
  rw [insert_union]
  exact equiv_iff.mp <| bigOpS_insert h

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

/-! ## Typeclass Instances -/

@[rocq_alias big_sepS_persistent]
theorem bigSepS_persistent_inst {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Persistent (Φ x)) :
    Persistent ([∗set] x ∈ X, Φ x) := by
  rw [show ([∗set] x ∈ X, Φ x) = bigSepS Φ X from rfl]
  unfold bigSepS bigOpS
  exact bigSepL_persistent fun {_ x} hget =>
    h x (LawfulFiniteSet.mem_toList.mp (List.mem_of_getElem? hget))

instance bigSepS_persistent' {Φ : A → PROP} {X : S}
    [h : ∀ x, Persistent (Φ x)] :
    Persistent ([∗set] x ∈ X, Φ x) :=
  bigSepS_persistent_inst fun _ _ => h _

@[rocq_alias big_sepS_affine]
theorem bigSepS_affine_inst {Φ : A → PROP} {X : S}
    (h : ∀ x, x ∈ X → Affine (Φ x)) :
    Affine ([∗set] x ∈ X, Φ x) := by
  rw [show ([∗set] x ∈ X, Φ x) = bigSepS Φ X from rfl]
  unfold bigSepS bigOpS
  exact bigSepL_affine fun {_ x} hget =>
    h x (LawfulFiniteSet.mem_toList.mp (List.mem_of_getElem? hget))

instance bigSepS_affine' {Φ : A → PROP} {X : S}
    [h : ∀ x, Affine (Φ x)] :
    Affine ([∗set] x ∈ X, Φ x) :=
  bigSepS_affine_inst fun _ _ => h _

/-! ## Separation Logic Combinators -/

@[rocq_alias big_sepS_sep]
theorem bigSepS_sep {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗set] y ∈ X, Φ y) ∗ ([∗set] y ∈ X, Ψ y) :=
  equiv_iff.mp bigOpS_op_equiv

@[rocq_alias big_sepS_sep_2]
theorem bigSepS_sep_2 {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y) ⊢ ([∗set] y ∈ X, Ψ y) -∗ ([∗set] y ∈ X, Φ y ∗ Ψ y) :=
  wand_intro <| sep_comm.1.trans <| bigSepS_sep.symm.1.trans <|
    bigSepS_mono fun _ _ => sep_comm.1

@[rocq_alias big_sepS_and]
theorem bigSepS_and {Φ Ψ : A → PROP} {X : S} :
    ([∗set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗set] y ∈ X, Φ y) ∧ ([∗set] y ∈ X, Ψ y) :=
  and_intro (bigSepS_mono fun _ _ => and_elim_l) (bigSepS_mono fun _ _ => and_elim_r)

@[rocq_alias big_sepS_wand]
theorem bigSepS_wand {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢ ([∗set] x ∈ X, Φ x -∗ Ψ x) -∗ [∗set] x ∈ X, Ψ x :=
  wand_intro <| sep_comm.1.trans <| bigSepS_sep.symm.1.trans <|
    bigSepS_mono fun _ _ => wand_elim_l

/-! ## Lookup and Access -/

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
theorem bigSepS_pure_1 {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  bigSepS_elements.1.trans <| bigSepL_pure_intro.trans <| pure_mono fun h y hy => by
    rw [← LawfulFiniteSet.mem_toList] at hy
    obtain ⟨i, hget⟩ := List.getElem?_of_mem hy
    exact h i y hget

@[rocq_alias big_sepS_affinely_pure_2]
theorem bigSepS_affinely_pure_2 {φ : A → Prop} {X : S} :
    (<affine> (⌜∀ y, y ∈ X → φ y⌝ : PROP)) ⊢ ([∗set] y ∈ X, <affine> ⌜φ y⌝) :=
  (affinely_mono <| pure_mono fun h _ x hget =>
    h x (LawfulFiniteSet.mem_toList.mp (List.mem_of_getElem? hget))).trans <|
  bigSepL_affinely_pure_elim.trans bigSepS_elements.2

@[rocq_alias big_sepS_pure]
theorem bigSepS_pure [BIAffine PROP] {φ : A → Prop} {X : S} :
    ([∗set] y ∈ X, ⌜φ y⌝) ⊣⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  ⟨bigSepS_pure_1, (affine_affinely _).2.trans <|
    bigSepS_affinely_pure_2.trans (bigSepS_mono fun _ _ => affinely_elim)⟩

/-! ## Introduction and Elimination -/

@[rocq_alias big_sepS_intro]
theorem bigSepS_intro {P : PROP} {Φ : A → PROP} {X : S} [Intuitionistic P]
    (h : ∀ x, x ∈ X → P ⊢ Φ x) :
    P ⊢ [∗set] x ∈ X, Φ x :=
  (bigSepL_intro fun _ x hget =>
      h x (LawfulFiniteSet.mem_toList.mp (List.mem_of_getElem? hget))).trans
    bigSepS_elements.2

@[rocq_alias big_sepS_impl]
theorem bigSepS_impl {Φ Ψ : A → PROP} {X : S} :
    ([∗set] x ∈ X, Φ x) ⊢
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) -∗
    [∗set] x ∈ X, Ψ x := by
  apply wand_intro
  refine (sep_mono_r <| bigSepS_intro (P := iprop(□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)))
    fun x hx => intuitionistically_elim.trans <|
      (forall_elim x).trans <| (imp_mono_l <| pure_mono fun _ => hx).trans true_imp.1).trans ?_
  exact bigSepS_sep.symm.1.trans <| bigSepS_mono fun _ _ => wand_elim_r

-- TODO: big_sepS_forall
-- Requires `Persistent` + `BIAffine` interaction with `bigSepS_elem_of` and `bigSepS_intro`.

/-! ## Modal Operators -/

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

/-! ## Subsumption -/

@[rocq_alias big_sepS_subseteq]
theorem bigSepS_subseteq {Φ : A → PROP} {X Y : S}
    [h : ∀ x, Affine (Φ x)]
    (hsub : Y ⊆ X) :
    ([∗set] x ∈ X, Φ x) ⊢ [∗set] x ∈ Y, Φ x := by
  have hdisj : Y ## X \ Y := fun x hx => (mem_diff.mp hx.2).2 hx.1
  rw [show X = Y ∪ X \ Y from (diff_subset_decomp hsub).trans union_comm]
  exact (bigSepS_union hdisj).1.trans sep_elim_l

/-! ## Commuting Lemmas -/

@[rocq_alias big_sepS_sepL]
theorem bigSepS_sepL {B : Type _} (Φ : A → Nat → B → PROP) (X : S) (l : List B) :
    ([∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y) ⊣⊢
      ([∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y) := by
  calc [∗set] x ∈ X, [∗list] k↦y ∈ l, Φ x k y
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗list] k↦y ∈ l, Φ x k y := bigSepS_elements
      _ ⊣⊢ [∗list] k↦y ∈ l, [∗list] x ∈ FiniteSet.toList X, Φ x k y :=
          bigSepL_comm (fun _ x k y => Φ x k y) (FiniteSet.toList X) l
      _ ⊣⊢ [∗list] k↦y ∈ l, [∗set] x ∈ X, Φ x k y :=
          equiv_iff.mp <| bigOpL_equiv fun _ =>
            equiv_iff.mpr bigSepS_elements.symm

@[rocq_alias big_sepS_sepS]
theorem bigSepS_sepS {B : Type _} {T : Type _} [LawfulFiniteSet T B]
    (Φ : A → B → PROP) (X : S) (Y : T) :
    ([∗set] x ∈ X, [∗set] y ∈ Y, Φ x y) ⊣⊢
      ([∗set] y ∈ Y, [∗set] x ∈ X, Φ x y) := by
  calc [∗set] x ∈ X, [∗set] y ∈ Y, Φ x y
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗set] y ∈ Y, Φ x y := bigSepS_elements
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗list] y ∈ FiniteSet.toList Y, Φ x y :=
          equiv_iff.mp <| bigOpL_equiv fun _ =>
            equiv_iff.mpr (bigSepS_elements (Φ := fun y => Φ _ y))
      _ ⊣⊢ [∗list] y ∈ FiniteSet.toList Y, [∗list] x ∈ FiniteSet.toList X, Φ x y :=
          bigSepL_comm (fun _ x _ y => Φ x y) (FiniteSet.toList X) (FiniteSet.toList Y)
      _ ⊣⊢ [∗list] y ∈ FiniteSet.toList Y, [∗set] x ∈ X, Φ x y :=
          equiv_iff.mp <| bigOpL_equiv fun _ =>
            equiv_iff.mpr (bigSepS_elements (Φ := fun x => Φ x _)).symm
      _ ⊣⊢ [∗set] y ∈ Y, [∗set] x ∈ X, Φ x y := bigSepS_elements.symm

@[rocq_alias big_sepS_sepM]
theorem bigSepS_sepM {B : Type _} {M : Type _ → Type _} {K : Type _}
    [LawfulFiniteMap M K]
    (Φ : A → K → B → PROP) (X : S) (m : M B) :
    ([∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y) ⊣⊢
      ([∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y) := by
  calc [∗set] x ∈ X, [∗map] k↦y ∈ m, Φ x k y
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗map] k↦y ∈ m, Φ x k y := bigSepS_elements
      _ ⊣⊢ [∗list] x ∈ FiniteSet.toList X, [∗list] kv ∈ LawfulFiniteMap.toList m, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply bigOpL_equiv
          intro _ _ _; exact equiv_iff.mpr .rfl
      _ ⊣⊢ [∗list] kv ∈ LawfulFiniteMap.toList m, [∗list] x ∈ FiniteSet.toList X, Φ x kv.1 kv.2 :=
          bigSepL_comm (fun _ x _ kv => Φ x kv.1 kv.2) (FiniteSet.toList X) (LawfulFiniteMap.toList m)
      _ ⊣⊢ [∗list] kv ∈ LawfulFiniteMap.toList m, [∗set] x ∈ X, Φ x kv.1 kv.2 := by
          apply equiv_iff.mp; apply bigOpL_equiv
          intro _ _ _; exact equiv_iff.mpr bigSepS_elements.symm
      _ ⊣⊢ [∗map] k↦y ∈ m, [∗set] x ∈ X, Φ x k y :=
          equiv_iff.mp <| bigOpL_equiv fun _ => .rfl

/-! ## List/Set Conversion -/

@[rocq_alias big_sepS_list_to_set]
theorem bigSepS_list_to_set {Φ : A → PROP} {l : List A}
    (h : l.Nodup) :
    ([∗set] x ∈ (ofList l : S), Φ x) ⊣⊢ [∗list] x ∈ l, Φ x :=
  bigSepS_elements.trans <| bigSepL_perm (FiniteSet.toList_ofList h).symm

/-! ## Filter -/

-- TODO: big_sepS_filter', big_sepS_filter, big_sepS_filter_acc', big_sepS_filter_acc
-- These require `FiniteSet.filter` interaction with `bigOpS` which needs additional
-- infrastructure (e.g., `toList_filter` permutation lemmas for bigOpS).

/-! ## Union with Overlap -/

-- TODO: big_sepS_union_2, big_sepS_insert_2, big_sepS_insert_2'
-- These require `TCOr (Affine (Φ x)) (Absorbing (Φ x))` handling and
-- set induction with `set_ind` at the BI level, which is complex.

-- TODO: big_sepS_delete_2
-- Requires careful case analysis on membership and set equality reasoning.

/-! ## Function Insertion -/

-- TODO: big_sepS_fn_insert, big_sepS_fn_insert'
-- These require a `fnInsert` helper and interaction with `bigSepS_insert`.

/-! ## Dup -/

-- TODO: big_sepS_dup
-- Requires intuitionistic modality reasoning over set induction.

/-! ## Elem of acc impl -/

-- TODO: big_sepS_elem_of_acc_impl
-- Requires combining delete with universal quantification and wand introduction.

end BigSepS

end Iris.BI
