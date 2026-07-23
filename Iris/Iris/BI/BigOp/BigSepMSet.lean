/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.BI.BigOp.BigOp
import Iris.BI.BigOp.BigSepList
import Iris.BI.BigOp.BigSepMap
import Iris.BI.BigOp.BigSepSet
import Iris.BI.DerivedLawsLater
import Iris.BI.Instances
import Iris.Std.TC
meta import Iris.Std.RocqPorting

public section

namespace Iris.BI

open Iris.Algebra BigOpL BigOpMS BIBase Iris.Std BigSepL

/-! # Big Separating Conjunction over Multisets -/

variable {PROP : Type _} [BI PROP]
variable {MS : Type _} {A : Type _} [LawfulFiniteMultiSet MS A]

namespace BigSepMS

@[rocq_alias big_sepMS_mono]
theorem bigSepMS_mono {Φ Ψ : A → PROP} {X : MS} (h : ∀ {x}, x ∈ X → Φ x ⊢ Ψ x) :
    ([∗mset] x ∈ X, Φ x) ⊢ [∗mset] x ∈ X, Ψ x :=
  bigOpMS_gen_proper _ .rfl sep_mono h

@[rocq_alias big_sepMS_ne]
theorem bigSepMS_ne {Φ Ψ : A → PROP} {X : MS} {n : Nat} (h : ∀ {x}, x ∈ X → Φ x ≡{n}≡ Ψ x) :
    ([∗mset] x ∈ X, Φ x) ≡{n}≡ ([∗mset] x ∈ X, Ψ x) :=
  bigOpMS_dist h

@[rocq_alias big_sepMS_proper]
theorem bigSepMS_eq {Φ Ψ : A → PROP} {X : MS} (h : ∀ {x}, x ∈ X → Φ x = Ψ x) :
    ([∗mset] x ∈ X, Φ x) = ([∗mset] x ∈ X, Ψ x) :=
  bigOpMS_eq h

theorem bigSepMS_eqv {Φ Ψ : A → PROP} {X : MS} (h : ∀ {x}, x ∈ X → Φ x ⊣⊢ Ψ x) :
    ([∗mset] x ∈ X, Φ x) ⊣⊢ ([∗mset] x ∈ X, Ψ x) :=
  equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpMS_eq fun hx => (equiv_iff.mpr (h hx)).to_eq

@[rocq_alias big_sepMS_mono']
theorem bigSepMS_mono_of_forall {Φ Ψ : A → PROP} {X : MS} (h : ∀ x, Φ x ⊢ Ψ x) :
    ([∗mset] x ∈ X, Φ x) ⊢ [∗mset] x ∈ X, Ψ x :=
  bigSepMS_mono fun {x} _ => h x

@[rocq_alias big_sepMS_flip_mono']
theorem bigSepMS_flip_mono {Φ Ψ : A → PROP} {X : MS} (h : ∀ x, Ψ x ⊢ Φ x) :
    ([∗mset] x ∈ X, Ψ x) ⊢ [∗mset] x ∈ X, Φ x :=
  bigSepMS_mono_of_forall h

/-- Lean helper (Coq has no `big_sepMS_elements`; only algebra `big_opMS_elements`). -/
theorem bigSepMS_elements {Φ : A → PROP} {X : MS} :
    ([∗mset] x ∈ X, Φ x) ⊣⊢ [∗list] x ∈ FiniteMultiSet.toList X, Φ x :=
  equiv_iff.mp <| OFE.Equiv.of_eq bigOpMS_bigOpL

@[simp, rocq_alias big_sepMS_empty]
theorem bigSepMS_empty {Φ : A → PROP} : ([∗mset] x ∈ (∅ : MS), Φ x) ⊣⊢ emp :=
  equiv_iff.mp <| .of_eq <| bigOpMS_empty

@[rocq_alias big_sepMS_empty']
theorem bigSepMS_empty_intro {P : PROP} [Affine P] {Φ : A → PROP} :
    P ⊢ [∗mset] x ∈ (∅ : MS), Φ x :=
  Affine.affine.trans bigSepMS_empty.2

/-- Lean helper (Coq has no `big_sepMS_emp`). -/
theorem bigSepMS_emp {X : MS} : ([∗mset] _x ∈ X, (emp : PROP)) ⊣⊢ emp :=
  bigSepMS_elements.trans bigSepL_emp

@[rocq_alias big_sepMS_singleton]
theorem bigSepMS_singleton {Φ : A → PROP} {x : A} : ([∗mset] y ∈ ({x} : MS), Φ y) ⊣⊢ Φ x :=
  equiv_iff.mp (OFE.Equiv.of_eq bigOpMS_singleton)

@[rocq_alias big_sepMS_disj_union]
theorem bigSepMS_disjUnion {Φ : A → PROP} {X Y : MS} :
    ([∗mset] y ∈ X ⊎ Y, Φ y) ⊣⊢ ([∗mset] y ∈ X, Φ y) ∗ ([∗mset] y ∈ Y, Φ y) :=
  equiv_iff.mp <| OFE.Equiv.of_eq bigOpMS_disjUnion

@[rocq_alias big_sepMS_insert]
theorem bigSepMS_insert {Φ : A → PROP} {X : MS} {x : A} :
    ([∗mset] y ∈ ({x} ⊎ X), Φ y) ⊣⊢ Φ x ∗ [∗mset] y ∈ X, Φ y :=
  equiv_iff.mp <| OFE.Equiv.of_eq bigOpMS_insert

@[rocq_alias big_sepMS_delete]
theorem bigSepMS_delete {Φ : A → PROP} {X : MS} {x : A} (h : x ∈ X) :
    ([∗mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗mset] y ∈ X \ {x}, Φ y :=
  equiv_iff.mp (OFE.Equiv.of_eq <| bigOpMS_delete h)

@[rocq_alias big_sepMS_persistent]
theorem bigSepMS_persistent {Φ : A → PROP} {X : MS}
    (h : ∀ {x}, x ∈ X → Persistent (Φ x)) :
    Persistent ([∗mset] x ∈ X, Φ x) where
  persistent := bigOpMS_closed (fun Q => Q ⊢ <pers> Q) Φ X persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_mpr) (fun hm => (h hm).persistent)

@[rocq_alias big_sepMS_persistent']
instance bigSepMS_persistent_inst {Φ : A → PROP} {X : MS} [h : ∀ x, Persistent (Φ x)] :
    Persistent ([∗mset] x ∈ X, Φ x) :=
  bigSepMS_persistent fun _ => h _

@[rocq_alias big_sepMS_affine]
theorem bigSepMS_affine {Φ : A → PROP} {X : MS} (h : ∀ {x}, x ∈ X → Affine (Φ x)) :
    Affine ([∗mset] x ∈ X, Φ x) where
  affine := bigOpMS_closed (fun Q => Q ⊢ emp) Φ X .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (fun hm => (h hm).affine)

@[rocq_alias big_sepMS_affine']
instance bigSepMS_affine_inst {Φ : A → PROP} {X : MS} [h : ∀ x, Affine (Φ x)] :
    Affine ([∗mset] x ∈ X, Φ x) :=
  bigSepMS_affine fun _ => h _

@[rocq_alias big_sepMS_empty_persistent]
instance bigSepMS_empty_persistent_inst {Φ : A → PROP} :
    Persistent ([∗mset] x ∈ (∅ : MS), Φ x) where
  persistent := bigSepMS_empty.1.trans <|
    Persistent.persistent.trans <| persistently_mono bigSepMS_empty.2

@[rocq_alias big_sepMS_empty_affine]
instance bigSepMS_empty_affine_inst {Φ : A → PROP} :
    Affine ([∗mset] x ∈ (∅ : MS), Φ x) where
  affine := bigSepMS_empty.1.trans Affine.affine

@[rocq_alias big_sepMS_empty_timeless]
instance bigSepMS_empty_timeless_inst [Timeless (emp : PROP)] {Φ : A → PROP} :
    Timeless ([∗mset] x ∈ (∅ : MS), Φ x) where
  timeless := (later_congr bigSepMS_empty).1.trans <|
    Timeless.timeless.trans <| except0_mono bigSepMS_empty.2

@[rocq_alias big_sepMS_timeless]
theorem bigSepMS_timeless [Timeless (emp : PROP)] {Φ : A → PROP} {X : MS}
    (h : ∀ {x}, x ∈ X → Timeless (Φ x)) :
    Timeless ([∗mset] x ∈ X, Φ x) where
  timeless := bigOpMS_closed (fun Q => ▷ Q ⊢ ◇ Q) Φ X Timeless.timeless
    (fun hx hy => later_sep.1.trans <| (sep_mono hx hy).trans except0_sep.2)
    (fun hm => (h hm).timeless)

@[rocq_alias big_sepMS_timeless']
instance bigSepMS_timeless_inst [Timeless (emp : PROP)] {Φ : A → PROP} {X : MS}
    [h : ∀ x, Timeless (Φ x)] :
    Timeless ([∗mset] x ∈ X, Φ x) :=
  bigSepMS_timeless fun _ => h _

@[rocq_alias big_sepMS_sep]
theorem bigSepMS_sep {Φ Ψ : A → PROP} {X : MS} :
    ([∗mset] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗mset] y ∈ X, Φ y) ∗ ([∗mset] y ∈ X, Ψ y) :=
  equiv_iff.mp <| OFE.Equiv.of_eq bigOpMS_op_eq

@[rocq_alias big_sepMS_and]
theorem bigSepMS_and {Φ Ψ : A → PROP} {X : MS} :
    ([∗mset] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗mset] y ∈ X, Φ y) ∧ ([∗mset] y ∈ X, Ψ y) :=
  and_intro (bigSepMS_mono fun _ => and_elim_l) (bigSepMS_mono fun _ => and_elim_r)

@[rocq_alias big_sepMS_wand]
theorem bigSepMS_wand {Φ Ψ : A → PROP} {X : MS} :
    ([∗mset] x ∈ X, Φ x) ⊢ ([∗mset] x ∈ X, Φ x -∗ Ψ x) -∗ [∗mset] x ∈ X, Ψ x :=
  wand_intro <| sep_comm.1.trans <| bigSepMS_sep.symm.1.trans <|
    bigSepMS_mono fun _ => wand_elim_left

@[rocq_alias big_sepMS_elem_of]
theorem bigSepMS_elem_of {Φ : A → PROP} {X : MS} {x : A} (hmem : x ∈ X) [∀ y, Affine (Φ y)] :
    ([∗mset] y ∈ X, Φ y) ⊢ Φ x :=
  (bigSepMS_delete hmem).1.trans sep_elim_left

@[rocq_alias big_sepMS_elem_of_acc]
theorem bigSepMS_elem_of_acc {Φ : A → PROP} {X : MS} {x : A} (h : x ∈ X) :
    ([∗mset] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗mset] y ∈ X, Φ y)) :=
  (bigSepMS_delete h).1.trans <| sep_mono_right <| wand_intro_left (bigSepMS_delete h).2

@[rocq_alias big_sepMS_pure_1]
theorem bigSepMS_pure_intro {φ : A → Prop} {X : MS} :
    ([∗mset] y ∈ X, ⌜φ y⌝) ⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  bigSepMS_elements.1.trans <| bigSepL_pure_intro.trans <| pure_mono fun h _ hy =>
    h _ _ (List.getElem?_of_mem (LawfulFiniteMultiSet.mem_toList.mpr hy)).choose_spec

@[rocq_alias big_sepMS_affinely_pure_2]
theorem bigSepMS_affinely_pure_elim {φ : A → Prop} {X : MS} :
    (<affine> (⌜∀ y, y ∈ X → φ y⌝ : PROP)) ⊢ ([∗mset] y ∈ X, <affine> ⌜φ y⌝) :=
  (affinely_mono <| pure_mono fun h _ x hget =>
      h x (LawfulFiniteMultiSet.mem_toList.mp (List.mem_of_getElem? hget))).trans <|
  bigSepL_affinely_pure_elim.trans bigSepMS_elements.2

@[rocq_alias big_sepMS_pure]
theorem bigSepMS_pure [BIAffine PROP] {φ : A → Prop} {X : MS} :
    ([∗mset] y ∈ X, ⌜φ y⌝) ⊣⊢ (⌜∀ y, y ∈ X → φ y⌝ : PROP) :=
  ⟨bigSepMS_pure_intro, (affine_affinely _).2.trans <|
    bigSepMS_affinely_pure_elim.trans (bigSepMS_mono fun _ => affinely_elim)⟩

@[rocq_alias big_sepMS_intro]
theorem bigSepMS_intro {P : PROP} {Φ : A → PROP} {X : MS} [Intuitionistic P]
    (h : ∀ {x}, x ∈ X → P ⊢ Φ x) :
    P ⊢ [∗mset] x ∈ X, Φ x :=
  (bigSepL_intro fun _ _ hget =>
    h (LawfulFiniteMultiSet.mem_toList.mp (List.mem_of_getElem? hget))).trans bigSepMS_elements.2

@[rocq_alias big_sepMS_impl]
theorem bigSepMS_impl {Φ Ψ : A → PROP} {X : MS} :
    ([∗mset] x ∈ X, Φ x) ⊢
    (□ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x)) -∗ [∗mset] x ∈ X, Ψ x := by
  refine wand_intro <| (sep_mono_right ?_).trans <|
    bigSepMS_sep.symm.1.trans <| bigSepMS_mono fun _ => wand_elim_right
  exact bigSepMS_intro fun hx => intuitionistically_elim.trans <|
    (forall_elim _).trans <| (imp_mono_left <| pure_mono fun _ => hx).trans true_imp.1

@[rocq_alias big_sepMS_forall]
theorem bigSepMS_forall [BIAffine PROP] {Φ : A → PROP} {X : MS} [∀ x, Persistent (Φ x)] :
    ([∗mset] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x) := by
  refine ⟨forall_intro fun x => imp_intro_swap ?_, ?_⟩
  · refine pure_elim_left fun hmem => (bigSepMS_elem_of_acc hmem).trans ?_
    refine (sep_mono_left Persistent.persistent).trans ?_
    exact sep_comm.1.trans <| persistently_absorb_right.trans persistently_elim
  · induction X using multiset_ind with
    | empty => exact bigSepMS_empty_intro
    | disjUnion_singleton a s ih =>
      refine .trans ?_ bigSepMS_insert.2
      refine .trans (and_intro ?_ ?_) persistent_and_sep_mp
      · exact (forall_elim _).trans <|
          (and_intro (pure_intro <| mem_disjUnion_iff.mpr <| .inl (mem_singleton_iff.mpr rfl))
            .rfl).trans imp_elim_right
      · exact (forall_mono fun x => imp_mono_left
          (pure_mono fun hx => mem_disjUnion_iff.mpr <| .inr hx)).trans ih

@[rocq_alias big_sepMS_elem_of_acc_impl]
theorem bigSepMS_elem_of_acc_impl {Φ : A → PROP} {X : MS} {x : A} (h : x ∈ X) :
    ([∗mset] y ∈ X, Φ y) ⊢
    Φ x ∗
    (∀ (Ψ : A → PROP), (□ (∀ y, ⌜y ∈ X \ {x}⌝ → Φ y -∗ Ψ y)) -∗ Ψ x -∗
      ([∗mset] y ∈ X, Ψ y)) := by
  refine (bigSepMS_delete h).1.trans <| sep_mono_right ?_
  refine forall_intro fun Ψ => wand_intro <| wand_intro ?_
  refine sep_comm.1.trans <| (sep_mono_right ?_).trans (bigSepMS_delete (Φ := Ψ) h).2
  exact (sep_mono_left bigSepMS_impl).trans wand_elim_left

@[rocq_alias big_sepMS_persistently]
theorem bigSepMS_persistently [BIAffine PROP] {Φ : A → PROP} {X : MS} :
    (<pers> ([∗mset] y ∈ X, Φ y)) ⊣⊢ [∗mset] y ∈ X, <pers> (Φ y) :=
  letI := MonoidHomomorphism.ofEq persistently_ne
    (equiv_iff.mpr persistently_sep).to_eq (equiv_iff.mpr persistently_emp_affine).to_eq
  equiv_iff.mp <| OFE.Equiv.of_eq <| BigOpMS.hom this Φ X

@[rocq_alias big_sepMS_later]
theorem bigSepMS_later [BIAffine PROP] {Φ : A → PROP} {X : MS} :
    (▷ [∗mset] y ∈ X, Φ y) ⊣⊢ [∗mset] y ∈ X, ▷ Φ y :=
  letI := MonoidHomomorphism.ofEq later_ne
    (equiv_iff.mpr later_sep).to_eq (equiv_iff.mpr later_emp).to_eq
  equiv_iff.mp <| OFE.Equiv.of_eq <| BigOpMS.hom this Φ X

@[rocq_alias big_sepMS_later_2]
theorem bigSepMS_later_2 {Φ : A → PROP} {X : MS} :
    ([∗mset] y ∈ X, ▷ Φ y) ⊢ (▷ [∗mset] y ∈ X, Φ y) :=
  bigSepMS_elements.1.trans <| bigSepL_later_2.trans <| later_mono bigSepMS_elements.2

@[rocq_alias big_sepMS_laterN]
theorem bigSepMS_laterN [BIAffine PROP] {Φ : A → PROP} {n : Nat} {X : MS} :
    (▷^[n] [∗mset] y ∈ X, Φ y) ⊣⊢ [∗mset] y ∈ X, ▷^[n] Φ y :=
  match n with
  | 0 => .rfl
  | _ + 1 => (later_congr bigSepMS_laterN).trans bigSepMS_later

@[rocq_alias big_sepMS_laterN_2]
theorem bigSepMS_laterN_2 {Φ : A → PROP} {n : Nat} {X : MS} :
    ([∗mset] y ∈ X, ▷^[n] Φ y) ⊢ (▷^[n] [∗mset] y ∈ X, Φ y) :=
  match n with
  | 0 => .rfl
  | _ + 1 => bigSepMS_later_2.trans <| later_mono bigSepMS_laterN_2

@[rocq_alias big_sepMS_subseteq]
theorem bigSepMS_subseteq {Φ : A → PROP} {X Y : MS}
    [∀ x, Affine (Φ x)] (hsub : Y ⊆ X) :
    ([∗mset] x ∈ X, Φ x) ⊢ [∗mset] x ∈ Y, Φ x := by
  conv => lhs; rw [disjUnion_difference_of_subseteq hsub]
  exact bigSepMS_disjUnion.1.trans sep_elim_left

@[rocq_alias big_sepMS_sepL]
theorem bigSepMS_comm_list {B : Type _} (Φ : A → Nat → B → PROP) (X : MS) (l : List B) :
    ([∗mset] x ∈ X, [∗list] k↦y ∈ l, Φ x k y) ⊣⊢
      ([∗list] k↦y ∈ l, [∗mset] x ∈ X, Φ x k y) := by
  refine bigSepMS_elements.trans ?_
  refine (bigSepL_comm _ (FiniteMultiSet.toList X) l).trans ?_
  exact equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr bigSepMS_elements.symm).to_eq

@[rocq_alias big_sepMS_sepM]
theorem bigSepMS_comm_map {B : Type _} {M : Type _ → Type _} {K : Type _}
    [LawfulFiniteMap M K]
    (Φ : A → K → B → PROP) (X : MS) (m : M B) :
    ([∗mset] x ∈ X, [∗map] k↦y ∈ m, Φ x k y) ⊣⊢
      ([∗map] k↦y ∈ m, [∗mset] x ∈ X, Φ x k y) := by
  refine bigSepMS_elements.trans ?_
  refine (bigSepL_comm _ (FiniteMultiSet.toList X) (LawfulFiniteMap.toList m)).trans ?_
  refine (equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr bigSepMS_elements.symm).to_eq).trans <|
    equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => rfl

@[rocq_alias big_sepMS_sepS]
theorem bigSepMS_comm_set {B : Type _} {T : Type _} [LawfulFiniteSet T B]
    (Φ : A → B → PROP) (X : MS) (Y : T) :
    ([∗mset] x ∈ X, [∗set] y ∈ Y, Φ x y) ⊣⊢
      ([∗set] y ∈ Y, [∗mset] x ∈ X, Φ x y) := by
  refine bigSepMS_elements.trans ?_
  refine (equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr BigSepS.bigSepS_elements).to_eq).trans ?_
  refine (bigSepL_comm _ (FiniteMultiSet.toList X) (FiniteSet.toList Y)).trans ?_
  exact (equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr bigSepMS_elements.symm).to_eq).trans <|
    BigSepS.bigSepS_elements.symm

@[rocq_alias big_sepMS_sepMS]
theorem bigSepMS_comm_mset {B : Type _} {T : Type _} [LawfulFiniteMultiSet T B]
    (Φ : A → B → PROP) (X : MS) (Y : T) :
    ([∗mset] x ∈ X, [∗mset] y ∈ Y, Φ x y) ⊣⊢
      ([∗mset] y ∈ Y, [∗mset] x ∈ X, Φ x y) := by
  refine bigSepMS_elements.trans ?_
  refine (equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr bigSepMS_elements).to_eq).trans ?_
  refine (bigSepL_comm _ (FiniteMultiSet.toList X) (FiniteMultiSet.toList Y)).trans ?_
  exact (equiv_iff.mp <| OFE.Equiv.of_eq <| bigOpL_eq fun _ => (equiv_iff.mpr bigSepMS_elements.symm).to_eq).trans <|
    bigSepMS_elements.symm

@[rocq_alias big_sepMS_dup]
theorem bigSepMS_dup {P : PROP} [Affine P] {X : MS} :
    ⊢ □ (P -∗ P ∗ P) -∗ P -∗ [∗mset] _x ∈ X, P :=
  entails_wand <| wand_intro_left <| sep_comm.1.trans <| bigSepL_dup.trans bigSepMS_elements.2

end BigSepMS
end Iris.BI
