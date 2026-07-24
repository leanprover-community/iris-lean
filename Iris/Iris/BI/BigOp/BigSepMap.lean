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
import Iris.BI.BigOp.BigSepSet
import Iris.Std.TC
import Batteries.Data.List.Perm
meta import Iris.Std.RocqPorting

public section

namespace Iris.BI

open Iris.Algebra BigOpL BigOpM BIBase Iris.Std BigSepL LawfulPartialMap PartialMap

/-! # Big Separating Conjunction over Maps -/

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

namespace BigSepM

@[simp, rocq_alias big_sepM_empty]
theorem bigSepM_empty {Φ : K → V → PROP} :
    ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) ⊣⊢ emp :=
  BiEntails.of_eq <| bigOpM_empty Φ

@[rocq_alias big_sepM_empty']
theorem bigSepM_empty_intro {P : PROP} [Affine P] {Φ : K → V → PROP} :
    P ⊢ [∗map] k ↦ x ∈ (∅ : M V), Φ k x :=
  Affine.affine.trans bigSepM_empty.2

theorem bigSepM_eqv_of_perm {Φ : K → V → PROP} {m₁ m₂ : M V} (h : m₁ ≡ₘ m₂) :
    ([∗map] k ↦ v ∈ m₁, Φ k v) ⊣⊢ ([∗map] k ↦ v ∈ m₂, Φ k v) :=
  BiEntails.of_eq <| bigOpM_eq_of_perm _ h

/-- A `bigSepM` over the empty map is `emp`. -/
theorem bigSepM_eqv_empty {Φ : K → V → PROP} {m : M V} (h : m = ∅) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢ emp := by
  simp [h]

@[rocq_alias big_sepM_singleton]
theorem bigSepM_singleton {Φ : K → V → PROP} {i : K} {x : V} :
    ([∗map] k ↦ v ∈ (singleton i x : M V), Φ k v) ⊣⊢ Φ i x :=
  BiEntails.of_eq <| bigOpM_singleton_eq Φ i x

@[rocq_alias big_sepM_insert]
theorem bigSepM_insert {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = none) :
    ([∗map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢ Φ i x ∗ [∗map] k ↦ v ∈ m, Φ k v :=
  BiEntails.of_eq <| bigOpM_insert_eq Φ x h

@[rocq_alias big_sepM_insert_delete]
theorem bigSepM_insert_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V} :
    ([∗map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢
      Φ i x ∗ [∗map] k ↦ v ∈ delete m i, Φ k v :=
  BiEntails.of_eq <| bigOpM_insert_delete_eq Φ m i x

@[rocq_alias big_sepM_delete]
theorem bigSepM_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢ Φ i x ∗ [∗map] k ↦ v ∈ delete m i, Φ k v :=
  BiEntails.of_eq <| bigOpM_delete_eq Φ h

@[rocq_alias big_sepM_mono]
theorem bigSepM_mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k v}, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_gen_proper .rfl sep_mono h

@[rocq_alias big_sepM_proper]
theorem bigSepM_eq {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Φ k x = Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) = [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_eq h

theorem bigSepM_eq_of_forall_eq {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Φ k x = Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) = [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_eq_of_forall_eq m h

@[rocq_alias big_sepM_ne]
theorem bigSepM_dist {Φ Ψ : K → V → PROP} {m : M V} {n : Nat}
    (h : ∀ {k x}, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡{n}≡ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_dist h

@[rocq_alias big_sepM_mono']
theorem bigSepM_mono_of_forall {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Φ k x ⊢ Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigSepM_mono fun _ => h

@[rocq_alias big_sepM_flip_mono']
theorem bigSepM_flip_mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Ψ k x ⊢ Φ k x) :
    ([∗map] k ↦ x ∈ m, Ψ k x) ⊢ [∗map] k ↦ x ∈ m, Φ k x :=
  bigSepM_mono fun _ => h

@[rocq_alias big_sepM_empty_persistent]
instance bigSepM_nil_persistent_inst {Φ : K → V → PROP} :
    Persistent ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  persistent := bigSepM_empty.1.trans (Persistent.persistent.trans (persistently_mono bigSepM_empty.2))

@[rocq_alias big_sepM_persistent]
theorem bigSepM_persistent {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Persistent (Φ k x)) :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) where
  persistent := bigOpM_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_mpr) (h · |>.persistent)

@[rocq_alias big_sepM_persistent']
instance bigSepM_persistent_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_persistent fun _ => inferInstance

@[rocq_alias big_sepM_empty_affine]
instance bigSepM_nil_affine_inst {Φ : K → V → PROP} :
    Affine ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  affine := bigSepM_empty.1.trans Affine.affine

@[rocq_alias big_sepM_affine]
theorem bigSepM_affine {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Affine (Φ k x)) :
    Affine ([∗map] k ↦ x ∈ m, Φ k x) where
  affine := bigOpM_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (h · |>.affine)

@[rocq_alias big_sepM_affine']
instance bigSepM_affine_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Affine (Φ k x)] :
    Affine ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_affine fun _ => inferInstance

instance bigSepM_affine_biaffine_inst {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    Affine ([∗map] k ↦ x ∈ m, Φ k x) where
  affine := bigOpM_closed (P := fun Q => Q ⊢ emp) .rfl
    (fun hx hy => (sep_mono hx hy).trans sep_emp.1) (fun _ => Affine.affine)

@[rocq_alias big_sepM_empty_timeless]
instance bigSepM_nil_timeless_inst [Timeless (emp : PROP)] {Φ : K → V → PROP} :
    Timeless ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  timeless := (later_congr bigSepM_empty).1.trans (Timeless.timeless.trans (except0_mono bigSepM_empty.2))

@[rocq_alias big_sepM_timeless]
theorem bigSepM_timeless [Timeless (emp : PROP)] {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Timeless (Φ k x)) :
    Timeless ([∗map] k ↦ x ∈ m, Φ k x) where
  timeless := bigOpM_closed (P := fun Q => ▷ Q ⊢ ◇ Q) Timeless.timeless
    (fun hx hy => later_sep.1.trans <| (sep_mono hx hy).trans except0_sep.2)
    (h · |>.timeless)

@[rocq_alias big_sepM_timeless']
instance bigSepM_timeless_inst [Timeless (emp : PROP)] {Φ : K → V → PROP} {m : M V}
    [∀ k x, Timeless (Φ k x)] :
    Timeless ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_timeless fun _ => inferInstance

instance bigSepM_nil_absorbing_inst [BIAffine PROP] {Φ : K → V → PROP} :
    Absorbing ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  absorbing := (absorbingly_mono bigSepM_empty.1).trans (absorbingly_emp.1.trans (true_emp.1.trans bigSepM_empty.2))

theorem bigSepM_absorbing [BIAffine PROP] {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Absorbing (Φ k x)) :
    Absorbing ([∗map] k ↦ x ∈ m, Φ k x) where
  absorbing := bigOpM_closed (P := fun Q => <absorb> Q ⊢ Q)
    (absorbingly_emp.1.trans true_emp.1)
    (fun hx hy => absorbingly_sep.1.trans (sep_mono hx hy)) (h · |>.absorbing)

instance bigSepM_absorbing_inst [BIAffine PROP] {Φ : K → V → PROP} {m : M V}
    [∀ k x, Absorbing (Φ k x)] :
    Absorbing ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_absorbing fun _ => inferInstance

theorem bigSepM_emp [DecidableEq K] {m : M V} :
    bigSepM (fun (_ : K) (_ : V) => (emp : PROP)) m ⊣⊢ emp :=
  BiEntails.of_eq <| bigOpM_const_unit_eq m

@[rocq_alias big_sepM_sep]
theorem bigSepM_sep_eq {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, iprop(Φ k x ∗ Ψ k x)) =
      iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗ [∗map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_op_eq Φ Ψ m

@[rocq_alias big_sepM_sep_2]
theorem bigSepM_sep_eq_symm {Φ Ψ : K → V → PROP} {m : M V} :
    iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗ [∗map] k ↦ x ∈ m, Ψ k x) =
      [∗map] k ↦ x ∈ m, iprop(Φ k x ∗ Ψ k x) :=
  bigSepM_sep_eq.symm

@[rocq_alias big_sepM_and]
theorem bigSepM_and {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x ∧ Ψ k x) ⊢
      ([∗map] k ↦ x ∈ m, Φ k x) ∧ [∗map] k ↦ x ∈ m, Ψ k x :=
  and_intro (bigSepM_mono fun _ => and_elim_l) (bigSepM_mono fun _ => and_elim_r)

@[rocq_alias big_sepM_wand]
theorem bigSepM_wand {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢
      ([∗map] k ↦ x ∈ m, iprop(Φ k x -∗ Ψ k x)) -∗ [∗map] k ↦ x ∈ m, Ψ k x :=
  wand_intro <| (BiEntails.of_eq bigSepM_sep_eq.symm).1.trans <|
  bigSepM_mono fun _ => wand_elim_right

/-! ## Lookup Lemmas -/

@[rocq_alias big_sepM_lookup_acc]
theorem bigSepM_lookup_acc {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢ Φ i x ∗ (Φ i x -∗ [∗map] k ↦ v ∈ m, Φ k v) := by
  refine ⟨?_, wand_elim_right⟩
  exact (bigSepM_delete h).1.trans <| sep_mono_right <| wand_intro <|
    sep_comm.1.trans (bigSepM_delete h).2


@[rocq_alias big_sepM_lookup]
theorem bigSepM_lookup {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    [TCOr (∀ k v, Affine (Φ k v)) (Absorbing (Φ i x))] → ([∗map] k ↦ v ∈ m, Φ k v) ⊢ Φ i x
  | TCOr.l => (bigSepM_delete h).1.trans sep_elim_left
  | TCOr.r => (bigSepM_lookup_acc h).1.trans sep_elim_left

@[rocq_alias big_sepM_lookup_dom]
theorem bigSepM_lookup_dom {Φ : K → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    [TCOr (∀ k, Affine (Φ k)) (Absorbing (Φ i))] → ([∗map] k ↦ _v ∈ m, Φ k) ⊢ Φ i
  | TCOr.l => (bigSepM_delete h).1.trans sep_elim_left
  | TCOr.r => (bigSepM_lookup_acc h).1.trans sep_elim_left

@[rocq_alias big_sepM_insert_acc]
theorem bigSepM_insert_acc {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢
      Φ i x ∗ (∀ v', Φ i v' -∗ [∗map] k ↦ v ∈ insert m i v', Φ k v) :=
  (bigSepM_delete h).1.trans <| sep_mono_right <| forall_intro fun _ =>
    wand_intro <| sep_comm.1.trans bigSepM_insert_delete.2

@[rocq_alias big_sepM_insert_2]
theorem bigSepM_insert_elim {Φ : K → V → PROP} {m : M V} {i : K} {x : V} [∀ k v, Affine (Φ k v)] :
    ⊢ Φ i x -∗ ([∗map] k ↦ v ∈ m, Φ k v) -∗ [∗map] k ↦ v ∈ insert m i x, Φ k v :=
  entails_wand <| wand_intro <|
  match hm : get? m i with
  | none => (bigSepM_insert hm).2
  | some _ => (sep_mono_right ((bigSepM_delete hm).1.trans sep_elim_right)).trans bigSepM_insert_delete.2

@[rocq_alias big_sepM_insert_override]
theorem bigSepM_insert_exist {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x = Φ i x') :
    ([∗map] k ↦ v ∈ insert m i x', Φ k v) = [∗map] k ↦ v ∈ m, Φ k v :=
  bigOpM_insert_override_eq hi hΦ

@[rocq_alias big_sepM_insert_override_1]
theorem bigSepM_insert_exist_elim {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x ⊢ Φ i x') :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢ [∗map] k ↦ v ∈ insert m i x', Φ k v :=
  (bigSepM_delete hi).1.trans <| (sep_mono_left hΦ).trans bigSepM_insert_delete.2

@[rocq_alias big_sepM_insert_override_2]
theorem bigSepM_insert_exist_intro {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x' ⊢ Φ i x) :
    ([∗map] k ↦ v ∈ insert m i x', Φ k v) ⊢ [∗map] k ↦ v ∈ m, Φ k v :=
  bigSepM_insert_delete.1.trans <| (sep_mono_left hΦ).trans (bigSepM_delete hi).2

@[rocq_alias big_sepM_fn_insert]
theorem bigSepM_fn_insert [DecidableEq K] {B : Type _} {g : K → V → B → PROP} {f : K → B}
    {m : M V} {i : K} {x : V} {b : B} (hi : get? m i = none) :
    ([∗map] k ↦ y ∈ insert m i x, g k y (if k = i then b else f k)) =
    iprop(g i x b ∗ [∗map] k ↦ y ∈ m, g k y (f k)) :=
  bigOpM_fn_insert_eq g f x b hi

@[rocq_alias big_sepM_fn_insert']
theorem bigSepM_fn_insert_key [DecidableEq K] {f : K → PROP} {m : M V} {i : K} {x : V} {P : PROP}
    (hi : get? m i = none) :
    ([∗map] k ↦ _v ∈ insert m i x, if k = i then P else f k) =
    iprop(P ∗ [∗map] k ↦ _v ∈ m, f k) :=
  bigOpM_fn_insert_eq' f x P hi

@[rocq_alias big_sepM_intro]
theorem bigSepM_intro {P : PROP} [Intuitionistic P] {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k v}, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∗map] k ↦ x ∈ m, Φ k x := by
  refine bigOpM_closed (P := fun Q => P ⊢ Q)
    (Intuitionistic.intuitionistic.trans affinely_elim_emp) (fun hx hy => ?_) (h ·)
  exact Intuitionistic.intuitionistic.trans <| intuitionistically_sep_idem.2.trans <|
    sep_mono (intuitionistically_elim.trans hx) (intuitionistically_elim.trans hy)

theorem bigSepM_forall_intro {Φ : K → V → PROP} {m : M V}
    [BIAffine PROP] [∀ k v, Persistent (Φ k v)] :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) :=
  forall_intro fun _ => forall_intro fun _ => imp_intro_swap <|
  pure_elim_left fun hget => (bigSepM_lookup_acc hget).1.trans <|
  (sep_mono_left Persistent.persistent).trans <| sep_comm.1.trans <|
  persistently_absorb_right.trans persistently_elim

theorem bigSepM_forall_elim {Φ : K → V → PROP} {m : M V}
    [BIAffine PROP] [inst : ∀ k v, Persistent (Φ k v)] :
    (∀ k v, ⌜get? m k = some v⌝ → Φ k v) ⊢ [∗map] k ↦ x ∈ m, Φ k x :=
  (bigOpM_closed
    (P := fun (Q : PROP) =>
      ((∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) : PROP) ⊢ Q) ∧ Persistent Q)
    ⟨Affine.affine, inferInstance⟩
    (fun ⟨hx, _⟩ ⟨hy, _⟩ => ⟨and_self.2.trans <| (and_mono hx hy).trans
      persistent_and_sep_mp, inferInstance⟩)
    (fun {k x} hget => ⟨(forall_elim k).trans <| (forall_elim x).trans <|
      (imp_congr_left <| pure_true hget).1.trans true_imp.1, inst k x⟩)).1

@[rocq_alias big_sepM_forall]
theorem bigSepM_forall {Φ : K → V → PROP} {m : M V}
    [BIAffine PROP] [∀ k v, Persistent (Φ k v)] :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) :=
  ⟨bigSepM_forall_intro, bigSepM_forall_elim⟩

@[rocq_alias big_sepM_impl]
theorem bigSepM_impl {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢
      □ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) -∗
      [∗map] k ↦ x ∈ m, Ψ k x := by
  refine wand_intro <| (sep_mono_right ?_).trans <|
    (BiEntails.of_eq bigSepM_sep_eq.symm).1.trans <| bigSepM_mono fun _ => wand_elim_right
  exact bigSepM_intro fun {k x} hget => intuitionistically_elim.trans <|
    (forall_elim k).trans <| (forall_elim x).trans <|
    (imp_mono_left <| pure_mono fun _ => hget).trans true_imp.1

@[rocq_alias big_sepM_dup]
theorem bigSepM_dup {P : PROP} [Affine P] {m : M V} :
    □ (P -∗ P ∗ P) ∗ P ⊢ bigSepM (fun (_ : K) (_ : V) => P) m :=
  bigSepL_dup

@[rocq_alias big_sepM_pure_1]
theorem bigSepM_pure_intro {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, (⌜φ k x⌝ : PROP)) ⊢ ⌜all φ m⌝ :=
  bigSepL_pure_intro.trans <| pure_mono fun h k v hget =>
    let ⟨idx, hidx⟩ := List.mem_iff_getElem.mp <| toList_get (M := M).mpr hget
    h idx ⟨k, v⟩ <| List.getElem?_eq_some_iff.mpr ⟨hidx.1, hidx.2⟩

@[rocq_alias big_sepM_affinely_pure_2]
theorem bigSepM_affinely_pure_elim {φ : K → V → Prop} {m : M V} :
    (<affine> ⌜all φ m⌝) ⊢ [∗map] k ↦ x ∈ m, (<affine> ⌜φ k x⌝ : PROP) := by
  refine bigOpM_closed (P := fun Q => (<affine> ⌜all φ m⌝) ⊢ Q)
    affinely_elim_emp (fun hx hy => ?_) (fun hget => affinely_mono <|
    pure_mono fun hall => hall _ _ hget)
  exact (affinely_mono <| pure_mono fun hall => ⟨hall, hall⟩).trans <|
    (affinely_mono pure_and.2).trans <| affinely_and.1.trans <|
    persistent_and_sep_mp.trans <| sep_mono hx hy

@[rocq_alias big_sepM_pure]
theorem bigSepM_pure [BIAffine PROP] {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, ⌜φ k x⌝ : PROP) ⊣⊢ ⌜all φ m⌝ :=
  ⟨bigSepM_pure_intro, (affine_affinely _).2.trans <|
    bigSepM_affinely_pure_elim.trans <| bigSepM_mono fun _ => affinely_elim⟩

@[rocq_alias big_sepM_map_to_list]
theorem bigSepM_toList {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗list] kv ∈ toList m, Φ kv.1 kv.2) :=
  .rfl

@[rocq_alias big_sepM_list_to_map]
theorem bigSepM_ofList [DecidableEq K] {Φ : K → V → PROP} {l : List (K × V)}
    (hd : NoDupKeys l) :
    ([∗map] k ↦ x ∈ (ofList l : M V), Φ k x) ⊣⊢
      [∗list] kv ∈ l, Φ kv.1 kv.2 :=
  BiEntails.of_eq <| bigOpM_ofList_eq Φ l hd

/-! ## Persistently and Later -/

@[rocq_alias big_sepM_persistently]
theorem bigSepM_persistently {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    (<pers> [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, <pers> Φ k x :=
  BiEntails.of_eq <| bigOpL_hom _ (toList m)

@[rocq_alias big_sepM_later]
theorem bigSepM_later {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    (▷ [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, ▷ Φ k x :=
  BiEntails.of_eq <| bigOpL_hom _ <| toList m

@[rocq_alias big_sepM_later_2]
theorem bigSepM_later_2 {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, ▷ Φ k x) ⊢ iprop(▷ [∗map] k ↦ x ∈ m, Φ k x) :=
  bigOpM_gen_proper (R := fun a b => a ⊢ later b)
    later_intro (fun h1 h2 => (sep_mono h1 h2).trans later_sep.2) (fun _ => .rfl)

@[rocq_alias big_sepM_laterN]
theorem bigSepM_laterN {Φ : K → V → PROP} {m : M V} {n : Nat} [BIAffine PROP] :
    (▷^[n] [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, ▷^[n] Φ k x :=
  match n with
  | 0 => .rfl
  | _ + 1 => (later_congr bigSepM_laterN).trans bigSepM_later

@[rocq_alias big_sepM_laterN_2]
theorem bigSepM_laterN_2 {Φ : K → V → PROP} {m : M V} {n : Nat} :
    ([∗map] k ↦ x ∈ m, ▷^[n] Φ k x) ⊢ ▷^[n] [∗map] k ↦ x ∈ m, Φ k x :=
  match n with
  | 0 => .rfl
  | _ + 1 => bigSepM_later_2.trans <| later_mono bigSepM_laterN_2

@[rocq_alias big_sepM_fmap]
theorem bigSepM_map {Φ : K → V → PROP} {m : M V} {f : V → V} :
    ([∗map] k ↦ y ∈ map f m, Φ k y) = [∗map] k ↦ y ∈ m, Φ k (f y) :=
  bigOpM_map_eq f Φ m

@[rocq_alias big_sepM_omap]
theorem bigSepM_filterMap {Φ : K → V → PROP} {m : M V} {f : V → Option V}
    (hinj : Function.Injective f) :
    ([∗map] k ↦ y ∈ filterMap f m, Φ k y) =
      [∗map] k ↦ y ∈ m, (f y).elim iprop(emp) (Φ k) :=
  bigOpM_filterMap_eq Φ m hinj

@[rocq_alias big_sepM_filter']
theorem bigSepM_filter_cond {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∗map] k ↦ x ∈ filter p m, Φ k x) =
      [∗map] k ↦ x ∈ m, if p k x then Φ k x else emp :=
  bigOpM_filter_eq p Φ m

@[rocq_alias big_sepM_filter]
theorem bigSepM_filter [BIAffine PROP] {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∗map] k ↦ x ∈ filter p m, Φ k x) =
      [∗map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) :=
  (bigSepM_filter_cond p).trans <| bigOpM_eq fun {k x} _ => by
    match hp : p k x with
    | false =>
      simpa using
        equiv_iff.mpr ⟨imp_intro_swap <| pure_elim_left False.elim, Affine.affine⟩
    | true => simpa using equiv_iff.mpr true_imp.symm

@[rocq_alias big_sepM_union]
theorem bigSepM_union [DecidableEq K] {Φ : K → V → PROP} {m₁ m₂ : M V} (hdisj : m₁ ##ₘ m₂) :
    ([∗map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢ ([∗map] k ↦ y ∈ m₁, Φ k y) ∗ [∗map] k ↦ y ∈ m₂, Φ k y :=
  BiEntails.of_eq <| bigOpM_union_eq Φ m₁ m₂ hdisj

@[rocq_alias big_sepM_subseteq]
theorem bigSepM_subseteq [DecidableEq K] {Φ : K → V → PROP} {m₁ m₂ : M V}
    [∀ k v, Affine (Φ k v)] (h : m₂ ⊆ m₁) :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢ [∗map] k ↦ x ∈ m₂, Φ k x :=
  union_difference_cancel h ▸ (bigSepM_union disjoint_difference_right).1.trans sep_elim_left

-- FIXME: Refactor for readability
@[rocq_alias big_sepM_lookup_acc_impl]
theorem bigSepM_lookup_acc_impl [DecidableEq K] {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢
      Φ i x ∗ ∀ (Ψ : K → V → PROP),
        □ (∀ k v, (⌜get? m k = some v⌝ → ⌜k ≠ i⌝ → Φ k v -∗ Ψ k v)) -∗
        Ψ i x -∗ ([∗map] k ↦ v ∈ m, Ψ k v) := by
  refine (bigSepM_delete h).1.trans <| sep_mono_right <| forall_intro fun Ψ => ?_
  refine wand_intro <| wand_intro <| sep_comm.1.trans <| ?_
  refine .trans ?_ (bigSepM_delete h).2
  have hki_of {k : K} {v : V} (hget : get? (delete m i) k = some v) : k ≠ i :=
    fun heq => absurd hget.symm <| (get?_delete_eq (M := M) heq.symm) ▸ nofun
  refine (sep_mono_right <| (sep_mono_right <|
    bigSepM_intro (m := delete m i)
      (Φ := fun k v => if k = i then emp else iprop(Φ k v -∗ Ψ k v))
      fun {k v} hget' => ?_).trans <| ?R2)
  case R2 =>
    refine (BiEntails.of_eq bigSepM_sep_eq.symm).1.trans ?_
    refine bigSepM_mono fun {k v} hget' => ?_
    simp [if_neg (hki_of hget'), wand_elim_right]
  refine intuitionistically_elim.trans <| (forall_elim k).trans <| (forall_elim v).trans <| ?_
  refine (pure_imp_elim <| (get?_delete_ne <| Ne.symm (hki_of hget')).symm.trans hget').trans <| ?_
  simpa only [if_neg (hki_of hget')] using pure_imp_elim (hki_of hget')

@[rocq_alias big_sepM_sep_zip_with]
theorem bigSepM_sep_zipWith {A B C : Type _}
    {f : A → B → C} {g₁ : C → A} {g₂ : C → B} {Φ₁ : K → A → PROP} {Φ₂ : K → B → PROP}
    {m₁ : M A} {m₂ : M B} (hg₁ : ∀ {x y}, g₁ (f x y) = x) (hg₂ : ∀ {x y}, g₂ (f x y) = y)
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome) :
    ([∗map] k ↦ xy ∈ zipWith f m₁ m₂, Φ₁ k (g₁ xy) ∗ Φ₂ k (g₂ xy)) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y :=
  BiEntails.of_eq <| by
    refine (bigOpM_op_eq (fun k xy => Φ₁ k (g₁ xy)) (fun k xy => Φ₂ k (g₂ xy)) _).trans ?_
    have hdom' : ∀ k, (get? m₁ k).isSome = (get? m₂ k).isSome := (Bool.eq_iff_iff.mpr <| hdom ·)
    refine congr (congrArg _ ?_) ?_ <;> {
      refine (bigOpM_map_eq _ _ _).symm.trans (bigOpM_eq_of_perm _ fun k => ?_)
      simp only [get?_map, get?_zipWith]
      have _ := hdom' k
      cases h1k : get? m₁ k <;> cases h2k : get? m₂ k <;> simp_all [Option.bind, Option.map] }

@[rocq_alias big_sepM_sep_zip]
theorem bigSepM_sep_zip {A B : Type _}
    {Φ₁ : K → A → PROP} {Φ₂ : K → B → PROP}
    {m₁ : M A} {m₂ : M B}
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome) :
    ([∗map] k ↦ xy ∈ zip m₁ m₂, Φ₁ k xy.1 ∗ Φ₂ k xy.2) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y :=
  bigSepM_sep_zipWith rfl rfl hdom


-- FIXME: Refactor for readability
@[rocq_alias big_sepM_impl_strong]
theorem bigSepM_impl_strong [DecidableEq K] {M₂ : Type _ → Type _} {V₂ : Type _}
    [LawfulFiniteMap M₂ K] {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M V} {m₂ : M₂ V₂} :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ∗
    □ (∀ k, ∀ y, (get? m₁ k).elim emp (Φ k) -∗ ⌜get? m₂ k = some y⌝ → Ψ k y)
    ⊢ ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
      [∗map] k ↦ x ∈ filter (fun k _ => (get? m₂ k).isNone) m₁, Φ k x := by
  let P (m₂ : M₂ V₂) : Prop := ∀ m₁ : M V,
    ([∗map] k ↦ x ∈ m₁, Φ k x) ∗
    □ (∀ k y, (get? m₁ k).elim emp (Φ k) -∗ ⌜get? m₂ k = some y⌝ → Ψ k y)
    ⊢ ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
      [∗map] k ↦ x ∈ filter (fun k _ => (get? m₂ k).isNone) m₁, Φ k x
  suffices P m₂ from this m₁
  refine LawfulFiniteMap.induction_on ?hemp ?hind m₂
  case hemp =>
    refine fun m₁ => ?_
    refine (sep_mono_right Affine.affine).trans ?_
    refine sep_emp.1.trans ?_
    refine .trans ?_ (sep_emp.2 |>.trans <| sep_comm.1.trans <| sep_mono_left bigSepM_empty.2)
    refine (BiEntails.of_eq <| bigOpM_eq_of_perm Φ fun k => ?_).2
    simp [get?_filter, get?_empty k]
  case hind =>
    refine fun i y m₂'' hi IH m₁ => ?_
    refine (sep_mono_right intuitionistically_sep_idem.2).trans ?_
    refine sep_assoc.2.trans ?_
    have hne_of_get {k v} (hget : get? m₂'' k = some v) : k ≠ i :=
      fun hki => absurd (hki ▸ hget) (hi.symm ▸ nofun)
    cases hm₁i : get? m₁ i with
    | none =>
      have H' : ((get? m₁ i).elim emp (Φ i) -∗ ⌜get? (insert m₂'' i y) i = some y⌝ → Ψ i y) ⊢ Ψ i y := by
        simp only [hm₁i, get?_insert_eq rfl]
        refine (wand_mono_right true_imp.1).trans ?_
        refine emp_sep.2.trans ?_
        refine sep_comm.1.trans ?_
        exact wand_elim_left
      refine (sep_mono_right (intuitionistically_elim.trans <| (forall_elim i).trans
        <| (forall_elim y).trans H')).trans ?_
      have H (k y') : (⌜get? (insert m₂'' i y) k = some y'⌝ → Ψ k y') ⊢ ⌜get? m₂'' k = some y'⌝ → Ψ k y' :=
        imp_intro_swap
        <| pure_elim_left fun hget => pure_imp_elim ((get?_insert_ne (hne_of_get hget).symm).trans hget)
      refine (sep_mono_left <| sep_mono_right <| intuitionistically_mono
        <| forall_mono fun k => forall_mono fun y' => wand_mono_right <| H k y').trans ?_
      -- Tail
      refine (sep_mono_left <| IH m₁).trans ?_
      refine sep_assoc.1.trans ?_
      refine (sep_mono_right sep_comm.1).trans ?_
      refine sep_assoc.2.trans ?_
      refine (sep_mono_left <| sep_comm.1.trans (bigSepM_insert hi).2).trans ?_
      refine sep_mono_right (BiEntails.of_eq <| bigOpM_eq_of_perm Φ fun k => ?_).2
      by_cases heq : i = k <;> simp_all [get?_filter, get?_insert]
    | some x =>
      refine (sep_mono_left <| sep_mono_left (bigSepM_delete hm₁i).1).trans ?_
      refine (sep_mono_left sep_assoc.1).trans ?_
      refine sep_assoc.1.trans ?_
      refine (sep_mono_right <| sep_mono_left sep_comm.1).trans ?_
      refine (sep_mono_right sep_assoc.1).trans ?_
      refine sep_assoc.2.trans ?_
      have H : Φ i x ∗ ((get? m₁ i).elim emp (Φ i) -∗ ⌜get? (insert m₂'' i y) i = some y⌝ → Ψ i y) ⊢ Ψ i y := by
        simpa [hm₁i, get?_insert_eq rfl] using (sep_mono_right <| wand_mono_right true_imp.1).trans wand_elim_right
      refine (sep_mono_left <| (sep_mono_right intuitionistically_elim).trans
        <| (sep_mono_right <| (forall_elim i).trans <| forall_elim y).trans H).trans ?_
      have hadapt (k : K) (y' : V₂) :
          ((get? m₁ k).elim emp (Φ k) -∗ ⌜get? (insert m₂'' i y) k = some y'⌝ → Ψ k y') ⊢
          (get? (delete m₁ i) k).elim emp (Φ k) -∗ ⌜get? m₂'' k = some y'⌝ → Ψ k y' :=
        wand_intro <| imp_intro_swap <| pure_elim_left fun hget => by
          let hne : i ≠ k := (hne_of_get hget).symm
          simp only [get?_delete_ne hne]
          exact (sep_mono_left <| wand_mono_right
            <| pure_imp_elim ((get?_insert_ne hne).trans hget)).trans wand_elim_left
      -- Tail
      refine (sep_mono_right <| sep_mono_right <| intuitionistically_mono
        <| forall_mono fun k => forall_mono fun y' => hadapt k y').trans
        <| (sep_mono_right <| IH (delete m₁ i)).trans ?_
      refine .trans ?_ <| sep_assoc.2.trans <| sep_mono_left (bigSepM_insert hi).2
      refine sep_mono_right <| sep_mono_right (BiEntails.of_eq <| bigOpM_eq_of_perm Φ fun k => ?_).2
      by_cases hki : i = k <;> simp_all [get?_filter, get?_insert, get?_delete]

-- TODO: `big_sepM_kmap` requires map operations which are not yet available in `PartialMap`.

theorem bigSepM_map_seq {M' : Type _ → Type _} [LawfulFiniteMap M' Nat] {V : Type _}
    {Φ : Nat → V → PROP} {start : Nat} {l : List V} :
    ([∗map] k ↦ v ∈ FiniteMap.map_seq (M := M') start l, Φ k v) ⊣⊢
    ([∗list] i ↦ v ∈ l, Φ (start + i) v) := by
  induction l generalizing start with
  | nil => simp [LawfulFiniteMap.map_seq_nil]
  | cons v l ih =>
      have Hget : get? (FiniteMap.map_seq (M := M') (start + 1) l) start = none := by
        rw [LawfulFiniteMap.get?_map_seq, if_neg (by omega)]
      rw [LawfulFiniteMap.map_seq_cons]
      refine (bigSepM_insert Hget).trans (sep_congr .rfl ?_)
      refine .trans (ih (start := start + 1)) ?_
      refine .of_eq ?_
      grind

/-! ## Map–Set Interaction -/

section MapSet
variable {S : Type _} [LawfulFiniteSet S K]

@[rocq_alias big_sepM_dom]
theorem bigSepM_dom {Φ : K → PROP} {m : M V} :
    ([∗map] k ↦ _v ∈ m, Φ k) ⊣⊢ ([∗set] k ∈ (FiniteMap.dom_set m : S), Φ k) := by
  exact BiEntails.of_eq <|
    (bigOpL_map_eq Prod.fst _ _).symm.trans
    (bigOpL_eq_of_perm _ <| LawfulFiniteMap.toList_dom_set_perm m).symm

@[rocq_alias big_sepM_impl_dom_subseteq]
theorem bigSepM_impl_dom_subseteq [DecidableEq K] {M₂ : Type _ → Type _} {V₂ : Type _}
    [LawfulFiniteMap M₂ K] {Φ : K → V → PROP} {Ψ : K → V₂ → PROP}
    {m₁ : M V} {m₂ : M₂ V₂} (hdom : FiniteMap.dom_set (S := S) m₂ ⊆ FiniteMap.dom_set m₁) :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢
    □ (∀ k, ∀ x, ∀ y, ⌜get? m₁ k = some x⌝ → ⌜get? m₂ k = some y⌝ → Φ k x -∗ Ψ k y) -∗
    ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
      [∗map] k ↦ x ∈ filter (fun k _ => (get? m₂ k).isNone) m₁, Φ k x := by
  refine wand_intro ?_
  refine .trans ?_ bigSepM_impl_strong
  refine sep_mono_right <| intuitionistically_mono <| forall_mono fun k => ?_
  refine forall_intro fun y => ?_
  refine wand_intro <| imp_intro_swap <| pure_elim_left fun hm₂ => ?_
  refine (sep_mono_left ?_).trans wand_elim_left
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp <|
    LawfulFiniteMap.mem_dom_set (S := S) |>.mp <|
    hdom k (LawfulFiniteMap.mem_dom_set.mpr (Option.isSome_iff_exists.mpr ⟨y, hm₂⟩))
  exact hx ▸ ((forall_elim x).trans <| (forall_elim y).trans <|
       (pure_imp_elim rfl).trans <| pure_imp_elim hm₂)

-- TODO: `big_sepM_gset_to_gmap` requires `gset_to_gmap`.

end MapSet

end BigSepM

end Iris.BI
