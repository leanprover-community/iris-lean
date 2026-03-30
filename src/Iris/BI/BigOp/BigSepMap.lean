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

open Iris.Algebra BigOpL BigOpM BIBase Iris.Std BigSepL LawfulPartialMap
open scoped PartialMap

/-! # Big Separating Conjunction over Maps

Rocq Iris: `iris/bi/big_op.v`, Section `big_op_map`
-/

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

namespace BigSepM

/-! ## Basic Structural Lemmas -/

@[simp, rocq_alias big_sepM_empty]
theorem bigSepM_empty {Φ : K → V → PROP} :
    ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) ⊣⊢ emp :=
  equiv_iff.mp (.of_eq (bigOpM_empty Φ))

@[rocq_alias big_sepM_empty']
theorem bigSepM_empty_intro {P : PROP} [Affine P] {Φ : K → V → PROP} :
    P ⊢ [∗map] k ↦ x ∈ (∅ : M V), Φ k x :=
  Affine.affine.trans bigSepM_empty.2

@[rocq_alias big_sepM_singleton]
theorem bigSepM_singleton {Φ : K → V → PROP} {i : K} {x : V} :
    ([∗map] k ↦ v ∈ (PartialMap.singleton i x : M V), Φ k v) ⊣⊢ Φ i x :=
  equiv_iff.mp (bigOpM_singleton_equiv Φ i x)

@[rocq_alias big_sepM_insert]
theorem bigSepM_insert {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = none) :
    ([∗map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢ Φ i x ∗ [∗map] k ↦ v ∈ m, Φ k v :=
  equiv_iff.mp (bigOpM_insert_equiv Φ x h)

@[rocq_alias big_sepM_insert_delete]
theorem bigSepM_insert_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V} :
    ([∗map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢
      Φ i x ∗ [∗map] k ↦ v ∈ delete m i, Φ k v :=
  equiv_iff.mp (bigOpM_insert_delete_equiv Φ m i x)

@[rocq_alias big_sepM_delete]
theorem bigSepM_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢ Φ i x ∗ [∗map] k ↦ v ∈ delete m i, Φ k v :=
  equiv_iff.mp (bigOpM_delete_equiv Φ h)

/-! ## Monotonicity and Congruence -/

@[rocq_alias big_sepM_mono]
theorem bigSepM_mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k v}, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_gen_proper .rfl sep_mono h

@[rocq_alias big_sepM_proper]
theorem bigSepM_equiv {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Φ k x ≡ Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_proper h

theorem bigSepM_equiv_of_forall_equiv {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∗map] k ↦ x ∈ m, Φ k x) ≡ [∗map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_proper_pointwise m h

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

@[rocq_alias big_sepM_flip_mono]
theorem bigSepM_flip_mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Ψ k x ⊢ Φ k x) :
    ([∗map] k ↦ x ∈ m, Ψ k x) ⊢ [∗map] k ↦ x ∈ m, Φ k x :=
  bigSepM_mono fun _ => h

/-! ## Typeclass Instances -/

@[rocq_alias big_sepM_empty_persistent]
instance bigSepM_nil_persistent_inst {Φ : K → V → PROP} :
    Persistent ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  persistent := by
    rw [show ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) = iprop(emp) from bigOpM_empty Φ]
    exact Persistent.persistent

@[rocq_alias big_sepM_persistent]
theorem bigSepM_persistent {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Persistent (Φ k x)) :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) where
  persistent := bigOpM_closed (P := fun Q => Q ⊢ <pers> Q) persistently_emp_2
    (fun hx hy => (sep_mono hx hy).trans persistently_sep_2) (h · |>.persistent)

@[rocq_alias big_sepM_persistent']
instance bigSepM_persistent_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_persistent fun _ => inferInstance

@[rocq_alias big_sepM_empty_affine]
instance bigSepM_nil_affine_inst {Φ : K → V → PROP} :
    Affine ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  affine := by
    rw [show ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) = iprop(emp) from bigOpM_empty Φ]
    exact Affine.affine

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
  timeless := by
    rw [show ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) = iprop(emp) from bigOpM_empty Φ]
    exact Timeless.timeless

@[rocq_alias big_sepM_timeless]
theorem bigSepM_timeless [Timeless (emp : PROP)] {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Timeless (Φ k x)) :
    Timeless ([∗map] k ↦ x ∈ m, Φ k x) where
  timeless := bigOpM_closed (P := fun Q => ▷ Q ⊢ ◇ Q) Timeless.timeless
    (fun hx hy => later_sep.1.trans ((sep_mono hx hy).trans except0_sep.2))
    (h · |>.timeless)

@[rocq_alias big_sepM_timeless']
instance bigSepM_timeless_inst [Timeless (emp : PROP)] {Φ : K → V → PROP} {m : M V}
    [∀ k x, Timeless (Φ k x)] :
    Timeless ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_timeless fun _ => inferInstance

@[rocq_alias big_sepM_empty_absorbing]
instance bigSepM_nil_absorbing_inst [BIAffine PROP] {Φ : K → V → PROP} :
    Absorbing ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) where
  absorbing := by
    rw [show ([∗map] k ↦ x ∈ (∅ : M V), Φ k x) = iprop(emp) from bigOpM_empty Φ]
    exact absorbingly_emp.1.trans true_emp.1

@[rocq_alias big_sepM_absorbing]
theorem bigSepM_absorbing [BIAffine PROP] {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Absorbing (Φ k x)) :
    Absorbing ([∗map] k ↦ x ∈ m, Φ k x) where
  absorbing := bigOpM_closed (P := fun Q => <absorb> Q ⊢ Q)
    (absorbingly_emp.1.trans true_emp.1)
    (fun hx hy => absorbingly_sep.1.trans (sep_mono hx hy)) (h · |>.absorbing)

@[rocq_alias big_sepM_absorbing']
instance bigSepM_absorbing_inst [BIAffine PROP] {Φ : K → V → PROP} {m : M V}
    [∀ k x, Absorbing (Φ k x)] :
    Absorbing ([∗map] k ↦ x ∈ m, Φ k x) :=
  bigSepM_absorbing fun _ => inferInstance

/-! ## Logical Operations -/

@[rocq_alias big_sepM_emp]
theorem bigSepM_emp [DecidableEq K] {m : M V} :
    bigSepM (fun (_ : K) (_ : V) => (emp : PROP)) m ⊣⊢ emp :=
  equiv_iff.mp (bigOpM_const_unit_equiv m)

@[rocq_alias big_sepM_sep]
theorem bigSepM_sep_equiv {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, iprop(Φ k x ∗ Ψ k x)) ≡
      iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗ [∗map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_op_equiv Φ Ψ m

@[deprecated "bigSepM_sep_equiv.symm" (since := "26/03/30"), rocq_alias big_sepM_sep_2]
theorem bigSepM_sep_equiv_symm {Φ Ψ : K → V → PROP} {m : M V} :
    iprop(([∗map] k ↦ x ∈ m, Φ k x) ∗ [∗map] k ↦ x ∈ m, Ψ k x) ≡
      [∗map] k ↦ x ∈ m, iprop(Φ k x ∗ Ψ k x) :=
  bigSepM_sep_equiv.symm

@[rocq_alias big_sepM_and]
theorem bigSepM_and {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, iprop(Φ k x ∧ Ψ k x)) ⊢
      ([∗map] k ↦ x ∈ m, Φ k x) ∧ [∗map] k ↦ x ∈ m, Ψ k x :=
  and_intro (bigSepM_mono fun _ => and_elim_l) (bigSepM_mono fun _ => and_elim_r)

@[rocq_alias big_sepM_wand]
theorem bigSepM_wand {Φ Ψ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢
      ([∗map] k ↦ x ∈ m, iprop(Φ k x -∗ Ψ k x)) -∗ [∗map] k ↦ x ∈ m, Ψ k x :=
  wand_intro <| (equiv_iff.mp bigSepM_sep_equiv.symm).1.trans <|
    bigSepM_mono fun _ => wand_elim_r

/-! ## Lookup Lemmas -/

@[rocq_alias big_sepM_lookup_acc]
theorem bigSepM_lookup_acc {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊣⊢
      Φ i x ∗ (Φ i x -∗ [∗map] k ↦ v ∈ m, Φ k v) :=
  ⟨(bigSepM_delete h).1.trans <| sep_mono_r <| wand_intro <| sep_comm.1.trans (bigSepM_delete h).2,
   wand_elim_r⟩

@[rocq_alias big_sepM_lookup]
theorem bigSepM_lookup {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    [TCOr (∀ k v, Affine (Φ k v)) (Absorbing (Φ i x))] →
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢ Φ i x
  | TCOr.l => (bigSepM_delete h).1.trans sep_elim_l
  | TCOr.r => (bigSepM_lookup_acc h).1.trans sep_elim_l

@[rocq_alias big_sepM_lookup_dom]
theorem bigSepM_lookup_dom {Φ : K → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    [TCOr (∀ k, Affine (Φ k)) (Absorbing (Φ i))] →
    ([∗map] k ↦ _v ∈ m, Φ k) ⊢ Φ i
  | TCOr.l => (bigSepM_delete (Φ := fun k _ => Φ k) h).1.trans sep_elim_l
  | TCOr.r => (bigSepM_lookup_acc (Φ := fun k _ => Φ k) h).1.trans sep_elim_l

@[rocq_alias big_sepM_insert_acc]
theorem bigSepM_insert_acc {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢
      Φ i x ∗ (∀ v', Φ i v' -∗ [∗map] k ↦ v ∈ insert m i v', Φ k v) :=
  (bigSepM_delete h).1.trans <| sep_mono_r <| forall_intro fun _ =>
    wand_intro <| sep_comm.1.trans bigSepM_insert_delete.2

-- Note: In Coq Iris, this is stated with wands: `Φ i x -∗ bigSepM m -∗ bigSepM (insert m i x)`.
-- The `∗` version requires `Affine` in the `some` case to discard the overridden value.
@[rocq_alias big_sepM_insert_2]
theorem bigSepM_insert_2 {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    [∀ k v, Affine (Φ k v)] :
    Φ i x ∗ ([∗map] k ↦ v ∈ m, Φ k v) ⊢ [∗map] k ↦ v ∈ insert m i x, Φ k v := by
  cases hm : get? m i with
  | none => exact (bigSepM_insert hm).2
  | some _ => exact (sep_mono_r ((bigSepM_delete hm).1.trans sep_elim_r)).trans
                bigSepM_insert_delete.2

/-! ## Insert Override and Function Insert -/

@[rocq_alias big_sepM_insert_override]
theorem bigSepM_insert_override {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x ≡ Φ i x') :
    ([∗map] k ↦ v ∈ insert m i x', Φ k v) ≡ ([∗map] k ↦ v ∈ m, Φ k v) :=
  bigOpM_insert_override_equiv hi hΦ

@[rocq_alias big_sepM_insert_override_1]
theorem bigSepM_insert_override_1 {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x ⊢ Φ i x') :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢ [∗map] k ↦ v ∈ insert m i x', Φ k v :=
  (bigSepM_delete hi).1.trans <| (sep_mono_l hΦ).trans bigSepM_insert_delete.2

@[rocq_alias big_sepM_insert_override_2]
theorem bigSepM_insert_override_2 {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x' ⊢ Φ i x) :
    ([∗map] k ↦ v ∈ insert m i x', Φ k v) ⊢ [∗map] k ↦ v ∈ m, Φ k v :=
  bigSepM_insert_delete.1.trans <| (sep_mono_l hΦ).trans (bigSepM_delete hi).2

@[rocq_alias big_sepM_fn_insert]
theorem bigSepM_fn_insert [DecidableEq K] {B : Type _} {g : K → V → B → PROP} {f : K → B}
    {m : M V} {i : K} {x : V} {b : B} (hi : get? m i = none) :
    ([∗map] k ↦ y ∈ insert m i x, g k y (if k = i then b else f k)) ≡
    iprop(g i x b ∗ [∗map] k ↦ y ∈ m, g k y (f k)) :=
  bigOpM_fn_insert_equiv g f x b hi

@[rocq_alias big_sepM_fn_insert']
theorem bigSepM_fn_insert' [DecidableEq K] {f : K → PROP} {m : M V} {i : K} {x : V} {P : PROP}
    (hi : get? m i = none) :
    ([∗map] k ↦ _v ∈ insert m i x, if k = i then P else f k) ≡
    iprop(P ∗ [∗map] k ↦ _v ∈ m, f k) :=
  bigOpM_fn_insert_equiv' f x P hi

/-! ## Intro, Forall, and Impl -/

@[rocq_alias big_sepM_intro]
theorem bigSepM_intro {P : PROP} [Intuitionistic P] {Φ : K → V → PROP} {m : M V}
    (h : ∀ k v, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∗map] k ↦ x ∈ m, Φ k x := by
  refine bigOpM_closed (P := fun Q => P ⊢ Q) ?_ ?_ (h _ _ ·)
  · exact Intuitionistic.intuitionistic.trans affinely_elim_emp
  · intro x y hx hy
    exact Intuitionistic.intuitionistic.trans <|
      intuitionistically_sep_idem.2.trans <|
        sep_mono (intuitionistically_elim.trans hx) (intuitionistically_elim.trans hy)

theorem bigSepM_forall_intro {Φ : K → V → PROP} {m : M V}
    [BIAffine PROP] [∀ k v, Persistent (Φ k v)] :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) :=
  forall_intro fun _ => forall_intro fun _ => imp_intro' <| pure_elim_l fun hget =>
    (bigSepM_lookup_acc hget).1.trans <| (sep_mono_l Persistent.persistent).trans <|
      sep_comm.1.trans <| persistently_absorb_r.trans persistently_elim

theorem bigSepM_forall_elim {Φ : K → V → PROP} {m : M V}
    [BIAffine PROP] [inst : ∀ k v, Persistent (Φ k v)] :
    (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗map] k ↦ x ∈ m, Φ k x :=
  have := bigOpM_closed (Φ := Φ) (m := m)
    (P := fun (Q : PROP) =>
      ((∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) : PROP) ⊢ Q) ∧ Persistent Q)
    ⟨Affine.affine, inferInstance⟩
    (fun ⟨hx, hpx⟩ ⟨hy, hpy⟩ =>
      ⟨(and_self.2.trans <| and_mono hx hy).trans
        (@persistent_and_sep_1 _ _ _ _ (TCOr.l (t := hpx))),
       @sep_persistent _ _ _ _ hpx hpy⟩)
    (fun {k x} hget => ⟨((forall_elim k).trans <| forall_elim x).trans <|
      (imp_congr_l (pure_true hget)).1.trans true_imp.1, inst k x⟩)
  this.1

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
  refine wand_intro <| (sep_mono_r ?_).trans <| (equiv_iff.mp bigSepM_sep_equiv.symm).1.trans <|
    bigSepM_mono fun _ => wand_elim_r
  exact bigSepM_intro (m := m) fun k x hget => intuitionistically_elim.trans <|
    ((forall_elim k).trans <| forall_elim x).trans <|
    (imp_mono_l <| pure_mono fun _ => hget).trans true_imp.1

@[rocq_alias big_sepM_dup]
theorem bigSepM_dup {P : PROP} [Affine P] {m : M V} :
    □ (P -∗ P ∗ P) ∗ P ⊢ bigSepM (fun (_ : K) (_ : V) => P) m :=
  bigSepL_dup

/-! ## Pure Lemmas -/

@[rocq_alias big_sepM_pure_1]
theorem bigSepM_pure_intro {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, (⌜φ k x⌝ : PROP)) ⊢ ⌜PartialMap.all φ m⌝ := by
  show bigOpL sep (fun _ (kv : K × V) => (pure (PROP := PROP) (φ kv.1 kv.2))) (toList m) ⊢ _
  exact (bigSepL_pure_intro (l := toList (K := K) m)).trans <| pure_mono fun h k v hget =>
    let ⟨idx, hidx⟩ := List.mem_iff_getElem.mp (toList_get (M := M).mpr hget)
    h idx ⟨k, v⟩ (List.getElem?_eq_some_iff.mpr ⟨hidx.1, hidx.2⟩)

@[rocq_alias big_sepM_affinely_pure_2]
theorem bigSepM_affinely_pure_elim {φ : K → V → Prop} {m : M V} :
    (<affine> ⌜PartialMap.all φ m⌝) ⊢ ([∗map] k ↦ x ∈ m, (<affine> ⌜φ k x⌝ : PROP)) := by
  refine bigOpM_closed (P := fun Q => (<affine> ⌜PartialMap.all φ m⌝) ⊢ Q) ?_ ?_ ?_
  · exact affinely_elim_emp
  · intro x y hx hy
    exact (affinely_mono <| pure_mono fun hall =>
      ⟨hall, hall⟩).trans <| (affinely_mono pure_and.2).trans <|
      affinely_and.1.trans <| persistent_and_sep_1.trans (sep_mono hx hy)
  · intro k x hget
    exact affinely_mono <| pure_mono fun hall => hall k x hget

@[rocq_alias big_sepM_pure]
theorem bigSepM_pure [BIAffine PROP] {φ : K → V → Prop} {m : M V} :
    ([∗map] k ↦ x ∈ m, (⌜φ k x⌝ : PROP)) ⊣⊢ ⌜PartialMap.all φ m⌝ :=
  ⟨bigSepM_pure_intro,
   (affine_affinely _).2.trans <|
    bigSepM_affinely_pure_elim.trans (bigSepM_mono fun _ => affinely_elim)⟩

/-! ## Map Conversion -/

@[rocq_alias big_sepM_map_to_list]
theorem bigSepM_toList {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗list] kv ∈ toList (K := K) m, Φ kv.1 kv.2) :=
  .rfl

@[rocq_alias big_sepM_list_to_map]
theorem bigSepM_ofList [DecidableEq K] {Φ : K → V → PROP} {l : List (K × V)}
    (hd : NoDupKeys l) :
    ([∗map] k ↦ x ∈ (PartialMap.ofList l : M V), Φ k x) ⊣⊢
      ([∗list] kv ∈ l, Φ kv.1 kv.2) :=
  equiv_iff.mp (bigOpM_ofList_equiv Φ l hd)

/-! ## Persistently and Later -/

@[rocq_alias big_sepM_persistently]
theorem bigSepM_persistently {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    (<pers> [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, <pers> Φ k x :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) persistently_ne
       (equiv_iff.mpr persistently_sep) (equiv_iff.mpr persistently_emp')
  equiv_iff.mp <| bigOpL_hom _ (toList m)

@[rocq_alias big_sepM_later]
theorem bigSepM_later {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    (▷ [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, (▷ Φ k x) :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) later_ne
    (equiv_iff.mpr later_sep) (equiv_iff.mpr later_emp)
  equiv_iff.mp <| bigOpL_hom _ (toList m)

@[rocq_alias big_sepM_later_2]
theorem bigSepM_later_2 {Φ : K → V → PROP} {m : M V} :
    ([∗map] k ↦ x ∈ m, ▷ Φ k x) ⊢ iprop(▷ [∗map] k ↦ x ∈ m, Φ k x) :=
  bigOpM_gen_proper (R := fun a b => a ⊢ later b) (Φ := fun k x => later (Φ k x)) (Ψ := Φ)
    later_intro (fun h1 h2 => (sep_mono h1 h2).trans later_sep.2) (fun _ => .rfl)

@[rocq_alias big_sepM_laterN]
theorem bigSepM_laterN {Φ : K → V → PROP} {m : M V} {n : Nat} [BIAffine PROP] :
    (▷^[n] [∗map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗map] k ↦ x ∈ m, ▷^[n] Φ k x :=
  match n with | 0 => .rfl | _ + 1 => (later_congr bigSepM_laterN).trans bigSepM_later

@[rocq_alias big_sepM_laterN_2]
theorem bigSepM_laterN_2 {Φ : K → V → PROP} {m : M V} {n : Nat} :
    ([∗map] k ↦ x ∈ m, ▷^[n] Φ k x) ⊢ (▷^[n] [∗map] k ↦ x ∈ m, Φ k x) :=
  match n with | 0 => .rfl | _ + 1 => bigSepM_later_2.trans <| later_mono bigSepM_laterN_2

@[rocq_alias big_sepM_fmap]
theorem bigSepM_map {Φ : K → V → PROP} {m : M V} {f : V → V} :
    ([∗map] k ↦ y ∈ PartialMap.map f m, Φ k y) ≡
      [∗map] k ↦ y ∈ m, Φ k (f y) :=
  bigOpM_map_equiv f Φ m

@[rocq_alias big_sepM_omap]
theorem bigSepM_filterMap {Φ : K → V → PROP} {m : M V} {f : V → Option V}
    (hinj : Function.Injective f) :
    ([∗map] k ↦ y ∈ PartialMap.filterMap f m, Φ k y) ≡
      [∗map] k ↦ y ∈ m, (f y).elim iprop(emp) (Φ k) :=
  bigOpM_filterMap_equiv Φ m hinj

@[rocq_alias big_sepM_filter']
theorem bigSepM_filter {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∗map] k ↦ x ∈ PartialMap.filter p m, Φ k x) ≡
      [∗map] k ↦ x ∈ m, if p k x then Φ k x else iprop(emp) :=
  bigOpM_filter_equiv p Φ m

@[rocq_alias big_sepM_filter]
theorem bigSepM_filter' [BIAffine PROP] {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∗map] k ↦ x ∈ PartialMap.filter p m, Φ k x) ≡
      [∗map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) :=
  (bigSepM_filter p).trans <| bigOpM_proper fun {k x} _ => by
    cases hp : p k x with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact equiv_iff.mpr ⟨imp_intro' <| pure_elim_l (by simp), Affine.affine⟩
    | true =>
      simp only [↓reduceIte]
      exact equiv_iff.mpr true_imp.symm

@[rocq_alias big_sepM_union]
theorem bigSepM_union [DecidableEq K] {Φ : K → V → PROP} {m₁ m₂ : M V}
    (hdisj : m₁ ##ₘ m₂) :
    ([∗map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∗map] k ↦ y ∈ m₁, Φ k y) ∗ [∗map] k ↦ y ∈ m₂, Φ k y :=
  equiv_iff.mp (bigOpM_union_equiv Φ m₁ m₂ hdisj)

@[rocq_alias big_sepM_lookup_acc_impl]
theorem bigSepM_lookup_acc_impl [DecidableEq K] {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∗map] k ↦ v ∈ m, Φ k v) ⊢
      Φ i x ∗ ∀ (Ψ : K → V → PROP),
        □ (∀ k v, iprop(⌜get? m k = some v⌝ → ⌜k ≠ i⌝ → Φ k v -∗ Ψ k v)) -∗
        Ψ i x -∗ ([∗map] k ↦ v ∈ m, Ψ k v) := by
  refine (bigSepM_delete h).1.trans <| sep_mono_r <| forall_intro fun Ψ => wand_intro <|
    wand_intro <| sep_comm.1.trans <| (sep_mono_r <| (sep_mono_r <|
      bigSepM_intro (Φ := fun k v => if k = i then emp else iprop(Φ k v -∗ Ψ k v))
        (m := delete m i) fun k v hget' => ?_
      ).trans <| (equiv_iff.mp bigSepM_sep_equiv.symm).1.trans <|
      bigSepM_mono fun {k v} hdel => ?_).trans (bigSepM_delete h).2
  · have hki : k ≠ i := fun heq => by subst heq; simp [get?_delete_eq] at hget'
    simp only [show (k = i) = False from eq_false hki, ite_false]
    exact intuitionistically_elim.trans <| ((forall_elim k).trans <| forall_elim v).trans <|
      ((and_intro (pure_intro (show get? (m : M V) k = some v from
        (get?_delete_ne (Ne.symm hki)).symm.trans hget')) .rfl).trans
        imp_elim_r).trans <|
      ((and_intro (pure_intro hki) .rfl).trans imp_elim_r)
  · have hki : k ≠ i := fun heq => by subst heq; simp [get?_delete_eq] at hdel
    simp only [show (k = i) = False from eq_false hki, ite_false]
    exact wand_elim_r

@[rocq_alias big_sepM_sep_zip_with]
theorem bigSepM_sep_zipWith {A B C : Type _}
    {f : A → B → C} {g₁ : C → A} {g₂ : C → B}
    {Φ₁ : K → A → PROP} {Φ₂ : K → B → PROP}
    {m₁ : M A} {m₂ : M B}
    (hg₁ : ∀ {x y}, g₁ (f x y) = x) (hg₂ : ∀ {x y}, g₂ (f x y) = y)
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome) :
    ([∗map] k ↦ xy ∈ PartialMap.zipWith f m₁ m₂, Φ₁ k (g₁ xy) ∗ Φ₂ k (g₂ xy)) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y :=
  equiv_iff.mp (bigOpM_sep_zipWith_equiv Φ₁ Φ₂ hg₁ hg₂ hdom)

@[rocq_alias big_sepM_sep_zip]
theorem bigSepM_sep_zip {A B : Type _}
    {Φ₁ : K → A → PROP} {Φ₂ : K → B → PROP}
    {m₁ : M A} {m₂ : M B}
    (hdom : ∀ k, (get? m₁ k).isSome ↔ (get? m₂ k).isSome) :
    ([∗map] k ↦ xy ∈ PartialMap.zip m₁ m₂, Φ₁ k xy.1 ∗ Φ₂ k xy.2) ⊣⊢
      ([∗map] k ↦ x ∈ m₁, Φ₁ k x) ∗ [∗map] k ↦ y ∈ m₂, Φ₂ k y :=
  equiv_iff.mp (bigOpM_sep_zip_equiv Φ₁ Φ₂ hdom)

@[rocq_alias big_sepM_impl_strong]
theorem bigSepM_impl_strong [DecidableEq K]
    {M₂ : Type _ → Type _} {V₂ : Type _} [LawfulFiniteMap M₂ K]
    {Φ : K → V → PROP} {Ψ : K → V₂ → PROP} {m₁ : M V} {m₂ : M₂ V₂} :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢
      □ (∀ k, ∀ y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗
         iprop(⌜get? m₂ k = some y⌝ → Ψ k y)) -∗
      ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
        [∗map] k ↦ x ∈ PartialMap.filter (fun k _ => (get? m₂ k).isNone) m₁, Φ k x := by
  refine wand_intro ?_
  let P : M₂ V₂ → Prop := fun m₂ => ∀ (m₁ : M V),
      ([∗map] k ↦ x ∈ m₁, Φ k x) ∗
      □ (∀ k y, (match get? m₁ k with | some x => Φ k x | none => emp) -∗
         iprop(⌜get? m₂ k = some y⌝ → Ψ k y))
      ⊢ ([∗map] k ↦ y ∈ m₂, Ψ k y) ∗
          [∗map] k ↦ x ∈ PartialMap.filter (fun k _ => (get? m₂ k).isNone) m₁, Φ k x
  suffices h : P m₂ from h m₁
  refine LawfulFiniteMap.induction_on (K := K) ?_ ?_ ?_ m₂
  · refine fun _ _ heq IH m₁ => (sep_mono_r ?_).trans (IH m₁) |>.trans
        (sep_mono (equiv_iff.mp (bigOpM_equiv_of_perm Ψ heq)).1
          (equiv_iff.mp (bigOpM_equiv_of_perm Φ ?_)).1)
    exact intuitionistically_mono <| forall_mono fun k => forall_mono fun y =>
      wand_mono_r <| imp_intro' <| pure_elim_l fun hget =>
        (and_intro (pure_intro (heq k ▸ hget)) .rfl).trans imp_elim_r
    exact fun k => by simp only [get?_filter]; congr 1; cases get? m₁ k <;> simp [heq k]
  · exact fun m₁ => (sep_mono_r Affine.affine).trans sep_emp.1 |>.trans
      (equiv_iff.mp (bigOpM_equiv_of_perm Φ (fun k => by
        rw [get?_filter]; cases get? m₁ k with | none => rfl | some v => simp [get?_empty k]))).2
      |>.trans sep_emp.2 |>.trans (sep_comm.1.trans (sep_mono_l bigSepM_empty.2))
  · refine fun i y m₂'' hi IH m₁ => ((sep_mono_r intuitionistically_sep_idem.2).trans sep_assoc.2).trans ?_
    cases hm₁i : get? m₁ i with
    | none =>
      refine (sep_mono_r (intuitionistically_elim.trans <| (forall_elim i).trans <|
          (forall_elim y).trans <| by simp only [hm₁i, get?_insert_eq rfl]; exact
          (wand_mono_r true_imp.1).trans (emp_sep.2.trans (sep_comm.1.trans wand_elim_l)))).trans ?_
      refine (sep_mono_l (sep_mono_r (intuitionistically_mono <| forall_mono fun k =>
          forall_mono fun y' => wand_mono_r <| imp_intro' <| pure_elim_l fun hget =>
            let hne : k ≠ i := fun h => absurd (h ▸ hget) (by simp [hi])
            (and_intro (pure_intro ((get?_insert_ne hne.symm).trans hget)) .rfl).trans
              imp_elim_r))).trans ?_
      refine (sep_mono_l (IH m₁)).trans <| sep_assoc.1.trans <|
        (sep_mono_r sep_comm.1).trans <| sep_assoc.2.trans <|
        (sep_mono_l (sep_comm.1.trans (bigSepM_insert hi).2)).trans ?_
      refine sep_mono_r (equiv_iff.mp (bigOpM_equiv_of_perm Φ (fun k => ?_))).2
      simp only [get?_filter]; cases hk : get? m₁ k with
      | none => simp
      | some v =>
        have hne : i ≠ k := fun h => by subst h; exact absurd hk (by simp [hm₁i])
        simp [Option.bind_some, get?_insert_ne hne]
    | some x =>
      refine (sep_mono_l (sep_mono_l (bigSepM_delete hm₁i).1)).trans <|
        (sep_mono_l sep_assoc.1).trans <| sep_assoc.1.trans <|
        (sep_mono_r (sep_mono_l sep_comm.1)).trans <| (sep_mono_r sep_assoc.1).trans <|
        sep_assoc.2.trans ?_
      refine (sep_mono_l ((sep_mono_r intuitionistically_elim).trans <|
          (sep_mono_r <| (forall_elim i).trans (forall_elim y)).trans <| by
            simp only [hm₁i, get?_insert_eq rfl]
            exact (sep_mono_r (wand_mono_r true_imp.1)).trans wand_elim_r)).trans ?_
      refine (sep_mono_r (sep_mono_r ?hweaken)).trans <|
        (sep_mono_r (IH (delete m₁ i))).trans ?_
      case hweaken =>
        exact intuitionistically_mono <| forall_mono fun k => forall_mono fun y' =>
          wand_intro <| imp_intro' <| pure_elim_l fun hget => by
            have hne : i ≠ k := fun h => by subst h; exact absurd hget (by simp [hi])
            rw [get?_delete_ne hne]
            exact (sep_mono_l (wand_mono_r <|
              (and_intro (pure_intro ((get?_insert_ne hne).trans hget)) .rfl).trans
                imp_elim_r)).trans wand_elim_l
      refine (sep_mono_r (sep_mono_r (equiv_iff.mp (bigOpM_equiv_of_perm Φ (fun k => ?_))).2)).trans <|
        sep_assoc.2.trans (sep_mono_l (bigSepM_insert hi).2)
      simp only [get?_filter]; by_cases hki : k = i
      · subst hki; simp [get?_insert_eq rfl, get?_delete_eq rfl]
      · simp only [get?_insert_ne (Ne.symm hki), get?_delete_ne (Ne.symm hki)]

-- TODO: `big_sepM_subseteq` requires set difference infrastructure which is not
-- yet available.

-- TODO: `big_sepM_kmap` and `big_sepM_map_seq` require `FiniteMapKmapLaws` and
-- `FiniteMapSeqLaws` which are not yet available in the current `PartialMap` interface.

-- TODO: `big_sepM_dom`, `big_sepM_ofSet`, and set-related lemmas require `FiniteMapDom`
-- infrastructure which is not yet available.

end BigSepM

end Iris.BI
