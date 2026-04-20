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

open Iris.Algebra BigOpL BigOpM BIBase Iris.Std
open scoped PartialMap

/-! # Big Conjunction over Maps -/

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

namespace BigAndM

@[simp, rocq_alias big_andM_empty]
theorem bigAndM_empty {Φ : K → V → PROP} :
    ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) ⊣⊢ True :=
  equiv_iff.mp <| .of_eq <| bigOpM_empty Φ

@[rocq_alias big_andM_empty']
theorem bigAndM_empty_intro {P : PROP} {Φ : K → V → PROP} :
    P ⊢ [∧map] k ↦ x ∈ (∅ : M V), Φ k x :=
  true_intro.trans bigAndM_empty.2

@[rocq_alias big_andM_singleton]
theorem bigAndM_singleton {Φ : K → V → PROP} {i : K} {x : V} :
    ([∧map] k ↦ v ∈ (PartialMap.singleton i x : M V), Φ k v) ⊣⊢ Φ i x :=
  equiv_iff.mp <| bigOpM_singleton_equiv Φ i x

@[rocq_alias big_andM_insert]
theorem bigAndM_insert {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = none) :
    ([∧map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢ Φ i x ∧ [∧map] k ↦ v ∈ m, Φ k v :=
  equiv_iff.mp <| bigOpM_insert_equiv Φ x h

@[rocq_alias big_andM_insert_delete]
theorem bigAndM_insert_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V} :
    ([∧map] k ↦ v ∈ insert m i x, Φ k v) ⊣⊢
      Φ i x ∧ [∧map] k ↦ v ∈ delete m i, Φ k v :=
  equiv_iff.mp <| bigOpM_insert_delete_equiv Φ m i x

@[rocq_alias big_andM_delete]
theorem bigAndM_delete {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∧map] k ↦ v ∈ m, Φ k v) ⊣⊢ Φ i x ∧ [∧map] k ↦ v ∈ delete m i, Φ k v :=
  equiv_iff.mp <| bigOpM_delete_equiv Φ h

@[rocq_alias big_andM_mono]
theorem bigAndM_mono {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k v}, get? m k = some v → Φ k v ⊢ Ψ k v) :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊢ [∧map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_gen_proper .rfl and_mono (h ·)

@[rocq_alias big_andM_proper]
theorem bigAndM_equiv {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Φ k x ≡ Ψ k x) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡ [∧map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_proper h

theorem bigAndM_equiv_of_forall_equiv {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡ [∧map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_proper_pointwise m h

@[rocq_alias big_andM_ne]
theorem bigAndM_dist {Φ Ψ : K → V → PROP} {m : M V} {n : Nat}
    (h : ∀ {k x}, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([∧map] k ↦ x ∈ m, Φ k x) ≡{n}≡ [∧map] k ↦ x ∈ m, Ψ k x :=
  bigOpM_dist h

@[rocq_alias big_andM_mono']
theorem bigAndM_mono_of_forall {Φ Ψ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, Φ k x ⊢ Ψ k x) :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊢ [∧map] k ↦ x ∈ m, Ψ k x :=
  bigAndM_mono fun _ => h

instance bigAndM_affine_inst {Φ : K → V → PROP} {m : M V} [BIAffine PROP] :
    Affine ([∧map] k ↦ x ∈ m, Φ k x) where
  affine := bigOpM_closed (P := fun Q => Q ⊢ emp) true_emp.1
    (fun hx _ => and_elim_l.trans hx) (fun _ => Affine.affine)

@[rocq_alias big_andM_empty_persistent]
instance bigAndM_nil_persistent_inst {Φ : K → V → PROP} :
    Persistent ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) where
  persistent := bigAndM_empty.1.trans <| Persistent.persistent.trans <|
    persistently_mono bigAndM_empty.2

@[rocq_alias big_andM_persistent]
theorem bigAndM_persistent {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Persistent (Φ k x)) :
    Persistent ([∧map] k ↦ x ∈ m, Φ k x) where
  persistent := bigOpM_closed (P := fun Q => Q ⊢ <pers> Q) persistently_true.2
    (and_mono · · |>.trans persistently_and.2) (h · |>.persistent)

@[rocq_alias big_andM_persistent']
instance bigAndM_persistent_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Persistent (Φ k x)] :
    Persistent ([∧map] k ↦ x ∈ m, Φ k x) :=
  bigAndM_persistent fun _ => inferInstance

@[rocq_alias big_andM_empty_absorbing]
instance bigAndM_nil_absorbing_inst {Φ : K → V → PROP} :
    Absorbing ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) where
  absorbing := (absorbingly_mono bigAndM_empty.1).trans <| Absorbing.absorbing.trans bigAndM_empty.2

@[rocq_alias big_andM_absorbing]
theorem bigAndM_absorbing {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Absorbing (Φ k x)) :
    Absorbing ([∧map] k ↦ x ∈ m, Φ k x) where
  absorbing := bigOpM_closed (P := fun Q => <absorb> Q ⊢ Q) true_intro
    (absorbingly_and_1.trans <| and_mono · ·) (h · |>.absorbing)

@[rocq_alias big_andM_absorbing']
instance bigAndM_absorbing_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Absorbing (Φ k x)] :
    Absorbing ([∧map] k ↦ x ∈ m, Φ k x) :=
  bigAndM_absorbing fun _ => inferInstance

@[rocq_alias big_andM_empty_timeless]
instance bigAndM_nil_timeless_inst {Φ : K → V → PROP} :
    Timeless ([∧map] k ↦ x ∈ (∅ : M V), Φ k x) where
  timeless := (later_congr bigAndM_empty).1.trans <| (later_true.1.trans except0_true.2).trans <|
    except0_mono bigAndM_empty.2

@[rocq_alias big_andM_timeless]
theorem bigAndM_timeless {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k x}, get? m k = some x → Timeless (Φ k x)) :
    Timeless ([∧map] k ↦ x ∈ m, Φ k x) where
  timeless := bigOpM_closed (P := fun Q => ▷ Q ⊢ ◇ Q)
    (later_true.1.trans except0_true.2)
    (later_and.1.trans <| and_mono · · |>.trans except0_and.2)
    (h · |>.timeless)

@[rocq_alias big_andM_timeless']
instance bigAndM_timeless_inst {Φ : K → V → PROP} {m : M V} [∀ k x, Timeless (Φ k x)] :
    Timeless ([∧map] k ↦ x ∈ m, Φ k x) :=
  bigAndM_timeless fun _ => inferInstance

@[rocq_alias big_andM_lookup]
theorem bigAndM_lookup {Φ : K → V → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∧map] k ↦ v ∈ m, Φ k v) ⊢ Φ i x :=
  (bigAndM_delete h).1.trans and_elim_l

@[rocq_alias big_andM_lookup_dom]
theorem bigAndM_lookup_dom {Φ : K → PROP} {m : M V} {i : K} {x : V}
    (h : get? m i = some x) :
    ([∧map] k ↦ _v ∈ m, Φ k) ⊢ Φ i :=
  bigAndM_lookup h

@[rocq_alias big_andM_insert_2]
theorem bigAndM_insert_elim {Φ : K → V → PROP} {m : M V} {i : K} {x : V} :
    Φ i x ∧ ([∧map] k ↦ v ∈ m, Φ k v) ⊢ [∧map] k ↦ v ∈ insert m i x, Φ k v :=
  match hm : get? m i with
  | none => (bigAndM_insert hm).2
  | some _ => (and_mono_r ((bigAndM_delete hm).1.trans and_elim_r)).trans bigAndM_insert_delete.2

@[rocq_alias big_andM_intro]
theorem bigAndM_intro {P : PROP} {Φ : K → V → PROP} {m : M V}
    (h : ∀ {k v}, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∧map] k ↦ x ∈ m, Φ k x :=
  bigOpM_closed true_intro and_intro (h ·)

@[rocq_alias big_andM_forall]
theorem bigAndM_forall {Φ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v) := by
  refine ⟨forall_intro fun _ => forall_intro fun _ => ?_, bigAndM_intro fun {k x} hget => ?_⟩
  · exact imp_intro <| and_comm.1.trans <| pure_elim_l (bigAndM_lookup ·)
  · exact (forall_elim k).trans <| (forall_elim x).trans <|
    (imp_congr_l <| pure_true hget).1.trans true_imp.1

@[rocq_alias big_andM_impl]
theorem bigAndM_impl {Φ Ψ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ∧ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v → Ψ k v)) ⊢
      [∧map] k ↦ x ∈ m, Ψ k x := by
  refine bigAndM_intro fun {k v} hget => (and_mono (bigAndM_lookup hget) <|
  (forall_elim k).trans (forall_elim v)).trans ?_
  exact (and_mono .rfl <| (and_intro (pure_intro hget) .rfl).trans imp_elim_r).trans imp_elim_r

@[rocq_alias big_andM_subseteq]
theorem bigAndM_subseteq {Φ : K → V → PROP} {m₁ m₂ : M V}
    (hsub : m₂ ⊆ m₁) :
    ([∧map] k ↦ x ∈ m₁, Φ k x) ⊢ [∧map] k ↦ x ∈ m₂, Φ k x :=
  bigAndM_intro fun hget₂ => bigAndM_lookup <| hsub _ _ hget₂

@[rocq_alias big_andM_and]
theorem bigAndM_and_equiv {Φ Ψ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, iprop(Φ k x ∧ Ψ k x)) ≡
      iprop(([∧map] k ↦ x ∈ m, Φ k x) ∧ [∧map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_op_equiv Φ Ψ m

@[rocq_alias big_andM_persistently]
theorem bigAndM_persistently {Φ : K → V → PROP} {m : M V} :
    (<pers> [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, <pers> Φ k x :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) persistently_ne
       (equiv_iff.mpr persistently_and) (equiv_iff.mpr persistently_true)
  equiv_iff.mp <| bigOpL_hom _ <| toList m

@[rocq_alias big_andM_pure_1]
theorem bigAndM_pure_intro {φ : K → V → Prop} {m : M V} :
    ([∧map] k ↦ x ∈ m, ⌜φ k x⌝ : PROP) ⊢ ⌜PartialMap.all φ m⌝ :=
  bigAndM_forall.1.trans <|
  (forall_mono fun _ => (forall_mono fun _ => pure_imp.2).trans pure_forall.2).trans pure_forall.2

@[rocq_alias big_andM_pure_2]
theorem bigAndM_pure_elim {φ : K → V → Prop} {m : M V} :
    (⌜PartialMap.all φ m⌝ : PROP) ⊢ [∧map] k ↦ x ∈ m, ⌜φ k x⌝ :=
  pure_forall.1.trans <|
  (forall_mono fun _ => pure_forall.1.trans <| forall_mono fun _ => pure_imp.1).trans bigAndM_forall.2

@[rocq_alias big_andM_pure]
theorem bigAndM_pure {φ : K → V → Prop} {m : M V} :
    ([∧map] k ↦ x ∈ m, ⌜φ k x⌝ : PROP) ⊣⊢ ⌜PartialMap.all φ m⌝ :=
  ⟨bigAndM_pure_intro, bigAndM_pure_elim⟩

@[rocq_alias big_andM_later]
theorem bigAndM_later {Φ : K → V → PROP} {m : M V} :
    (▷ [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, (▷ Φ k x) :=
  letI := MonoidHomomorphism.ofEquiv (PROP := PROP) later_ne
    (equiv_iff.mpr later_and) (equiv_iff.mpr later_true)
  equiv_iff.mp <| bigOpL_hom _ <| toList m

@[rocq_alias big_andM_laterN]
theorem bigAndM_laterN {Φ : K → V → PROP} {m : M V} {n : Nat} :
    (▷^[n] [∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧map] k ↦ x ∈ m, ▷^[n] Φ k x :=
  match n with
  | 0 => .rfl
  | _ + 1 => (later_congr bigAndM_laterN).trans bigAndM_later

@[rocq_alias big_andM_map_to_list]
theorem bigAndM_toList {Φ : K → V → PROP} {m : M V} :
    ([∧map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∧list] kv ∈ toList m, Φ kv.1 kv.2) :=
  .rfl

@[rocq_alias big_andM_fmap]
theorem bigAndM_map {Φ : K → V → PROP} {m : M V} {f : V → V} :
    ([∧map] k ↦ y ∈ PartialMap.map f m, Φ k y) ≡ [∧map] k ↦ y ∈ m, Φ k (f y) :=
  bigOpM_map_equiv f Φ m

@[rocq_alias big_andM_omap]
theorem bigAndM_filterMap {Φ : K → V → PROP} {m : M V} {f : V → Option V}
    (hinj : Function.Injective f) :
    ([∧map] k ↦ y ∈ PartialMap.filterMap f m, Φ k y) ≡
      [∧map] k ↦ y ∈ m, (f y).elim iprop(True) (Φ k) :=
  bigOpM_filterMap_equiv Φ m hinj

@[rocq_alias big_andM_filter']
theorem bigAndM_filter_cond {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∧map] k ↦ x ∈ PartialMap.filter p m, Φ k x) ≡
      [∧map] k ↦ x ∈ m, if p k x then Φ k x else iprop(True) :=
  bigOpM_filter_equiv p Φ m

@[rocq_alias big_andM_filter]
theorem bigAndM_filter {Φ : K → V → PROP} {m : M V} (p : K → V → Bool) :
    ([∧map] k ↦ x ∈ PartialMap.filter p m, Φ k x) ≡
      [∧map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x) :=
  (bigAndM_filter_cond p).trans <| bigOpM_proper fun {k x} _ => by
    match hp : p k x with
    | false => simpa using equiv_iff.mpr ⟨imp_intro' <| pure_elim_l False.elim, true_intro⟩
    | true => simpa using equiv_iff.mpr true_imp.symm

@[rocq_alias big_andM_union]
theorem bigAndM_union [DecidableEq K] {Φ : K → V → PROP} {m₁ m₂ : M V} (hdisj : m₁ ##ₘ m₂) :
    ([∧map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∧map] k ↦ y ∈ m₁, Φ k y) ∧ [∧map] k ↦ y ∈ m₂, Φ k y :=
  equiv_iff.mp <| bigOpM_union_equiv Φ m₁ m₂ hdisj

@[rocq_alias big_andM_insert_override]
theorem bigAndM_insert_override {Φ : K → V → PROP} {m : M V} {i : K} {x x' : V}
    (hi : get? m i = some x) (hΦ : Φ i x ≡ Φ i x') :
    ([∧map] k ↦ v ∈ insert m i x', Φ k v) ≡ ([∧map] k ↦ v ∈ m, Φ k v) :=
  bigOpM_insert_override_equiv hi hΦ

@[rocq_alias big_andM_fn_insert]
theorem bigAndM_fn_insert [DecidableEq K] {B : Type _} {g : K → V → B → PROP} {f : K → B}
    {m : M V} {i : K} {x : V} {b : B} (hi : get? m i = none) :
    ([∧map] k ↦ y ∈ insert m i x, g k y (if k = i then b else f k)) ≡
    iprop(g i x b ∧ [∧map] k ↦ y ∈ m, g k y (f k)) :=
  bigOpM_fn_insert_equiv g f x b hi

@[rocq_alias big_andM_fn_insert']
theorem bigAndM_fn_insert_cond [DecidableEq K] {f : K → PROP} {m : M V} {i : K} {x : V} {P : PROP}
    (hi : get? m i = none) :
    ([∧map] k ↦ _v ∈ insert m i x, if k = i then P else f k) ≡
    iprop(P ∧ [∧map] k ↦ _v ∈ m, f k) :=
  bigOpM_fn_insert_equiv' f x P hi

-- TODO: `big_andM_kmap` and `big_andM_map_seq` require `FiniteMapKmapLaws` and
-- `FiniteMapSeqLaws` which are not yet available in the current `PartialMap` interface.

end BigAndM

end Iris.BI
