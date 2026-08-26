/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.BI.BigOp.BigSepMap
import Iris.BI.DerivedLawsLater
import Iris.BI.Instances
import Iris.Std.TC
meta import Iris.Std.RocqPorting

public section

namespace Iris.BI

open Iris.Algebra BigOpM BIBase Iris.Std BigSepM LawfulPartialMap PartialMap
open scoped PartialMap

/-! # Big Separating Conjunction over Two Maps -/

namespace BigSepM2

variable {PROP : Type _} [BI PROP]
variable {K : Type _} {A B : Type u} {M : Type _ → Type _} [LawfulFiniteMap M K]

attribute [local grind =]
  LawfulPartialMap.get?_zipWith LawfulPartialMap.get?_map LawfulPartialMap.get?_empty
  LawfulPartialMap.get?_delete_isSome Option.isSome_iff_exists
  Option.not_isSome_iff_eq_none

attribute [local grind cases eager] Option.Rel

#rocq_ignore big_sepM2_aux "Not needed"
#rocq_ignore big_sepM2_unseal "Not needed"

@[rocq_alias big_sepM2_alt]
theorem bigSepM2_alt {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢
      ⌜dom m1 = dom m2⌝ ∧
        [∗map] k ↦ xy ∈ zipWith (fun (x : A) (y : B) => (x, y)) m1 m2, Φ k xy.1 xy.2 := .rfl

@[rocq_alias big_sepM2_alt_lookup]
theorem bigSepM2_alt_lookup {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢
      ⌜∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome⌝ ∧
        [∗map] k ↦ xy ∈ zipWith (fun (x : A) (y : B) => (x, y)) m1 m2, Φ k xy.1 xy.2 := by
  refine bigSepM2_alt.trans (and_congr (pure_congr ?_) .rfl)
  exact ⟨fun h k => iff_of_eq (congrArg (fun d => d k) h), fun h => funext fun k => propext (h k)⟩

@[rocq_alias big_sepM2_lookup_iff]
theorem bigSepM2_lookup_iff {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢ ⌜∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome⌝ :=
  bigSepM2_alt_lookup.mp.trans and_elim_l

@[rocq_alias big_sepM2_dom]
theorem bigSepM2_dom (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢ ⌜PartialMap.dom m1 = PartialMap.dom m2⌝ :=
  bigSepM2_alt.mp.trans and_elim_l

@[rocq_alias big_sepM2_flip]
theorem bigSepM2_flip {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x2;x1 ∈ m2;m1, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 := by
  refine bigSepM2_alt.trans <| (and_congr (pure_congr eq_comm) ?_).trans <| bigSepM2_alt.symm
  refine BiEntails.of_eq <| (congrArg _ ?_).trans (bigOpM_map_eq (fun (xy : A × B) => (xy.2, xy.1)) _ _)
  refine equiv_iff_eq.mp (fun k => ?_)
  simp only [get?_zipWith, get?_map]
  cases get? m1 k <;> cases get? m2 k <;> rfl

@[simp, rocq_alias big_sepM2_empty]
theorem bigSepM2_empty (Φ : K → A → B → PROP) :
    ([∗map] k ↦ x1;x2 ∈ (∅ : M A);(∅ : M B), Φ k x1 x2) ⊣⊢ emp := by
  refine (and_congr .rfl (BiEntails.of_eq <| congrArg _ ?_)).trans <|
    (and_congr (pure_true ?_) (bigSepM_empty (V := A × B))).trans true_and
  · refine eq_empty_iff.mpr fun k => by grind
  · exact funext fun k => propext (by grind [PartialMap.dom])

@[rocq_alias big_sepM2_empty']
theorem bigSepM2_empty_intro (P : PROP) [Affine P] (Φ : K → A → B → PROP) :
    P ⊢ [∗map] k ↦ x1;x2 ∈ (∅ : M A);(∅ : M B), Φ k x1 x2 :=
  Affine.affine.trans (bigSepM2_empty Φ).2

@[rocq_alias big_sepM2_empty_l]
theorem bigSepM2_empty_left (m1 : M A) (Φ : K → A → B → PROP) :
    ([∗map] k ↦ x1;x2 ∈ m1;(∅ : M B), Φ k x1 x2) ⊢ ⌜m1 = ∅⌝ :=
  bigSepM2_lookup_iff.trans <| pure_mono fun h => eq_empty_iff.mpr fun k => by grind

@[rocq_alias big_sepM2_empty_r]
theorem bigSepM2_empty_right (m2 : M B) (Φ : K → A → B → PROP) :
    ([∗map] k ↦ x1;x2 ∈ (∅ : M A);m2, Φ k x1 x2) ⊢ ⌜m2 = ∅⌝ :=
  bigSepM2_lookup_iff.trans <| pure_mono fun h => eq_empty_iff.mpr fun k => by grind

@[rocq_alias big_sepM2_delete]
theorem bigSepM2_delete {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B} (h1 : get? m1 i = some x1) (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢
      Φ i x1 x2 ∗ [∗map] k ↦ y1;y2 ∈ delete m1 i;delete m2 i, Φ k y1 y2 := by
  refine persistent_and_affinely_sep_left |>.trans ?_
  refine (sep_congr_right <| bigSepM_delete (i:= i) (x := (x1, x2)) (by grind)).trans ?_
  refine (sep_assoc.symm.trans <| (sep_congr_left sep_comm).trans sep_assoc).trans (sep_congr_right ?_)
  refine (sep_congr_left ?_).trans <| (sep_congr_right ?_).trans persistent_and_affinely_sep_left.symm
  · refine (affinely_congr <| pure_congr <| ?_).symm
    classical
    constructor <;> intro h <;> ext k <;>
    grind [dom, congrFun h k]
  · exact BiEntails.of_eq <| congrArg _ zipWith_delete.symm

@[rocq_alias big_sepM2_insert]
theorem bigSepM2_insert {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B} (h1 : get? m1 i = none) (h2 : get? m2 i = none) :
    ([∗map] k ↦ y1;y2 ∈ insert m1 i x1;insert m2 i x2, Φ k y1 y2) ⊣⊢
      Φ i x1 x2 ∗ [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2 := by
  simpa only [delete_insert_cancel h1, delete_insert_cancel h2] using
    bigSepM2_delete (m1 := insert m1 i x1) (m2 := insert m2 i x2)
      (get?_insert_eq rfl) (get?_insert_eq rfl)

@[rocq_alias big_sepM2_mono]
theorem bigSepM2_mono {Φ Ψ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  and_mono_right <| bigSepM_mono fun hget =>
    let ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
    h h1 h2

@[rocq_alias big_sepM2_ne]
theorem bigSepM2_dist (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B) (n : Nat)
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ≡{n}≡ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  and_ne.ne .rfl <| bigSepM_dist fun hget =>
    let ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
    h h1 h2

@[rocq_alias big_sepM2_proper]
theorem bigSepM2_eqv {Φ Ψ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  ⟨bigSepM2_mono fun h1 h2 => (h h1 h2).1, bigSepM2_mono fun h1 h2 => (h h1 h2).2⟩

@[rocq_alias big_sepM2_proper_2]
theorem bigSepM2_proper_2 [HasEquiv A] [HasEquiv B]
    (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B) (m1' : M A) (m2' : M B)
    (hm1 : ∀ k, Option.Rel (· ≈ ·) (get? m1 k) (get? m1' k))
    (hm2 : ∀ k, Option.Rel (· ≈ ·) (get? m2 k) (get? m2' k))
    (h : ∀ {k x1 x1' x2 x2'}, get? m1 k = some x1 → get? m1' k = some x1' →
      x1 ≈ x1' → get? m2 k = some x2 → get? m2' k = some x2' → x2 ≈ x2' →
      Φ k x1 x2 ⊣⊢ Ψ k x1' x2') :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1';m2', Ψ k x1 x2 := by
  refine bigSepM2_alt.trans <| (and_congr (pure_congr (by
    rw [dom_eq_of_option_rel hm1, dom_eq_of_option_rel hm2])) ?_).trans <| bigSepM2_alt.symm
  apply bigOpM_gen_proper_2 (fun hEq => BiEntails.of_eq hEq)
    ⟨fun _ => .rfl, fun hEq => hEq.symm, fun hEq1 hEq2 => hEq1.trans hEq2⟩
    (fun hΦ hΨ => sep_congr hΦ hΨ)
    (isSome_zipWith_prod_congr hm1 hm2)
  rintro k ⟨x1, x2⟩ ⟨x1', x2'⟩ hxy hxy'
  obtain ⟨hx1, hx2⟩ := get?_zipWith_prod_eq_some hxy
  obtain ⟨hx1', hx2'⟩ := get?_zipWith_prod_eq_some hxy'
  exact h hx1 hx1' (by grind) hx2 hx2' (by grind)

@[rocq_alias big_sepM2_ne']
theorem bigSepM2_dist_of_forall (n : Nat) (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, Φ k x1 x2 ≡{n}≡ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ≡{n}≡ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  bigSepM2_dist Φ Ψ m1 m2 n fun _ _ => h

@[rocq_alias big_sepM2_mono']
theorem bigSepM2_mono_of_forall (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊢ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  bigSepM2_mono fun _ _ => h

@[rocq_alias big_sepM2_flip_mono']
theorem bigSepM2_flip_mono (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, Ψ k x1 x2 ⊢ Φ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2) ⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 :=
  bigSepM2_mono fun _ _ => h

@[rocq_alias big_sepM2_proper']
theorem bigSepM2_eqv_of_forall (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, Φ k x1 x2 ⊣⊢ Ψ k x1 x2) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  bigSepM2_eqv fun _ _ => h

@[rocq_alias big_sepM2_closed]
theorem bigSepM2_closed (P : PROP → Prop) (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (hproper : ∀ {Q1 Q2}, Q1 ⊣⊢ Q2 → (P Q1 ↔ P Q2))
    (hemp : P emp) (hfalse : P iprop(False))
    (hsep : ∀ Q1 Q2, P Q1 → P Q2 → P iprop(Q1 ∗ Q2))
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → P (Φ k x1 x2)) :
    P ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) := by
  classical
  by_cases hdom : PartialMap.dom m1 = PartialMap.dom m2
  · refine (hproper <| bigSepM2_alt.trans <| (and_congr (pure_true hdom) .rfl).trans true_and).mpr ?_
    refine bigOpM_closed hemp (fun hx hy => hsep _ _ hx hy) fun hget => ?_
    obtain ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
    exact h h1 h2
  · exact (hproper <| bigSepM2_alt.trans <| (and_congr (pure_false hdom) .rfl).trans false_and).mpr hfalse

@[rocq_alias big_sepM2_persistent]
theorem bigSepM2_persistent (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Persistent (Φ k x1 x2)) :
    Persistent ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_closed Persistent Φ m1 m2
    (fun hQ => ⟨fun hP => ⟨hQ.2.trans <| hP.persistent.trans <|
      persistently_mono hQ.1⟩, fun hP => ⟨hQ.1.trans <| hP.persistent.trans <|
      persistently_mono hQ.2⟩⟩)
    inferInstance inferInstance
    (fun _ _ hP hQ => ⟨(sep_mono hP.persistent hQ.persistent).trans persistently_sep_mpr⟩) h

@[rocq_alias big_sepM2_empty_persistent]
instance bigSepM2_empty_persistent_inst (Φ : K → A → B → PROP) :
    Persistent ([∗map] k ↦ x1;x2 ∈ (∅ : M A);(∅ : M B), Φ k x1 x2) where
  persistent := (bigSepM2_empty Φ).1.trans <|
    Persistent.persistent.trans <| persistently_mono (bigSepM2_empty Φ).2

@[rocq_alias big_sepM2_persistent']
instance bigSepM2_persistent_inst {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    [h : ∀ k x1 x2, Persistent (Φ k x1 x2)] :
    Persistent ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_persistent Φ m1 m2 fun _ _ => h _ _ _

@[rocq_alias big_sepM2_affine]
theorem bigSepM2_affine (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Affine (Φ k x1 x2)) :
    Affine ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_closed Affine Φ m1 m2
    (fun hQ => ⟨fun hP => ⟨hQ.2.trans hP.affine⟩, fun hP => ⟨hQ.1.trans hP.affine⟩⟩)
    inferInstance inferInstance
    (fun _ _ hP hQ => ⟨(sep_mono hP.affine hQ.affine).trans sep_emp.1⟩) h

@[rocq_alias big_sepM2_empty_affine]
instance bigSepM2_empty_affine_inst (Φ : K → A → B → PROP) :
    Affine ([∗map] k ↦ x1;x2 ∈ (∅ : M A);(∅ : M B), Φ k x1 x2) where
  affine := (bigSepM2_empty Φ).1.trans Affine.affine

@[rocq_alias big_sepM2_affine']
instance bigSepM2_affine_inst {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    [h : ∀ k x1 x2, Affine (Φ k x1 x2)] :
    Affine ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_affine Φ m1 m2 fun _ _ => h _ _ _

@[rocq_alias big_sepM2_timeless]
theorem bigSepM2_timeless [Timeless (emp : PROP)] (Φ : K → A → B → PROP)
    (m1 : M A) (m2 : M B)
    (h : ∀ {k x1 x2}, get? m1 k = some x1 → get? m2 k = some x2 → Timeless (Φ k x1 x2)) :
    Timeless ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_closed Timeless Φ m1 m2
    (fun hQ => ⟨fun hP => ⟨later_mono hQ.2 |>.trans <| hP.timeless.trans <|
      except0_mono hQ.1⟩, fun hP => ⟨later_mono hQ.1 |>.trans <|
      hP.timeless.trans <| except0_mono hQ.2⟩⟩)
    inferInstance inferInstance
    (fun _ _ hP hQ => ⟨later_sep.1.trans <| (sep_mono hP.timeless hQ.timeless).trans
      except0_sep.2⟩) h

@[rocq_alias big_sepM2_empty_timeless]
instance bigSepM2_empty_timeless_inst [Timeless (emp : PROP)] (Φ : K → A → B → PROP) :
    Timeless ([∗map] k ↦ x1;x2 ∈ (∅ : M A);(∅ : M B), Φ k x1 x2) where
  timeless := (later_congr (bigSepM2_empty Φ)).1.trans <|
    Timeless.timeless.trans <| except0_mono (bigSepM2_empty Φ).2

@[rocq_alias big_sepM2_timeless']
instance bigSepM2_timeless_inst [Timeless (emp : PROP)] {Φ : K → A → B → PROP}
    {m1 : M A} {m2 : M B} [h : ∀ k x1 x2, Timeless (Φ k x1 x2)] :
    Timeless ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) :=
  bigSepM2_timeless Φ m1 m2 fun _ _ => h _ _ _

@[rocq_alias big_sepM2_delete_l]
theorem bigSepM2_delete_left {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} {i : K} {x1 : A}
    (h1 : get? m1 i = some x1) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢
      ∃ x2, ⌜get? m2 i = some x2⌝ ∧ (Φ i x1 x2 ∗ [∗map] k ↦ y1;y2 ∈ delete m1 i;delete m2 i, Φ k y1 y2) := by
  refine ⟨(and_intro bigSepM2_lookup_iff .rfl).trans <| pure_elim_left fun hdom => ?_, ?_⟩
  · obtain ⟨x2, h2⟩ : ∃ x2, get? m2 i = some x2 := by grind
    exact exists_intro_trans x2 <| and_intro (pure_intro h2) <| (bigSepM2_delete h1 h2).1
  · exact exists_elim fun x2 => pure_elim_left fun h2 => (bigSepM2_delete h1 h2).2

@[rocq_alias big_sepM2_delete_r]
theorem bigSepM2_delete_right {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} {i : K} {x2 : B}
    (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢
      ∃ x1, ⌜get? m1 i = some x1⌝ ∧ (Φ i x1 x2 ∗ [∗map] k ↦ y1;y2 ∈ delete m1 i;delete m2 i, Φ k y1 y2) := by
  refine ⟨(and_intro bigSepM2_lookup_iff .rfl).trans <| pure_elim_left fun hdom => ?_, ?_⟩
  · obtain ⟨x1, h1⟩ : ∃ x1, get? m1 i = some x1 := by grind
    exact exists_intro_trans x1 <| and_intro (pure_intro h1) <| (bigSepM2_delete h1 h2).1
  · exact exists_elim fun x1 => pure_elim_left fun h1 => (bigSepM2_delete h1 h2).2

@[rocq_alias big_sepM2_insert_delete]
theorem bigSepM2_insert_delete {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} {i : K} {x1 : A} {x2 : B} :
    ([∗map] k ↦ y1;y2 ∈ insert m1 i x1;insert m2 i x2, Φ k y1 y2) ⊣⊢
      Φ i x1 x2 ∗ [∗map] k ↦ y1;y2 ∈ delete m1 i;delete m2 i, Φ k y1 y2 := by
  simpa only [insert_delete] using
    bigSepM2_insert (get?_delete_eq rfl) (get?_delete_eq rfl)

@[rocq_alias big_sepM2_insert_acc]
theorem bigSepM2_insert_acc {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B} (h1 : get? m1 i = some x1) (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
      Φ i x1 x2 ∗ ∀ x1' x2', Φ i x1' x2' -∗
        [∗map] k ↦ y1;y2 ∈ insert m1 i x1';insert m2 i x2', Φ k y1 y2 := by
  refine (bigSepM2_delete h1 h2).1.trans <| sep_mono_right ?_
  refine forall_intro fun x1' => forall_intro fun x2' => wand_intro <| sep_comm.1.trans ?_
  exact (bigSepM2_insert_delete).2

@[rocq_alias big_sepM2_insert_2]
theorem bigSepM2_insert_elim {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B} [hor: TCOr (∀ x y, Affine (Φ i x y)) (Absorbing (Φ i x1 x2))] :
    Φ i x1 x2 -∗ ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
      [∗map] k ↦ y1;y2 ∈ insert m1 i x1;insert m2 i x2, Φ k y1 y2 := by
  refine entails_wand <| wand_intro ?_
  have hfalse (hne : ¬((get? m1 i).isSome ↔ (get? m2 i).isSome)) :
      ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ iprop(False) :=
    bigSepM2_lookup_iff.trans <| pure_mono fun hdom => hne (hdom i)
  match h1 : get? m1 i, h2 : get? m2 i with
  | none, none => exact (bigSepM2_insert h1 h2).2
  | none, some _ => exact (sep_mono_right (hfalse (by grind))).trans <|
      sep_elim_right.trans false_elim
  | some _, none => exact (sep_mono_right (hfalse (by grind))).trans <|
      sep_elim_right.trans false_elim
  | some y1, some y2 =>
      match hor with
      | TCOr.l | TCOr.r =>
          refine (sep_mono_right (bigSepM2_delete h1 h2).1).trans ?_
          refine sep_assoc.symm.1.trans <| (sep_mono_left sep_elim_left).trans ?_
          exact (bigSepM2_insert_delete).2

@[rocq_alias big_sepM2_lookup_acc]
theorem bigSepM2_lookup_acc {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B} (h1 : get? m1 i = some x1) (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
      Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) :=
  (bigSepM2_delete h1 h2).1.trans <| sep_mono_right <|
    wand_intro <| sep_comm.1.trans (bigSepM2_delete h1 h2).2

@[rocq_alias big_sepM2_lookup]
theorem bigSepM2_lookup {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A} {x2 : B}
    [hor: TCOr (∀ k y1 y2, Affine (Φ k y1 y2)) (Absorbing (Φ i x1 x2))]
    (h1 : get? m1 i = some x1) (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ Φ i x1 x2 :=
  match hor with
  | TCOr.l =>
      (bigSepM2_delete h1 h2).1.trans sep_elim_left
  | TCOr.r =>
      (bigSepM2_lookup_acc h1 h2).trans sep_elim_left

@[rocq_alias big_sepM2_lookup_l]
theorem bigSepM2_lookup_left {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B}
    {i : K} {x1 : A}
    [hor: TCOr (∀ k y1 y2, Affine (Φ k y1 y2)) (∀ x2, Absorbing (Φ i x1 x2))]
    (h1 : get? m1 i = some x1) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ∃ x2, ⌜get? m2 i = some x2⌝ ∧ Φ i x1 x2 :=
  match hor with
  | TCOr.l | TCOr.r => (bigSepM2_delete_left h1).1.trans <|
      exists_mono fun _ => and_mono_right sep_elim_left

@[rocq_alias big_sepM2_lookup_r]
theorem bigSepM2_lookup_right (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (i : K) (x2 : B)
    [hor: TCOr (∀ k y1 y2, Affine (Φ k y1 y2)) (∀ x1, Absorbing (Φ i x1 x2))]
    (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ ∃ x1, ⌜get? m1 i = some x1⌝ ∧ Φ i x1 x2 :=
  match hor with
  | TCOr.l | TCOr.r => (bigSepM2_delete_right h2).1.trans <|
      exists_mono fun _ => and_mono_right sep_elim_left

@[rocq_alias big_sepM2_singleton]
theorem bigSepM2_singleton (Φ : K → A → B → PROP) (i : K) (x1 : A) (x2 : B) :
    ([∗map] k ↦ y1;y2 ∈ ({[i := x1]} : M A);({[i := x2]} : M B), Φ k y1 y2) ⊣⊢ Φ i x1 x2 :=
  (bigSepM2_insert (get?_empty i) (get?_empty i)).trans <|
    (sep_congr_right <| bigSepM2_empty Φ).trans sep_emp

@[rocq_alias big_sepM2_fst_snd]
theorem bigSepM2_fst_snd (Φ : K → A → B → PROP) (m : M (A × B)) :
    ([∗map] k ↦ x1;x2 ∈ map Prod.fst m;map Prod.snd m, Φ k x1 x2) ⊣⊢
      [∗map] k ↦ xy ∈ m, Φ k xy.1 xy.2 := by
  refine bigSepM2_alt.trans ?_
  rw [dom_map, dom_map]
  refine (and_congr (pure_true rfl) (BiEntails.of_eq <| congrArg _ ?_)).trans true_and
  apply equiv_iff_eq.mp
  intro k
  simp only [get?_zipWith, get?_map]
  cases get? m k <;> rfl

@[rocq_alias big_sepM2_fmap]
theorem bigSepM2_map {A' B' : Type u} (f : A → A') (g : B → B')
    {Φ : K → A' → B' → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ map f m1;map g m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k (f x1) (g x2) := by
  refine bigSepM2_alt.trans <| (and_congr (pure_congr ?_) ?_).trans <| bigSepM2_alt.symm
  · simp only [dom_map]
  · refine BiEntails.of_eq <| (congrArg _ ?_).trans <| BigOpM.bigOpM_map_eq
        (fun (xy : A × B) => (f xy.1, g xy.2)) _ (zipWith (fun (x : A) (y : B) => (x, y)) m1 m2)
    apply equiv_iff_eq.mp
    intro k
    simp only [get?_zipWith, get?_map]
    cases get? m1 k <;> cases get? m2 k <;> rfl

@[rocq_alias big_sepM2_fmap_l]
theorem bigSepM2_map_left {A' : Type u} (f : A → A') (Φ : K → A' → B → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ x1;x2 ∈ map f m1;m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k (f x1) x2 := by
  simpa only [map_id, id] using bigSepM2_map f id

@[rocq_alias big_sepM2_fmap_r]
theorem bigSepM2_map_right {B' : Type u} (g : B → B') (Φ : K → A → B' → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ x1;x2 ∈ m1;map g m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 (g x2) := by
  simpa only [map_id, id] using bigSepM2_map id g

@[rocq_alias big_sepM2_sep]
theorem bigSepM2_sep_eqv {Φ Ψ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 ∗ Ψ k x1 x2) ⊣⊢
      ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ∗ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 := by
  refine (and_congr_right <| BiEntails.of_eq bigSepM_sep_eq).trans ?_
  refine persistent_and_affinely_sep_left.trans <| (sep_congr_left persistent_sep_dup).trans ?_
  refine sep_sep_sep_comm.trans ?_
  exact sep_congr persistent_and_affinely_sep_left.symm persistent_and_affinely_sep_left.symm

@[rocq_alias big_sepM2_sep_2]
theorem bigSepM2_sep_eqv_symm (Φ Ψ : K → A → B → PROP) {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) -∗
      ([∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2) -∗
        [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 ∗ Ψ k x1 x2 :=
  entails_wand <| wand_intro <| bigSepM2_sep_eqv.mpr

@[rocq_alias big_sepM2_and]
theorem bigSepM2_and (Φ Ψ : K → A → B → PROP) {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 ∧ Ψ k x1 x2) ⊢
      ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ∧ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  and_intro (bigSepM2_mono fun _ _ => and_elim_l) (bigSepM2_mono fun _ _ => and_elim_r)

@[rocq_alias big_sepM2_pure_1]
theorem bigSepM2_pure_intro {φ : K → A → B → Prop} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, (⌜φ k x1 x2⌝ : PROP)) ⊢
      ⌜∀ k x1 x2, get? m1 k = some x1 → get? m2 k = some x2 → φ k x1 x2⌝ := by
  refine bigSepM2_alt.mp.trans <| and_elim_r.trans ?_
  exact bigSepM_pure_intro.trans <| pure_mono fun hall k x1 x2 h1 h2 => hall k (x1, x2) <| by grind

@[rocq_alias big_sepM2_affinely_pure_2]
theorem bigSepM2_affinely_pure_elim (φ : K → A → B → Prop) {m1 : M A} {m2 : M B}
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    (<affine> ⌜∀ k x1 x2, get? m1 k = some x1 → get? m2 k = some x2 → φ k x1 x2⌝ : PROP) ⊢
      [∗map] k ↦ x1;x2 ∈ m1;m2, (<affine> ⌜φ k x1 x2⌝ : PROP) := by
  refine and_intro (affinely_elim.trans <| pure_intro hdom) ?_ |>.trans <|
    (bigSepM2_alt_lookup (Φ := fun k x1 x2 => iprop(<affine> ⌜φ k x1 x2⌝))).mpr
  refine (affinely_mono <| pure_mono fun hall k xy hget => ?_).trans bigSepM_affinely_pure_elim
  obtain ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
  exact hall k xy.1 xy.2 h1 h2

@[rocq_alias big_sepM2_pure]
theorem bigSepM2_pure [BIAffine PROP] (φ : K → A → B → Prop) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, (⌜φ k x1 x2⌝ : PROP)) ⊣⊢
      ⌜(∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) ∧
        ∀ k x1 x2, get? m1 k = some x1 → get? m2 k = some x2 → φ k x1 x2⌝ := by
  refine ⟨(and_intro bigSepM2_lookup_iff bigSepM2_pure_intro).trans pure_and.1,
    pure_elim _ .rfl fun ⟨hdom, hall⟩ => ?_ ⟩
  refine (pure_intro hall).trans <| (affine_affinely _).2.trans ?_
  exact (bigSepM2_affinely_pure_elim φ hdom).trans <| bigSepM2_mono fun _ _ => affinely_elim

@[rocq_alias big_sepM2_persistently]
theorem bigSepM2_persistently [BIAffine PROP] (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    (<pers> [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢ [∗map] k ↦ x1;x2 ∈ m1;m2, <pers> Φ k x1 x2 :=
  (persistently_congr bigSepM2_alt).trans <| persistently_and.trans <|
    (and_congr persistently_pure bigSepM_persistently).trans <|
      (bigSepM2_alt (Φ := fun k x1 x2 => iprop(<pers> Φ k x1 x2))).symm

@[rocq_alias big_sepM2_intro]
theorem bigSepM2_intro (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    (□ ∀ k x1 x2, ⌜get? m1 k = some x1⌝ → ⌜get? m2 k = some x2⌝ → Φ k x1 x2) ⊢
      [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 :=
  and_intro (pure_intro hdom) (bigSepM_intro fun hget =>
    let ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
    intuitionistically_elim.trans <| (forall_elim _).trans <| (forall_elim _).trans <|
      (forall_elim _).trans <| (pure_imp_elim h1).trans <| pure_imp_elim h2) |>.trans <|
    bigSepM2_alt_lookup.mpr

@[rocq_alias big_sepM2_forall]
theorem bigSepM2_forall [BIAffine PROP] (Φ : K → A → B → PROP) (m1 : M A) (m2 : M B)
    (h : ∀ k x1 x2, Persistent (Φ k x1 x2)) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢
      ⌜∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome⌝ ∧
        ∀ k x1 x2, ⌜get? m1 k = some x1⌝ → ⌜get? m2 k = some x2⌝ → Φ k x1 x2 := by
  refine ⟨and_intro bigSepM2_lookup_iff ?_, ?_⟩
  · refine forall_intro fun k => forall_intro fun x1 => forall_intro fun x2 => ?_
    refine imp_intro_swap <| pure_elim_left fun h1 => ?_
    exact imp_intro_swap <| pure_elim_left fun h2 => bigSepM2_lookup h1 h2
  · refine pure_elim_left fun hdom => ?_
    refine (and_intro (pure_intro hdom) ?_).trans bigSepM2_alt_lookup.mpr
    refine (forall_intro fun k => forall_intro fun x : A × B => ?_).trans bigSepM_forall.2
    refine imp_intro_swap <| pure_elim_left fun hget => ?_
    obtain ⟨h1, h2⟩ := get?_zipWith_prod_eq_some hget
    refine (forall_elim k).trans <| (forall_elim x.1).trans <| (forall_elim x.2).trans ?_
    exact (pure_imp_elim h1).trans <| pure_imp_elim h2

@[rocq_alias big_sepM2_impl]
theorem bigSepM2_impl {Φ Ψ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢
      (□ ∀ k x1 x2, ⌜get? m1 k = some x1⌝ → ⌜get? m2 k = some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
      [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 := by
  refine wand_intro <| (sep_mono_left (and_intro bigSepM2_lookup_iff .rfl)).trans ?_
  refine sep_and_right.trans <| (and_mono_left sep_elim_left).trans <| pure_elim_left fun hdom => ?_
  refine (sep_mono_right <|
    bigSepM2_intro (fun k x1 x2 => iprop(Φ k x1 x2 -∗ Ψ k x1 x2)) m1 m2 hdom).trans ?_
  refine bigSepM2_sep_eqv.mpr.trans ?_
  exact bigSepM2_mono fun _ _ => wand_elim_right

@[rocq_alias big_sepM2_wand]
theorem bigSepM2_wand (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢
      ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 -∗ Ψ k x1 x2) -∗ [∗map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2 :=
  wand_intro <| bigSepM2_sep_eqv.mpr.trans <| bigSepM2_mono fun _ _ => wand_elim_right

@[rocq_alias big_sepM2_lookup_acc_impl]
theorem bigSepM2_lookup_acc_impl [DecidableEq K] {Φ : K → A → B → PROP}
    {m1 : M A} {m2 : M B} {i : K} {x1 : A} {x2 : B}
    (h1 : get? m1 i = some x1) (h2 : get? m2 i = some x2) :
    ([∗map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
      Φ i x1 x2 ∗ ∀ (Ψ : K → A → B → PROP), (□ ∀ k y1 y2,
        ⌜get? m1 k = some y1⌝ → ⌜get? m2 k = some y2⌝ → ⌜k ≠ i⌝ → Φ k y1 y2 -∗ Ψ k y1 y2) -∗
        Ψ i x1 x2 -∗ [∗map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2 := by
  refine (bigSepM2_delete h1 h2).1.trans <| sep_mono_right <| forall_intro fun Ψ => ?_
  refine wand_intro <| wand_intro <| sep_comm.1.trans <| (sep_mono_right ?_).trans (bigSepM2_delete h1 h2).2
  refine (sep_mono bigSepM2_impl ?_).trans wand_elim_left
  refine intuitionistically_mono <| forall_intro fun k => forall_intro fun y1 => ?_
  refine forall_intro fun y2 => imp_intro_swap <| pure_elim_left fun hd1 => imp_intro_swap ?_
  refine pure_elim_left fun hd2 => ?_
  obtain ⟨hne, hm1⟩ := get?_delete_some_iff.mp hd1
  obtain ⟨_, hm2⟩ := get?_delete_some_iff.mp hd2
  refine (forall_elim k).trans <| (forall_elim y1).trans <| (forall_elim y2).trans ?_
  refine (pure_imp_elim hm1).trans <| (pure_imp_elim hm2).trans ?_
  exact pure_imp_elim fun hki => hne hki.symm

@[rocq_alias big_sepM2_later_1]
theorem bigSepM2_later_1 [BIAffine PROP] {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    (▷ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ⊢ ◇ [∗map] k ↦ x1;x2 ∈ m1;m2, ▷ Φ k x1 x2 := by
  refine (later_mono bigSepM2_alt.mp).trans <| later_and.1.trans ?_
  refine (and_mono Timeless.timeless (bigSepM_later.1.trans except0_intro)).trans ?_
  exact except0_and.2.trans <| except0_mono (bigSepM2_alt (Φ := fun k x1 x2 => iprop(▷ Φ k x1 x2))).mpr

@[rocq_alias big_sepM2_later_2]
theorem bigSepM2_later_2 {Φ : K → A → B → PROP} {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, ▷ Φ k x1 x2) ⊢ ▷ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 :=
  bigSepM2_alt.mp.trans <| (and_mono later_intro bigSepM_later_2).trans <| later_and.2.trans <|
      later_mono bigSepM2_alt.mpr

@[rocq_alias big_sepM2_laterN_2]
theorem bigSepM2_laterN_2 {Φ : K → A → B → PROP} (n : Nat) {m1 : M A} {m2 : M B} :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, ▷^[n] Φ k x1 x2) ⊢ ▷^[n] [∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2 :=
  match n with
  | 0 => .rfl
  | _ + 1 => bigSepM2_later_2.trans <| later_mono (bigSepM2_laterN_2 _)

@[rocq_alias big_sepM2_sepM]
theorem bigSepM2_sepM {Φ1 : K → A → PROP} {Φ2 : K → B → PROP}
    {m1 : M A} {m2 : M B} (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ1 k x1 ∗ Φ2 k x2) ⊣⊢
      ([∗map] k ↦ x1 ∈ m1, Φ1 k x1) ∗ [∗map] k ↦ x2 ∈ m2, Φ2 k x2 := by
  refine bigSepM2_sep_eqv.trans <| sep_congr ?_ ?_
  · refine bigSepM2_alt_lookup.trans <| (and_congr (pure_true hdom) ?_).trans true_and
    refine BiEntails.of_eq <| (bigOpM_map_eq Prod.fst Φ1 (zipWith _ m1 m2)).symm.trans ?_
    refine congrArg _ <| equiv_iff_eq.mp fun k => ?_
    cases h1 : get? m1 k <;> cases h2 : get? m2 k <;> grind
  · refine bigSepM2_alt_lookup.trans <| (and_congr (pure_true hdom) ?_).trans true_and
    refine BiEntails.of_eq <| (bigOpM_map_eq Prod.snd Φ2 (zipWith _ m1 m2)).symm.trans ?_
    refine congrArg _ <| equiv_iff_eq.mp fun k => ?_
    cases h1 : get? m1 k <;> cases h2 : get? m2 k <;> grind

@[rocq_alias big_sepM2_sepM_2]
theorem bigSepM2_sepM_2 (Φ1 : K → A → PROP) (Φ2 : K → B → PROP)
    (m1 : M A) (m2 : M B) (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([∗map] k ↦ x1 ∈ m1, Φ1 k x1) ⊢
      ([∗map] k ↦ x2 ∈ m2, Φ2 k x2) -∗ [∗map] k ↦ x1;x2 ∈ m1;m2, Φ1 k x1 ∗ Φ2 k x2 :=
  wand_intro <| (bigSepM2_sepM hdom).mpr

@[rocq_alias big_sepM2_union_inv_l]
theorem bigSepM2_union_inv_left [DecidableEq K] (Φ : K → A → B → PROP)
    (m1 m2 : M A) (m' : M B) (hdisj : m1 ##ₘ m2) :
    ([∗map] k ↦ x;y ∈ m1 ∪ m2;m', Φ k x y) ⊢
      ∃ m1' m2', (⌜m' = m1' ∪ m2'⌝ ∧ ⌜m1' ##ₘ m2'⌝ ∧
        ([∗map] k ↦ x;y ∈ m1;m1', Φ k x y) ∗ [∗map] k ↦ x;y ∈ m2;m2', Φ k x y) := by
  induction m1 using LawfulFiniteMap.induction_on generalizing m2 m' with
  | hemp =>
    rw [union_empty_left]
    refine exists_intro_trans ∅ <| exists_intro_trans m' ?_
    refine and_intro (pure_intro ?_) (and_intro (pure_intro ?_) ?_)
    · exact union_empty_left.symm
    · exact disjoint_empty_left m'
    · exact emp_sep.2.trans <| sep_mono_left (bigSepM2_empty Φ).2
  | hins i x m1 hi ih =>
    obtain ⟨hm2i, hdisj'⟩ := (disjoint_insert_left_iff hi).mp hdisj
    rw [← union_insert_left]
    refine (bigSepM2_delete_left (get?_insert_eq rfl)).1.trans ?_
    refine exists_elim fun y => pure_elim_left fun hy => ?_
    rw [delete_insert_cancel <| get?_union_none.mpr ⟨hi, hm2i⟩]
    refine wand_elim_swap <| (ih m2 (delete m' i) hdisj').trans ?_
    refine exists_elim fun n1 => exists_elim fun n2 => ?_
    refine pure_elim_left fun hUnion => pure_elim_left fun hDisj => ?_
    refine wand_intro_left ?_
    obtain ⟨hn1, hn2⟩ := (get?_union_none (m₁ := n1) (m₂ := n2) (i := i)).mp <| by
      rw [← hUnion, get?_delete_eq rfl]
    refine exists_intro_trans (insert n1 i y) <| exists_intro_trans n2 ?_
    refine and_intro (pure_intro ?_) (and_intro (pure_intro ?_) ?_)
    · rw [← union_insert_left, ← hUnion, insert_delete_cancel hy]
    · exact (disjoint_insert_left_iff hn1).mpr ⟨hn2, hDisj⟩
    · exact sep_assoc.symm.1.trans <| sep_mono_left (bigSepM2_insert hi hn1).2

@[rocq_alias big_sepM2_union_inv_r]
theorem bigSepM2_union_inv_right [DecidableEq K] (Φ : K → A → B → PROP)
    (m1 m2 : M B) (m' : M A) (hdisj : m1 ##ₘ m2) :
    ([∗map] k ↦ x;y ∈ m';m1 ∪ m2, Φ k x y) ⊢
      ∃ m1' m2', iprop(⌜m' = m1' ∪ m2'⌝ ∧ ⌜m1' ##ₘ m2'⌝ ∧
        ([∗map] k ↦ x;y ∈ m1';m1, Φ k x y) ∗ [∗map] k ↦ x;y ∈ m2';m2, Φ k x y) := by
  refine bigSepM2_flip.mp.trans ?_
  refine (bigSepM2_union_inv_left (fun k (y : B) (x : A) => Φ k x y) m1 m2 m' hdisj).trans ?_
  refine exists_mono fun _ => exists_mono fun _ => and_mono_right <| and_mono_right ?_
  exact sep_mono bigSepM2_flip.mp bigSepM2_flip.mp

@[rocq_alias big_sepM_sepM2_diag]
theorem bigSepM_bigSepM2_diag (Φ : K → A → A → PROP) (m : M A) :
    ([∗map] k ↦ x ∈ m, Φ k x x) ⊢ [∗map] k ↦ x1;x2 ∈ m;m, Φ k x1 x2 := by
  refine (and_intro (pure_intro rfl) ?_).trans bigSepM2_alt.mpr
  refine (BiEntails.of_eq <|
    (bigOpM_map_eq (fun x : A => (x, x)) (fun k xy => Φ k xy.1 xy.2) m).symm.trans <|
    congrArg _ (Eq.symm ?_)).1
  apply equiv_iff_eq.mp
  intro k
  simp only [get?_zipWith, get?_map]
  cases get? m k <;> rfl

@[rocq_alias big_sepM2_ne_2]
theorem bigSepM2_dist_2 (A B : Type uV) [OFE A] [OFE B]
    (Φ Ψ : K → A → B → PROP) (m1 : M A) (m2 : M B) (m1' : M A) (m2' : M B) (n : Nat)
    (hm1 : ∀ k, Option.Rel (fun x y => x ≡{n}≡ y) (get? m1 k) (get? m1' k))
    (hm2 : ∀ k, Option.Rel (fun x y => x ≡{n}≡ y) (get? m2 k) (get? m2' k))
    (h : ∀ k x1 x1' x2 x2', get? m1 k = some x1 → get? m1' k = some x1' →
      x1 ≡{n}≡ x1' → get? m2 k = some x2 → get? m2' k = some x2' → x2 ≡{n}≡ x2' →
      Φ k x1 x2 ≡{n}≡ Ψ k x1' x2') :
    ([∗map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ≡{n}≡ [∗map] k ↦ x1;x2 ∈ m1';m2', Ψ k x1 x2 := by
  apply and_ne.ne (by rw [dom_eq_of_option_rel hm1, dom_eq_of_option_rel hm2])
  apply bigOpM_gen_proper_2 (fun hEq => hEq ▸ .rfl) OFE.dist_equivalence
    (fun hΦ hΨ => sep_ne.ne hΦ hΨ) (isSome_zipWith_prod_congr hm1 hm2)
  rintro k ⟨x1, x2⟩ ⟨x1', x2'⟩ hxy hxy'
  obtain ⟨hx1, hx2⟩ := get?_zipWith_prod_eq_some hxy
  obtain ⟨hx1', hx2'⟩ := get?_zipWith_prod_eq_some hxy'
  exact h k x1 x1' x2 x2' hx1 hx1' (by grind) hx2 hx2' (by grind)

end BigSepM2

end Iris.BI
