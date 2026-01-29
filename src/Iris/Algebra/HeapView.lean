/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/
import Iris.Algebra.Heap
import Iris.Algebra.View
import Iris.Algebra.DFrac
import Iris.Algebra.Frac

/-!
# Heap Views

This file defines the `HeapView` type, which combines heap algebra with view relations.
It provides authoritative and fragmental ownership over heap elements with fractional permissions.

## Main definitions

* `HeapR`: The view relation for heaps
* `HeapView`: The view type combining heaps with fractional permissions
* `HeapView.Auth`: Authoritative ownership over an entire heap
* `HeapView.Frag`: Fragmental ownership over an allocated element

## Main statements

* `HeapView.update_one_alloc`: Allocation update lemma
* `HeapView.update_one_delete`: Deletion update lemma
* `HeapView.update_replace`: Replacement update lemma
-/

open Iris

section heapView
open Store Heap OFE CMRA

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]
variable [IHHmap : ∀ V, HasHeapMap (H (DFrac F × V)) (H V) K (DFrac F × V) V]

/-- The view relation for heaps: relates a model heap to a fragment heap at step index `n`. -/
def HeapR (n : Nat) (m : H V) (f : H (DFrac F × V)) : Prop :=
  ∀ k fv, get f k = some fv →
    ∃ (v : V) (dq : DFrac F), get m k = some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))

instance : IsViewRel (HeapR F K V H) where
  mono {n1 m1 f1 n2 m2 f2 Hrel Hm Hf Hn k} vk Hk := by
    obtain Hf' : ∃ z, get f1 k ≡{n2}≡ some vk • z := by
      have ⟨z, Hz⟩ := lookup_incN (n := n2) (m1 := f2) (m2 := f1) |>.1 Hf k
      exact ⟨z, Hk ▸ Hz⟩
    match h : get f1 k with
    | none => rcases h ▸ Hf' with ⟨_|_, HK⟩ <;> simp [CMRA.op, optionOp] at HK
    | some ⟨dq', v'⟩ =>
      obtain ⟨v, dq, Hm1, ⟨Hvval, Hdqval⟩, Hvincl⟩ := Hrel k ⟨dq', v'⟩ h
      obtain ⟨v', Hm2, Hv⟩ : ∃ y : V, get m2 k = some y ∧ v ≡{n2}≡ y := by
        have Hmm := Hm1 ▸ Hm k <;> revert Hmm
        cases get m2 k <;> simp
      exists v', dq
      refine ⟨Hm2, ⟨Hvval, validN_ne Hv (validN_of_le Hn Hdqval)⟩, ?_⟩
      suffices some vk ≼{n2} some (dq, v) by exact incN_of_incN_of_dist this ⟨rfl, Hv⟩
      refine incN_trans Hf' ?_
      refine incN_trans ?_ (incN_of_incN_le Hn Hvincl)
      rw [h]
  rel_validN n m f Hrel k := by
    match Hf : get f k with
    | none => simp [ValidN, optionValidN]
    | some _ =>
      obtain ⟨_, _, _, Hvv, Hvi⟩ := Hf ▸ Hrel k _ Hf
      exact (Hf ▸ validN_of_incN Hvi Hvv)
  rel_unit n := by
    refine ⟨empty, fun _ _ => ?_⟩
    simp [UCMRA.unit, Store.unit, get_empty]

namespace HeapR

omit IHHmap in
theorem unit : HeapR F K V H n m UCMRA.unit := by
  simp [HeapR, UCMRA.unit, Heap.get_empty]

theorem exists_iff_validN {n f} : (∃ m, HeapR F K V H n m f) ↔ ✓{n} f := by
  refine ⟨fun ⟨m, Hrel⟩ => IsViewRel.rel_validN _ _ _ Hrel, fun Hv => ?_⟩
  let FF : K → (DFrac F × V) → Option V := fun k _ => get f k |>.bind (·.2)
  refine ⟨hhmap FF f, fun k => ?_⟩
  cases h : get f k
  · simp
  simp only [Option.some.injEq, exists_and_left]
  rintro ⟨dq, v⟩ rfl
  exists v
  simp only [hhmap_get, h, Option.bind_some, true_and, FF]
  exact ⟨dq, (h ▸ Hv k : ✓{n} some (dq, v)), incN_refl _⟩

omit IHHmap in
theorem point_get_iff n m k dq v :
    HeapR F K V H n m (point k <| some (dq, v)) ↔
      ∃ (v' : V) (dq' : DFrac F),
        get m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := by
  constructor
  · refine fun Hrel => Hrel k (dq, v) ?_
    simp [point, get_set_eq]
  · rintro ⟨v', dq', Hlookup, Hval, Hinc⟩ j
    simp only [point]
    by_cases h : k = j
    · simp [get_set_eq h]
      exact ⟨v', h ▸ Hlookup, dq', Hval, Hinc⟩
    · simp [get_set_ne h, get_empty]

instance [CMRA.Discrete V] : IsViewRelDiscrete (HeapR F K V H) where
  discrete n _ _ H k v He := by
    have ⟨v, Hv1, ⟨x, Hx1, Hx2⟩⟩ := H k v He
    refine ⟨v, Hv1, ⟨x, ?_, inc_0_iff_incN n |>.mp Hx2⟩⟩
    exact ⟨Hx1.1, valid_iff_validN.mp (Discrete.discrete_valid Hx1.2) _⟩

end HeapR

/-- A view of a Heap, that gives element-wise ownership. -/
abbrev HeapView := View F (HeapR F K V H)

end heapView

namespace HeapView

open Heap OFE View One Store DFrac CMRA UFraction

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]

/-- Authoritative (fractional) ownership over an entire heap. -/
def Auth (dq : DFrac F) (m : H V) : HeapView F K V H := ●V{dq} m

/-- Fragmental (fractional) ownership over an allocated element in the heap. -/
def Frag (k : K) (dq : DFrac F) (v : V) : HeapView F K V H := ◯V point k <| some (dq, v)

/-- Fragmental (fractional) ownership over an element in the heap. -/
def Elem (k : K) (v : Option (DFrac F × V)) : HeapView F K V H := ◯V point k v

-- TODO: Do we need this?
instance : NonExpansive (Auth dq : _ → HeapView F K V H) := auth_ne

instance : NonExpansive (Frag k dq : _ → HeapView F K V H) where
  ne _ _ _ Hx := by
    refine frag_ne.ne (fun k' => ?_)
    by_cases h : k = k'
    · simp [point, get_set_eq h]
      exact dist_prod_ext rfl Hx
    · simp [point, get_set_ne h]

variable {dp dq : DFrac F} {n : Nat} {m1 m2 : H V} {k : K} {v1 v2 : V}

theorem auth_dfrac_op_equiv : Auth (dp • dq) m1 ≡ Auth dp m1 • Auth dq m1 :=
  auth_op_auth_eqv

theorem dist_of_validN_auth_op : ✓{n} Auth dp m1 • Auth dq m2 → m1 ≡{n}≡ m2 :=
  dist_of_validN_auth

theorem equiv_of_valid_auth_op : ✓ Auth dp m1 • Auth dq m2 → m1 ≡ m2 :=
  eqv_of_valid_auth

nonrec theorem auth_validN_iff : ✓{n} Auth dq m1 ↔ ✓ dq :=
  auth_validN_iff.trans <| and_iff_left_of_imp (fun _ => HeapR.unit _ _ _ _)

nonrec theorem auth_valid_iff : ✓ Auth dq m1 ↔ ✓ dq :=
  auth_valid_iff.trans <| and_iff_left_of_imp (fun _ _ => HeapR.unit _ _ _ _)

theorem auth_one_valid : ✓ Auth (.own (F := F) one) m1 := auth_valid_iff.mpr valid_own_one

nonrec theorem auth_op_auth_validN_iff : ✓{n} Auth dp m1 • Auth dq m2 ↔ ✓ dp • dq ∧ m1 ≡{n}≡ m2 :=
  auth_op_auth_validN_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ => HeapR.unit _ _ _ _

nonrec theorem auth_op_auth_valid_iff : ✓ Auth dp m1 • Auth dq m2 ↔ ✓ dp • dq ∧ m1 ≡ m2 :=
  auth_op_auth_valid_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ _ => HeapR.unit _ _ _ _

nonrec theorem auth_one_op_auth_one_validN_iff :
    ✓{n} Auth (F := F) (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_validN_iff

nonrec theorem auth_one_op_auth_one_valid_iff :
    ✓ Auth (F := F) (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_valid_iff

theorem frag_op_equiv : Frag (H := H) k (dp • dq) (v1 • v2) ≡ Frag k dp v1 • Frag k dq v2 := by
  refine frag_ne.eqv (Store.eqv_of_Equiv ?_)
  refine Store.Equiv_trans.trans ?_ point_op_point.symm
  rfl

theorem frag_add_op_equiv {q1 q2 : F} :
    Frag (H := H) k (.own (q1 + q2)) (v1 • v2) ≡ Frag k (.own q1) v1 • Frag k (.own q2) v2 :=
  frag_op_equiv

nonrec theorem auth_op_frag_validN_iff :
    ✓{n} Auth dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓ dp ∧ Store.get m1 k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') :=
  auth_op_frag_validN_iff.trans <|
    (and_congr_right fun _ => (HeapR.point_get_iff ..).trans <|
    exists_congr fun _ => exists_and_left).trans (by grind)

theorem auth_op_frag_one_validN_iff :
    ✓{n} (Auth dp m1 • Frag k (.own one) v1) ↔ ✓ dp ∧ ✓{n} v1 ∧ get m1 k ≡{n}≡ some v1 := by
  refine auth_op_frag_validN_iff.trans ⟨fun ⟨Hp, v', dq', Hl, Hv, Hi⟩ => ?_, fun ⟨Hp, Hv, Hl⟩ => ?_⟩
  · have Heq : v1 ≡{n}≡ Hp := Option.dist_of_inc_exclusive Hi Hv |>.2
    exact ⟨dq', validN_ne Heq.symm Hv.2, Hl ▸ Heq.symm⟩
  · match h : get m1 k with
    | none => simp [h] at Hl
    | some v' =>
      exists v', .own one
      refine ⟨Hp, rfl, ?_, ?_⟩
      · exact ⟨one_whole (α := F) |>.1, Dist.validN (h ▸ Hl).symm |>.mp Hv⟩
      · exact Option.some_incN_some_iff.mpr <| .inl <| dist_prod_ext rfl (h.symm ▸ Hl).symm

theorem auth_op_frag_validN_total_iff [IsTotal V] (H : ✓{n} Auth dp m1 • Frag k dq v1) :
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m1 k = some v' ∧ ✓{n} v' ∧ v1 ≼{n} v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, ⟨x, Hx⟩⟩ := auth_op_frag_validN_iff.mp H
  exists v'
  refine ⟨Hdp, ?_, Hl, Hv.2, ?_⟩
  · refine Option.valid_of_inc_valid (valid_iff_validN' n |>.mpr Hv.1) ?_
    refine inc_iff_incN n |>.mpr ?_
    match x with
    | none => exact incN_of_incN_of_dist (incN_refl _) Hx.1.symm
    | some x => exact ⟨x.1, Hx.1⟩
  · match x with
    | none => exact incN_of_incN_of_dist (incN_refl _) Hx.2.symm
    | some x => exact ⟨x.2, Hx.2⟩

theorem auth_op_frag_discrete_valid_iff [CMRA.Discrete V] :
    ✓ Auth dp m1 • Frag k dq v1 ↔
      ∃ v' dq', ✓ dp ∧ get m1 k = some v' ∧ ✓ (dq', v') ∧ some (dq, v1) ≼ some (dq', v') := by
  refine valid_iff_validN.trans ?_
  refine forall_congr' (fun _ => auth_op_frag_validN_iff) |>.trans ?_
  refine ⟨fun Hvalid' => ?_, ?_⟩
  · obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := Hvalid' 0
    refine ⟨v', dq', Hdp, Hl, ?_, inc_iff_incN 0 |>.mpr Hi⟩
    exact ⟨discrete_valid Hv.1, discrete_valid Hv.2⟩
  · exact fun ⟨v', dq', Hdp, Hl, Hv, Hi⟩ n => ⟨v', dq', Hdp, Hl, Hv.validN, inc_iff_incN n |>.mp Hi⟩

theorem auth_op_frag_valid_total_discrete_iff [IsTotal V] [CMRA.Discrete V]
    (H : ✓ Auth dp m1 • Frag k dq v1) :
    ∃ v', ✓ dp ∧ ✓ dq ∧ get m1 k = some v' ∧ ✓ v' ∧ v1 ≼ v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := auth_op_frag_discrete_valid_iff |>.mp H
  refine ⟨v', Hdp, ?_, Hl, Hv.2, ?_⟩
  · rcases Hi with ⟨(_|x), Hx⟩
    · exact valid_of_eqv Hx.1 Hv.1
    · exact Option.valid_of_inc_valid Hv.1 ⟨x.fst, Hx.1⟩
  · rcases Hi with ⟨(_|x), Hx⟩
    · exact inc_of_inc_of_eqv (inc_refl _) Hx.2.symm
    · rcases (⟨x.snd, Hx.2⟩ : some v1 ≼ some v') with ⟨(_|z), Hz⟩
      · exact inc_of_inc_of_eqv (inc_refl _) Hz.symm
      · exists z

theorem auth_op_frag_one_valid_iff :
    ✓ Auth dp m1 • Frag k (.own one) v1 ↔ ✓ dp ∧ ✓ v1 ∧ get m1 k ≡ some v1 := by
  refine valid_iff_validN.trans ?_
  refine forall_congr' (fun _ => auth_op_frag_one_validN_iff) |>.trans ?_
  refine ⟨fun Hv => ?_, ?_⟩
  · exact ⟨Hv 0 |>.1, valid_iff_validN.mpr (Hv · |>.2.1), equiv_dist.mpr (Hv · |>.2.2)⟩
  · exact fun ⟨Hdp, Hv, Hl⟩ n => ⟨Hdp, Hv.validN, Hl.dist⟩

instance [Hdq : CoreId dq] [Hv1 : CoreId v1] : CoreId (Frag (H := H) k dq v1) where
  core_id := by
    obtain ⟨H⟩ := Hdq
    simp [CMRA.pcore] at H
    simp only [CMRA.pcore, View.Pcore, some_eqv_some]
    refine NonExpansive₂.eqv trivial (point_core_eqv ?_)
    simp [CMRA.pcore, Prod.pcore]
    cases h : CMRA.pcore v1
    · exact not_none_eqv_some (h ▸ Hv1.core_id) |>.elim
    · simp only [Option.bind_some, H]
      exact ⟨rfl, some_eqv_some.mp (h ▸ Hv1.core_id)⟩

section WithMap

variable [IHHmap : ∀ V, HasHeapMap (H (DFrac F × V)) (H V) K (DFrac F × V) V]

nonrec theorem frag_validN_iff : ✓{n} Frag (H := H) k dq v1 ↔ ✓ dq ∧ ✓{n} v1 :=
  frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans point_validN_iff

theorem frag_valid_iff : ✓ Frag (H := H) k dq v1 ↔ ✓ dq ∧ ✓ v1 := by
  refine (forall_congr' (fun _ => frag_validN_iff)).trans ?_
  refine ⟨fun H => ?_, fun ⟨H1, H2⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp H1 n, valid_iff_validN.mp H2 n⟩

theorem frag_op_validN_iff :
    ✓{n} Frag (H := H) k dp v1 • Frag k dq v2 ↔ ✓ (dp • dq) ∧ ✓{n} (v1 • v2) := by
  refine View.frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans ?_
  refine (validN_iff <| equiv_dist.mp (eqv_of_Equiv point_op_point) _).trans ?_
  exact point_validN_iff

theorem frag_op_valid_iff :
    ✓ (Frag (H := H) k dp v1 • Frag k dq v2) ↔
    ✓ (dp • dq) ∧ ✓ (v1 • v2) := by
  suffices (∀ (n : Nat), ✓{n} dp • dq ∧ ✓{n} v1 • v2) ↔ ✓ dp • dq ∧ ✓ v1 • v2 by
    refine (forall_congr' (fun _ => ?_)).trans this
    refine (HeapR.exists_iff_validN ..).trans ?_
    refine (validN_iff <| equiv_dist.mp (eqv_of_Equiv point_op_point) _).trans ?_
    exact point_validN_iff
  refine ⟨fun H => ?_, fun ⟨Hp, Hv⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp Hp n, CMRA.valid_iff_validN.mp Hv n⟩

end WithMap

section heapUpdates

theorem update_one_alloc (Hfresh : get m1 k = none) (Hdq : ✓ dq) (Hval : ✓ v1) :
    Auth (.own one) m1 ~~> Auth (H := H) (.own one) (set m1 k <| some v1) • Frag k dq v1 := by
  refine auth_one_alloc (fun n bf Hrel j => ?_)
  simp only [CMRA.op, Store.op, get_merge, Option.merge, exists_and_left, Prod.forall]
  by_cases h : k = j
  · have Hbf : get bf j = none := by cases _ : get bf j <;> grind [HeapR]
    rw [point_get_eq h, Hbf]
    rintro _ _ ⟨rfl⟩
    exact ⟨v1, get_set_eq h, dq, ⟨Hdq, Hval.validN⟩, incN_refl _⟩
  · rw [point_get_ne h, get_set_ne h]
    simp only [HeapR, exists_and_left, Prod.forall] at Hrel
    cases Hbf : get bf j
    · grind
    exact (Hrel j · · <| · ▸ Hbf)

theorem update_one_delete :
    Auth (F := F) (.own one) m1 • Frag k (.own one) v1 ~~> Auth (.own one) (delete m1 k) := by
  refine auth_one_op_frag_dealloc <| fun n bf Hrel j => ?_
  match He : get bf j with
  | none =>
    intro _ HK
    simp at HK
  | some v =>
    by_cases h : k = j
    · specialize Hrel k
      simp only [CMRA.op, Store.op, get_merge, Option.merge, h, point_get_eq rfl, He,
                 Option.some.injEq, forall_eq'] at Hrel
      obtain ⟨_, _, _, Hqv, Hinc⟩ := Hrel
      have Hval := Option.validN_of_incN_validN (Hv := Hqv) (Hinc := Hinc)
      rcases v with ⟨(f|_|f), _⟩
      · exact one_whole.2 ⟨f, Hval.1⟩ |>.elim
      · exact one_whole.2 Hval.1 |>.elim
      · exact one_whole.2 ⟨f, Fraction.Fractional.proper Hval.1⟩ |>.elim
    · specialize Hrel j
      simp only [CMRA.op, Store.op, get_merge, exists_and_left, Prod.forall, point_get_ne h,
        He] at Hrel
      rintro ⟨a, b⟩ ⟨rfl⟩
      obtain ⟨v, H, q, H'⟩ := Hrel a b rfl
      exact ⟨v, q, H.symm ▸ get_set_ne h, H'⟩

theorem update_auth_op_frag
    (Hup :
      ∀ (n : Nat) (mv : V) (f : Option (DFrac F × V)), (get m1 k = some mv) →
      ✓{n} ((dq, v) •? f) → (mv ≡{n}≡ ((v : V) •? (Prod.snd <$> f))) →
      ✓{n} ((dq', v') •? f) ∧ (mv' ≡{n}≡ v' •? (Prod.snd <$> f))) :
    Auth (F := F) (.own one) m1 • Frag k dq v ~~>
    Auth (.own one) (set m1 k (some mv')) • Frag k dq' v' := by
  refine auth_one_op_frag_update fun n bf Hrel j ⟨df, va⟩ => ?_
  simp [CMRA.op, get_merge]
  by_cases h : k = j
  · simp only [point, get_set_eq h, Option.some.injEq, exists_eq_left']
    intro Hbf
    specialize Hrel k ((dq, v) •? Store.get bf k) ?G
    case G =>
      simp [CMRA.op, get_merge, point, op?]
      cases _ : get bf k <;> simp [Option.merge, get_set_eq rfl]
    obtain ⟨mv, mdf, Hlookup, Hval, Hincl'⟩ := Hrel
    obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl'
    clear Hincl'
    let f := get bf k • f'
    have Hincl' : (mdf, mv) ≡{n}≡ (dq, v) •? f := Hincl.trans Option.opM_opM_assoc.dist
    clear Hincl
    specialize Hup n mv f Hlookup (Hincl'.validN.mp Hval) ?G
    case G =>
      apply Hincl'.2.trans
      match f with
      | none => simp [CMRA.op?]
      | some ⟨_, _⟩ => simp [CMRA.op?, CMRA.op]
    obtain ⟨Hval', Hincl'⟩ := Hup
    exists (dq' •? Option.map Prod.fst f)
    constructor
    · refine validN_ne (x := (dq' •? Option.map Prod.fst f, v' •? Prod.snd <$> f))
        ⟨.rfl, Hincl'.symm⟩ ?_
      cases h : f <;> simp only [op?, Option.map_none, Option.map_eq_map]
      · exact validN_opM Hval'
      · simp only [h] at Hval'
        exact Hval'
    · rw [← Hbf]
      suffices HF : some ((dq', v') •? get bf j) ≼{n} some (dq' •? Option.map Prod.fst f, mv') by
        apply incN_trans ?_ HF
        cases _ : get bf j <;> exact incN_refl _
      refine Option.some_incN_some_iff_opM.mpr ?_
      exists f'
      refine (dist_prod_ext rfl Hincl').trans ?_
      refine .trans ?_ (equiv_dist.mp Option.opM_opM_assoc.symm _)
      obtain H : get bf j • f' = f := by rw [← h]
      rw [H]
      cases _ : f <;> rfl
  · simp [point, get_set_ne h, get_empty]
    intro Hbf
    have Hrel' := Hrel j (df, va)
    simp only [CMRA.op, Store.op, point, get_merge, Store.get_set_ne h, get_empty,
      exists_and_left] at Hrel'
    refine Hrel' ?_
    rw [← Hbf]
    simp

theorem update_of_local_update (Hl : get m1 k = some mv) (Hup : (mv, v) ~l~> (mv', v')) :
    Auth (F := F) (.own one) m1 • Frag k dq v ~~>
    Auth (.own one) (set m1 k (some mv')) • Frag k dq v' := by
  refine update_auth_op_frag (fun n mv0 f Hmv0 ⟨Hv1, Hv2⟩ Hincl => ?_)
  simp [Hl] at Hmv0
  subst Hmv0
  have Hup' := Hup n (Prod.snd <$> f) ?G1 Hincl
  case G1 =>
    refine validN_ne Hincl.symm ?_
    cases _ : f <;> simp_all [op?, CMRA.op]
  cases f <;> exact ⟨⟨Hv1, validN_ne Hup'.2 Hup'.1⟩, Hup'.2⟩

theorem update_replace (Hval' : ✓ v2) :
    Auth (.own one) m1 • Frag (F := F) k (.own one) v1 ~~>
    Auth (.own one) (set m1 k (some v2)) • Frag k (.own one) v2 := by
  refine update_auth_op_frag fun n mv f Hlookup Hval Hincl => ?_
  cases _ : f <;> simp only [Option.map_eq_map, Option.map_none]
  · simp_all only [op?, Dist.rfl, and_true]
    exact ⟨Hval.1, Valid.validN Hval'⟩
  · simp_all [CMRA.op?, CMRA.op, Prod.op]
    exact (own_whole_exclusive one_whole |>.exclusive0_l _ (valid0_of_validN Hval.1)).elim

theorem auth_dfrac_discard : Auth dq m1 ~~> Auth .discard m1 := auth_discard

theorem auth_dfrac_acquire [IsSplitFraction F] :
    Auth (F := F) .discard m1 ~~>: fun a => ∃ q, a = Auth (.own q) m1 :=
  auth_acquire

theorem update_of_dfrac_update P (Hdq : dq ~~>: P) :
    Frag (H := H) k dq v1 ~~>: fun a => ∃ dq', a = Frag k dq' v1 ∧ P dq' := by
  apply UpdateP.weaken
  · apply frag_updateP (P := fun b' => ∃ dq', (◯V b') = Frag k dq' v1 ∧ P dq')
    intro m n bf Hrel
    have Hrel' := Hrel k ((dq, v1) •? get bf k) ?G
    case G =>
      simp only [CMRA.op, Store.op, get_merge, point_get_eq rfl, op?]
      cases _ : get bf k <;> simp
    obtain ⟨v', dq', Hlookup, Hval, Hincl⟩ := Hrel'
    obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl
    replace Hincl := Hincl.trans (equiv_dist.mp Option.opM_opM_assoc _)
    replace Hdq := Hdq n (Option.map Prod.fst (get bf k • f')) ?G
    case G => cases h : get bf k • f' <;> exact validN_ne (h ▸ Hincl).1 Hval.1
    obtain ⟨dq'', HPdq'', Hvdq''⟩ := Hdq
    exists point k (dq'', v1)
    refine ⟨⟨dq'', rfl, HPdq''⟩, fun j ⟨df, va⟩ Heq => ?_⟩
    by_cases h : k = j
    · simp [CMRA.op, get_merge, point_get_eq h] at Heq
      refine ⟨v', dq'' •? (Option.map Prod.fst <| (Store.get bf k) • f'), ?_⟩
      refine ⟨h ▸ Hlookup, ⟨Hvdq'', Hval.2⟩, f', ?_⟩
      cases _ : f' <;> cases _ : get bf k <;>
        simp [Dist, Option.Forall₂, CMRA.op?] <;>
        simp_all [CMRA.op, op?, Prod.op] <;>
        try exact Hincl.2
      exact ⟨Heq.1.symm ▸ op_assocN, Heq.2.symm ▸ Hincl.2.trans op_assocN⟩
    · apply Hrel
      simp [CMRA.op, get_merge, point_get_ne h] at Heq ⊢
      exact Heq
  · rintro y ⟨b, rfl, q, _, _⟩
    exists q

theorem update_frag_discard : Frag (H := H) k dq v1 ~~> Frag k .discard v1 :=
  .lift_updateP (Frag k · v1) _ _ update_of_dfrac_update DFrac.update_discard

theorem update_frag_acquire [IsSplitFraction F] :
    (Frag k .discard v1 : HeapView F K V H) ~~>: fun a => ∃ q, a = Frag k (.own q) v1 := by
  apply UpdateP.weaken (update_of_dfrac_update _ DFrac.update_acquire)
  rintro y ⟨q, rfl, ⟨q1, rfl⟩⟩
  exists q1

end heapUpdates

section heapViewFunctor

variable [∀ α β, HasHeapMap (H α) (H β) K α β]

theorem heapR_map_eq [OFE A] [OFE B] [OFE A'] [OFE B'] [RFunctor T] (f : A' -n> A) (g : B -n> B') (n : Nat) (m : H (T A B)) (mv : H (DFrac F × T A B)) :
    HeapR F K (T A B) H n m mv →
    HeapR F K (T A' B') H n ((Heap.mapO H (RFunctor.map f g).toHom).f m) ((Heap.mapC H (Prod.mapC (CMRA.Hom.id (α := DFrac F)) (RFunctor.map (F:=T) f g))).f mv) := by
  simp [HeapR, Heap.mapC, Heap.mapO, Heap.map', CMRA.Hom.id, OFE.Hom.id, Prod.mapC, hhmap_get]
  intros hr k a b
  rcases h : Store.get mv k with _ | ⟨a,b⟩ <;> simp
  rintro rfl rfl
  obtain ⟨v, hq, ⟨fr, ⟨hv1, hv2⟩, ho⟩⟩ := hr k a b h
  exists (RFunctor.map f g).f v
  constructor
  simp [hq]
  exists fr
  constructor
  · constructor <;> simp_all
    exact (Hom.validN _ hv2)
  · rw [Option.incN_iff] at ho ⊢
    rcases ho with _ | he <;> simp_all
    rcases he with ⟨he1, he2⟩ | he
    · left
      constructor <;> simp_all
      exact (NonExpansive.ne he2)
    · right
      rw [<-Prod.incN_iff] at *
      rcases he with ⟨_ , he⟩
      constructor
      simp_all
      apply (Hom.monoN _ _ he)

abbrev HeapViewURF T [RFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => HeapView F K (T A B) H

instance {T} [RFunctor T] : URFunctor (HeapViewURF (F := F) (H := H) T) where
  map {A A'} {B B'} _ _ _ _ f g := View.mapC (Heap.mapO H (RFunctor.map (F:=T) f g).toHom) (Heap.mapC H (Prod.mapC Hom.id (RFunctor.map (F:=T) f g))) (heapR_map_eq f g)
  map_ne.ne a b c Hx d e Hy mv := by
    simp [View.mapC]
    apply View.map_ne
    · intro
      apply Heap.map_ne
      apply RFunctor.map_ne.ne <;> simp_all
    · intro m
      apply Heap.map_ne
      intro a
      apply Prod.map_ne
      simp
      apply RFunctor.map_ne.ne <;> simp_all
  map_id x := by
    -- rw [View.map_id]
    sorry
  map_comp f g f' g' x := by
    sorry

instance {T} [RFunctorContractive T] : URFunctorContractive (HeapViewURF (F := F) (H := H) T) where
  map_contractive.1 H _ := sorry

end heapViewFunctor

end HeapView
