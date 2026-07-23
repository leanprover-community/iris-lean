/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu
-/
module

public import Iris.Algebra.Heap
public import Iris.Algebra.View
public import Iris.Algebra.DFrac
public import Iris.Algebra.Frac
public import Iris.Algebra.BigOp

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

@[expose] public section

open Iris

section heapView
open Std PartialMap Heap OFE CMRA

variable (K V : Type _) (H : Type _ → Type _) [LawfulPartialMap H K] [CMRA V]

/-- The view relation for heaps: relates a model heap to a fragment heap at step index `n`. -/
def HeapR (n : Nat) (m : H V) (f : H (DFrac × V)) : Prop :=
  ∀ k fv, get? f k = some fv →
    ∃ (v : V) (dq : DFrac), get? m k = some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))

instance : IsViewRel (HeapR K V H) where
  mono {n1 m1 f1 n2 m2 f2 Hrel Hm Hf Hn k} vk Hk := by
    obtain Hf' : ∃ z, get? f1 k ≡{n2}≡ some vk • z := by
      have ⟨z, Hz⟩ := lookup_incN (n := n2) (m1 := f2) (m2 := f1) |>.1 Hf k
      exact ⟨z, Hk ▸ Hz⟩
    match h : get? f1 k with
    | none => rcases h ▸ Hf' with ⟨_|_, HK⟩ <;> simp [CMRA.op, optionOp] at HK
    | some ⟨dq', v'⟩ =>
      obtain ⟨v, dq, Hm1, ⟨Hvval, Hdqval⟩, Hvincl⟩ := Hrel k ⟨dq', v'⟩ h
      obtain ⟨v', Hm2, Hv⟩ : ∃ y : V, get? m2 k = some y ∧ v ≡{n2}≡ y := by
        have Hmm := Hm1 ▸ Hm k <;> revert Hmm
        cases get? m2 k <;> simp
      exists v', dq
      refine ⟨Hm2, ⟨Hvval, validN_ne Hv (validN_of_le Hn Hdqval)⟩, ?_⟩
      suffices some vk ≼{n2} some (dq, v) by exact incN_of_incN_of_dist this ⟨rfl, Hv⟩
      refine incN_trans Hf' ?_
      refine incN_trans ?_ (incN_of_incN_le Hn Hvincl)
      rw [h]
  rel_validN n m f Hrel k := by
    match Hf : get? f k with
    | none => simp [ValidN, optionValidN]
    | some _ =>
      obtain ⟨_, _, _, Hvv, Hvi⟩ := Hf ▸ Hrel k _ Hf
      exact (Hf ▸ validN_of_incN Hvi Hvv)
  rel_unit n := by
    refine ⟨empty, fun _ _ => ?_⟩
    simp [UCMRA.unit, Heap.unit, get?_empty]

namespace HeapR

theorem unit : HeapR K V H n m UCMRA.unit := by
  simp [HeapR, UCMRA.unit, Heap.unit, get?_empty]

theorem exists_iff_validN {n f} : (∃ m, HeapR K V H n m f) ↔ ✓{n} f := by
  refine ⟨fun ⟨m, Hrel⟩ => IsViewRel.rel_validN _ _ _ Hrel, fun Hv => ?_⟩
  let FF : K → (DFrac × V) → Option V := fun k _ => get? f k |>.bind (·.2)
  refine ⟨bindAlter FF f, fun k => ?_⟩
  cases h : get? f k
  · simp
  simp only [Option.some.injEq, exists_and_left]
  rintro ⟨dq, v⟩ rfl
  exists v
  simp only [get?_bindAlter, h, Option.bind_some, true_and, FF]
  exact ⟨dq, (h ▸ Hv k : ✓{n} some (dq, v)), incN_refl _⟩

theorem singleton_get_iff n m k dq v :
    HeapR K V H n m (PartialMap.singleton k (dq, v)) ↔
      ∃ (v' : V) (dq' : DFrac),
        get? m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := by
  constructor
  · refine fun Hrel => Hrel k (dq, v) ?_
    rw [PartialMap.singleton, get?_insert_eq rfl]
  · rintro ⟨v', dq', Hlookup, Hval, Hinc⟩ j fv Hfv
    by_cases h : k = j
    · rw [PartialMap.singleton, get?_insert_eq h] at Hfv
      cases Hfv
      exact ⟨v', dq', h ▸ Hlookup, Hval, Hinc⟩
    · rw [PartialMap.singleton, get?_insert_ne h, get?_empty] at Hfv
      cases Hfv

instance [CMRA.Discrete V] : IsViewRelDiscrete (HeapR K V H) where
  discrete n _ _ H k v He := by
    have ⟨v, Hv1, ⟨x, Hx1, Hx2⟩⟩ := H k v He
    refine ⟨v, Hv1, ⟨x, ?_, inc_0_iff_incN n |>.mp Hx2⟩⟩
    exact ⟨Hx1.1, valid_iff_validN.mp (Discrete.discrete_valid Hx1.2) _⟩

end HeapR

/-- A view of a Heap, that gives element-wise ownership. -/
abbrev HeapView := View (HeapR K V H)

end heapView

namespace HeapView

open Heap OFE View One DFrac CMRA PartialMap Std LawfulPartialMap

variable {K V : Type _} {H : Type _ → Type _} [LawfulPartialMap H K] [CMRA V]

/-- Authoritative (fractional) ownership over an entire heap. -/
def Auth (dq : DFrac) (m : H V) : HeapView K V H := ●V{dq} m

/-- Fragmental (fractional) ownership over an allocated element in the heap. -/
def Frag (k : K) (dq : DFrac) (v : V) : HeapView K V H := ◯V (Std.PartialMap.singleton k (dq, v))

/-- Fragmental (fractional) ownership over an element in the heap. -/
def Elem (k : K) (v : DFrac × V) : HeapView K V H := ◯V (Std.PartialMap.singleton k v)

-- TODO: Do we need this?
instance : NonExpansive (Auth dq : _ → HeapView K V H) := View.auth_ne

instance : NonExpansive (Frag k dq : _ → HeapView K V H) where
  ne _ _ _ Hx := by
    refine frag_ne.ne (fun k' => ?_)
    by_cases h : k = k'
    · rw [Std.PartialMap.singleton, get?_insert_eq h, get?_singleton_eq h]
      exact dist_prod_ext rfl Hx
    · rw [Std.PartialMap.singleton, get?_insert_ne h, get?_empty, get?_singleton_ne h]

variable {dp dq : DFrac} {n : Nat} {m1 m2 : H V} {k : K} {v1 v2 : V}

theorem auth_dfrac_op_eqv : Auth (dp • dq) m1 = Auth dp m1 • Auth dq m1 :=
  View.auth_op_auth_eqv

/-- An `Auth` inclusion follows from a map equality on the underlying heap.
This is the workhorse for proofs that rewrite the authoritative map along identities like
`PartialMap.map_insert`, `map_delete`, or `map_union`. -/
theorem auth_inc_of_map_eq (dq : DFrac) (h : m1 = m2) :
    Auth dq m1 ≼ Auth dq m2 :=
  by rw [h]

theorem dist_of_validN_auth_op : ✓{n} Auth dp m1 • Auth dq m2 → m1 ≡{n}≡ m2 :=
  dist_of_validN_auth

theorem equiv_of_valid_auth_op : ✓ Auth dp m1 • Auth dq m2 → m1 = m2 :=
  eq_of_valid_auth

nonrec theorem auth_validN_iff : ✓{n} Auth dq m1 ↔ ✓ dq :=
  auth_validN_iff.trans <| and_iff_left_of_imp (fun _ => HeapR.unit _ _ _)

nonrec theorem auth_valid_iff : ✓ Auth dq m1 ↔ ✓ dq :=
  auth_valid_iff.trans <| and_iff_left_of_imp (fun _ _ => HeapR.unit _ _ _)

theorem auth_one_valid : ✓ Auth (.own one) m1 := auth_valid_iff.mpr valid_own_one

nonrec theorem auth_op_auth_validN_iff : ✓{n} Auth dp m1 • Auth dq m2 ↔ ✓ dp • dq ∧ m1 ≡{n}≡ m2 :=
  auth_op_auth_validN_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ => HeapR.unit _ _ _

nonrec theorem auth_op_auth_valid_iff : ✓ Auth dp m1 • Auth dq m2 ↔ ✓ dp • dq ∧ m1 = m2 :=
  auth_op_auth_valid_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ _ => HeapR.unit _ _ _

nonrec theorem auth_one_op_auth_one_validN_iff :
    ✓{n} Auth (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_validN_iff

nonrec theorem auth_one_op_auth_one_valid_iff :
    ✓ Auth (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_valid_iff


theorem frag_op_eqv : Frag (H := H) k (dp • dq) (v1 • v2) = Frag (H := H) k dp v1 • Frag k dq v2 :=
  congrArg (◯V ·) (eqv_of_Equiv (singleton_op_singleton (x := (dp, v1)) (y := (dq, v2)))).symm

set_option synthInstance.checkSynthOrder false in
instance
  [hdp : IsOp io1 dp io2 dp1 io3 dp2]
  [hv : IsOp io1 v io2 v1 io3 v2] :
  IsOp io1 (Frag k dp v) io2 (Frag k dp1 v1) io3 (Frag (H := H) k dp2 v2) where
  is_op := by
    rw [hdp.is_op, hv.is_op]
    exact frag_op_eqv

theorem frag_add_op_eqv {q1 q2 : Qp} :
    Frag (H := H) k (.own (q1 + q2)) (v1 • v2) = Frag (H := H) k (.own q1) v1 • Frag k (.own q2) v2 :=
  frag_op_eqv (dp := .own q1) (dq := .own q2)

nonrec theorem auth_op_frag_validN_iff :
    ✓{n} Auth dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓ dp ∧ (Std.PartialMap.get? m1 k = some v') ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') :=
  auth_op_frag_validN_iff.trans <|
    (and_congr_right fun _ => (HeapR.singleton_get_iff ..).trans <|
    exists_congr fun _ => exists_and_left).trans (by grind)

theorem auth_op_frag_one_validN_iff :
    ✓{n} (Auth dp m1 • Frag k (.own one) v1) ↔ ✓ dp ∧ ✓{n} v1 ∧ Std.PartialMap.get? m1 k ≡{n}≡ some v1 := by
  refine auth_op_frag_validN_iff.trans ⟨fun ⟨Hp, v', dq', Hl, Hv, Hi⟩ => ?_, fun ⟨Hp, Hv, Hl⟩ => ?_⟩
  · have Heq : v1 ≡{n}≡ Hp := Option.dist_of_inc_exclusive Hi Hv |>.2
    exact ⟨dq', validN_ne Heq.symm Hv.2, Hl ▸ Heq.symm⟩
  · match h : Std.PartialMap.get? m1 k with
    | none => simp [h] at Hl
    | some v' =>
      exists v', .own one
      refine ⟨Hp, rfl, ?_, ?_⟩
      · exact ⟨valid_own_one, Dist.validN (h ▸ Hl).symm |>.mp Hv⟩
      · exact Option.some_incN_some_iff.mpr <| .inl <| dist_prod_ext rfl (h.symm ▸ Hl).symm

theorem auth_op_frag_validN_total_iff [IsTotal V] (H : ✓{n} Auth dp m1 • Frag k dq v1) :
    ∃ v', ✓ dp ∧ ✓ dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓{n} v' ∧ v1 ≼{n} v' := by
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
      ∃ v' dq', ✓ dp ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓ (dq', v') ∧ some (dq, v1) ≼ some (dq', v') := by
  refine valid_iff_validN.trans ?_
  refine forall_congr' (fun _ => auth_op_frag_validN_iff) |>.trans ?_
  refine ⟨fun Hvalid' => ?_, ?_⟩
  · obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := Hvalid' 0
    refine ⟨v', dq', Hdp, Hl, ?_, inc_iff_incN 0 |>.mpr Hi⟩
    exact ⟨discrete_valid Hv.1, discrete_valid Hv.2⟩
  · exact fun ⟨v', dq', Hdp, Hl, Hv, Hi⟩ n => ⟨v', dq', Hdp, Hl, Hv.validN, inc_iff_incN n |>.mp Hi⟩

theorem auth_op_frag_valid_total_discrete_iff [IsTotal V] [CMRA.Discrete V]
    (H : ✓ Auth dp m1 • Frag k dq v1) :
    ∃ v', ✓ dp ∧ ✓ dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓ v' ∧ v1 ≼ v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := auth_op_frag_discrete_valid_iff |>.mp H
  refine ⟨v', Hdp, ?_, Hl, Hv.2, ?_⟩
  · rcases Hi with ⟨(_|x), Hx⟩
    · exact (show dq' = dq from
        (OFE.equiv_dist.mpr (fun n => (Equiv.of_eq (some_eqv_some.mp Hx) n).1)).to_eq) ▸ Hv.1
    · exact Option.valid_of_inc_valid Hv.1 ⟨some x.fst, congrArg (fun p => some p.fst) (some_eqv_some.mp Hx)⟩
  · rcases Hi with ⟨(_|x), Hx⟩
    · rw [show v1 = v' from
        (OFE.Equiv.symm (fun n => (Equiv.of_eq (some_eqv_some.mp Hx) n).2)).to_eq]
    · exact ⟨x.snd, congrArg Prod.snd (some_eqv_some.mp Hx)⟩

theorem auth_op_frag_one_valid_iff :
    ✓ Auth dp m1 • Frag k (.own one) v1 ↔ ✓ dp ∧ ✓ v1 ∧ Std.PartialMap.get?  m1 k = some v1 := by
  refine valid_iff_validN.trans ?_
  refine forall_congr' (fun _ => auth_op_frag_one_validN_iff) |>.trans ?_
  refine ⟨fun Hv => ?_, ?_⟩
  · exact ⟨Hv 0 |>.1, valid_iff_validN.mpr (Hv · |>.2.1),
      OFE.Equiv.to_eq (equiv_dist.mpr (Hv · |>.2.2))⟩
  · exact fun ⟨Hdp, Hv, Hl⟩ n => ⟨Hdp, Hv.validN, Hl.dist⟩

instance [Hdq : CoreId dq] [Hv1 : CoreId v1] : CoreId (Frag (H := H) k dq v1) where
  core_id := by
    obtain ⟨H⟩ := Hdq
    simp [CMRA.pcore] at H
    simp only [CMRA.pcore, View.Pcore]
    refine OFE.Equiv.to_eq ?_
    refine Equiv.of_eq (congrArg some (congrArg (View.mk _) (singleton_core_eqv ?_)))
    simp [CMRA.pcore, Prod.pcore]
    cases h : CMRA.pcore v1
    · exact OFE.not_none_eqv_some (h ▸ Hv1.core_id) |>.elim
    · simp only [Option.bind_some, H]
      exact OFE.some_eqv_some.mpr
        (congrArg (Prod.mk _) (OFE.some_eqv_some.mp (h ▸ Hv1.core_id)))

nonrec theorem frag_validN_iff : ✓{n} Frag (H := H) k dq v1 ↔ ✓ dq ∧ ✓{n} v1 :=
  frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans singleton_validN_iff

theorem frag_valid_iff : ✓ Frag (H := H) k dq v1 ↔ ✓ dq ∧ ✓ v1 := by
  refine (forall_congr' (fun _ => frag_validN_iff)).trans ?_
  refine ⟨fun H => ?_, fun ⟨H1, H2⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp H1 n, valid_iff_validN.mp H2 n⟩

theorem frag_op_validN_iff :
    ✓{n} Frag (H := H) k dp v1 • Frag k dq v2 ↔ ✓ (dp • dq) ∧ ✓{n} (v1 • v2) := by
  refine View.frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans ?_
  refine (validN_dist_iff (eqv_of_Equiv singleton_op_singleton).dist).trans ?_
  exact singleton_validN_iff

theorem frag_op_valid_iff :
    ✓ (Frag (H := H) k dp v1 • Frag k dq v2) ↔
    ✓ (dp • dq) ∧ ✓ (v1 • v2) := by
  suffices (∀ (n : Nat), ✓{n} dp • dq ∧ ✓{n} v1 • v2) ↔ ✓ dp • dq ∧ ✓ v1 • v2 by
    refine (forall_congr' (fun _ => ?_)).trans this
    refine (HeapR.exists_iff_validN ..).trans ?_
    refine (validN_dist_iff (eqv_of_Equiv singleton_op_singleton).dist).trans ?_
    exact singleton_validN_iff
  refine ⟨fun H => ?_, fun ⟨Hp, Hv⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp Hp n, CMRA.valid_iff_validN.mp Hv n⟩

section heapUpdates

theorem update_one_alloc (Hfresh : Std.PartialMap.get? m1 k = none) (Hdq : ✓ dq) (Hval : ✓ v1) :
    Auth (.own one) m1 ~~> Auth (H := H) (.own one) (Std.PartialMap.insert m1 k v1) • Frag k dq v1 := by
  refine auth_one_alloc (fun n bf Hrel j => ?_)
  simp only [CMRA.op, Heap.op, get?_merge, Option.merge, exists_and_left, Prod.forall]
  by_cases h : k = j
  · have Hbf : Std.PartialMap.get? bf j = none := by cases _ : Std.PartialMap.get? bf j <;> grind [HeapR]
    rw [get?_singleton_eq h, Hbf]
    rintro _ _ ⟨rfl⟩
    exact ⟨v1, get?_insert_eq h, dq, ⟨Hdq, Hval.validN⟩, incN_refl _⟩
  · rw [get?_singleton_ne h, get?_insert_ne h]
    simp only [HeapR, exists_and_left, Prod.forall] at Hrel
    cases Hbf : Std.PartialMap.get? bf j
    · grind
    exact (Hrel j · · <| · ▸ Hbf)

theorem update_one_delete :
    Auth (.own one) m1 • Frag k (.own one) v1 ~~> Auth (.own one) (Std.PartialMap.delete m1 k) := by
  refine auth_one_op_frag_dealloc <| fun n bf Hrel j => ?_
  match He : Std.PartialMap.get? bf j with
  | none =>
    intro _ HK
    simp at HK
  | some v =>
    by_cases h : k = j
    · specialize Hrel k
      simp only [CMRA.op, Heap.op, get?_merge, Option.merge, h, get?_singleton_eq rfl, He,
                 Option.some.injEq, forall_eq'] at Hrel
      obtain ⟨_, _, _, Hqv, Hinc⟩ := Hrel
      have Hval := Option.validN_of_incN_validN (Hv := Hqv) (Hinc := Hinc)
      -- `own 1` is exclusive, so it cannot validly compose with the frame's fraction
      exact (own_whole_exclusive.exclusive0_l _ (valid0_of_validN Hval.1)).elim
    · specialize Hrel j
      simp only [CMRA.op, Heap.op, get?_merge, exists_and_left, Prod.forall, get?_singleton_ne h,
        He] at Hrel
      rintro ⟨a, b⟩ ⟨rfl⟩
      obtain ⟨v, H, q, H'⟩ := Hrel a b rfl
      exact ⟨v, q, H.symm ▸ get?_delete_ne h, H'⟩

theorem update_auth_op_frag
    (Hup :
      ∀ (n : Nat) (mv : V) (f : Option (DFrac × V)), (Std.PartialMap.get? m1 k = some mv) →
      ✓{n} ((dq, v) •? f) → (mv ≡{n}≡ ((v : V) •? (Prod.snd <$> f))) →
      ✓{n} ((dq', v') •? f) ∧ (mv' ≡{n}≡ v' •? (Prod.snd <$> f))) :
    Auth (.own one) m1 • Frag k dq v ~~>
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq' v' := by
  refine auth_one_op_frag_update fun n bf Hrel j ⟨df, va⟩ => ?_
  simp [CMRA.op, get?_merge]
  by_cases h : k = j
  · simp only [get?_insert_eq h, Option.some.injEq, exists_eq_left']
    intro Hbf
    specialize Hrel k ((dq, v) •? Std.PartialMap.get? bf k) ?G
    case G =>
      simp [CMRA.op, get?_merge, op?]
      cases _ : Std.PartialMap.get? bf k <;> simp [Option.merge, get?_singleton_eq rfl]
    obtain ⟨mv, mdf, Hlookup, Hval, Hincl'⟩ := Hrel
    obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl'
    clear Hincl'
    let f := Std.PartialMap.get? bf k • f'
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
      suffices HF : some ((dq', v') •? Std.PartialMap.get? bf j) ≼{n} some (dq' •? Option.map Prod.fst f, mv') by
        subst h
        rename_i HH
        simp [f] at HH
        apply incN_trans ?_ HF
        simp [Option.merge, CMRA.op?]
        split <;> simp_all
        · rename_i H1 H2
          simp [← H1, get?_singleton_eq rfl]
          exact incN_refl _
        · rename_i H1 H2
          exfalso
          simp [get?_singleton_eq rfl] at H1
        · rename_i H1 H2
          simp [get?_singleton_eq rfl] at H1
          simp [← H1]
          exact incN_refl _
      refine Option.some_incN_some_iff_opM.mpr ?_
      exists f'
      refine (dist_prod_ext rfl Hincl').trans ?_
      refine .trans ?_ Option.opM_opM_assoc.symm.dist
      obtain H : Std.PartialMap.get? bf j • f' = f := by rw [← h]
      rw [H]
      cases _ : f <;> rfl
  · simp [get?_insert_ne h]
    intro Hbf
    have Hrel' := Hrel j (df, va)
    simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_ne h,  exists_and_left] at Hrel'
    refine Hrel' ?_
    rw [← Hbf]
    simp [get?_singleton_ne h]

theorem update_of_local_update (Hl : Std.PartialMap.get? m1 k = some mv) (Hup : (mv, v) ~l~> (mv', v')) :
    Auth (.own one) m1 • Frag k dq v ~~>
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq v' := by
  refine update_auth_op_frag (fun n mv0 f Hmv0 ⟨Hv1, Hv2⟩ Hincl => ?_)
  simp [Hl] at Hmv0
  subst Hmv0
  have Hup' := Hup n (Prod.snd <$> f) ?G1 Hincl
  case G1 =>
    refine validN_ne Hincl.symm ?_
    cases _ : f <;> simp_all [op?, CMRA.op]
  cases f <;> exact ⟨⟨Hv1, validN_ne Hup'.2 Hup'.1⟩, Hup'.2⟩

theorem update_replace (Hval' : ✓ v2) :
    Auth (.own one) m1 • Frag k (.own one) v1 ~~>
    Auth (.own one) (Std.PartialMap.insert m1 k v2) • Frag k (.own one) v2 := by
  refine update_auth_op_frag fun n mv f Hlookup Hval Hincl => ?_
  cases _ : f <;> simp only [Option.map_eq_map, Option.map_none]
  · simp_all only [op?, Dist.rfl, and_true]
    exact ⟨Hval.1, Valid.validN Hval'⟩
  · simp_all [CMRA.op?, CMRA.op, Prod.op]
    exact (own_whole_exclusive.exclusive0_l _ (valid0_of_validN Hval.1)).elim

theorem auth_dfrac_discard : Auth dq m1 ~~> Auth .discard m1 := auth_discard

theorem auth_dfrac_acquire :
    Auth .discard m1 ~~>: fun a => ∃ q, a = Auth (.own q) m1 :=
  auth_acquire

theorem update_of_dfrac_update P (Hdq : dq ~~>: P) :
    Frag (H := H) k dq v1 ~~>: fun a => ∃ dq', a = Frag k dq' v1 ∧ P dq' := by
  apply UpdateP.weaken
  · apply frag_updateP (P := fun b' => ∃ dq', (◯V b') = Frag k dq' v1 ∧ P dq')
    intro m n bf Hrel
    have Hrel' := Hrel k ((dq, v1) •? Std.PartialMap.get? bf k) ?G
    case G =>
      simp only [CMRA.op, Heap.op, get?_merge, get?_singleton_eq rfl, op?]
      cases _ : Std.PartialMap.get? bf k <;> simp
    obtain ⟨v', dq', Hlookup, Hval, Hincl⟩ := Hrel'
    obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl
    replace Hincl := Hincl.trans Option.opM_opM_assoc.dist
    replace Hdq := Hdq n (Option.map Prod.fst (Std.PartialMap.get? bf k • f')) ?G
    case G => cases h : Std.PartialMap.get? bf k • f' <;> exact validN_ne (h ▸ Hincl).1 Hval.1
    obtain ⟨dq'', HPdq'', Hvdq''⟩ := Hdq
    exists Std.PartialMap.singleton k (dq'', v1)
    refine ⟨⟨dq'', rfl, HPdq''⟩, fun j ⟨df, va⟩ Heq => ?_⟩
    by_cases h : k = j
    · simp [CMRA.op, get?_merge, get?_singleton_eq h] at Heq
      refine ⟨v', dq'' •? (Option.map Prod.fst <| (Std.PartialMap.get? bf k) • f'), ?_⟩
      refine ⟨h ▸ Hlookup, ⟨Hvdq'', Hval.2⟩, f', ?_⟩
      cases _ : f' <;> cases _ : Std.PartialMap.get? bf k <;>
        simp [Dist, Option.Forall₂, CMRA.op?] <;>
        simp_all [CMRA.op, op?, Prod.op] <;>
        try exact Hincl.2
      exact ⟨Heq.1.symm ▸ assoc_L, Heq.2.symm ▸ Hincl.2.trans op_assocN⟩
    · apply Hrel
      simp [CMRA.op, get?_merge, get?_singleton_ne h] at Heq ⊢
      exact Heq
  · rintro y ⟨b, rfl, q, _, _⟩
    exists q

theorem update_frag_discard : Frag (H := H) k dq v1 ~~> Frag k .discard v1 :=
  .lift_updateP (Frag k · v1) _ _ update_of_dfrac_update DFrac.update_discard

theorem update_frag_acquire :
    (Frag k .discard v1 : HeapView K V H) ~~>: fun a => ∃ q, a = Frag k (.own q) v1 := by
  apply UpdateP.weaken (update_of_dfrac_update _ DFrac.update_acquire)
  rintro y ⟨q, rfl, ⟨q1, rfl⟩⟩
  exists q1

end heapUpdates

section heapViewFunctor

open Iris.Std PartialMap

theorem heapR_map_eq [COFE A] [COFE B] [COFE A'] [COFE B'] [RFunctor T] (f : A' -n> A) (g : B -n> B')
    (n : Nat) (m : H (T A B)) (mv : H (DFrac × T A B)) :
    HeapR K (T A B) H n m mv →
    HeapR K (T A' B') H n
      ((mapO H (RFunctor.map f g).toHom).f m)
      ((mapC H (Prod.mapC (CMRA.Hom.id (α := DFrac))
      (RFunctor.map (F:=T) f g))).f mv) := by
  simp [HeapR, PartialMap.mapC, PartialMap.mapO, PartialMap.map, CMRA.Hom.id, OFE.Hom.id, Prod.mapC, get?_bindAlter]
  intros hr k a b
  rcases h : get? mv k with _ | ⟨a,b⟩ <;> simp
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
      · simp_all
      · exact (Hom.monoN _ _ he)

abbrev HeapViewURF T [RFunctor T] : COFE.OFunctorPre :=
  fun A B _ _ => HeapView K (T A B) H

instance {T} [RFunctor T] : URFunctor (HeapViewURF (H := H) T) where
  map {A A'} {B B'} _ _ _ _ f g :=
    View.mapC
      (PartialMap.mapO H (RFunctor.map f g).toHom)
      (PartialMap.mapC H (Prod.mapC Hom.id (RFunctor.map f g)))
      (heapR_map_eq f g)
  map_ne.ne n _ _ Hx _ _ Hy mv := by
    apply View.map_ne
    · refine fun _ => ?_
      apply PartialMap.map_ne
      exact RFunctor.map_ne.ne Hx Hy
    · refine fun _ => ?_
      apply PartialMap.map_ne _ _ _
      exact fun _ => Prod.map_ne (fun _ => rfl) (RFunctor.map_ne.ne Hx Hy)
  map_id x := by
    rw (config := { occs := .pos [2] }) [<- (View.map_id x)]
    refine OFE.Equiv.to_eq (equiv_dist.mpr fun n => View.map_ne x (fun a => ?_) (fun b => ?_))
    · exact (COFE.OFunctor.map_id (F := PartialMapOF H T) a).dist
    · refine OFE.Dist.trans ?_ (OFE.Equiv.of_eq (map_id _ b)).dist
      apply PartialMap.map_ne
      exact fun _ => ⟨rfl, (RFunctor.map_id _).dist⟩
  map_comp f g f' g' x := by
    simp [View.mapC]
    rw [<- View.map_compose']
    refine OFE.Equiv.to_eq (equiv_dist.mpr fun n => View.map_ne x (fun a => (?_ : _ ≡ _).dist) (fun b => (?_ : _ ≡ _).dist))
    · exact Equiv.of_eq ((inferInstance : URFunctor (PartialMapOF H T)).map_comp _ _ _ _ a)
    · simp only [Prod.mapC, CMRA.Hom.id, PartialMap.mapC]
      refine .trans ?_ (OFE.Equiv.of_eq (PartialMap.map_compose _ _ _ _))
      apply OFE.Equiv.of_eq
      refine congrArg (PartialMap.map _ · _) ?_
      rw [Prod.map_comp_map]
      refine funext fun p => ?_
      exact Prod.ext rfl (RFunctor.map_comp _ _ _ _ p.2)

instance {T} [RFunctorContractive T] : URFunctorContractive (HeapViewURF (H := H) T) where
  map_contractive.1 H _ := by
    apply View.map_ne <;> intros <;> apply PartialMap.map_ne
    · exact (RFunctorContractive.map_contractive.1 H)
    · exact (fun _ => Prod.map_ne (fun _ => rfl) (RFunctorContractive.map_contractive.1 H))

end heapViewFunctor

end HeapView

section FiniteHeapView
open Std PartialMap Heap OFE CMRA HeapView
open One DFrac LawfulPartialMap Algebra

variable {K V : Type _} {H : Type _ → Type _} [DecidableEq K] [LawfulFiniteMap H K] [CMRA V]

omit [DecidableEq K] in
private theorem bigOpM_frag_empty (dq : DFrac) :
    bigOpM (M := HeapView K V H) op (fun k x => Frag k dq x) (∅ : H V) = UCMRA.unit :=
  BigOpM.bigOpM_empty (M := HeapView K V H) (M' := H) (K := K) (op := op) (V := V) _

theorem update_big_delete (m m' : H V) :
  Auth (.own one) m • (bigOpM (M := HeapView K V H) op (fun k v => Frag k (.own one) v) m') ~~>
  Auth (.own one) (m \ m') := by
  induction m' using LawfulFiniteMap.induction_on with
  | hemp =>
    rw [bigOpM_frag_empty, CMRA.unit_right_id]
    refine Trans.trans Update.id (OFE.Equiv.symm ?_)
    refine Equiv.of_eq (congrArg _ (OFE.Equiv.to_eq ?_))
    refine OFE.Equiv.of_eq (eqv_of_Equiv (fun j => ?_))
    simp [get?_difference, get?_empty]
  | hins k v m2 Hm2 IH =>
    rw [← congrArg (CMRA.op _) (BigOpM.bigOpM_insert_eqv _ _ Hm2).symm]
    rw [← congrArg (CMRA.op _) CMRA.comm]
    rw [CMRA.assoc]
    refine (Update.op IH .id).trans ?_
    refine update_one_delete.trans ?_
    refine Trans.trans Update.id (OFE.Equiv.symm ?_)
    refine Equiv.of_eq (congrArg _ (OFE.Equiv.to_eq ?_))
    refine OFE.Equiv.of_eq (eqv_of_Equiv (fun j => ?_))
    by_cases hjk : k = j
      <;> simp [get?_difference, get?_delete_eq, get?_delete_ne, get?_insert_eq, get?_insert_ne, hjk]

theorem update_big_replace (m m0 m1 : H V)
  (Hdom : dom m0 = dom m1)
  (Hall : all (fun _ v => ✓ v) m1) :
  Auth (.own one) m • (bigOpM (M := HeapView K V H) op (fun k v => Frag k (.own one) v) m0) ~~>
  Auth (.own one) (m1 ∪ m) • (bigOpM (M := HeapView K V H) op (fun k v => Frag k (.own one) v) m1) := by
  revert m1 Hdom
  induction m0 using LawfulFiniteMap.induction_on with
  | hemp =>
    intro m1 Hdom Hall
    rw [bigOpM_frag_empty, CMRA.unit_right_id]
    have Heq : m1 = ∅ := by
      apply Std.LawfulPartialMap.equiv_iff_eq.mp; intro j; have h := congrFun Hdom.symm j
      simp [dom, get?_empty] at h; simp [get?_empty, h]
    rw [Heq]
    simp only [BigOpM.bigOpM_empty]
    rw [CMRA.unit_right_id]
    refine Trans.trans Update.id (OFE.Equiv.symm ?_)
    refine Equiv.of_eq (congrArg _ (OFE.Equiv.to_eq ?_))
    rw [union_empty_left]
  | hins k v m2 Hm2 IH =>
    intro m1 Hdom Hall
    rw [← congrArg (CMRA.op _) (BigOpM.bigOpM_insert_eqv _ _ Hm2).symm]
    rw [← congrArg (CMRA.op _) CMRA.comm]
    rw [CMRA.assoc]
    refine (Update.op (IH (delete m1 k) ?_ ?_) .id).trans ?_
    · funext j; by_cases hjk : k = j; subst hjk; simp [dom, Hm2, get?_delete_eq rfl]
      have h := congrFun Hdom j; simp only [dom, get?_insert_ne hjk] at h
      simp only [dom, get?_delete_ne hjk]; exact h
    · exact all_delete _ Hall
    rw [← CMRA.assoc]
    rw [← congrArg (CMRA.op _) CMRA.comm]
    rw [CMRA.assoc]
    obtain ⟨v', Hin⟩ : ∃ v', get? m1 k = .some v' := by
      have h := congrFun Hdom k; simp [dom, get?_insert_eq rfl] at h
      exact Option.isSome_iff_exists.mp h
    refine (Update.op (update_replace (v2 := v') ?_) .id).trans ?_
    · exact Hall k v' Hin
    rw [← CMRA.assoc]
    refine Trans.trans Update.id (OFE.Equiv.symm ?_)
    refine Equiv.of_eq ((congrArg (CMRA.op · _) (OFE.Equiv.to_eq ?_)).trans (congrArg (CMRA.op _) (OFE.Equiv.to_eq ?_)))
    · refine Equiv.of_eq (congrArg _ (OFE.Equiv.to_eq ?_))
      refine OFE.Equiv.of_eq (eqv_of_Equiv (fun j => ?_))
      show get? (PartialMap.union m1 m) j = get? (Std.insert (PartialMap.union (delete m1 k) m) k v') j
      by_cases hjk : k = j
      · rw [← hjk, get?_insert_eq rfl]; simp [PartialMap.union, get?_merge, Hin]
        cases get? m k <;> rfl
      · rw [get?_insert_ne hjk]; simp [PartialMap.union, get?_merge, get?_delete_ne hjk]
    · refine .trans ?_ (Equiv.of_eq (BigOpM.bigOpM_insert_eqv _ _ ?_))
      · exact ((insert_delete_cancel Hin).symm ▸ .rfl)
      · exact get?_delete_eq rfl

-- TODO: golf
theorem update_big_alloc (m1 m2 : H V) dq
  (Hdisj : m2 ##ₘ m1) (Hdq : ✓ dq)
  (Hall : all (fun _ v => ✓ v) m2) :
  Auth (.own one) m1 ~~>
    Auth (.own one) (m2 ∪ m1)
    • bigOpM (M := HeapView K V H) op (fun k v => Frag k dq v) m2 := by
    induction m2 using LawfulFiniteMap.induction_on generalizing m1 with
    | hemp =>
      rw [bigOpM_frag_empty]
      refine Update.included ?_
      rw [union_empty_left, CMRA.unit_right_id]
    | hins k v m2 Hm2 IH =>
      have Hall' : all (fun k v => ✓ v) m2 := by exact all_of_all_insert _ Hm2 Hall
      have Hdisj' : m2 ##ₘ m1 := by
        intro j ⟨hs1, hs2⟩; by_cases hjk : k = j; subst hjk; simp [Hm2] at hs1
        exact Hdisj j ⟨by rw [get?_insert_ne hjk]; exact hs1, hs2⟩
      have IH := IH m1 Hdisj' Hall'
      refine IH.trans ?_
      have Hms : get? (m2 ∪ m1) k = none := by
        rw [get?_union_none]
        exact ⟨Hm2, Option.not_isSome_iff_eq_none.mp (fun h => Hdisj k ⟨by simp [get?_insert_eq rfl], h⟩)⟩
      have Hv := all_insert_of_all _ Hall
      have Hstep := update_one_alloc Hms Hdq Hv
      refine (Update.op Hstep .id).trans ?_
      rw [← CMRA.assoc]
      refine Update.op ?_ ?_
      · refine Trans.trans Update.id (OFE.Equiv.symm ?_)
        rw [← union_insert_left]
      · refine Trans.trans Update.id (OFE.Equiv.symm ?_)
        exact Equiv.of_eq (BigOpM.bigOpM_insert_eqv _ _ Hm2)

end FiniteHeapView
