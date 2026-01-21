/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
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

section heap_view
open Store Heap OFE CMRA

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]
variable [IHHmap : ∀ V, HasHeapMap (H (DFrac F × V)) (H V) K (DFrac F × V) V]

/-- The view relation for heaps: relates a model heap to a fragment heap at step index `n`. -/
def HeapR (n : Nat) (m : H V) (f : H ((DFrac F) × V)) : Prop :=
  ∀ k fv, get f k = some fv →
    ∃ (v : V) (dq : DFrac F), get m k = .some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))

instance : IsViewRel (HeapR F K V H) where
  mono {n1 m1 f1 n2 m2 f2 Hrel Hm Hf Hn k} vk Hk := by
    obtain Hf' : ∃ z, get f1 k ≡{n2}≡ (some vk) • z := by
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
  let FF : (K → (DFrac F × V) → Option V) := fun k _ => get f k |>.bind (·.2)
  refine ⟨hhmap FF f, fun k => ?_⟩
  cases h : get f k; simp
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

/-- A view of a Heap, that gives element-wise ownership -/
abbrev HeapView := View F (HeapR F K V H)

end heap_view

namespace HeapView

open Heap OFE View One Store DFrac

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
    · simp [point, get_set_eq h]; exact dist_prod_ext rfl Hx
    · simp [point, get_set_ne h]

variable {dp dq : DFrac F} {n : Nat} {m1 m2 : H V} {k : K} {v1 v2 : V}

theorem auth_dfrac_op_equiv : Auth (dp • dq) m1 ≡ (Auth dp m1) • Auth dq m1 :=
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

nonrec theorem auth_op_auth_valid_iff  : ✓ Auth dp m1 • Auth dq m2 ↔ ✓ dp • dq ∧ m1 ≡ m2 :=
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

-- Here
theorem auth_op_frag_validN_iff :
    ✓{n} Auth dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓ dp ∧ Store.get m1 k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := by
  simp [HeapView.Auth, HeapView.Frag]
  apply View.auth_op_frag_validN_iff.trans
  refine and_congr_right (fun H1 => ?_)
  refine (HeapR.point_get_iff _ _ _ _ _ _ _ _ _).trans ?_
  refine exists_congr (fun x => ?_)
  exact exists_and_left

theorem auth_op_frag_one_validN_iff n dp m k v :
    ✓{n} ((HeapView.Auth dp m : HeapView F K V H) • HeapView.Frag k (.own One.one) v) ↔
      ✓ dp ∧ ✓{n} v ∧ Store.get m k ≡{n}≡ some v := by
  apply (HeapView.auth_op_frag_validN_iff).trans
  constructor
  · rintro ⟨Hdp, v', dq', Hlookup, Hvalid, Hincl⟩
    have Heq : v ≡{n}≡ Hdp := by
      have Z := @Option.dist_of_inc_exclusive _ _ (DFrac.own One.one, v) n ?G _ Hincl Hvalid
      case G =>
        -- TODO: This should be a DFrac lemma
        constructor
        rintro ⟨y1, y2⟩
        simp [CMRA.ValidN, CMRA.op]
        intro H
        exfalso
        cases y1 <;> simp [DFrac.valid, DFrac.op] at H
        · apply (UFraction.one_whole (α := F)).2
          rename_i f; exists f
        · apply (UFraction.one_whole (α := F)).2 H
        · apply (UFraction.one_whole (α := F)).2
          exact Fraction.Fractional.of_add_left H
      exact Z.2
    refine ⟨dq', ?_, ?_⟩
    · simp [CMRA.ValidN, Prod.ValidN] at Hvalid
      apply CMRA.validN_ne Heq.symm Hvalid.2
    · rw [Hlookup]
      exact Heq.symm
  · rintro ⟨Hdp, Hval, Hlookup⟩
    rcases h : Store.get m k with (_|v'); simp [h] at Hlookup
    exists v'; exists (DFrac.own One.one)
    refine ⟨Hdp, rfl, ?_, ?_⟩
    · simp [CMRA.ValidN, Prod.ValidN]
      refine ⟨?_, ?_⟩
      · simp [DFrac.valid]
        apply (UFraction.one_whole (α := F)).1
      rw [h] at Hlookup
      exact (Dist.validN Hlookup.symm).mp Hval
    · apply Option.some_incN_some_iff.mpr ?_
      left
      apply dist_prod_ext rfl ?_
      exact (h.symm ▸ Hlookup : some _ ≡{n}≡ some _).symm

theorem auth_op_frag_validN_total_iff [CMRA.IsTotal V] n dp m k dq v :
    ✓{n} ((HeapView.Auth dp m : HeapView F K V H) • HeapView.Frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓{n} v' ∧ v ≼{n} v' := by
  intro H; have H' := (HeapView.auth_op_frag_validN_iff).mp H; clear H
  obtain ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ := H'
  exists v'
  refine ⟨Hdp, ?_, Hlookup, Hvalid.2, ?_⟩
  · suffices some dq ≼ some dq' by
      refine Option.valid_of_inc_valid ?_ this
      apply (CMRA.valid_iff_validN' n).mpr Hvalid.1
    apply (CMRA.inc_iff_incN n).mpr
    rcases Hincl with ⟨x, Hx⟩
    rcases x with (_|x) <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.incN_of_incN_of_dist (CMRA.incN_refl _)
      apply Hx.1.symm
    · exists x.1
      simp [CMRA.op, optionOp]
      apply Hx.1
  · suffices some v ≼{n} some v' by
      apply Option.some_incN_some_iff_isTotal.mp this
    refine Option.some_incN_some_iff_isTotal.mpr ?_
    rcases Hincl with ⟨x, Hx⟩
    rcases x with (_|x) <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.incN_of_incN_of_dist (CMRA.incN_refl _)
      apply Hx.2.symm
    · exists x.2
      apply Hx.2

theorem auth_op_frag_discrete_valid_iff [CMRA.Discrete V] dp m k dq v :
    ✓ ((HeapView.Auth dp m : HeapView F K V H) • HeapView.Frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ Store.get m k = some v' ∧ ✓ (dq', v') ∧ some (dq, v) ≼ some (dq', v') := by
  apply CMRA.valid_iff_validN.trans
  apply Iff.trans
  · apply forall_congr'
    intro _
    apply HeapView.auth_op_frag_validN_iff
  constructor
  · intro Hvalid'
    obtain ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ := Hvalid' 0
    exists v'; exists dq'
    refine ⟨Hdp, Hlookup, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · apply CMRA.Discrete.discrete_valid
        apply Hvalid.1
      · apply CMRA.Discrete.discrete_valid
        apply Hvalid.2
    · exact (CMRA.inc_iff_incN 0).mpr Hincl
  · rintro ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ n
    exact ⟨v', dq', Hdp, Hlookup, Hvalid.validN, (CMRA.inc_iff_incN n).mp Hincl⟩

theorem auth_op_frag_valid_total_discrete_iff [CMRA.IsTotal V] [CMRA.Discrete V]
    dp m k dq v :
    ✓ ((HeapView.Auth dp m : HeapView F K V H) • HeapView.Frag k dq v) →
      ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓ v' ∧ v ≼ v' := by
  intro H
  obtain ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ :=
    (HeapView.auth_op_frag_discrete_valid_iff _ _ _ _ _).mp H
  exists v'
  refine ⟨Hdp, ?_, Hlookup , ?_, ?_⟩
  · rcases Hincl with ⟨(_|x), Hx⟩ <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.valid_of_eqv Hx.1
      simp [CMRA.Valid, Prod.Valid] at Hvalid
      apply Hvalid.1
    · suffices some dq ≼ some dq' by exact Option.valid_of_inc_valid Hvalid.1 this
      exists x.fst
      simp [CMRA.op, optionOp]
      have Hx' := Hx.1
      exact Hx'
  · exact Hvalid.2
  · rcases Hincl with ⟨(_|x), Hx⟩ <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · simp [OFE.Equiv] at Hx
      apply CMRA.inc_of_inc_of_eqv (CMRA.inc_refl _)
      exact Hx.2.symm
    · suffices some v ≼ some v' by
        rcases this with ⟨z, Hz⟩
        rcases z with (_|z) <;> simp [CMRA.op, optionOp] at Hz
        · apply CMRA.inc_of_inc_of_eqv
          · apply CMRA.inc_refl
          · apply Hz.symm
        · exists z
      exists x.snd
      simp [CMRA.op, optionOp]
      have Hx' := Hx.2
      exact Hx'

theorem auth_op_frag_one_valid_iff m dp k v :
    ✓ ((HeapView.Auth dp m : HeapView F K V H) • HeapView.Frag k (.own One.one) v) ↔
    ✓ dp ∧ ✓ v ∧ Store.get m k ≡ some v := by
  apply CMRA.valid_iff_validN.trans
  apply Iff.trans
  · apply forall_congr'
    intro _
    apply HeapView.auth_op_frag_one_validN_iff
  constructor
  · intro Hvalid
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨Hdp, Hv, Hl⟩ := Hvalid 0
      exact Hdp
    · apply CMRA.valid_iff_validN.mpr (fun n => ?_)
      obtain ⟨Hdp, Hv, Hl⟩ := Hvalid n
      exact Hv
    · apply OFE.equiv_dist.mpr (fun n => ?_)
      obtain ⟨Hdp, Hv, Hl⟩ := Hvalid n
      exact Hl
  · rintro ⟨Hdp, Hv, Hl⟩ n
    refine ⟨Hdp, Hv.validN, Hl.dist⟩

instance [CMRA.CoreId dq] [CMRA.CoreId v] :
    CMRA.CoreId (HeapView.Frag k dq v : HeapView F K V H) := by
  rename_i H1 H2
  obtain ⟨H1⟩ := H1
  obtain ⟨H2⟩ := H2
  constructor
  simp only [HeapView.Frag, CMRA.pcore]
  simp only [View.Pcore, some_eqv_some]
  refine NonExpansive₂.eqv trivial ?_
  refine Heap.point_core_eqv ?_
  simp [CMRA.pcore, Prod.pcore]
  simp [CMRA.pcore] at H1
  simp [H1]
  cases h : (CMRA.pcore v) <;> simp_all
  refine ⟨rfl, ?_⟩
  exact H2

section WithMap

variable [IHHmap : ∀ V, HasHeapMap (H (DFrac F × V)) (H V) K (DFrac F × V) V]

theorem frag_validN_iff n k dq v  :
    ✓{n} (HeapView.Frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓{n} v := by
  apply View.frag_validN_iff.trans
  apply (HeapR.exists_iff_validN F K V H).trans
  apply Heap.point_validN_iff

theorem frag_valid_iff k dq v :
    ✓ (HeapView.Frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓ v := by
  suffices (∀ n, ✓{n} (HeapView.Frag k dq v : HeapView F K V H)) ↔ ✓ dq ∧ ✓ v by exact this
  suffices (∀ n, ✓ dq ∧ ✓{n} v) ↔ ✓ dq ∧ ✓ v by
    apply Iff.trans (forall_congr' (HeapView.frag_validN_iff · k dq v)) this
  constructor
  · intro H
    exact ⟨CMRA.valid_iff_validN.mpr (H · |>.1), CMRA.valid_iff_validN.mpr (H · |>.2)⟩
  · rintro ⟨H1, H2⟩ n
    exact ⟨CMRA.valid_iff_validN.mp H1 n, CMRA.valid_iff_validN.mp H2 n⟩

theorem frag_op_validN_iff n k dq1 dq2 v1 v2 :
    ✓{n} ((HeapView.Frag k dq1 v1 : HeapView F K V H) • HeapView.Frag k dq2 v2) ↔
      ✓ (dq1 • dq2) ∧ ✓{n} (v1 • v2) := by
  apply View.frag_validN_iff.trans
  apply (HeapR.exists_iff_validN F K V H).trans
  apply Iff.trans
  · apply CMRA.validN_iff
    apply OFE.equiv_dist.mp
    apply Store.eqv_of_Equiv
    apply Heap.point_op_point
  apply Heap.point_validN_iff.trans
  rfl

theorem frag_op_valid_iff k dq1 dq2 v1 v2 :
    ✓ ((HeapView.Frag k dq1 v1 : HeapView F K V H) • HeapView.Frag k dq2 v2) ↔
      ✓ (dq1 • dq2) ∧ ✓ (v1 • v2) := by
  apply View.frag_valid_iff.trans
  suffices (∀ (n : Nat), ✓{n} dq1 • dq2 ∧ ✓{n} v1 • v2) ↔ ✓ dq1 • dq2 ∧ ✓ v1 • v2 by
    apply Iff.trans _ this
    apply forall_congr'
    intro n
    apply (HeapR.exists_iff_validN F K V H).trans
    simp [HeapView.Frag]
    apply Iff.trans
    · apply CMRA.validN_iff
      apply OFE.equiv_dist.mp
      apply Store.eqv_of_Equiv
      apply Heap.point_op_point
    apply Heap.point_validN_iff.trans
    rfl
  constructor
  · intro H
    exact ⟨CMRA.valid_iff_validN.mpr fun n => (H n).1,
           CMRA.valid_iff_validN.mpr fun n => (H n).2⟩
  · rintro ⟨H1, H2⟩ n
    exact ⟨CMRA.valid_iff_validN.mp H1 n, CMRA.valid_iff_validN.mp H2 n⟩

end WithMap

section heap_updates

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]

theorem update_one_alloc m k dq (v : V) :
    (Store.get m k = none) → ✓ dq → ✓ v →
      HeapView.Auth (.own 1) m ~~>
        ((HeapView.Auth (.own 1) (Store.set m k (.some v)) : HeapView F K V H) •
          HeapView.Frag k dq v) := by
  intro Hfresh Hdq Hval
  refine View.auth_one_alloc (fun n bf Hrel j => ?_ )
  simp [CMRA.op, get_merge, Option.merge]
  if h : k = j
    then
      rw [Heap.point_get_eq h]
      have Hbf : Store.get bf j = none := by
        cases hc : Store.get bf j; rfl
        simp [HeapR] at Hrel
        exfalso
        rename_i val
        have Hrel' := Hrel _ _ _ hc
        rcases Hrel' with ⟨_, HK, _, _, _⟩
        subst h
        simp [HK] at Hfresh
      simp only [Hbf]
      intro a b Hab
      obtain ⟨rfl⟩ := Hab
      exists v
      rw [get_set_eq h]
      refine ⟨rfl, ?_⟩
      exists dq
      exact ⟨⟨Hdq, Hval.validN⟩, CMRA.incN_refl _⟩
    else
      rw [Heap.point_get_ne h]
      cases hc : Store.get bf j <;> simp only []
      · rintro _ _ ⟨⟩
      intro a b Hab
      obtain ⟨rfl⟩ := Hab
      simp [HeapR] at Hrel
      rcases Hrel j a b hc with ⟨v, He, q, Hv, Hframe, Hinc⟩
      rw [get_set_ne h]
      exists v
      refine ⟨He, ?_⟩
      exists q
      refine ⟨Hv, ?_⟩
      exists Hframe

theorem update_one_delete m k (v : V) :
    (HeapView.Auth (.own 1) m : HeapView F K V H) •
      (HeapView.Frag k (.own 1) v : HeapView F K V H) ~~>
        HeapView.Auth (.own 1) (Heap.delete m k) := by
  refine View.auth_one_op_frag_dealloc (fun n bf Hrel j => ?_)
  cases He : Store.get bf j
  · intro _ HK; simp at HK
  if h : k = j
    then
      simp [HeapR, CMRA.op, get_merge, Option.merge] at Hrel
      have Hrel' := Hrel k; clear Hrel
      simp [h, He, Heap.point_get_eq rfl] at Hrel'
      obtain ⟨v, HK, q, Hqv, Hqinc⟩ := Hrel'
      rename_i vv
      have Hval := Option.validN_of_incN_validN (Hv := Hqv) (Hinc := Hqinc)
      exfalso
      obtain ⟨z, _⟩ := Hqinc
      simp [CMRA.ValidN, Prod.ValidN] at Hval
      have HK := Hval.1
      obtain ⟨(f|_|f), _⟩ := vv <;> simp [DFrac.valid, CMRA.op, DFrac.op] at HK
      · apply (UFraction.one_whole (α := F)).2; exists f
      · apply (UFraction.one_whole (α := F)).2; exact HK
      · apply (UFraction.one_whole (α := F)).2
        exists f
        exact Fraction.Fractional.proper HK
    else
      simp [HeapR, CMRA.op, get_merge, Option.merge] at Hrel
      have Hrel' := Hrel j; clear Hrel
      simp [He, Heap.point_get_ne h] at Hrel'
      rintro ⟨a, b⟩ Hab
      obtain ⟨rfl⟩ := Hab
      obtain ⟨v, H1, q, H2⟩ := Hrel' a b rfl
      exists v
      exists q
      refine ⟨?_, H2⟩
      · unfold Heap.delete
        rw [Store.get_set_ne h]
        trivial

theorem update_auth_op_frag (m : H _) k (dq : DFrac F) (v mv' v' : V) (dq' : DFrac F) :
    (∀ (n : Nat) (mv : V) (f : Option (DFrac F × V)),
      (Store.get m k = some mv) →
      ✓{n} ((dq, v) •? f) →
      (mv ≡{n}≡ ((v : V) •? (Prod.snd <$> f))) →
      ✓{n} ((dq', v') •? f) ∧ (mv' ≡{n}≡ v' •? (Prod.snd <$> f))) →
    ((HeapView.Auth (.own 1) m : HeapView F K V H) • (HeapView.Frag k dq v : HeapView F K V H)) ~~>
      ((HeapView.Auth (.own 1) (Store.set m k (some mv')) : HeapView F K V H) •
        (HeapView.Frag k dq' v' : HeapView F K V H)) := by
  intro Hup
  apply View.auth_one_op_frag_update
  rintro n bf Hrel j ⟨df, va⟩
  simp [CMRA.op, Heap.get_merge]
  if h : k = j
    then
      simp [Heap.point, Store.get_set_eq h]
      intro Hbf
      have Hrel' := Hrel k ((dq, v) •? (Store.get bf k))
      have Hrel'' := Hrel' ?G; clear Hrel'
      case G=>
        clear Hrel'
        simp [CMRA.op, Heap.get_merge, Heap.point, CMRA.op?]
        cases h : Store.get bf k <;> simp [Option.merge, Store.get_set_eq rfl]
      obtain ⟨mv, mdf, Hlookup, Hval, Hincl'⟩ := Hrel''
      obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl'; clear Hincl'
      let f := (Store.get bf k) • f'
      have Hincl' : (mdf, mv) ≡{n}≡ (dq, v) •? f := by
        refine .trans Hincl ?_
        apply OFE.Equiv.dist
        exact Option.opM_opM_assoc
      clear Hincl
      have Hup' := Hup n mv f Hlookup (Hincl'.validN.mp Hval) ?G
      case G=>
        apply Hincl'.2.trans
        match f with
        | none => simp [CMRA.op?]
        | some ⟨_, _⟩ => simp [CMRA.op?, CMRA.op]
      obtain ⟨Hval', Hincl'⟩ := Hup'
      exists ((dq' •? (Option.map Prod.fst f)))
      refine ⟨?_, ?_⟩
      · apply CMRA.validN_ne (x := (dq' •? Option.map Prod.fst f, v' •? Prod.snd <$> f))
        · refine ⟨.rfl, Hincl'.symm⟩
        cases h : f <;> simp [CMRA.op?]
        · exact CMRA.validN_opM Hval'
        · simp [h, CMRA.op?, CMRA.op, Prod.op] at Hval'
          exact Hval'
      · rw [← Hbf]
        suffices HF : some ((dq', v') •? (Store.get bf j)) ≼{n}
            some (dq' •? (Option.map Prod.fst f), mv') by
          apply CMRA.incN_trans ?_ HF
          simp [Option.merge, Prod.op, CMRA.op?]
          cases h : Store.get bf j <;> simp
          · exact CMRA.incN_refl _
          · exact CMRA.incN_refl _
        apply Option.some_incN_some_iff_opM.mpr
        exists f'
        refine OFE.Dist.trans (y := (dq' •? Option.map Prod.fst f, v' •? Prod.snd <$> f)) ?_ ?_
        · exact OFE.dist_prod_ext rfl Hincl'
        apply OFE.Dist.trans ?_
        · apply OFE.equiv_dist.mp
          exact Option.opM_opM_assoc.symm
        obtain H : Store.get bf j • f' = f := by rw [← h]
        rw [H]
        simp [Option.map]
        cases h : f <;> simp [CMRA.op, CMRA.op?, Prod.op]
    else
      simp [Heap.point, Store.get_set_ne h, Heap.get_empty]
      intro Hbf
      have Hrel' := Hrel j (df, va)
      simp [CMRA.op, Heap.get_merge] at Hrel'
      simp [Option.merge, Heap.point, Store.get_set_ne h, Heap.get_empty] at Hrel'
      simp only [Hbf] at Hrel'
      exact Hrel' trivial

theorem update_of_local_update m k dq v mv' v' :
    (Store.get m k = some mv) →
    (mv, v) ~l~> (mv', v') →
    ((HeapView.Auth (.own 1) m : HeapView F K V H) • HeapView.Frag k dq v) ~~>
      ((HeapView.Auth (.own 1) (Store.set m k (.some mv')) : HeapView F K V H) •
        HeapView.Frag k dq v') := by
  intro Hlookup Hup
  apply HeapView.update_auth_op_frag
  intro n mv0 f Hmv0 Hval Hincl
  simp [Hlookup] at Hmv0; subst Hmv0
  have Hup' := Hup n (Prod.snd <$> f) ?G1 Hincl
  case G1 =>
    refine CMRA.validN_ne Hincl.symm ?_
    cases Hval; cases f <;> simp_all [CMRA.op?, CMRA.op]
  obtain ⟨Hval', Hincl'⟩ := Hup'
  refine ⟨?_, Hincl'⟩
  simp_all
  simp [CMRA.op?] at ⊢ Hincl Hincl'
  cases f <;> simp_all [CMRA.op?, CMRA.op, Prod.op] <;>
  refine ⟨Hval.1, CMRA.validN_ne Hincl' Hval'⟩

theorem update_replace m k v v' :
    ✓ v' →
    ((HeapView.Auth (.own 1) m : HeapView F K V H) •
      (HeapView.Frag k (.own 1) v : HeapView F K V H)) ~~>
        ((HeapView.Auth (F := F) (.own 1) (Store.set m k (.some v'))) •
          (HeapView.Frag (F := F) k (.own 1) v')) := by
  intro Hval'
  apply HeapView.update_auth_op_frag
  intro n mv f Hlookup Hval Hincl
  cases f <;> simp
  · simp_all [CMRA.op?]
    refine ⟨Hval.1, ?_⟩
    simp
    exact CMRA.Valid.validN Hval'
  · simp_all [CMRA.op?, CMRA.op, Prod.op]
    exfalso
    apply (own_whole_exclusive (UFraction.one_whole (α := F))).exclusive0_l
    apply CMRA.valid0_of_validN
    exact Hval.1

theorem auth_dfrac_discard dq m :
    (HeapView.Auth dq m : HeapView F K V H) ~~> HeapView.Auth .discard m :=
  View.auth_discard

theorem auth_dfrac_acquire [IsSplitFraction F] m :
    (HeapView.Auth .discard m : HeapView F K V H) ~~>:
      fun a => ∃ q, a = HeapView.Auth (F := F) (.own q) m :=
  View.auth_acquire

theorem update_of_dfrac_update k dq P v :
    dq ~~>: P →
    (HeapView.Frag k dq v : HeapView F K V H) ~~>:
      fun a => ∃ dq', a = HeapView.Frag k dq' v ∧ P dq' := by
  intro Hdq
  apply UpdateP.weaken
  · apply View.frag_updateP (P := fun b' => ∃ dq', ((◯V b') = HeapView.Frag k dq' v) ∧ P dq')
    intros m n bf Hrel
    simp only [HeapR] at Hrel
    have Hrel' := Hrel k ((dq, v) •? Store.get bf k) ?G
    case G=>
      simp [CMRA.op, Heap.get_merge, Heap.point_get_eq rfl, Option.merge, CMRA.op?]
      cases Store.get bf k <;> simp
    obtain ⟨v', dq', Hlookup, Hval, Hincl⟩ := Hrel'
    obtain ⟨f', Hincl⟩ := Option.some_incN_some_iff_opM.mp Hincl
    have Hincl' : (dq', v') ≡{n}≡ (dq, v) •? ((Store.get bf k) • f') := by
      refine Hincl.trans ?_
      apply OFE.equiv_dist.mp
      exact Option.opM_opM_assoc
    clear Hincl
    -- f := bf !! k ⋅ f'
    -- (Store.get bf k) • f'
    have X := Hdq n (Option.map Prod.fst ((Store.get bf k) • f')) ?G
    case G =>
      cases h : (Store.get bf k) • f' <;> simp [Option.map, CMRA.op?]
      · simp [h, CMRA.op?] at Hincl'
        exact CMRA.validN_ne Hincl'.1 Hval.1
      · simp [h, CMRA.op?] at Hincl'
        exact CMRA.validN_ne Hincl'.1 Hval.1
    obtain ⟨dq'', HPdq'', Hvdq''⟩ := X
    exists Heap.point k (dq'', v)
    refine ⟨?_, ?_⟩
    · exists dq''
    rintro j ⟨df, va⟩ Heq
    if h : k = j
      then
        simp [CMRA.op, Heap.get_merge, Heap.point_get_eq h] at Heq
        exists v'
        exists ((dq'' •? (Option.map Prod.fst $ (Store.get bf k) • f')))
        refine ⟨h ▸ Hlookup, ⟨Hvdq'' , Hval.2⟩, ?_⟩
        exists f'
        cases h : f' <;> cases h' : Store.get bf k <;>
          simp [OFE.Dist, Option.Forall₂, CMRA.op, optionOp, CMRA.op?] <;>
          simp_all [CMRA.op, optionOp, CMRA.op?, Prod.op]
        · exact Hincl'.2
        · exact Hincl'.2
        · exact Hincl'.2
        · have HR := Hincl'.2
          refine ⟨?_, ?_⟩
          · rw [← Heq.1]
            exact CMRA.op_assocN
          · simp at HR
            rw [← Heq.2]
            refine HR.trans ?_
            exact CMRA.op_assocN
      else
        apply Hrel
        simp [CMRA.op, Heap.get_merge, Heap.point_get_ne h] at Heq ⊢
        exact Heq
  · intro y
    rintro ⟨b, rfl, q, _, _⟩
    exists q

theorem update_frag_discard k dq v :
  (HeapView.Frag k dq v : HeapView F K V H) ~~> HeapView.Frag k .discard v := by
  apply Update.lift_updateP (fun (dq : DFrac F) => HeapView.Frag (H := H) (F := F) k dq v)
  · exact fun P Hupd => HeapView.update_of_dfrac_update k dq P v Hupd
  · exact DFrac.update_discard

theorem update_frag_acquire [IsSplitFraction F] k v :
    (HeapView.Frag k .discard v : HeapView F K V H) ~~>:
    fun a => ∃ q, a = HeapView.Frag k (.own q) v := by
  apply UpdateP.weaken
  · apply HeapView.update_of_dfrac_update
    apply DFrac.update_acquire
  rintro y ⟨q, rfl, ⟨q1, rfl⟩⟩
  exists q1

end heap_updates

-- TODO: Port functors

end HeapView
