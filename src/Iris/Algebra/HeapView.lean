/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap
import Iris.Algebra.View
import Iris.Algebra.DFrac

open Iris

section heap_view

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]

abbrev heapR (n : Nat) (m : H V) (f : H ((DFrac F) × V)) : Prop :=
  let P (k : K) (fv : DFrac F × V) : Prop :=
    ∃ (v : V) (dq : DFrac F), Store.get m k = .some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))
  Store.all (toHeapPred P) f

instance : ViewRel (heapR F K V H) where
  mono {n1 n2 m1 m2 f1 f2 Hrel Hm Hf Hn k} := by
    unfold toHeapPred; split <;> try trivial
    rename_i dqa vk Hk
    simp only []
    obtain ⟨Hf'', _⟩ := lookup_includedN n2 f2 f1
    have Hf''' := Hf'' Hf k; clear Hf Hf''
    obtain Hf' : ∃ z, Store.get f1 k ≡{n2}≡ (some vk) • z := by
      obtain ⟨z, Hz⟩ := Hf'''; exists z
      apply Hz.trans
      exact OFE.Dist.of_eq (congrFun (congrArg CMRA.op Hk) z)
    clear Hf'''
    cases h : Store.get f1 k
    · exfalso
      rw [h] at Hf'
      obtain ⟨z, HK⟩ := Hf'
      cases z <;> simp [CMRA.op, optionOp] at HK
    rename_i val
    rcases Heq : val with ⟨q', va'⟩
    rw [h, Heq] at Hf'
    simp only [heapR, Store.all, toHeapPred] at Hrel
    obtain ⟨v, dq, Hm1, ⟨Hvval, Hdqval⟩, Hvincl⟩ := (Heq ▸ h ▸ Hrel k)
    have X : ∃ y : V, get m2 k = some y ∧ v ≡{n2}≡ y := by
      simp_all
      have Hmm := Hm1 ▸ Hm k
      rcases h : Store.get m2 k with (_|y) <;> simp [h] at Hmm
      exists y
    obtain ⟨v', Hm2, Hv⟩ := X
    exists v'
    exists dq
    refine ⟨Hm2, ⟨Hvval, ?_⟩, ?_⟩
    · exact CMRA.validN_ne Hv (CMRA.validN_of_le Hn Hdqval)
    · suffices some vk ≼{n2} some (dq, v) by
        apply CMRA.incN_of_incN_of_dist this
        refine ⟨rfl, Hv⟩
      apply CMRA.incN_trans
      · apply Hf'
      · exact CMRA.incN_of_incN_le Hn Hvincl
  rel_validN := by
    intro n m f Hrel k
    rcases Hf : Store.get f k with (_|⟨dqa, va⟩)
    · simp [CMRA.ValidN, optionValidN]
    · simp only [heapR, Store.all, toHeapPred] at Hrel
      obtain ⟨v, dq, Hmval, Hvval, Hvincl⟩ := Hf ▸ Hrel k
      exact CMRA.validN_of_incN Hvincl Hvval
  rel_unit n := by
    exists Heap.empty
    intro k
    simp only [heapR, Store.all, toHeapPred, UCMRA.unit, store_unit, Heap.get_empty]


theorem view_rel_unit : heapR F K V H n m UCMRA.unit := by
  simp [heapR, Store.all, toHeapPred, UCMRA.unit, Heap.get_empty]


-- TODO: This one might need the exists trick. Do I have to map between heaps of different types?
theorem heap_view_rel_exists n f : (∃ m, heapR F K V H n m f) ↔ ✓{n} f := by
  constructor
  · rintro ⟨m, Hrel⟩
    exact ViewRel.rel_validN _ _ _ Hrel
  sorry

instance gmap_view_rel_discrete [CMRA.Discrete V] : ViewRelDiscrete (heapR F K V H) where
  discrete n h H := by
    simp [heapR, Store.all, toHeapPred]
    intro H k; have H' := H k; clear H
    split <;> try trivial
    simp_all
    obtain ⟨v, Hv1, ⟨x, Hx1, Hx2⟩⟩ := H'
    refine ⟨v, Hv1, ⟨x, ?_, ?_⟩⟩
    ·
      -- apply CMRA.Discrete.discrete_valid
      sorry
    · exact (CMRA.inc_0_iff_incN n).mp Hx2

abbrev HeapView := View F (heapR F K V H)

end heap_view

section heap_view_laws

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]

def heap_view_auth (dq : DFrac F) (m : H V) : HeapView F K V H := ●V{dq} m

def heap_view_frag (k : K) (dq : DFrac F) (v : V) : HeapView F K V H :=
  ◯V Heap.point k <| .some (dq, v)

open OFE

instance view_ne : NonExpansive (heap_view_auth dq : _ → HeapView F K V H) := View.auth_ne


instance frag_ne : NonExpansive (heap_view_frag k dq : _ → HeapView F K V H) where
  ne := by
    intro i x1 x2 Hx
    apply View.frag_ne.ne
    intro k'
    simp [Heap.point]
    if h : k = k'
      then simp [get_set_eq h]; exact dist_prod_ext rfl Hx
      else simp [get_set_ne h]

theorem heap_view_rel_lookup n m k dq v :
    heapR F K V H n m (Heap.point k <| .some (dq, v)) ↔
    ∃ (v' : V) (dq' : DFrac F), Store.get m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := by
  constructor
  · intro Hrel
    have Hrel' := Hrel k
    simp only [heapR, Store.all, toHeapPred, Heap.point, Store.get_set_eq] at Hrel'
    obtain ⟨v', dq', Hlookup, Hval, Hinc⟩ := Hrel'
    exists v'; exists dq'
  · rintro ⟨v', dq', Hlookup, Hval, _⟩ j
    simp only [heapR, Store.all, toHeapPred, Heap.point]
    if h : k = j
      then
        simp [Store.get_set_eq h]
        exists v'
        refine ⟨h ▸ Hlookup, ?_⟩
        exists dq'
      else simp [Store.get_set_ne h, Heap.get_empty]


theorem heap_view_auth_dfrac_op (dp dq : DFrac F) (m : H V) :
    (heap_view_auth (dp • dq) m) ≡ (heap_view_auth dp m) • heap_view_auth dq m := by
  exact View.view_auth_dfrac_op

theorem heap_view_auth_dfrac_op_invN n dp m1 dq m2 :
    (✓{n} ((heap_view_auth dp m1) : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡{n}≡ m2 := by
  exact fun a => View.view_auth_dfrac_op_invN a

theorem heap_view_auth_dfrac_op_inv dp m1 dq m2 : ✓ ((heap_view_auth dp m1 : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡ m2 := by
  exact fun a => View.view_auth_dfrac_op_inv a

theorem heap_view_auth_dfrac_validN m n dq : ✓{n} (heap_view_auth dq m : HeapView F K V H) ↔ ✓ (dq : DFrac F) := by
  apply View.view_auth_dfrac_validN.trans
  suffices ✓{n} dq ↔ ✓ dq by
    apply and_iff_left_of_imp (fun _ => ?_)
    apply view_rel_unit
  exact Eq.to_iff rfl

theorem heap_view_auth_dfrac_valid m dq : ✓ (heap_view_auth dq m : HeapView F K V H) ↔ ✓ dq := by
  apply View.view_auth_dfrac_valid.trans
  refine and_iff_left_of_imp (fun _ n => ?_)
  exact view_rel_unit F K V H

theorem heap_view_auth_valid m : ✓ (heap_view_auth (.own One.one) m : HeapView F K V H) := by
  apply (heap_view_auth_dfrac_valid _ _).mpr valid_own_one

theorem heap_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1 • dq2) ∧ m1 ≡{n}≡ m2 := by
  apply View.view_auth_dfrac_op_validN.trans
  refine and_congr_right (fun _ => ?_)
  refine and_iff_left_of_imp (fun _ => ?_)
  exact view_rel_unit F K V H

theorem heap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1  • dq2) ∧ m1 ≡ m2 := by
  apply View.view_auth_dfrac_op_valid.trans
  refine and_congr_right (fun _ => ?_)
  refine and_iff_left_of_imp (fun _ n => ?_)
  exact view_rel_unit F K V H

theorem heap_view_auth_op_validN n m1 m2 : ✓{n} ((heap_view_auth (.own One.one) m1 : HeapView F K V H) • (heap_view_auth (.own One.one) m2)) ↔ False := by
  apply View.view_auth_op_validN

theorem heap_view_auth_op_valid m1 m2 : ✓ ((heap_view_auth (.own One.one) m1 : HeapView F K V H)  • heap_view_auth (.own One.one) m2) ↔ False := by
  apply View.view_auth_op_valid

theorem heap_view_frag_validN n k dq v : ✓{n} (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓{n} v := by
  apply View.view_frag_validN.trans
  apply (heap_view_rel_exists F K V H _ _).trans
  have Hrw : (✓{n} (Heap.point k (some (dq, v)) : H _)) ↔ (✓ (Heap.point k (some (dq, v)) : H _)) := by
    constructor
    · intro H
      apply point_valid.mpr
      sorry
    · exact fun a => CMRA.Valid.validN a
  apply Iff.trans Hrw ?_
  --

  sorry

theorem heap_view_frag_valid k dq v : ✓ (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓ v := by
  sorry

theorem heap_view_frag_op k dq1 dq2 v1 v2 :
    (heap_view_frag k (dq1 • dq2) (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k dq1 v1  • heap_view_frag k dq2 v2 := by
  sorry

theorem heap_view_frag_add k q1 q2 v1 v2 :
    (heap_view_frag k (.own (q1 + q2)) (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k (.own q1) v1  • heap_view_frag k (.own q2) v2 := by
  sorry

theorem heap_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓{n} (v1  • v2) := by
  sorry

theorem heap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓ (v1  • v2) := sorry

theorem heap_view_both_dfrac_validN n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H)  • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ Store.get m k = some v' ∧ ✓{n} (dq', v') ∧
                some (dq, v) ≼{n} some (dq', v') := sorry

theorem heap_view_both_validN n dp m k v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k (.own One.one) v) ↔
      ✓ dp ∧ ✓{n} v ∧ Store.get m k ≡{n}≡ some v := sorry

theorem heap_view_both_dfrac_validN_total [CMRA.IsTotal V] n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓{n} v' ∧ v ≼{n} v' := sorry

theorem heap_view_both_dfrac_valid_discrete [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ Store.get m k = some v' ∧ ✓ (dq', v') ∧ some (dq, v) ≼ some (dq', v') := sorry

theorem heap_view_both_dfrac_valid_discrete_total [CMRA.IsTotal V] [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓ v' ∧ v ≼ v' := sorry

theorem heap_view_both_valid m dp k v :
    ✓ ((heap_view_auth dp m : HeapView F K V H)  • heap_view_frag k (.own One.one) v) ↔
    ✓ dp ∧ ✓ v ∧ Store.get m k ≡ some v := sorry

end heap_view_laws

section heap_updates
-- TODO: Port updates


section heap_updates

-- TODO: Port functors
