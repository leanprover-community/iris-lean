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

variable (F K V : Type _) (H : Type _ → Type _) [DFractional F] [∀ T, Heap (H T) K T] [CMRA V]

abbrev heapR (n : Nat) (m : StoreO (H V)) (f : StoreO (H ((DFrac F) × V))) : Prop :=
  let P (k : K) (fv : DFrac F × V) : Prop :=
    ∃ (v : V) (dq : DFrac F), StoreO.get k m = .some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))
  StoreO.all (lift_dom P) f

instance : ViewRel (heapR F K V H) where
  mono {n1 n2 m1 m2 f1 f2 Hrel Hm Hf Hn k} := by
    unfold lift_dom; split <;> try trivial
    rename_i dqa vk Heq
    simp only []
    sorry
  rel_validN := sorry
  rel_unit := sorry

abbrev HeapView := View F (heapR F K V H)

-- #synth CMRA (HeapView F K V H)

end heap_view

section heap_view_laws

variable {F K V : Type _} {H : Type _ → Type _} [DFractional F] [∀ T, Heap (H T) K T] [CMRA V]

def heap_view_auth (dq : DFrac F) (m : StoreO (H V)) : HeapView F K V H :=
  ●V{dq} .mk m.1

def heap_view_frag (k : K) (dq : DFrac F) (v : V) : HeapView F K V H :=
  ◯V .singleton k <| .some (dq, v)

open OFE

instance view_ne : NonExpansive (heap_view_auth dq : _ → HeapView F K V H) where
  ne := sorry

instance frag_ne : NonExpansive (heap_view_frag dq k : _ → HeapView F K V H) where
  ne := sorry

theorem heap_view_rel_lookup n m k dq v :
    heapR F K V H n m (.singleton k <| .some (dq, v)) ↔
    ∃ (v' : V) (dq' : DFrac F), m.get k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := sorry

theorem heap_view_auth_dfrac_op (dp dq : DFrac F) (m : StoreO (H V)) :
    (heap_view_auth (dp • dq) m) ≡ (heap_view_auth dp m) • heap_view_auth dq m := sorry


theorem heap_view_auth_dfrac_op_invN n dp m1 dq m2 :
    (✓{n} ((heap_view_auth dp m1) : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡{n}≡ m2 := sorry

theorem heap_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ ((heap_view_auth dp m1 : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡ m2 := sorry

theorem heap_view_auth_dfrac_validN m n dq : ✓{n} (heap_view_auth dq m : HeapView F K V H) ↔ ✓ (dq : DFrac F) := sorry

theorem heap_view_auth_dfrac_valid m dq : ✓ (heap_view_auth dq m : HeapView F K V H) ↔ ✓ dq := sorry

theorem heap_view_auth_valid m : ✓ (heap_view_auth ⟨DFracK.Own One.one⟩ m : HeapView F K V H) := sorry

theorem heap_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1 • dq2) ∧ m1 ≡{n}≡ m := sorry

theorem heap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1  • dq2) ∧ m1 ≡ m2 := sorry

theorem heap_view_auth_op_validN n m1 m2 : ✓{n} ((heap_view_auth ⟨DFracK.Own One.one⟩ m1 : HeapView F K V H) • (heap_view_auth ⟨DFracK.Own One.one⟩ m2)) ↔ False := sorry

theorem heap_view_auth_op_valid m1 m2 : ✓ ((heap_view_auth ⟨DFracK.Own One.one⟩ m1 : HeapView F K V H)  • heap_view_auth ⟨DFracK.Own One.one⟩ m2) ↔ False := sorry

theorem heap_view_frag_validN n k dq v : ✓{n} (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓{n} v := sorry

theorem heap_view_frag_valid k dq v : ✓ (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓ v := sorry

theorem heap_view_frag_op k dq1 dq2 v1 v2 :
    (heap_view_frag k (dq1 • dq2) (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k dq1 v1  • heap_view_frag k dq2 v2 := sorry

theorem heap_view_frag_add k q1 q2 v1 v2 :
    (heap_view_frag k ⟨DFracK.Own (q1 + q2)⟩ (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k ⟨DFracK.Own q1⟩ v1  • heap_view_frag k ⟨DFracK.Own q2⟩ v2 := sorry

theorem heap_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓{n} (v1  • v2) := sorry

theorem heap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓ (v1  • v2) := sorry

theorem heap_view_both_dfrac_validN n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H)  • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ StoreO.get k m = some v' ∧ ✓{n} (dq', v') ∧
                some (dq, v) ≼{n} some (dq', v') := sorry

theorem heap_view_both_validN n dp m k v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k ⟨DFracK.Own One.one⟩ v) ↔
      ✓ dp ∧ ✓{n} v ∧ StoreO.get k m ≡{n}≡ some v := sorry

theorem heap_view_both_dfrac_validN_total [CMRA.IsTotal V] n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ StoreO.get k m = some v' ∧ ✓{n} v' ∧ v ≼{n} v' := sorry

theorem heap_view_both_dfrac_valid_discrete [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ StoreO.get k m = some v' ∧ ✓ (dq', v') ∧ some (dq, v) ≼ some (dq', v') := sorry

theorem heap_view_both_dfrac_valid_discrete_total [CMRA.IsTotal V] [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ StoreO.get k m = some v' ∧ ✓ v' ∧ v ≼ v' := sorry

theorem heap_view_both_valid m dp k v :
    ✓ ((heap_view_auth dp m : HeapView F K V H)  • heap_view_frag k ⟨DFracK.Own One.one⟩ v) ↔
    ✓ dp ∧ ✓ v ∧ StoreO.get k m ≡ some v := sorry

end heap_view_laws

section heap_updates
-- TODO: Port updates


section heap_updates

-- TODO: Port functors

