/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap
import Iris.Algebra.View
import Iris.Algebra.DFrac
import Iris.Algebra.Frac

open Iris

section heap_view

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]
variable [IHHmap : ∀ V, HasHHMap (H (DFrac F × V)) (H V) K (DFrac F × V) V]

@[simp] def HeapR (n : Nat) (m : H V) (f : H ((DFrac F) × V)) : Prop :=
  ∀ k fv, Store.get f k = some fv →
    ∃ (v : V) (dq : DFrac F), Store.get m k = .some v ∧ ✓{n} (dq, v) ∧ (some fv ≼{n} some (dq, v))

instance : ViewRel (HeapR F K V H) where
  mono {n1 n2 m1 m2 f1 f2 Hrel Hm Hf Hn k} := by
    intro vk Hk
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
    simp only [HeapR, Store.all] at Hrel
    obtain ⟨v, dq, Hm1, ⟨Hvval, Hdqval⟩, Hvincl⟩ := Hrel k val h
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
      apply CMRA.incN_trans _ (CMRA.incN_of_incN_le Hn Hvincl)
      rw [Heq]
  rel_validN := by
    intro n m f Hrel k
    rcases Hf : Store.get f k with (_|⟨dqa, va⟩)
    · simp [CMRA.ValidN, optionValidN]
    · simp only [HeapR, Store.all] at Hrel
      obtain ⟨v, dq, Hmval, Hvval, Hvincl⟩ := Hf ▸ Hrel k _ Hf
      rw [Hf] at Hvincl
      refine CMRA.validN_of_incN Hvincl ?_
      exact Hvval
  rel_unit n := by
    exists Heap.empty
    intro k
    simp [HeapR, Store.all, UCMRA.unit, Heap.get_empty]

omit IHHmap in
theorem view_rel_unit : HeapR F K V H n m UCMRA.unit := by
  simp [HeapR, Store.all,   UCMRA.unit, Heap.get_empty]

theorem heap_view_rel_exists n f : (∃ m, HeapR F K V H n m f) ↔ ✓{n} f := by
  constructor
  · rintro ⟨m, Hrel⟩
    exact ViewRel.rel_validN _ _ _ Hrel
  intro Hv
  let FF : (K → (DFrac F × V) → Option V) := fun k _ => (Store.get f k).bind (fun x => some x.2)
  exists ((IHHmap V).hhmap FF f)
  simp [HeapR, Store.all]
  intro k
  cases h : Store.get f k <;> simp []
  rename_i val
  rintro a b rfl
  exists b
  simp [hhmap_get, h, FF]
  exists a
  refine ⟨?_, CMRA.incN_refl _⟩
  have Hv' := h ▸ Hv k
  exact Hv'

instance gmap_view_rel_discrete [CMRA.Discrete V] : ViewRelDiscrete (HeapR F K V H) where
  discrete n h H := by
    simp [HeapR, Store.all]
    intro H k a b He
    have H' := H k a b He
    obtain ⟨v, Hv1, ⟨x, Hx1, Hx2⟩⟩ := H'
    refine ⟨v, Hv1, ⟨x, ?_, ?_⟩⟩
    · simp [CMRA.ValidN, Prod.ValidN] at Hx1 ⊢
      refine ⟨Hx1.1, ?_⟩
      apply CMRA.valid_iff_validN.mp
      apply CMRA.Discrete.discrete_valid
      exact Hx1.2
    · exact (CMRA.inc_0_iff_incN n).mp Hx2

abbrev HeapView := View F (HeapR F K V H)

end heap_view

section heap_view_laws

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]
variable [IHHmap : ∀ V, HasHHMap (H  (DFrac F × V)) (H V) K (DFrac F × V) V]

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

omit IHHmap in
theorem heap_view_rel_lookup n m k dq v :
    HeapR F K V H n m (Heap.point k <| .some (dq, v)) ↔
    ∃ (v' : V) (dq' : DFrac F), Store.get m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') := by
  constructor
  · intro Hrel
    have Hrel' := Hrel k (dq, v)
    simp only [HeapR, Store.all,   Heap.point, Store.get_set_eq] at Hrel'
    obtain ⟨v', dq', Hlookup, Hval, Hinc⟩ := Hrel' trivial
    exists v'; exists dq'
  · rintro ⟨v', dq', Hlookup, Hval, _⟩ j
    simp only [HeapR, Store.all,   Heap.point]
    if h : k = j
      then
        simp [Store.get_set_eq h]
        exists v'
        refine ⟨h ▸ Hlookup, ?_⟩
        exists dq'
      else simp [Store.get_set_ne h, Heap.get_empty]

omit IHHmap in
theorem heap_view_auth_dfrac_op (dp dq : DFrac F) (m : H V) :
    (heap_view_auth (dp • dq) m) ≡ (heap_view_auth dp m) • heap_view_auth dq m := by
  exact View.view_auth_dfrac_op

omit IHHmap in
theorem heap_view_auth_dfrac_op_invN n dp m1 dq m2 :
    (✓{n} ((heap_view_auth dp m1) : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡{n}≡ m2 := by
  exact fun a => View.view_auth_dfrac_op_invN a

omit IHHmap in
theorem heap_view_auth_dfrac_op_inv dp m1 dq m2 : ✓ ((heap_view_auth dp m1 : HeapView F K V H) • heap_view_auth dq m2) → m1 ≡ m2 := by
  exact fun a => View.view_auth_dfrac_op_inv a

omit IHHmap in
theorem heap_view_auth_dfrac_validN m n dq : ✓{n} (heap_view_auth dq m : HeapView F K V H) ↔ ✓ (dq : DFrac F) := by
  apply View.view_auth_dfrac_validN.trans
  suffices ✓{n} dq ↔ ✓ dq by
    apply and_iff_left_of_imp (fun _ => ?_)
    apply view_rel_unit
  exact Eq.to_iff rfl

omit IHHmap in
theorem heap_view_auth_dfrac_valid m dq : ✓ (heap_view_auth dq m : HeapView F K V H) ↔ ✓ dq := by
  apply View.view_auth_dfrac_valid.trans
  refine and_iff_left_of_imp (fun _ n => ?_)
  exact view_rel_unit F K V H

omit IHHmap in
theorem heap_view_auth_valid m : ✓ (heap_view_auth (.own One.one) m : HeapView F K V H) := by
  apply (heap_view_auth_dfrac_valid _ _).mpr valid_own_one

omit IHHmap in
theorem heap_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1 • dq2) ∧ m1 ≡{n}≡ m2 := by
  apply View.view_auth_dfrac_op_validN.trans
  refine and_congr_right (fun _ => ?_)
  refine and_iff_left_of_imp (fun _ => ?_)
  exact view_rel_unit F K V H

omit IHHmap in
theorem heap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ ((heap_view_auth dq1 m1 : HeapView F K V H) • heap_view_auth dq2 m2) ↔ ✓ (dq1  • dq2) ∧ m1 ≡ m2 := by
  apply View.view_auth_dfrac_op_valid.trans
  refine and_congr_right (fun _ => ?_)
  refine and_iff_left_of_imp (fun _ n => ?_)
  exact view_rel_unit F K V H

omit IHHmap in
theorem heap_view_auth_op_validN n m1 m2 : ✓{n} ((heap_view_auth (.own One.one) m1 : HeapView F K V H) • (heap_view_auth (.own One.one) m2)) ↔ False := by
  apply View.view_auth_op_validN

omit IHHmap in
theorem heap_view_auth_op_valid m1 m2 : ✓ ((heap_view_auth (.own One.one) m1 : HeapView F K V H)  • heap_view_auth (.own One.one) m2) ↔ False := by
  apply View.view_auth_op_valid

theorem heap_view_frag_validN n k dq v : ✓{n} (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓{n} v := by
  apply View.view_frag_validN.trans
  apply (heap_view_rel_exists F K V H _ _).trans
  apply point_validN

theorem heap_view_frag_valid k dq v : ✓ (heap_view_frag k dq v : HeapView F K V H) ↔ ✓ dq ∧ ✓ v := by
  suffices (∀ n, ✓{n} (heap_view_frag k dq v : HeapView F K V H)) ↔ ✓ dq ∧ ✓ v by exact this
  suffices (∀ n, ✓ dq ∧ ✓{n} v) ↔ ✓ dq ∧ ✓ v by
    apply Iff.trans (forall_congr' (heap_view_frag_validN · k dq v)) this
  constructor
  · refine fun H => ⟨?_, ?_⟩
    · apply CMRA.valid_iff_validN.mpr (H · |>.1)
    · apply CMRA.valid_iff_validN.mpr (H · |>.2)
  · rintro ⟨H1, H2⟩ n
    refine ⟨?_, ?_⟩
    · apply CMRA.valid_iff_validN.mp H1 n
    · apply CMRA.valid_iff_validN.mp H2 n

omit IHHmap in
theorem heap_view_frag_op k dq1 dq2 v1 v2 :
    (heap_view_frag k (dq1 • dq2) (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k dq1 v1  • heap_view_frag k dq2 v2 := by
  simp [heap_view_frag]
  rw [← View.view_frag_op]
  apply View.frag_ne.eqv
  apply Store.eqv_of_Equiv
  apply Store.Equiv_trans.trans _ point_op.symm
  rfl

omit IHHmap in
theorem heap_view_frag_add k q1 q2 v1 v2 :
    (heap_view_frag k (.own (q1 + q2)) (v1  • v2) : HeapView F K V H) ≡
      heap_view_frag k (.own q1) v1  • heap_view_frag k (.own q2) v2 := by
  apply heap_view_frag_op

theorem heap_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓{n} (v1  • v2) := by
  apply View.view_frag_validN.trans
  apply (heap_view_rel_exists F K V H _ _ ).trans
  apply Iff.trans
  · apply CMRA.validN_iff
    apply OFE.equiv_dist.mp
    apply Store.eqv_of_Equiv
    apply point_op
  apply point_validN.trans
  apply Eq.to_iff rfl

theorem heap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ ((heap_view_frag k dq1 v1 : HeapView F K V H) • heap_view_frag k dq2 v2) ↔
      ✓ (dq1  • dq2) ∧ ✓ (v1  • v2) := by
  apply View.view_frag_valid.trans
  suffices (∀ (n : Nat), ✓{n} dq1 • dq2 ∧ ✓{n} v1 • v2) ↔ ✓ dq1 • dq2 ∧ ✓ v1 • v2 by
    apply Iff.trans _ this
    apply forall_congr'
    intro n
    apply (heap_view_rel_exists F K V H _ _ ).trans
    simp [heap_view_frag]
    apply Iff.trans
    · apply CMRA.validN_iff
      apply OFE.equiv_dist.mp
      apply Store.eqv_of_Equiv
      apply point_op
    apply point_validN.trans
    apply Eq.to_iff rfl
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · apply CMRA.valid_iff_validN.mpr <| fun n => (H n).1
    · apply CMRA.valid_iff_validN.mpr <| fun n => (H n).2
  · rintro ⟨H1, H2⟩ n
    refine ⟨?_, ?_⟩
    · apply CMRA.valid_iff_validN.mp H1
    · apply CMRA.valid_iff_validN.mp H2


omit IHHmap in
theorem heap_view_both_dfrac_validN n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H)  • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ Store.get m k = some v' ∧ ✓{n} (dq', v') ∧
                some (dq, v) ≼{n} some (dq', v') := by
  simp [heap_view_auth, heap_view_frag]
  apply View.view_both_dfrac_validN.trans
  refine and_congr_right (fun H1 => ?_)
  apply (heap_view_rel_lookup _ _ _ _ _).trans
  refine exists_congr (fun x => ?_)
  exact exists_and_left

omit IHHmap in
theorem heap_view_both_validN n dp m k v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k (.own One.one) v) ↔
      ✓ dp ∧ ✓{n} v ∧ Store.get m k ≡{n}≡ some v := by
  apply (heap_view_both_dfrac_validN _ _ _ _ _ _).trans
  constructor
  · rintro ⟨Hdp, v', dq', Hlookup, Hvalid, Hincl⟩
    have Heq : v ≡{n}≡ Hdp := by
      have Z := @some_incN_exclusive _ _ (DFrac.own One.one, v) n ?G _ Hincl Hvalid
      case G =>
        -- TODO: This should be a DFrac lemma
        constructor
        rintro ⟨y1, y2⟩
        simp [CMRA.ValidN, CMRA.op]
        intro H
        exfalso
        cases y1 <;> simp [valid, op] at H
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
      · simp [valid]
        apply  (UFraction.one_whole (α := F)).1
      rw [h] at Hlookup
      exact (Dist.validN (id (Dist.symm Hlookup))).mp Hval
    · apply some_incN.mpr ?_; left
      apply dist_prod_ext rfl ?_
      exact id (Dist.symm (h.symm ▸ Hlookup : some _ ≡{n}≡ some _))

omit IHHmap in
theorem heap_view_both_dfrac_validN_total [CMRA.IsTotal V] n dp m k dq v :
    ✓{n} ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓{n} v' ∧ v ≼{n} v' := by
  intro H; have H' := (heap_view_both_dfrac_validN _ _ _ _ _ _).mp H; clear H
  obtain ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ := H'
  exists v'
  refine ⟨Hdp, ?_, Hlookup, Hvalid.2, ?_⟩
  · suffices some dq ≼ some dq' by
      apply option_valid_Some_included ?_ this
      apply (CMRA.valid_iff_validN' n).mpr Hvalid.1
    apply (CMRA.inc_iff_incN n).mpr
    rcases Hincl with ⟨x, Hx⟩
    rcases x with (_|x) <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.incN_of_incN_of_dist (CMRA.incN_refl _)
      apply Hx.1.symm
    · exists x.1
      simp [CMRA.op, optionOp]
      apply Hx.1
  · suffices some v ≼{n} some v' by exact some_incN_total.mp this
    apply some_incN_total.mpr ?_
    rcases Hincl with ⟨x, Hx⟩
    rcases x with (_|x) <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.incN_of_incN_of_dist (CMRA.incN_refl _)
      apply Hx.2.symm
    · exists x.2
      apply Hx.2

omit IHHmap in
theorem heap_view_both_dfrac_valid_discrete [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) ↔
      ∃ v' dq', ✓ dp ∧ Store.get m k = some v' ∧ ✓ (dq', v') ∧ some (dq, v) ≼ some (dq', v') := by
  apply CMRA.valid_iff_validN.trans
  apply Iff.trans
  · apply forall_congr'
    intro _
    apply heap_view_both_dfrac_validN
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
    exists v'; exists dq'
    refine ⟨Hdp, Hlookup, Hvalid.validN, (CMRA.inc_iff_incN n).mp Hincl⟩

omit IHHmap in
theorem heap_view_both_dfrac_valid_discrete_total [CMRA.IsTotal V] [CMRA.Discrete V] dp m k dq v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k dq v) →
    ∃ v', ✓ dp ∧ ✓ dq ∧ Store.get m k = some v' ∧ ✓ v' ∧ v ≼ v' := by
  intro H
  obtain ⟨v', dq', Hdp, Hlookup, Hvalid, Hincl⟩ :=  (heap_view_both_dfrac_valid_discrete _ _ _ _ _).mp H
  exists v'
  refine ⟨Hdp, ?_, Hlookup , ?_, ?_⟩
  · rcases Hincl with ⟨(_|x), Hx⟩ <;> simp [CMRA.op, optionOp, Prod.op] at Hx
    · apply CMRA.valid_of_eqv Hx.1
      simp [CMRA.Valid, Prod.Valid] at Hvalid
      apply Hvalid.1
    · suffices some dq ≼ some dq' by exact option_valid_Some_included Hvalid.1 this
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

omit IHHmap in
theorem heap_view_both_valid m dp k v :
    ✓ ((heap_view_auth dp m : HeapView F K V H) • heap_view_frag k (.own One.one) v) ↔
    ✓ dp ∧ ✓ v ∧ Store.get m k ≡ some v := by
  apply CMRA.valid_iff_validN.trans
  apply Iff.trans
  · apply forall_congr'
    intro _
    apply heap_view_both_validN
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

instance heap_view_frag_core_id [CMRA.CoreId dq] [CMRA.CoreId v] :
    CMRA.CoreId (heap_view_frag k dq v : HeapView F K V H) := by
  rename_i H1 H2
  obtain ⟨H1⟩ := H1
  obtain ⟨H2⟩ := H2
  constructor
  simp only [heap_view_frag, CMRA.pcore]
  simp only [View.pcore, some_eqv_some]
  refine NonExpansive₂.eqv trivial ?_
  refine point_core' ?_
  simp [CMRA.pcore, Prod.pcore]
  simp [CMRA.pcore] at H1
  simp [H1]
  cases h : (CMRA.pcore v) <;> simp_all
  refine ⟨rfl, ?_⟩
  exact H2

instance heap_view_cmra_discrete [CMRA.Discrete V] : CMRA.Discrete (HeapView F K V H) := by
  infer_instance

end heap_view_laws

section heap_updates

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [∀ V, Heap (H V) K V] [CMRA V]

theorem heap_view_alloc m k dq (v : V) : (Store.get m k = none) → ✓ dq → ✓ v →
    heap_view_auth (.own 1) m ~~>
    ((heap_view_auth (.own 1) (Store.set m k (.some v)) : HeapView F K V H) • heap_view_frag k dq v) := by
  intro Hfresh Hdq Hval
  refine View.view_update_alloc (fun n bf Hrel j => ?_ )
  simp [CMRA.op, get_merge, Option.merge]
  if h : k = j
    then
      rw [Heap.point_get_eq h]
      have Hbf : Store.get bf j = none := by
        cases hc : Store.get bf j; rfl
        simp [HeapR, Store.all] at Hrel
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
      simp [HeapR, Store.all] at Hrel
      rcases Hrel j a b hc with ⟨v, He, q, Hv, Hframe, Hinc⟩
      rw [get_set_ne h]
      exists v
      refine ⟨He, ?_⟩
      exists q
      refine ⟨Hv, ?_⟩
      exists Hframe

theorem heap_view_delete m k (v : V) :
   (heap_view_auth (.own 1) m : HeapView F K V H) • (heap_view_frag k (.own 1) v : HeapView F K V H) ~~>
   heap_view_auth (.own 1) (Heap.delete m k) := by
  refine View.view_update_dealloc (fun n bf Hrel j => ?_)
  cases He : Store.get bf j
  · intro _ HK; simp at HK
  if h : k = j
    then
      simp [HeapR, Store.all,   CMRA.op, get_merge, Option.merge] at Hrel
      have Hrel' := Hrel k; clear Hrel
      simp [h, He, Heap.point_get_eq rfl] at Hrel'
      obtain ⟨v, HK, q, Hqv, Hqinc⟩ := Hrel'
      rename_i vv
      have Hval := option_validN_Some_includedN (Hv := Hqv) (Hinc := Hqinc)
      exfalso
      obtain ⟨z, _⟩ := Hqinc
      simp [CMRA.ValidN, Prod.op, Prod.ValidN] at Hval
      have HK := Hval.1
      obtain ⟨(f|_|f), _⟩ := vv <;> simp [valid, CMRA.op, op] at HK
      · apply (UFraction.one_whole (α := F)).2; exists f
      · apply (UFraction.one_whole (α := F)).2; exact HK
      · apply (UFraction.one_whole (α := F)).2
        exists f
        exact Fraction.Fractional.proper HK
    else
      simp [HeapR, Store.all, CMRA.op, get_merge, Option.merge] at Hrel
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

theorem heap_view_update (m : H _) k (dq : DFrac F) (v mv' v': V) (dq' : DFrac F) :
  (∀ (n : Nat) (mv : V) (f : Option (DFrac F × V)),
    (Store.get m k = some mv) →
    ✓{n} ((dq, v) •? f) →
     (mv ≡{n}≡ ((v : V) •? (Prod.snd <$> f))) →
     ✓{n} ((dq', v') •? f) ∧ (mv' ≡{n}≡ v' •? (Prod.snd <$> f))) →
  ((heap_view_auth (.own 1) m : HeapView F K V H) • (heap_view_frag k dq v : HeapView F K V H)) ~~>
  ((heap_view_auth (.own 1) (Store.set m k (some mv')) : HeapView F K V H) • (heap_view_frag k dq' v' : HeapView F K V H)) := by
  intro Hup
  apply View.view_update
  rintro n bf Hrel j ⟨df, va⟩
  simp [CMRA.op, Heap.get_merge, Prod.op]
  if h : k = j
    then
      simp [Heap.point, Store.get_set_eq h, Heap.get_empty]
      intro Hbf
      have Hrel' := Hrel k ((dq, v) •? (Store.get bf k))
      have Hrel'' := Hrel' ?G; clear Hrel'
      case G=>
        clear Hrel'
        simp [CMRA.op, Heap.get_merge, Heap.point, Store.get_set_eq h, CMRA.op?]
        cases h : Store.get bf k <;> simp [Option.merge, h, Store.get_set_eq rfl]
      obtain ⟨mv, mdf, Hlookup, Hval, Hincl'⟩ := Hrel''
      obtain ⟨f', Hincl⟩ := option_some_incN_opM_iff.mp Hincl'; clear Hincl'
      let f := (Store.get bf k) • f'
      have Hincl' : (mdf, mv) ≡{n}≡ (dq, v) •? f := by
        refine .trans Hincl ?_
        apply OFE.Equiv.dist
        apply CMRA.opM_opM_assoc
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
        suffices HF : some ((dq', v') •? (Store.get bf j)) ≼{n} some (dq' •? (Option.map Prod.fst f), mv') by
          apply CMRA.incN_trans ?_ HF
          simp [Option.merge, Prod.op, CMRA.op?]
          cases h : Store.get bf j <;> simp
          · exact CMRA.incN_refl _
          · exact CMRA.incN_refl _
        apply option_some_incN_opM_iff.mpr
        exists f'
        refine OFE.Dist.trans (y := (dq' •? Option.map Prod.fst f, v' •? Prod.snd <$> f)) ?_ ?_
        · exact OFE.dist_prod_ext rfl Hincl'
        apply OFE.Dist.trans ?_
        · apply OFE.equiv_dist.mp
          exact CMRA.opM_opM_assoc.symm
        obtain H : Store.get bf j • f' = f := by rw [← h]
        rw [H]
        simp [Option.map]
        cases h : f
        · simp [CMRA.op, optionOp, CMRA.op?]
        · simp [CMRA.op, optionOp, CMRA.op?, Prod.op]
    else
      simp [Heap.point, Store.get_set_ne h, Heap.get_empty]
      intro Hbf
      have Hrel' := Hrel j (df, va) -- (dq • df, v • va)
      simp [CMRA.op, Heap.get_merge, Prod.op] at Hrel'
      simp [Option.merge, Heap.point, Store.get_set_ne h, Heap.get_empty] at Hrel'
      simp only [Hbf] at Hrel'
      exact Hrel' trivial

theorem heap_update_local m k dq v mv' v' :
    (Store.get m k = some mv) →
    (mv, v) ~l~> (mv', v') →
    ((heap_view_auth (.own 1) m : HeapView F K V H) • heap_view_frag k dq v) ~~>
    ((heap_view_auth (.own 1) (Store.set m k (.some mv')) : HeapView F K V H) • heap_view_frag k dq v') := by
  intro Hlookup Hup
  apply heap_view_update
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

theorem heap_view_replace m k v v' :
    ✓ v' →
    ((heap_view_auth (.own 1) m : HeapView F K V H) • (heap_view_frag k (.own 1) v : HeapView F K V H)) ~~>
    ((heap_view_auth (F := F) (.own 1) (Store.set m k (.some v'))) • (heap_view_frag (F := F) k (.own 1) v')) := by
  intro Hval'
  apply heap_view_update
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

theorem heap_view_auth_persist dq m : (heap_view_auth dq m : HeapView F K V H) ~~> heap_view_auth .discard m := by
  exact View.view_update_auth_persist

theorem heap_view_auth_unpersist [IsSplitFraction F] m :
  (heap_view_auth .discard m : HeapView F K V H) ~~>: fun a => ∃ q, a = heap_view_auth (F := F) (.own q) m := by
  exact View.view_updateP_auth_unpersist

theorem heap_view_frag_dfrac k dq P v : dq ~~>: P →
    (heap_view_frag k dq v : HeapView F K V H) ~~>: fun a => ∃ dq', a = heap_view_frag k dq' v ∧ P dq' := by
  intro Hdq
  apply UpdateP.weaken
  · apply View.view_updateP_frag (P := fun b' => ∃ dq', ((◯V b') = heap_view_frag k dq' v) ∧ P dq')
    intros m n bf Hrel
    simp only [HeapR, Store.all] at Hrel
    have Hrel' := Hrel k ((dq, v) •? Store.get bf k) ?G
    case G=>
      simp [CMRA.op, Heap.get_merge, Heap.point_get_eq rfl, Option.merge, CMRA.op?]
      cases Store.get bf k <;> simp
    obtain ⟨v', dq', Hlookup, Hval, Hincl⟩ := Hrel'
    obtain ⟨f', Hincl⟩ := option_some_incN_opM_iff.mp Hincl
    have Hincl' : (dq', v') ≡{n}≡ (dq, v) •? ((Store.get bf k) • f') := by
      refine Hincl.trans ?_
      apply OFE.equiv_dist.mp
      exact CMRA.opM_opM_assoc
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
        cases h : f' <;> cases h' : Store.get bf k <;> simp [OFE.Dist, Option.Forall₂, CMRA.op, optionOp, CMRA.op?] <;>
        simp_all [h', h, CMRA.op, optionOp, CMRA.op?, Prod.op]
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

theorem heap_view_frag_persist k dq v :
  (heap_view_frag k dq v : HeapView F K V H) ~~> heap_view_frag k .discard v := by
  apply Update.lift_updateP (fun (dq : DFrac F) => heap_view_frag (H := H) (F := F) k dq v)
  · exact fun P Hupd => heap_view_frag_dfrac k dq P v Hupd
  · exact dfrac_discard_update

theorem heap_view_frag_unpersist [IsSplitFraction F] k v :
    (heap_view_frag k .discard v : HeapView F K V H) ~~>:
    fun a => ∃ q, a = heap_view_frag k (.own q) v := by
  apply UpdateP.weaken
  · apply heap_view_frag_dfrac
    apply dfrac_undiscard_update
  rintro y ⟨q, rfl, ⟨q1, rfl⟩⟩
  exists q1

section heap_updates

-- TODO: Port functors
