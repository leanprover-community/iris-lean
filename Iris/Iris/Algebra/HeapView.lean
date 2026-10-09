/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu, Janine Lohse
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

variable {SI : Type _} [instSI : Iris.SIdx SI]

open Iris

section heapView
open Std PartialMap Heap OFE ORA

variable (K V : Type _) (H : Type _ → Type _) [LawfulPartialMap H K] [RA V] [ORA SI V]

#rocq_ignore gmap_view_fragUR "Inlined as the fragment type `H (DFrac × V)`"

/-- The view relation for heaps: relates a model heap to a fragment heap at step index `n`. -/
@[rocq_alias gmap_view_rel_raw]
def HeapR (n : SI) (m : H V) (f : H (DFrac × V)) : Prop :=
  ∀ k fv, get? f k = some fv →
    ∃ (v : V) (dq : DFrac), get? m k = some v ∧ ✓{n} (dq, v) ∧ ∃ c, some fv • c ≼ₒ{n} some (dq, v)

def HeapRInc (n : SI) (m : H V) (f : H (DFrac × V)) : Prop :=
  ∀ k fv, get? f k = some fv →
    ∃ (v : V) (dq : DFrac), get? m k = some v ∧ ✓{n} (dq, v) ∧ some fv ≼{n} some (dq, v)

#rocq_ignore gmap_view_rel_raw_mono "The `mono` field of the `IsViewRel (HeapR ..)` instance"
#rocq_ignore gmap_view_rel_raw_valid "The `rel_validN` field of the `IsViewRel (HeapR ..)` instance"
#rocq_ignore gmap_view_rel_raw_unit "The `rel_unit` field of the `IsViewRel (HeapR ..)` instance"

@[rocq_alias gmap_view_rel]
instance : IsViewRel (HeapR (SI := SI) K V H) where
  mono := by
    intro n1 m1 f1 n2 m2 f2 Hrel Hm Hf Hn k vk Hk
    obtain Hf' : (some vk : Option ((DFrac) × V)) ≼ₒ{n2} get? f1 k := Hk ▸ Hf k
    match h : get? f1 k with
    | none => exact absurd (h ▸ Hf') Option.not_some_ordN_none
    | some ⟨dq', v'⟩ =>
      obtain ⟨v, dq, Hm1, ⟨Hvval, Hdqval⟩, c, Hvincl⟩ := Hrel k ⟨dq', v'⟩ h
      obtain ⟨v'', Hm2, Hv⟩ : ∃ y : V, get? m2 k = some y ∧ v ≡{n2}≡ y := by
        have Hmm := Hm1 ▸ Hm k; revert Hmm
        cases get? m2 k <;> simp
      refine ⟨v'', dq, Hm2, ⟨Hvval, validN_ne Hv (validN_of_le Hn Hdqval)⟩, c, ?_⟩
      refine ordN_of_ordN_of_dist (b := some (dq, v)) ?_ (OFE.some_dist_some.mpr ⟨rfl, Hv⟩)
      exact (op_monoN_left_ord c (h ▸ Hf')).trans (ordN_of_ordN_le Hn Hvincl)
  op_left {n : SI} {m f g} Hrel k fv Hk := by
    have e : some fv • get? g k = some (fv •? get? g k) := by cases get? g k <;> rfl
    obtain ⟨v, dq, Hm, Hv, c, Hc⟩ := Hrel k _ ((get?_op f g).trans (Hk ▸ e))
    refine ⟨v, dq, Hm, Hv, get? g k • c, ?_⟩
    rw [assoc', e]
    exact Hc
  rel_validN n m f Hrel k := by
    match Hf : get? f k with
    | none => simp [ValidN, optionValidN]
    | some _ =>
      obtain ⟨_, _, _, Hvv, _, Hvi⟩ := Hf ▸ Hrel k _ Hf
      exact (Hf ▸ validN_op_left (validN_of_ordN Hvi Hvv))
  rel_unit n := by
    refine ⟨empty, fun _ _ => ?_⟩
    simp [UnitOp.unit, Heap.unit, get?_empty]

namespace HeapR

theorem of_inc {n : SI} {m f} (h : HeapRInc K V H n m f) : HeapR K V H n m f := fun k fv hk =>
  let ⟨v, dq, hm, hv, c, hc⟩ := h k fv hk
  ⟨v, dq, hm, hv, c, ordN_of_dist hc.symm⟩

theorem iff_inc [OrdInc SI V] {n : SI} {m f} : HeapR K V H n m f ↔ HeapRInc K V H n m f :=
  forall₂_congr fun _ _ => imp_congr_right fun _ => exists₂_congr fun _ _ =>
    and_congr_right fun _ => and_congr_right fun _ => exists_op_ordN_iff_incN

@[rocq_alias gmap_view_rel_unit]
theorem unit {n : SI} {m : H V} : HeapR K V H n m UnitOp.unit := by
  simp [HeapR, UnitOp.unit, Heap.unit, get?_empty]

@[rocq_alias gmap_view_rel_exists]
theorem exists_iff_validN {n : SI} {f} : (∃ m, HeapR K V H n m f) ↔ ✓{n} f := by
  refine ⟨fun ⟨m, Hrel⟩ => IsViewRel.rel_validN _ _ _ Hrel, fun Hv => ?_⟩
  let FF : K → (DFrac × V) → Option V := fun k _ => get? f k |>.bind (·.2)
  refine ⟨bindAlter FF f, fun k => ?_⟩
  cases h : get? f k
  · simp
  simp only [Option.some.injEq, exists_and_left]
  rintro ⟨dq, v⟩ rfl
  exists v
  simp only [get?_bindAlter, h, Option.bind_some, true_and, FF]
  exact ⟨dq, (h ▸ Hv k : ✓{n} some (dq, v)), none, ordN_refl _⟩

theorem singleton_get_iff_frame (n : SI) m k dq v :
    HeapR K V H n m (PartialMap.singleton k (dq, v)) ↔
      ∃ (v' : V) (dq' : DFrac),
        get? m k = some v' ∧ ✓{n} (dq', v') ∧ ∃ c, some (dq, v) • c ≼ₒ{n} some (dq', v') := by
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

theorem singleton_get_iff_ord [IncOrd SI V] (n : SI) m k dq v :
    HeapR K V H n m (PartialMap.singleton k (dq, v)) ↔
      ∃ (v' : V) (dq' : DFrac),
        get? m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼ₒ{n} some (dq', v') :=
  (singleton_get_iff_frame ..).trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => exists_op_ordN_iff_ordN

@[rocq_alias gmap_view_rel_lookup]
theorem singleton_get_iff [OrdInc SI V] (n : SI) m k dq v :
    HeapR K V H n m (PartialMap.singleton k (dq, v)) ↔
      ∃ (v' : V) (dq' : DFrac),
        get? m k = some v' ∧ ✓{n} (dq', v') ∧ some (dq, v) ≼{n} some (dq', v') :=
  (singleton_get_iff_frame ..).trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => exists_op_ordN_iff_incN

@[rocq_alias gmap_view_rel_discrete]
instance [ORA.Discrete SI V] : IsViewRelDiscrete (HeapR (SI := SI) K V H) where
  discrete n _ _ H k v He := by
    have ⟨v, Hv1, ⟨x, Hx1, c, Hx2⟩⟩ := H k v He
    refine ⟨v, Hv1, ⟨x, ?_, c, ordN_of_ord _ (discrete_ord Hx2)⟩⟩
    exact ⟨Hx1.1, valid_iff_validN.mp (Discrete.discrete_valid Hx1.2) _⟩

end HeapR

#rocq_ignore gmap_viewO "Use `HeapView`; the OFE instance is found by typeclass inference"
#rocq_ignore gmap_viewUR "Use `HeapView`; the UCMRA instance is found by typeclass inference"
#rocq_ignore gmap_view_cmra_discrete "Found by typeclass inference"

/-- A view of a Heap, that gives element-wise ownership. -/
@[rocq_alias gmap_viewR]
abbrev HeapView := View (HeapR (SI := SI) K V H)

end heapView

namespace HeapView

open Heap OFE View One DFrac ORA PartialMap Std LawfulPartialMap

variable {K V : Type _} {H : Type _ → Type _} [LawfulPartialMap H K] [RA V] [ORA SI V]

/-- Authoritative (fractional) ownership over an entire heap. -/
@[rocq_alias gmap_view_auth]
def Auth (dq : DFrac) (m : H V) : HeapView (SI := SI) K V H := ●V{dq} m

/-- Fragmental (fractional) ownership over an allocated element in the heap. -/
@[rocq_alias gmap_view_frag]
def Frag (k : K) (dq : DFrac) (v : V) : HeapView (SI := SI) K V H := ◯V (Std.PartialMap.singleton k (dq, v))

/-- Fragmental (fractional) ownership over an element in the heap. -/
def Elem (k : K) (v : DFrac × V) : HeapView (SI := SI) K V H := ◯V (Std.PartialMap.singleton k v)

-- TODO: Do we need this?
@[rocq_alias gmap_view_auth_ne]
instance : NonExpansive SI (Auth (SI := SI) dq : _ → HeapView K V H) := View.auth_ne

#rocq_ignore gmap_view_auth_proper "OFE is Leibniz; use `congrArg`"

@[rocq_alias gmap_view_frag_ne]
instance : NonExpansive SI (Frag (SI := SI) k dq : _ → HeapView K V H) where
  ne _ _ _ Hx := by
    refine frag_ne.ne (fun k' => ?_)
    by_cases h : k = k'
    · rw [Std.PartialMap.singleton, get?_insert_eq h, get?_singleton_eq h]
      exact dist_prod_ext rfl Hx
    · rw [Std.PartialMap.singleton, get?_insert_ne h, get?_empty, get?_singleton_ne h]
      try rfl

#rocq_ignore gmap_view_frag_proper "OFE is Leibniz; use `congrArg`"

variable {dp dq : DFrac} {n : SI} {m1 m2 : H V} {k : K} {v1 v2 : V}

@[rocq_alias gmap_view_auth_dfrac_op]
theorem auth_dfrac_op_eqv : Auth (dp • dq) m1 = Auth (SI := SI) dp m1 • Auth dq m1 :=
  View.auth_op_auth_eqv (SI := SI)

set_option synthInstance.checkSynthOrder false in
@[rocq_alias gmap_view_auth_dfrac_is_op]
instance [h : IsOp d dq dq1 dq2] :
    IsOp d (Auth (H := H) dq m1) (Auth (SI := SI) dq1 m1) (Auth dq2 m1) where
  is_op := by
    rw [h.is_op]
    exact auth_dfrac_op_eqv

/-- An `Auth` inclusion follows from a map equality on the underlying heap.
This is the workhorse for proofs that rewrite the authoritative map along identities like
`PartialMap.map_insert`, `map_delete`, or `map_union`. -/
theorem auth_ord_of_map_eq (dq : DFrac) (h : m1 = m2) :
    Auth (SI := SI) dq m1 ≼ₒ[SI] Auth dq m2 := h ▸ ord_refl _

@[rocq_alias gmap_view_auth_dfrac_op_invN]
theorem dist_of_validN_auth_op : ✓{n} Auth (SI := SI) dp m1 • Auth dq m2 → m1 ≡{n}≡ m2 :=
  dist_of_validN_auth

@[rocq_alias gmap_view_auth_dfrac_op_inv]
theorem equiv_of_valid_auth_op : ✓[SI] Auth (SI := SI) dp m1 • Auth dq m2 → m1 = m2 :=
  eq_of_valid_auth

@[rocq_alias gmap_view_auth_dfrac_validN]
nonrec theorem auth_validN_iff : ✓{n} Auth (SI := SI) dq m1 ↔ ✓[SI] dq :=
  auth_validN_iff.trans <| and_iff_left_of_imp (fun _ => HeapR.unit _ _ _)

@[rocq_alias gmap_view_auth_dfrac_valid]
nonrec theorem auth_valid_iff : ✓[SI] Auth (SI := SI) dq m1 ↔ ✓[SI] dq :=
  auth_valid_iff.trans <| and_iff_left_of_imp (fun _ _ => HeapR.unit _ _ _)

@[rocq_alias gmap_view_auth_valid]
theorem auth_one_valid : ✓[SI] Auth (SI := SI) (.own one) m1 := auth_valid_iff.mpr valid_own_one

@[rocq_alias gmap_view_auth_dfrac_op_validN]
nonrec theorem auth_op_auth_validN_iff : ✓{n} Auth (SI := SI) dp m1 • Auth dq m2 ↔ ✓[SI] dp • dq ∧ m1 ≡{n}≡ m2 :=
  auth_op_auth_validN_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ => HeapR.unit _ _ _

@[rocq_alias gmap_view_auth_dfrac_op_valid]
nonrec theorem auth_op_auth_valid_iff : ✓[SI] Auth (SI := SI) dp m1 • Auth dq m2 ↔ ✓[SI] dp • dq ∧ m1 = m2 :=
  auth_op_auth_valid_iff.trans <|
  and_congr_right <| fun _ => and_iff_left_of_imp <| fun _ _ => HeapR.unit _ _ _

@[rocq_alias gmap_view_auth_op_validN]
nonrec theorem auth_one_op_auth_one_validN_iff :
    ✓{n} Auth (SI := SI) (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_validN_iff

@[rocq_alias gmap_view_auth_op_valid]
nonrec theorem auth_one_op_auth_one_valid_iff :
    ✓[SI] Auth (SI := SI) (.own one) m1 • Auth (.own one) m2 ↔ False :=
  auth_one_op_auth_one_valid_iff


@[rocq_alias gmap_view_frag_op]
theorem frag_op_eqv : Frag (H := H) k (dp • dq) (v1 • v2) = Frag (H := H) k dp v1 • Frag (SI := SI) k dq v2 :=
  congrArg (◯V ·) (singleton_op_singleton (x := (dp, v1)) (y := (dq, v2))).symm

set_option synthInstance.checkSynthOrder false in
@[rocq_alias gmap_view_frag_mut_is_op]
instance
  [hdp : IsOp d dp dp1 dp2]
  [hv : IsOp d v v1 v2] :
  IsOp d (Frag (SI := SI) k dp v) (Frag k dp1 v1) (Frag (H := H) k dp2 v2) where
  is_op := by
    rw [hdp.is_op, hv.is_op]
    exact frag_op_eqv

@[rocq_alias gmap_view_frag_add]
theorem frag_add_op_eqv {q1 q2 : Qp} :
    Frag (H := H) k (.own (q1 + q2)) (v1 • v2) = Frag (H := H) k (.own q1) v1 • Frag (SI := SI) k (.own q2) v2 :=
  frag_op_eqv (dp := .own q1) (dq := .own q2)

theorem auth_op_frag_validN_iff_frame :
    ✓{n} Auth (SI := SI) dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓[SI] dp ∧ (Std.PartialMap.get? m1 k = some v') ∧ ✓{n} (dq', v') ∧
      ∃ c : Option (DFrac × V), some (dq, v) • c ≼ₒ{n} some (dq', v') :=
  View.auth_op_frag_validN_iff.trans <|
    (and_congr_right fun _ => (HeapR.singleton_get_iff_frame ..).trans <|
    exists_congr fun _ => exists_and_left).trans (by grind)

theorem auth_op_frag_validN_iff_ord [IncOrd SI V] :
    ✓{n} Auth (SI := SI) dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓[SI] dp ∧ (Std.PartialMap.get? m1 k = some v') ∧ ✓{n} (dq', v') ∧
      some (dq, v) ≼ₒ{n} some (dq', v') :=
  auth_op_frag_validN_iff_frame.trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      exists_op_ordN_iff_ordN

@[rocq_alias gmap_view_both_dfrac_validN]
theorem auth_op_frag_validN_iff [OrdInc SI V] :
    ✓{n} Auth (SI := SI) dp m1 • Frag k dq v ↔
    ∃ v' dq', ✓[SI] dp ∧ (Std.PartialMap.get? m1 k = some v') ∧ ✓{n} (dq', v') ∧
      some (dq, v) ≼{n} some (dq', v') :=
  auth_op_frag_validN_iff_frame.trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      exists_op_ordN_iff_incN

@[rocq_alias gmap_view_both_validN]
theorem auth_op_frag_one_validN_iff :
    ✓{n} (Auth (SI := SI) dp m1 • Frag k (.own one) v1) ↔ ✓[SI] dp ∧ ✓{n} v1 ∧ Std.PartialMap.get? m1 k ≡{n}≡ some v1 := by
  refine auth_op_frag_validN_iff_frame.trans ⟨fun ⟨v', dq', Hp, Hl, Hv, c, Hi⟩ => ?_,
    fun ⟨Hp, Hv, Hl⟩ => ?_⟩
  · haveI : Exclusive SI (DFrac.own one) := DFrac.own_whole_exclusive
    cases c with
    | none =>
      exact Hi.elim (fun e => ⟨Hp, validN_ne e.2.symm Hv.2, Hl ▸ e.2.symm⟩)
        (absurd Hv.1 <| not_valid_of_exclN_inc (x := DFrac.own one) ·.1)
    | some _ => exact absurd (Ordered.OrderNR.validN Hi Hv) not_valid_exclN_op_left
  · match h : Std.PartialMap.get? m1 k with
    | none => simp [h] at Hl
    | some v' =>
      refine ⟨v', .own one, Hp, rfl, ⟨valid_own_one (SI := SI), Dist.validN (h ▸ Hl).symm |>.mp Hv⟩, none, ?_⟩
      exact Option.some_ordN_some_iff.mpr <| .inl <| dist_prod_ext rfl (h.symm ▸ Hl).symm

theorem auth_op_frag_validN_total_iff_ord [OrderRefl SI V] [IncOrd SI V]
    (H : ✓{n} Auth (SI := SI) dp m1 • Frag k dq v1) :
    ∃ v', ✓[SI] dp ∧ ✓[SI] dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓{n} v' ∧ v1 ≼ₒ{n} v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := (auth_op_frag_validN_iff_ord (SI := SI)).mp H
  exact ⟨v', Hdp, Hi.elim (validN_ne ·.1.symm Hv.1) (validN_of_ordN ·.1 Hv.1), Hl, Hv.2,
    Hi.elim (·.2.to_ordN) (·.2)⟩

@[rocq_alias gmap_view_both_dfrac_validN_total]
theorem auth_op_frag_validN_total_iff [OrderRefl SI V] [OrdInc SI V]
    (H : ✓{n} Auth (SI := SI) dp m1 • Frag k dq v1) :
    ∃ v', ✓[SI] dp ∧ ✓[SI] dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓{n} v' ∧ v1 ≼{n} v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := (auth_op_frag_validN_iff (SI := SI)).mp H
  have Hi := Option.dist_or_incN_of_some_incN_some Hi
  exact ⟨v', Hdp, Hi.elim (validN_ne ·.1.symm Hv.1) (validN_of_incN · Hv |>.1), Hl, Hv.2,
    Hi.elim (ordN_incN ·.2.to_ordN) fun ⟨z, hz⟩ => ⟨z.2, hz.2⟩⟩

theorem auth_op_frag_discrete_valid_iff_frame [ORA.Discrete SI V] :
    ✓[SI] Auth (SI := SI) dp m1 • Frag k dq v1 ↔
      ∃ v' dq', ✓[SI] dp ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓[SI] (dq', v') ∧
        ∃ c : Option (DFrac × V), some (dq, v1) • c ≼ₒ[SI] some (dq', v') := by
  refine (valid_iff_validN (SI := SI)).trans ?_
  refine forall_congr' (fun _ => auth_op_frag_validN_iff_frame) |>.trans ?_
  refine ⟨fun Hvalid' => ?_, ?_⟩
  · obtain ⟨v', dq', Hdp, Hl, Hv, c, Hi⟩ := Hvalid' 0
    refine ⟨v', dq', Hdp, Hl, ?_, c, (ord_iff_ordN 0).mpr Hi⟩
    exact ⟨discrete_valid Hv.1, discrete_valid Hv.2⟩
  · exact fun ⟨v', dq', Hdp, Hl, Hv, c, Hi⟩ n =>
      ⟨v', dq', Hdp, Hl, Hv.validN, c, (ord_iff_ordN n).mp Hi⟩

theorem auth_op_frag_discrete_valid_iff_ord [ORA.Discrete SI V] [IncOrd SI V] :
    ✓[SI] Auth (SI := SI) dp m1 • Frag k dq v1 ↔
      ∃ v' dq', ✓[SI] dp ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓[SI] (dq', v') ∧
        some (dq, v1) ≼ₒ[SI] some (dq', v') :=
  auth_op_frag_discrete_valid_iff_frame.trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      exists_op_ord_iff_ord

@[rocq_alias gmap_view_both_dfrac_valid_discrete]
theorem auth_op_frag_discrete_valid_iff [ORA.Discrete SI V] [OrdInc SI V] :
    ✓[SI] Auth (SI := SI) dp m1 • Frag k dq v1 ↔
      ∃ v' dq', ✓[SI] dp ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓[SI] (dq', v') ∧
        some (dq, v1) ≼ some (dq', v') :=
  auth_op_frag_discrete_valid_iff_frame.trans <| exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      exists_op_ord_iff_inc

theorem auth_op_frag_valid_total_discrete_iff_ord [OrderRefl SI V] [ORA.Discrete SI V] [IncOrd SI V]
    (H : ✓[SI] Auth (SI := SI) dp m1 • Frag k dq v1) :
    ∃ v', ✓[SI] dp ∧ ✓[SI] dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓[SI] v' ∧ v1 ≼ₒ[SI] v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := auth_op_frag_discrete_valid_iff_ord (SI := SI) |>.mp H
  exact ⟨v', Hdp, Hi.elim (fun e => (Prod.mk.inj e).1 ▸ Hv.1) (valid_of_ord ·.1 Hv.1), Hl, Hv.2,
    Hi.elim (fun e => (Prod.mk.inj e).2 ▸ ord_refl v1) (·.2)⟩

@[rocq_alias gmap_view_both_dfrac_valid_discrete_total]
theorem auth_op_frag_valid_total_discrete_iff [OrderRefl SI V] [ORA.Discrete SI V] [OrdInc SI V]
    (H : ✓[SI] Auth (SI := SI) dp m1 • Frag k dq v1) :
    ∃ v', ✓[SI] dp ∧ ✓[SI] dq ∧ Std.PartialMap.get? m1 k = some v' ∧ ✓[SI] v' ∧ v1 ≼ v' := by
  obtain ⟨v', dq', Hdp, Hl, Hv, Hi⟩ := auth_op_frag_discrete_valid_iff (SI := SI) |>.mp H
  have Hi := Option.eq_or_inc_of_some_inc_some Hi
  exact ⟨v', Hdp, Hi.elim (fun e => (Prod.mk.inj e).1 ▸ Hv.1) (valid_of_inc · Hv |>.1), Hl, Hv.2,
    Hi.elim (fun e => (Prod.mk.inj e).2 ▸ ord_inc (ord_refl (SI := SI) v1))
      fun ⟨z, hz⟩ => ⟨z.2, congrArg Prod.snd hz⟩⟩

@[rocq_alias gmap_view_both_valid]
theorem auth_op_frag_one_valid_iff :
    ✓[SI] Auth (SI := SI) dp m1 • Frag k (.own one) v1 ↔ ✓[SI] dp ∧ ✓[SI] v1 ∧ Std.PartialMap.get?  m1 k = some v1 := by
  refine (valid_iff_validN (SI := SI)).trans ?_
  refine forall_congr' (fun _ => auth_op_frag_one_validN_iff) |>.trans ?_
  refine ⟨fun Hv => ?_, ?_⟩
  · exact ⟨Hv 0 |>.1, valid_iff_validN.mpr (Hv · |>.2.1),
      OFE.eq_dist_2 (Hv · |>.2.2)⟩
  · exact fun ⟨Hdp, Hv, Hl⟩ n => ⟨Hdp, Hv.validN, Hl.dist⟩

@[rocq_alias gmap_view_frag_core_id]
instance [Hdq : CoreId dq] [Hv1 : CoreId v1] : CoreId (Frag (SI := SI) (H := H) k dq v1) where
  core_id := by
    obtain ⟨H⟩ := Hdq
    simp [ORA.pcore] at H
    simp only [ORA.pcore, View.Pcore]
    refine congrArg some (congrArg (View.mk _) (singleton_core_eq ?_))
    simp [ORA.pcore, Prod.pcore]
    cases h : ORA.pcore v1
    · exact OFE.not_none_eqv_some (h ▸ Hv1.core_id) |>.elim
    · simp only [Option.bind_some, H]
      exact (OFE.some_eqv_some).mpr
        (congrArg (Prod.mk _) ((OFE.some_eqv_some).mp (h ▸ Hv1.core_id)))

@[rocq_alias gmap_view_frag_validN]
nonrec theorem frag_validN_iff : ✓{n} Frag (SI := SI) (H := H) k dq v1 ↔ ✓[SI] dq ∧ ✓{n} v1 :=
  frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans singleton_validN_iff

@[rocq_alias gmap_view_frag_valid]
theorem frag_valid_iff : ✓[SI] Frag (SI := SI) (H := H) k dq v1 ↔ ✓[SI] dq ∧ ✓[SI] v1 := by
  refine (forall_congr' (fun _ => frag_validN_iff)).trans ?_
  refine ⟨fun H => ?_, fun ⟨H1, H2⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp H1 n, valid_iff_validN.mp H2 n⟩

@[rocq_alias gmap_view_frag_op_validN]
theorem frag_op_validN_iff :
    ✓{n} Frag (H := H) k dp v1 • Frag (SI := SI) k dq v2 ↔ ✓[SI] (dp • dq) ∧ ✓{n} (v1 • v2) := by
  refine View.frag_validN_iff.trans <| (HeapR.exists_iff_validN ..).trans ?_
  refine (validN_dist_iff (Dist.of_eq (singleton_op_singleton))).trans ?_
  exact singleton_validN_iff

@[rocq_alias gmap_view_frag_op_valid]
theorem frag_op_valid_iff :
    ✓[SI] (Frag (H := H) k dp v1 • Frag (SI := SI) k dq v2) ↔
    ✓[SI] (dp • dq) ∧ ✓[SI] (v1 • v2) := by
  suffices (∀ (n : SI), ✓{n} dp • dq ∧ ✓{n} v1 • v2) ↔ ✓[SI] dp • dq ∧ ✓[SI] v1 • v2 by
    refine (forall_congr' (fun _ => ?_)).trans this
    refine (HeapR.exists_iff_validN ..).trans ?_
    refine (validN_dist_iff (Dist.of_eq (singleton_op_singleton))).trans ?_
    exact singleton_validN_iff
  refine ⟨fun H => ?_, fun ⟨Hp, Hv⟩ n => ?_⟩
  · exact ⟨valid_iff_validN.mpr (H · |>.1), valid_iff_validN.mpr (H · |>.2)⟩
  · exact ⟨valid_iff_validN.mp Hp n, valid_iff_validN.mp Hv n⟩

section heapUpdates

@[rocq_alias gmap_view_alloc]
theorem update_one_alloc (Hfresh : Std.PartialMap.get? m1 k = none) (Hdq : ✓[SI] dq) (Hval : ✓[SI] v1) :
    Auth (.own one) m1 ~~>[SI] Auth (H := H) (.own one) (Std.PartialMap.insert m1 k v1) • Frag (SI := SI) k dq v1 := by
  refine auth_one_alloc (fun n bf Hrel j => ?_)
  simp only [ORA.op, Heap.op, get?_merge, Option.merge, exists_and_left, Prod.forall]
  by_cases h : k = j
  · have Hbf : Std.PartialMap.get? bf j = none := by cases _ : Std.PartialMap.get? bf j <;> grind [HeapR]
    rw [get?_singleton_eq h, Hbf]
    rintro _ _ ⟨rfl⟩
    exact ⟨v1, get?_insert_eq h, dq, ⟨Hdq, Hval.validN⟩, none, ordN_refl _⟩
  · rw [get?_singleton_ne h, get?_insert_ne h]
    simp only [HeapR, exists_and_left, Prod.forall] at Hrel
    cases Hbf : Std.PartialMap.get? bf j
    · grind
    exact (Hrel j · · <| · ▸ Hbf)

@[rocq_alias gmap_view_delete]
theorem update_one_delete :
    Auth (SI := SI) (.own one) m1 • Frag k (.own one) v1 ~~>[SI] Auth (.own one) (Std.PartialMap.delete m1 k) := by
  refine auth_one_op_frag_dealloc <| fun n bf Hrel j => ?_
  match He : Std.PartialMap.get? bf j with
  | none =>
    intro _ HK
    simp at HK
  | some v =>
    by_cases h : k = j
    · specialize Hrel k
      simp only [ORA.op, Heap.op, get?_merge, Option.merge, h, get?_singleton_eq rfl, He,
                 Option.some.injEq, forall_eq'] at Hrel
      obtain ⟨_, _, _, Hqv, c, Hinc⟩ := Hrel
      have Hval' : ✓{n} (some ((DFrac.own one, v1) • v) • c) := validN_of_ordN Hinc Hqv
      have Hval'' : ✓{n} (some ((DFrac.own one, v1) • v)) := validN_op_left Hval'
      have Hval : ✓{n} ((DFrac.own one, v1) • v) := Hval''
      -- `own 1` is exclusive, so it cannot validly compose with the frame's fraction
      exact (own_whole_exclusive.exclusive0_l _ (valid0_of_validN Hval.1)).elim
    · specialize Hrel j
      simp only [ORA.op, Heap.op, get?_merge, exists_and_left, Prod.forall, get?_singleton_ne h,
        He] at Hrel
      rintro ⟨a, b⟩ ⟨rfl⟩
      obtain ⟨v, H, q, H'⟩ := Hrel a b rfl
      exact ⟨v, q, H.symm ▸ get?_delete_ne h, H'⟩

theorem update_auth_op_frag_frame
    (Hup : ∀ (n : SI) (dq₁ : DFrac) (mv : V) (f : Option ((DFrac) × V)),
      Std.PartialMap.get? m1 k = some mv → ✓{n} (dq₁, mv) →
      some ((dq, v) •? f) ≼ₒ{n} some (dq₁, mv) →
      ∃ (dq₂ : DFrac) (g : Option (DFrac × V)), ✓{n} (dq₂, mv') ∧
        some ((dq', v') •? f) • g ≼ₒ{n} some (dq₂, mv')) :
    Auth (SI := SI) (.own one) m1 • Frag k dq v ~~>[SI]
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq' v' := by
  have e (x : DFrac × V) (o c : Option (DFrac × V)) : some (x •? o) • c = some (x •? (o • c)) := by
    rw [Option.some_op_opM, Option.opM_opM_assoc]
  refine auth_one_op_frag_update fun n bf Hrel j ⟨df, va⟩ Hj => ?_
  rw [get?_op] at Hj
  by_cases h : k = j
  · subst h
    rw [get?_singleton_eq rfl] at Hj
    rw [get?_insert_eq rfl]
    have Hk : get? (PartialMap.singleton k (dq, v) • bf) k = some ((dq, v) •? get? bf k) := by
      rw [get?_op, get?_singleton_eq rfl, Option.some_op_opM]
    obtain ⟨mv0, mdf, Hlookup, Hval, c, Hincl⟩ := Hrel k _ Hk
    rw [e] at Hincl
    obtain ⟨dq₂, g, Hval₂, Hincl₂⟩ := Hup n mdf mv0 _ Hlookup Hval Hincl
    refine ⟨mv', dq₂, rfl, Hval₂, c • g, ?_⟩
    rw [← Hj, Option.some_op_opM (a := (dq', v')), assoc', e]
    exact Hincl₂
  · rw [get?_singleton_ne h] at Hj
    rw [get?_insert_ne h]
    refine Hrel j (df, va) ?_
    rw [get?_op, get?_singleton_ne h]
    exact Hj

theorem update_auth_op_frag_ord
    (Hup : ∀ (n : SI) (dq₁ : DFrac) (mv : V) (f : Option ((DFrac) × V)),
      Std.PartialMap.get? m1 k = some mv → ✓{n} (dq₁, mv) →
      some ((dq, v) •? f) ≼ₒ{n} some (dq₁, mv) →
      ∃ dq₂, ✓{n} (dq₂, mv') ∧ some ((dq', v') •? f) ≼ₒ{n} some (dq₂, mv')) :
    Auth (SI := SI) (.own one) m1 • Frag k dq v ~~>[SI]
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq' v' :=
  update_auth_op_frag_frame fun n dq₁ mv f Hl Hv Hi =>
    let ⟨dq₂, Hv₂, Hi₂⟩ := Hup n dq₁ mv f Hl Hv Hi
    ⟨dq₂, none, Hv₂, Hi₂⟩

@[rocq_alias gmap_view_update]
theorem update_auth_op_frag [OrdInc SI V]
    (Hup :
      ∀ (n : SI) (mv : V) (f : Option (DFrac × V)), (Std.PartialMap.get? m1 k = some mv) →
      ✓{n} ((dq, v) •? f) → (mv ≡{n}≡ ((v : V) •? (Prod.snd <$> f))) →
      ✓{n} ((dq', v') •? f) ∧ (mv' ≡{n}≡ v' •? (Prod.snd <$> f))) :
    Auth (SI := SI) (.own one) m1 • Frag k dq v ~~>[SI]
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq' v' := by
  have key : ∀ (x : DFrac × V) (F : Option (DFrac × V)),
      (x •? F).1 = x.1 •? (Option.map Prod.fst F) ∧ (x •? F).2 = x.2 •? (Prod.snd <$> F) := by
    intro x F; cases F <;> exact ⟨rfl, rfl⟩
  refine update_auth_op_frag_frame fun n dq₁ mv f Hl Hval Hincl => ?_
  obtain ⟨g, hg⟩ := Option.some_incN_some_iff_opM.mp (ordN_incN Hincl)
  have hF : (dq₁, mv) ≡{n}≡ (dq, v) •? (f • g) := hg.trans (Option.opM_opM_assoc).dist
  obtain ⟨Hv', He'⟩ := Hup n mv (f • g) Hl (hF.validN.mp Hval)
    (hF.2.trans (Dist.of_eq (key (dq, v) (f • g)).2))
  have hE : (dq' •? (Option.map Prod.fst (f • g)), mv') ≡{n}≡ (dq', v') •? (f • g) :=
    ⟨Dist.of_eq (key (dq', v') (f • g)).1.symm,
      He'.trans (Dist.of_eq (key (dq', v') (f • g)).2.symm)⟩
  refine ⟨dq' •? (Option.map Prod.fst (f • g)), g, validN_ne hE.symm Hv', ordN_of_dist ?_⟩
  rw [Option.some_op_opM, Option.opM_opM_assoc]
  exact OFE.some_dist_some.mpr hE.symm

@[rocq_alias gmap_view_update_local]
theorem update_of_local_update [OrdInc SI V]
    (Hl : Std.PartialMap.get? m1 k = some mv) (Hup : (mv, v) ~l~>[SI] (mv', v')) :
    Auth (SI := SI) (.own one) m1 • Frag k dq v ~~>[SI]
    Auth (.own one) (Std.PartialMap.insert m1 k mv') • Frag k dq v' := by
  refine update_auth_op_frag fun n mv0 f Hmv0 Hval He => ?_
  obtain rfl : mv0 = mv := Option.some_inj.mp (Hmv0.symm.trans Hl)
  cases f <;>
    exact let ⟨Hv', He'⟩ := Hup n _ (validN_ne He.symm Hval.2) He
      ⟨⟨Hval.1, validN_ne He' Hv'⟩, He'⟩

@[rocq_alias gmap_view_replace]
theorem update_replace (Hval' : ✓[SI] v2) :
    Auth (SI := SI) (.own one) m1 • Frag k (.own one) v1 ~~>[SI]
    Auth (.own one) (Std.PartialMap.insert m1 k v2) • Frag k (.own one) v2 := by
  refine update_auth_op_frag_ord fun n dq₁ mv f Hlookup Hval Hincl => ?_
  match f with
  | none => exact ⟨.own one, ⟨valid_own_one (SI := SI), Hval'.validN⟩, ordN_refl _⟩
  | some p =>
    have := Option.validN_of_ordN_validN (Hv := Hval) (Hinc := Hincl)
    exact (own_whole_exclusive.exclusive0_l _ (valid0_of_validN this.1)).elim

@[rocq_alias gmap_view_auth_persist]
theorem auth_dfrac_discard : Auth (SI := SI) dq m1 ~~>[SI] Auth .discard m1 := auth_discard

@[rocq_alias gmap_view_auth_unpersist]
theorem auth_dfrac_acquire :
    Auth (SI := SI) .discard m1 ~~>:[SI] fun a => ∃ q, a = Auth (.own q) m1 :=
  auth_acquire

@[rocq_alias gmap_view_frag_dfrac]
theorem update_of_dfrac_update P (Hdq : dq ~~>:[SI] P) :
    Frag (H := H) k dq v1 ~~>:[SI] fun a => ∃ dq', a = Frag (SI := SI) k dq' v1 ∧ P dq' := by
  apply UpdateP.weaken
  · apply frag_updateP (P := fun b' => ∃ dq', (◯V b') = Frag (SI := SI) k dq' v1 ∧ P dq')
    intro m n bf Hrel
    have Hrel' := Hrel k ((dq, v1) •? Std.PartialMap.get? bf k) ?G
    case G =>
      simp only [ORA.op, Heap.op, get?_merge, get?_singleton_eq rfl, op?]
      cases _ : Std.PartialMap.get? bf k <;> simp
    obtain ⟨v', dq', Hlookup, Hval, c, Hincl⟩ := Hrel'
    rw [Option.some_op_opM, Option.opM_opM_assoc] at Hincl
    -- Extract a fraction frame `w`, the updated fraction `dq''`, and the new authoritative
    -- pair — in each of the four frame/order cases (`bf k` absent or present × dist or
    -- order-inclusion).
    obtain ⟨dq'', HPdq'', dq₀, Hv₀, Hi₀⟩ :
        ∃ dq'', P dq'' ∧ ∃ dq₀, ✓{n} (dq₀, v') ∧
          some ((dq'', v1) •? (Std.PartialMap.get? bf k • c)) ≼ₒ{n} some (dq₀, v') := by
      rcases hbf : Std.PartialMap.get? bf k • c with _ | p <;> rw [hbf] at Hincl
      · rcases Hincl with e | i
        · obtain ⟨dq'', HP, Hv''⟩ := Hdq n none (validN_ne e.1.symm Hval.1)
          exact ⟨dq'', HP, dq'', ⟨Hv'', Hval.2⟩, Option.some_ordN_some_iff.mpr (.inl ⟨.rfl, e.2⟩)⟩
        · obtain ⟨w, hw⟩ := i.1
          obtain ⟨dq'', HP, Hv''⟩ := Hdq n (some w) (validN_ne hw Hval.1)
          exact ⟨dq'', HP, dq'' • w, ⟨Hv'', Hval.2⟩,
            Option.some_ordN_some_iff.mpr (.inr ⟨⟨w, .rfl⟩, i.2⟩)⟩
      · rcases Hincl with e | i
        · obtain ⟨dq'', HP, Hv''⟩ := Hdq n (some p.1) (validN_ne e.1.symm Hval.1)
          exact ⟨dq'', HP, dq'' • p.1, ⟨Hv'', Hval.2⟩,
            Option.some_ordN_some_iff.mpr (.inl ⟨.rfl, e.2⟩)⟩
        · obtain ⟨w, hw⟩ := i.1
          obtain ⟨dq'', HP, Hv''⟩ := Hdq n (some (p.1 • w))
            (validN_ne (hw.trans assoc.symm.dist) Hval.1)
          refine ⟨dq'', HP, (dq'' • p.1) • w, ⟨validN_ne assoc.dist Hv'', Hval.2⟩,
            Option.some_ordN_some_iff.mpr (.inr ⟨⟨w, .rfl⟩, i.2⟩)⟩
    exists Std.PartialMap.singleton k (dq'', v1)
    refine ⟨⟨dq'', rfl, HPdq''⟩, fun j ⟨df, va⟩ Heq => ?_⟩
    by_cases h : k = j
    · subst h
      simp only [ORA.op, Heap.op, get?_merge, get?_singleton_eq rfl] at Heq
      refine ⟨v', dq₀, Hlookup, Hv₀, c, ordN_of_dist_of_ordN (Dist.of_eq ?_) Hi₀⟩
      rw [← Option.opM_opM_assoc, ← Option.some_op_opM, ← Heq]
      cases Std.PartialMap.get? bf k <;> rfl
    · apply Hrel
      simp [ORA.op, get?_merge, get?_singleton_ne h] at Heq ⊢
      exact Heq
  · rintro y ⟨b, rfl, q, _, _⟩
    exists q

@[rocq_alias gmap_view_frag_persist]
theorem update_frag_discard : Frag (H := H) k dq v1 ~~>[SI] Frag (SI := SI) k .discard v1 :=
  .lift_updateP (Frag k · v1) _ _ update_of_dfrac_update DFrac.update_discard

@[rocq_alias gmap_view_frag_unpersist]
theorem update_frag_acquire :
    (Frag k .discard v1 : HeapView (SI := SI) K V H) ~~>:[SI] fun a => ∃ q, a = Frag k (.own q) v1 := by
  apply UpdateP.weaken (update_of_dfrac_update _ DFrac.update_acquire)
  rintro y ⟨q, rfl, ⟨q1, rfl⟩⟩
  exists q1

end heapUpdates

section heapViewFunctor

open Iris.Std PartialMap

theorem heapR_map_eq [COFE SI A] [COFE SI B] [COFE SI A'] [COFE SI B'] [RFunctor SI T] (f : A' -n>[SI] A) (g : B -n>[SI] B')
    (n : SI) (m : H (T A B)) (mv : H (DFrac × T A B)) :
    HeapR K (T A B) H n m mv →
    HeapR K (T A' B') H n
      ((mapO H (RFunctor.map f g).toHom).f m)
      ((mapC H (Prod.mapC (ORA.Hom.id (α := DFrac))
      (RFunctor.map (F:=T) f g))).f mv) := by
  simp [HeapR, PartialMap.mapC, PartialMap.mapO, PartialMap.map, ORA.Hom.id, OFE.Hom.id, Prod.mapC, get?_bindAlter]
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
    exact (CMRA.Hom.validN _ hv2)
  · obtain ⟨c, hc⟩ := ho
    let G := Option.mapC (Prod.mapC (ORA.Hom.id (α := DFrac)) (RFunctor.map (F := T) f g))
    exact ⟨_, G.op _ c ▸ G.monoN_ord hc⟩

@[rocq_alias gmap_viewURF]
abbrev HeapViewURF T [RFunctor SI T] : COFE.OFunctorPre SI :=
  fun A B _ _ => HeapView (SI := SI) K (T A B) H

instance {T} [RFunctor SI T] :
    URFunctor SI (HeapViewURF (H := H) T) where
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
      exact fun _ => Prod.map_ne .refl (RFunctor.map_ne.ne Hx Hy)
  map_id x := by
    rw (config := { occs := .pos [2] }) [<- (View.map_id x)]
    refine OFE.eq_dist_2 (fun n => View.map_ne x (fun a => ?_) (fun b => ?_))
    · exact (COFE.OFunctor.map_id (F := PartialMapOF H T) a).dist
    · refine OFE.Dist.trans ?_ (map_id (SI := SI) _ b).dist
      apply PartialMap.map_ne
      exact fun _ => ⟨rfl, (RFunctor.map_id _).dist⟩
  map_comp f g f' g' x := by
    simp [View.mapC]
    rw [<- View.map_compose']
    refine OFE.eq_dist_2 (fun n => View.map_ne x (fun a => (?_ : _ = _).dist) (fun b => (?_ : _ = _).dist))
    · exact (inferInstance : URFunctor SI (PartialMapOF H T)).map_comp _ _ _ _ a
    · simp only [Prod.mapC, ORA.Hom.id, PartialMap.mapC]
      refine .trans ?_ (PartialMap.map_compose (SI := SI) _ _ _ _)
      refine congrArg (PartialMap.map _ · _) ?_
      rw [Prod.map_comp_map]
      refine funext fun p => ?_
      exact Prod.ext rfl (RFunctor.map_comp _ _ _ _ p.2)

instance instRFunctorAffine {T} [RFunctor SI T] [RFunctorAffine SI T] :
    RFunctorAffine SI (HeapViewURF (H := H) T) where
  affine := inferInstance

@[rocq_alias gmap_viewURF_contractive]
instance {T} [RFunctorContractive SI T] :
    URFunctorContractive SI (HeapViewURF (H := H) T) where
  map_contractive.1 H _ := by
    apply View.map_ne <;> intros <;> apply PartialMap.map_ne
    · exact (RFunctorContractive.map_contractive.1 H)
    · exact (fun _ => Prod.map_ne .refl (RFunctorContractive.map_contractive.1 H))

#rocq_ignore gmap_viewRF "Use `HeapViewURF`; `RFunctor` comes from `URFunctor.toRFunctor`"
#rocq_ignore gmap_viewRF_contractive "Use `HeapViewURF`; `RFunctorContractive` comes from `URFunctorContractive.toRFunctorContractive`"

end heapViewFunctor

end HeapView

section FiniteHeapView
open Std PartialMap Heap OFE ORA HeapView
open One DFrac LawfulPartialMap Algebra

variable {K V : Type _} {H : Type _ → Type _} [DecidableEq K] [LawfulFiniteMap H K] [RA V] [ORA SI V]

omit [DecidableEq K] in
private theorem bigOpM_frag_empty (dq : DFrac) :
    bigOpM (M := HeapView (SI := SI) K V H) op (fun k x => Frag k dq x) (∅ : H V) = UnitOp.unit :=
  BigOpM.bigOpM_empty (M := HeapView (SI := SI) K V H) (M' := H) (K := K) (op := op) (V := V) _

@[rocq_alias gmap_view_delete_big]
theorem update_big_delete (m m' : H V) :
  Auth (.own one) m • (bigOpM (M := HeapView (SI := SI) K V H) op (fun k v => Frag k (.own one) v) m') ~~>[SI]
  Auth (.own one) (m \ m') := by
  induction m' using LawfulFiniteMap.induction_on with
  | hemp =>
    suffices h : (m \ ∅ : H V) = m by
      rw [bigOpM_frag_empty, unit_right_id, h]
    exact eqv_of_Equiv (SI := SI) fun j => by simp [get?_difference, get?_empty]
  | hins k v m2 Hm2 IH =>
    suffices h : (m \ Std.insert m2 k v) = delete (m \ m2) k by
      rw [BigOpM.bigOpM_insert_eq _ _ Hm2, comm' (x := Frag k (.own one) v), assoc', h]
      exact (Update.op IH .id).trans update_one_delete
    exact eqv_of_Equiv (SI := SI) fun j => by
      by_cases hjk : k = j
        <;> simp [get?_difference, get?_delete_eq, get?_delete_ne, get?_insert_eq,
              get?_insert_ne, hjk]

@[rocq_alias gmap_view_replace_big]
theorem update_big_replace (m m0 m1 : H V)
  (Hdom : dom m0 = dom m1)
  (Hall : all (fun _ v => ✓[SI] v) m1) :
  Auth (.own one) m • (bigOpM (M := HeapView (SI := SI) K V H) op (fun k v => Frag k (.own one) v) m0) ~~>[SI]
  Auth (.own one) (m1 ∪ m) • (bigOpM (M := HeapView (SI := SI) K V H) op (fun k v => Frag k (.own one) v) m1) := by
  revert m1 Hdom
  induction m0 using LawfulFiniteMap.induction_on with
  | hemp =>
    intro m1 Hdom Hall
    suffices h : m1 = ∅ by
      simp only [h, bigOpM_frag_empty, unit_right_id, union_empty_left]
      exact Update.id
    refine Std.LawfulPartialMap.equiv_iff_eq.mp fun j => ?_
    cases hj : get? m1 j with
    | none => exact (get?_empty j).symm
    | some w => simpa [dom, get?_empty, hj] using congrFun Hdom j
  | hins k v m2 Hm2 IH =>
    intro m1 Hdom Hall
    obtain ⟨v', Hin⟩ : ∃ v', get? m1 k = some v' :=
      Option.isSome_iff_exists.mp (by simpa [dom, get?_insert_eq rfl] using congrFun Hdom k)
    have hdom : dom m2 = dom (delete m1 k) := funext fun j => by
      by_cases hjk : k = j
      · simp [dom, ← hjk, Hm2, get?_delete_eq rfl]
      · simpa [dom, get?_delete_ne hjk, get?_insert_ne hjk] using congrFun Hdom j
    have hunion : (m1 ∪ m) = Std.insert (delete m1 k ∪ m) k v' :=
      eqv_of_Equiv (SI := SI) fun j => by
        change get? (PartialMap.union m1 m) j
          = get? (Std.insert (PartialMap.union (delete m1 k) m) k v') j
        by_cases hjk : k = j
        · rw [← hjk, get?_insert_eq rfl]
          simp only [PartialMap.union, get?_merge, Hin]
          cases get? m k <;> rfl
        · rw [get?_insert_ne hjk]
          simp [PartialMap.union, get?_merge, get?_delete_ne hjk]
    rw [BigOpM.bigOpM_insert_eq _ _ Hm2, comm' (x := Frag k (.own one) v), assoc',
      hunion, BigOpM.bigOpM_delete_eq _ Hin, assoc']
    refine (Update.op (IH _ hdom (all_delete _ Hall)) .id).trans ?_
    rw [← assoc', comm' (y := Frag k (.own one) v), assoc']
    exact Update.op (update_replace (Hall k v' Hin)) .id

-- TODO: golf
@[rocq_alias gmap_view_alloc_big]
theorem update_big_alloc (m1 m2 : H V) dq
  (Hdisj : m2 ##ₘ m1) (Hdq : ✓[SI] dq)
  (Hall : all (fun _ v => ✓[SI] v) m2) :
  Auth (.own one) m1 ~~>[SI]
    Auth (.own one) (m2 ∪ m1)
    • bigOpM (M := HeapView (SI := SI) K V H) op (fun k v => Frag k dq v) m2 := by
    induction m2 using LawfulFiniteMap.induction_on generalizing m1 with
    | hemp =>
      rw [bigOpM_frag_empty]
      refine Update.ord ?_
      rw [union_empty_left, unit_right_id]
      try exact ord_refl _
    | hins k v m2 Hm2 IH =>
      have Hall' : all (fun k v => ✓[SI] v) m2 := by exact all_of_all_insert _ Hm2 Hall
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
      rw [← assoc]
      refine Update.op ?_ ?_
      · rw [← union_insert_left]
      · rw [BigOpM.bigOpM_insert_eq _ _ Hm2]

end FiniteHeapView
