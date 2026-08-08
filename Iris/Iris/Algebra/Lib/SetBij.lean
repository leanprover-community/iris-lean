/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.LeibnizSet
public import Iris.Algebra.View
public import Iris.Algebra.Updates
meta import Iris.Std.RocqPorting

@[expose] public section

/-!
# RA for monotone partial bijections

This RA is a view where the authoritative element is a partial bijection between types `A` and `B`
and the fragments are subrelations of the bijection. The data for the bijection is represented as a
set of pairs `A × B`, and the view relation enforces that when an authoritative element is valid it
is a bijection (that is, it is deterministic as a function from `A → Option B` and `B → Option A`).

The fragments compose by set union, which means that fragments are their own core, ownership of a
fragment is persistent, and the authoritative element can only grow (in that it can only map more
pairs `(a, b)`).

As with `LeibnizSet`, the set of pairs is not fixed to a concrete representation: the construction
is generic in any `LawfulSet S (A × B)`.
-/

namespace Iris

open Std CMRA OFE LawfulSet LeibnizSet View

variable {S A B : Type _} [LawfulSet S (A × B)]
variable {a a₁ a₂ : A} {b b₁ b₂ : B} {L L' L₁ L₂ : S} {dq dq₁ dq₂ : DFrac}

/-- `SetBijective L` states that for a graph `L` of `(a, b)` pairs, `L` maps from `A` to `B` and
back deterministically. The key property characterizing `SetBijective` is `SetBijective.eq_iff`. -/
@[rocq_alias gset_bijective]
def SetBijective (L : S) : Prop :=
  ∀ a b, (a, b) ∈ L → (∀ b', (a, b') ∈ L → b' = b) ∧ (∀ a', (a', b) ∈ L → a' = a)

namespace SetBijective

@[rocq_alias gset_bijective_empty]
theorem empty : SetBijective (∅ : S) := fun _ _ h => absurd h mem_empty

/-- A bijective graph `L` can be extended with a new mapping `(a, b)` as long as neither `a` nor
`b` is currently mapped to anything. -/
@[rocq_alias gset_bijective_extend]
theorem extend (hL : SetBijective L) (ha : ∀ b', (a, b') ∉ L) (hb : ∀ a', (a', b) ∉ L) :
    SetBijective ({(a, b)} ∪ L) := by
  rw [← insert_union]
  intro a₁ b₁ h₁
  rw [mem_insert, Prod.mk.injEq] at h₁
  refine ⟨fun b₂ h₂ => ?_, fun a₂ h₂ => ?_⟩ <;>
    rw [mem_insert, Prod.mk.injEq] at h₂ <;> obtain ⟨rfl, rfl⟩ | h₁ := h₁
  · exact h₂.elim (·.2) (absurd · (ha b₂))
  · exact h₂.elim (fun h => absurd (h.1 ▸ h₁) (ha b₁)) fun h₂ => (hL _ _ h₁).1 b₂ h₂
  · exact h₂.elim (·.1) (absurd · (hb a₂))
  · exact h₂.elim (fun h => absurd (h.2 ▸ h₁) (hb a₁)) fun h₂ => (hL _ _ h₁).2 a₂ h₂

@[rocq_alias gset_bijective_eq_iff]
theorem eq_iff (hL : SetBijective L) (h₁ : (a₁, b₁) ∈ L) (h₂ : (a₂, b₂) ∈ L) :
    a₁ = a₂ ↔ b₁ = b₂ := by
  refine ⟨?_, ?_⟩ <;> rintro rfl
  · exact ((hL _ _ h₁).1 _ h₂).symm
  · exact ((hL _ _ h₁).2 _ h₂).symm

@[rocq_alias gset_bijective_pair]
theorem pair (h : SetBijective ({(a₁, b₁), (a₂, b₂)} : S)) : a₁ = a₂ ↔ b₁ = b₂ :=
  h.eq_iff (mem_insert.mpr (.inl rfl)) (mem_insert.mpr (.inr (mem_singleton.mpr rfl)))

@[rocq_alias subseteq_gset_bijective]
theorem mono (hL : SetBijective L) (h : L' ⊆ L) : SetBijective L' := fun a b hab =>
  ⟨fun b' h' => (hL a b (mem_of_subset h hab)).1 b' (mem_of_subset h h'),
   fun a' h' => (hL a b (mem_of_subset h hab)).2 a' (mem_of_subset h h')⟩

end SetBijective

namespace SetBij

/-- The view relation: a fragment is a subrelation of the authoritative bijection. -/
@[rocq_alias gset_bij_view_rel, rocq_alias gset_bij_view_rel_raw]
def viewRel : ViewRel (LeibnizSet S) (LeibnizSet S)
  | _, valid bijL, valid L => L ⊆ bijL ∧ SetBijective bijL

@[rocq_alias gset_bij_view_rel_iff]
theorem viewRel_iff {n} : viewRel n (valid L') (valid L) ↔ L ⊆ L' ∧ SetBijective L' := .rfl

@[rocq_alias gset_bij_view_rel_raw_mono, rocq_alias gset_bij_view_rel_raw_valid,
  rocq_alias gset_bij_view_rel_raw_unit]
instance : IsViewRel (viewRel (S := S)) where
  mono {_ x₁ y₁ n₂ x₂ y₂} h hx hy _ := by
    obtain ⟨_⟩ := x₁
    obtain ⟨_⟩ := x₂
    obtain ⟨_⟩ := y₁
    obtain ⟨_⟩ := y₂
    injection (hx : _ = _) with hx
    subst hx
    exact ⟨subset_trans ((included_iff_subset ..).mp ((inc_iff_incN n₂).mpr hy)) h.1, h.2⟩
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨valid ∅, subset_refl, .empty⟩

@[rocq_alias gset_bij_view_rel_discrete]
instance : IsViewRelDiscrete (viewRel (S := S)) where
  discrete _ _ _ h := h

end SetBij

/-- The RA of monotone partial bijections over a set `S` of pairs. -/
@[rocq_alias gset_bij, rocq_alias gset_bijO, rocq_alias gset_bijR, rocq_alias gset_bijUR]
abbrev SetBij (S : Type _) [LawfulSet S (A × B)] := View (SetBij.viewRel (S := S))

namespace SetBij

@[rocq_alias gset_bij_auth]
def auth (dq : DFrac) (L : S) : SetBij S := (●V{dq} valid L) • ◯V valid L

@[rocq_alias gset_bij_elem]
def elem (a : A) (b : B) : SetBij S := ◯V valid {(a, b)}

@[rocq_alias gset_bij_elem_core_id]
instance : CoreId (elem a b : SetBij S) := inferInstanceAs (CoreId (◯V _))

theorem frag_op_union : ((◯V valid L₁ : SetBij S) • ◯V valid L₂) = ◯V valid (L₁ ∪ L₂) := by
  rw [← frag_op_eq, op_union]

/-- The authoritative and fragment parts of two `auth`s, regrouped. -/
theorem auth_op_auth_eq : ((auth dq₁ L₁ : SetBij S) • auth dq₂ L₂)
    = ((●V{dq₁} valid L₁ : SetBij S) • ●V{dq₂} valid L₂) • ◯V valid (L₁ ∪ L₂) := by
  rw [auth, auth, ← frag_op_union, ← assoc_L, assoc_L (x := (◯V valid L₁ : SetBij S)),
    comm_L (x := (◯V valid L₁ : SetBij S)), ← assoc_L, assoc_L]

@[rocq_alias gset_bij_auth_dfrac_op]
theorem auth_op_auth : ((auth dq₁ L : SetBij S) • auth dq₂ L) = auth (dq₁ • dq₂) L := by
  rw [auth_op_auth_eq, union_idem, ← auth_op_auth_eqv, auth]

@[rocq_alias gset_bij_auth_dfrac_valid]
theorem auth_valid_iff : ✓ (auth dq L : SetBij S) ↔ ✓ dq ∧ SetBijective L := by
  rw [auth, auth_op_frag_valid_iff]
  exact and_congr_right fun _ => ⟨fun h => (h 0).2, fun h _ => ⟨subset_refl, h⟩⟩

@[rocq_alias gset_bij_auth_valid]
theorem auth_one_valid_iff : ✓ (auth (.own 1) L : SetBij S) ↔ SetBijective L :=
  auth_valid_iff.trans <| and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias gset_bij_auth_empty_dfrac_valid]
theorem auth_empty_valid_iff : ✓ (auth dq (∅ : S) : SetBij S) ↔ ✓ dq :=
  auth_valid_iff.trans <| and_iff_left_iff_imp.mpr fun _ => .empty

@[rocq_alias gset_bij_auth_empty_valid]
theorem auth_one_empty_valid : ✓ (auth (.own 1) (∅ : S) : SetBij S) :=
  auth_empty_valid_iff.mpr DFrac.valid_own_one

@[rocq_alias gset_bij_auth_dfrac_op_valid]
theorem auth_op_auth_valid_iff : ✓ ((auth dq₁ L₁ : SetBij S) • auth dq₂ L₂)
    ↔ ✓ (dq₁ • dq₂) ∧ L₁ = L₂ ∧ SetBijective L₁ := by
  rw [auth_op_auth_eq]
  refine ⟨fun h => ?_, fun ⟨hdq, rfl, hbij⟩ => ?_⟩
  · obtain ⟨hdq, hL, hrel⟩ := View.auth_op_auth_valid_iff.mp (valid_op_left h)
    injection hL with hL
    exact ⟨hdq, hL, (hrel 0).2⟩
  · rw [union_idem, ← auth_op_auth_eqv]
    exact auth_op_frag_valid_iff.mpr ⟨hdq, fun _ => ⟨subset_refl, hbij⟩⟩

@[rocq_alias gset_bij_auth_op_valid]
theorem auth_one_op_auth_one_valid_iff :
    ✓ ((auth (.own 1) L₁ : SetBij S) • auth (.own 1) L₂) ↔ False := by
  rw [auth_op_auth_eq]
  exact ⟨fun h => View.auth_one_op_auth_one_valid_iff.mp (valid_op_left h), False.elim⟩

@[rocq_alias bij_both_dfrac_valid]
theorem auth_op_elem_valid_iff : ✓ ((auth dq L : SetBij S) • elem a b)
    ↔ ✓ dq ∧ SetBijective L ∧ (a, b) ∈ L := by
  rw [auth, elem, ← assoc_L, frag_op_union, auth_op_frag_valid_iff]
  refine and_congr_right fun _ => ⟨fun h => ⟨(h 0).2, ?_⟩, fun ⟨hbij, hmem⟩ _ => ⟨?_, hbij⟩⟩
  · exact mem_of_subset (h 0).1 (mem_union.mpr (.inr (mem_singleton.mpr rfl)))
  · intro x hx
    obtain hx | hx := mem_union.mp hx
    · exact hx
    · rw [mem_singleton.mp hx]
      exact hmem

@[rocq_alias bij_both_valid]
theorem auth_one_op_elem_valid_iff : ✓ ((auth (.own 1) L : SetBij S) • elem a b)
    ↔ SetBijective L ∧ (a, b) ∈ L :=
  auth_op_elem_valid_iff.trans <| and_iff_right_iff_imp.mpr fun _ => DFrac.valid_own_one

@[rocq_alias gset_bij_elem_agree]
theorem elem_agree (h : ✓ ((elem a₁ b₁ : SetBij S) • elem a₂ b₂)) : a₁ = a₂ ↔ b₁ = b₂ := by
  rw [elem, elem, frag_op_union, frag_valid_iff] at h
  obtain ⟨⟨bijL⟩, hsub, hbij⟩ := h 0
  refine SetBijective.pair (S := S) ?_
  rw [insert_union]
  exact hbij.mono hsub

@[rocq_alias bij_view_included]
theorem elem_inc_auth (h : (a, b) ∈ L) : (elem a b : SetBij S) ≼ auth dq L :=
  inc_trans (frag_inc_of_inc <| (included_iff_subset ..).mpr fun _ hx => mem_singleton.mp hx ▸ h)
    (inc_op_right ..)

@[rocq_alias gset_bij_auth_extend]
theorem auth_extend (ha : ∀ b', (a, b') ∉ L) (hb : ∀ a', (a', b) ∉ L) :
    (auth (.own 1) L : SetBij S) ~~> auth (.own 1) ({(a, b)} ∪ L) := by
  refine auth_one_op_frag_update fun _ bf h => ?_
  obtain ⟨_⟩ := bf
  rw [op_union] at h ⊢
  refine ⟨fun x hx => ?_, h.2.extend ha hb⟩
  obtain hx | hx := mem_union.mp hx
  · exact hx
  · exact mem_union.mpr (.inr (mem_of_subset h.1 (mem_union.mpr (.inr hx))))

end SetBij

end Iris
