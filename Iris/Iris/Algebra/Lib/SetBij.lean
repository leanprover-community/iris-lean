/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.LeibnizSet
public import Iris.Algebra.View
public import Iris.Algebra.Updates
meta import Iris.Std.RocqPorting

@[expose] public section

/-! # RA for monotone partial bijections -/

namespace Iris

open _root_.Iris.Std CMRA OFE LawfulSet LeibnizSet View

variable {S A B : Type _} [LawfulSet S (A × B)]
variable {a a₁ a₂ : A} {b b₁ b₂ : B} {L L' L₁ L₂ : S} {dq dq₁ dq₂ : DFrac}

@[rocq_alias gset_bijective]
def SetBijective (L : S) : Prop :=
  ∀ {a b}, (a, b) ∈ L → (∀ b', (a, b') ∈ L → b' = b) ∧ (∀ a', (a', b) ∈ L → a' = a)

namespace SetBijective

@[rocq_alias gset_bijective_empty]
theorem empty : SetBijective (∅ : S) := (absurd · mem_empty)

@[rocq_alias gset_bijective_extend]
theorem extend (hL : SetBijective L) (ha : ∀ b', (a, b') ∉ L) (hb : ∀ a', (a', b) ∉ L) :
    SetBijective ({(a, b)} ∪ L) := by
  simp only [SetBijective, mem_union, mem_singleton, Prod.mk.injEq] at hL ⊢
  grind

@[rocq_alias gset_bijective_eq_iff]
theorem eq_iff (hL : SetBijective L) (h₁ : (a₁, b₁) ∈ L) (h₂ : (a₂, b₂) ∈ L) :
    a₁ = a₂ ↔ b₁ = b₂ :=
  ⟨fun h => ((hL h₁).1 b₂ (h ▸ h₂)).symm, fun h => ((hL h₁).2 a₂ (h ▸ h₂)).symm⟩

@[rocq_alias gset_bijective_pair]
theorem pair (h : SetBijective ({(a₁, b₁), (a₂, b₂)} : S)) : a₁ = a₂ ↔ b₁ = b₂ :=
  h.eq_iff (mem_insert.mpr (.inl rfl)) (mem_insert.mpr (.inr (mem_singleton.mpr rfl)))

@[rocq_alias subseteq_gset_bijective]
theorem mono (hL : SetBijective L) (hs : L' ⊆ L) : SetBijective L' := fun hab =>
  ⟨fun b' h => (hL (hs _ hab)).1 b' (hs _ h), fun a' h => (hL (hs _ hab)).2 a' (hs _ h)⟩

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
    obtain ⟨_⟩ := x₁; obtain ⟨_⟩ := y₁; obtain ⟨_⟩ := y₂; obtain rfl := (hx : _ = _)
    exact ⟨subset_trans ((included_iff_subset ..).mp ((inc_iff_incN n₂).mpr hy)) h.1, h.2⟩
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨valid ∅, subset_refl, SetBijective.empty⟩

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
  rw [auth, auth, ← frag_op_union]
  exact Algebra.MonoidOps.op_op_op_comm
attribute [local grind =] auth_op_auth_eq

@[rocq_alias gset_bij_auth_dfrac_op]
theorem auth_op_auth : ((auth dq₁ L : SetBij S) • auth dq₂ L) = auth (dq₁ • dq₂) L := by
  grind [union_idem, auth_op_auth_eqv, auth]
attribute [local grind =] auth_op_auth

@[rocq_alias gset_bij_auth_dfrac_valid]
theorem auth_valid_iff : ✓ (auth dq L : SetBij S) ↔ ✓ dq ∧ SetBijective L := by
  rw [auth, auth_op_frag_valid_iff]
  exact and_congr_right fun _ => ⟨fun h => (h 0).2, fun h _ => ⟨subset_refl, h⟩⟩
attribute [local grind =] auth_valid_iff

@[rocq_alias gset_bij_auth_valid]
theorem auth_one_valid_iff : ✓ (auth (.own 1) L : SetBij S) ↔ SetBijective L := by
  grind [DFrac.valid_own_one]

@[rocq_alias gset_bij_auth_empty_dfrac_valid]
theorem auth_empty_valid_iff : ✓ (auth dq (∅ : S) : SetBij S) ↔ ✓ dq := by
  grind [SetBijective.empty]

@[rocq_alias gset_bij_auth_empty_valid]
theorem auth_one_empty_valid : ✓ (auth (.own 1) (∅ : S) : SetBij S) := by
  grind [auth_empty_valid_iff, DFrac.valid_own_one]

@[rocq_alias gset_bij_auth_dfrac_op_valid]
theorem auth_op_auth_valid_iff : ✓ (auth dq₁ L₁ • auth dq₂ L₂)
    ↔ ✓ (dq₁ • dq₂) ∧ L₁ = L₂ ∧ SetBijective L₁ := by
  grind [View.auth_op_auth_valid_iff, valid_op_left]

@[rocq_alias gset_bij_auth_op_valid]
theorem auth_one_op_auth_one_valid_iff :
    ✓ ((auth (.own 1) L₁ : SetBij S) • auth (.own 1) L₂) ↔ False := by
  grind [View.auth_one_op_auth_one_valid_iff, valid_op_left]

@[rocq_alias bij_both_dfrac_valid]
theorem auth_op_elem_valid_iff : ✓ (auth dq L • elem a b) ↔ ✓ dq ∧ SetBijective L ∧ (a, b) ∈ L := by
  rw [auth, elem, ← assoc_L, frag_op_union, auth_op_frag_valid_iff]
  exact and_congr_right fun _ =>
    ⟨fun h => ⟨(h 0).2, (h 0).1 _ (mem_union.mpr (.inr (mem_singleton.mpr rfl)))⟩,
     fun ⟨hbij, hmem⟩ _ =>
       ⟨fun _ hx => (mem_union.mp hx).elim id (mem_singleton.mp · ▸ hmem), hbij⟩⟩

@[rocq_alias bij_both_valid]
theorem auth_one_op_elem_valid_iff : ✓ (auth (.own 1) L • elem a b) ↔ SetBijective L ∧ (a, b) ∈ L := by
  grind [auth_op_elem_valid_iff, DFrac.valid_own_one]

@[rocq_alias gset_bij_elem_agree]
theorem elem_agree (h : ✓ ((elem a₁ b₁ • elem a₂ b₂) : SetBij S)) : a₁ = a₂ ↔ b₁ = b₂ := by
  rw [elem, elem, frag_op_union, frag_valid_iff] at h
  obtain ⟨⟨_⟩, hsub, hbij⟩ := h 0
  exact SetBijective.eq_iff (hbij.mono hsub) (mem_union.mpr (.inl (mem_singleton.mpr rfl)))
    (mem_union.mpr (.inr (mem_singleton.mpr rfl)))

@[rocq_alias bij_view_included]
theorem elem_inc_auth (h : (a, b) ∈ L) : elem a b ≼ auth dq L :=
  inc_trans (frag_inc_of_inc <| (included_iff_subset ..).mpr fun _ hx => mem_singleton.mp hx ▸ h)
    (inc_op_right ..)

@[rocq_alias gset_bij_auth_extend]
theorem auth_extend (ha : ∀ b', (a, b') ∉ L) (hb : ∀ a', (a', b) ∉ L) :
    auth (.own 1) L ~~> auth (.own 1) ({(a, b)} ∪ L) := by
  refine auth_one_op_frag_update fun _ bf h => ?_
  obtain ⟨_⟩ := bf
  rw [op_union] at h ⊢
  exact ⟨fun _ hx => (mem_union.mp hx).elim id fun hx =>
    mem_union.mpr (.inr (h.1 _ (mem_union.mpr (.inr hx)))), SetBijective.extend h.2 ha hb⟩

end SetBij

end Iris
