/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.LeibnizSet
public import Iris.Algebra.View
meta import Iris.Std.RocqPorting

@[expose] public section

/-!
# Monotone Partial Bijections

This camera represents a partial bijection as a set of pairs. Its
authoritative element owns the whole graph, while persistent fragments own
subgraphs. The graph can grow by adding a pair whose domain and codomain
elements do not yet occur in the graph.
-/

namespace Iris

open OFE CMRA DFrac Std LawfulSet

namespace GSetBij

variable {S α β : Type _} [LawfulSet S (α × β)]

@[rocq_alias gset_bijective]
def Bijective (L : S) : Prop :=
  ∀ a b, (a, b) ∈ L →
    (∀ b', (a, b') ∈ L → b' = b) ∧ (∀ a', (a', b) ∈ L → a' = a)

@[rocq_alias gset_bijective_empty]
theorem bijective_empty : Bijective (∅ : S) :=
  fun _ _ hab => (mem_empty hab).elim

@[rocq_alias gset_bijective_extend]
theorem bijective_extend {L : S} {a : α} {b : β} (hbij : Bijective L)
    (ha : ∀ {b'}, (a, b') ∉ L) (hb : ∀ {a'}, (a', b) ∉ L) :
    Bijective ({(a, b)} ∪ L) :=
  by grind [Bijective, mem_union, mem_singleton]

@[rocq_alias gset_bijective_eq_iff]
theorem bijective_eq_iff {L : S} {a₁ a₂ : α} {b₁ b₂ : β}
    (hbij : Bijective L) (h₁ : (a₁, b₁) ∈ L)
    (h₂ : (a₂, b₂) ∈ L) :
    a₁ = a₂ ↔ b₁ = b₂ := by
  grind [hbij a₁ b₁ h₁]

@[rocq_alias gset_bijective_pair]
theorem bijective_pair {a₁ : α} {b₁ : β} {a₂ : α} {b₂ : β}
    (hbij : Bijective ({(a₁, b₁)} ∪ {(a₂, b₂)} : S)) :
    a₁ = a₂ ↔ b₁ = b₂ :=
  bijective_eq_iff hbij (mem_union.mpr <| .inl <| mem_singleton.mpr rfl)
    (mem_union.mpr <| .inr <| mem_singleton.mpr rfl)

@[rocq_alias subseteq_gset_bijective]
theorem bijective_of_subset {L L' : S} (hbij : Bijective L) (hsub : L' ⊆ L) :
    Bijective L' :=
  fun a b hab => (hbij a b <| hsub _ hab).imp
    (fun h _ hx => h _ <| hsub _ hx) (fun h _ hx => h _ <| hsub _ hx)

private theorem union_singleton_subset_iff {S' α : Type _} [LawfulSet S' α]
    {X : S'} {x : α} : X ∪ {x} ⊆ X ↔ x ∈ X := by
  constructor
  · intro h
    exact h x <| mem_union.mpr <| .inr <| mem_singleton.mpr rfl
  · intro hx y hy
    exact (mem_union.mp hy).elim id fun hy => mem_singleton.mp hy ▸ hx

@[rocq_alias gset_bij_view_rel_raw]
def rel (_ : Nat) (bijL : DiscreteO S) (L : LeibnizSet S) : Prop :=
  match L with
  | .valid L => L ⊆ bijL.car ∧ Bijective bijL.car

private theorem rel_mono_valid {n₁ n₂ : Nat}
    {bijL₁ bijL₂ : DiscreteO S} {L₁ L₂ : S}
    (hrel : rel n₁ bijL₁ (.valid L₁))
    (hbij : bijL₁ ≡{n₂}≡ bijL₂)
    (hL : LeibnizSet.valid L₂ ≼{n₂} LeibnizSet.valid L₁) :
    rel n₂ bijL₂ (.valid L₂) := by
  obtain rfl := (OFE.Discrete.discrete hbij).to_eq
  exact ⟨subset_trans ((LeibnizSet.included_iff_subset _ _).mp <|
    (CMRA.inc_iff_incN n₂).mpr hL) hrel.1, hrel.2⟩

@[rocq_alias gset_bij_view_rel_raw_mono]
theorem rel_mono {n₁ n₂ : Nat} {bijL₁ bijL₂ : DiscreteO S}
    {L₁ L₂ : LeibnizSet S} (hrel : rel n₁ bijL₁ L₁)
    (hbij : bijL₁ ≡{n₂}≡ bijL₂) (hL : L₂ ≼{n₂} L₁)
    (_hn : n₂ ≤ n₁) :
    rel n₂ bijL₂ L₂ :=
  match L₁, L₂ with
  | .valid _, .valid _ => rel_mono_valid hrel hbij hL

@[rocq_alias gset_bij_view_rel_raw_valid]
theorem rel_valid (n : Nat) (bijL : DiscreteO S) (L : LeibnizSet S)
    (_hrel : rel n bijL L) : ✓{n} L := trivial

@[rocq_alias gset_bij_view_rel_raw_unit]
theorem rel_unit (n : Nat) : ∃ bijL : DiscreteO S, rel n bijL UCMRA.unit :=
  ⟨DiscreteO.mk ∅, subset_refl, bijective_empty⟩

@[rocq_alias gset_bij_view_rel]
instance rel_isViewRel : IsViewRel (rel (S := S) (α := α) (β := β)) where
  mono := rel_mono
  rel_validN := rel_valid
  rel_unit := rel_unit

@[rocq_alias gset_bij_view_rel_discrete]
instance rel_isViewRelDiscrete :
    IsViewRelDiscrete (rel (S := S) (α := α) (β := β)) where
  discrete _ _ _ := id

@[rocq_alias gset_bij_view_rel_iff]
theorem rel_iff {n : Nat} {bijL : DiscreteO S} {L : S} :
    rel n bijL (LeibnizSet.valid L) ↔
      L ⊆ bijL.car ∧ Bijective bijL.car := .rfl

@[rocq_alias gset_bij, rocq_alias gset_bijO, rocq_alias gset_bijR,
  rocq_alias gset_bijUR]
abbrev GSetBij := View (rel (S := S) (α := α) (β := β))

@[rocq_alias gset_bij_auth]
def auth (dq : DFrac) (L : S) : GSetBij (S := S) (α := α) (β := β) :=
  (●V{dq} (DiscreteO.mk L)) • ◯V (LeibnizSet.valid L)

@[rocq_alias gset_bij_elem]
def elem (a : α) (b : β) : GSetBij (S := S) (α := α) (β := β) :=
  ◯V (LeibnizSet.valid ({(a, b)} : S))

private theorem op_op_op_comm {γ : Type _} [CMRA γ]
    {x₁ y₁ x₂ y₂ : γ} :
    (x₁ • y₁) • (x₂ • y₂) ≡
      (x₁ • x₂) • (y₁ • y₂) := by
  calc
    _ ≡ x₁ • (y₁ • (x₂ • y₂)) := CMRA.assoc.symm
    _ ≡ x₁ • ((y₁ • x₂) • y₂) := CMRA.assoc.op_r
    _ ≡ x₁ • ((x₂ • y₁) • y₂) := CMRA.comm.op_l.op_r
    _ ≡ x₁ • (x₂ • (y₁ • y₂)) := CMRA.assoc.symm.op_r
    _ ≡ _ := CMRA.assoc

@[rocq_alias gset_bij_elem_core_id]
instance elem_core_id {a : α} {b : β} :
    CMRA.CoreId (elem (S := S) a b) :=
  inferInstanceAs
    (CMRA.CoreId (◯V (LeibnizSet.valid ({(a, b)} : S))))

@[rocq_alias gset_bij_auth_dfrac_op]
theorem auth_dfrac_op {dq₁ dq₂ : DFrac} {L : S} :
    auth dq₁ L • auth dq₂ L ≡ auth (dq₁ • dq₂) L := by
  unfold auth
  calc
    _ ≡ _ := op_op_op_comm
    _ ≡ _ := View.auth_op_auth_eqv.symm.op (CMRA.op_self _)

@[rocq_alias gset_bij_auth_dfrac_valid]
theorem auth_dfrac_valid {dq : DFrac} {L : S} :
    ✓ auth dq L ↔ ✓ dq ∧ Bijective L := by
  unfold auth
  refine View.auth_op_frag_valid_iff.trans ?_
  simp only [rel, subset_refl, true_and, forall_const]

@[rocq_alias gset_bij_auth_valid]
theorem auth_valid {L : S} : ✓ auth (.own 1) L ↔ Bijective L :=
  auth_dfrac_valid.trans ⟨And.right, fun h => ⟨valid_own_one, h⟩⟩

@[rocq_alias gset_bij_auth_empty_dfrac_valid]
theorem auth_empty_dfrac_valid {dq : DFrac} :
    ✓ auth (S := S) (α := α) (β := β) dq ∅ ↔ ✓ dq :=
  auth_dfrac_valid.trans ⟨And.left, fun h => ⟨h, bijective_empty⟩⟩

@[rocq_alias gset_bij_auth_empty_valid]
theorem auth_empty_valid :
    ✓ auth (S := S) (α := α) (β := β) (.own 1) ∅ :=
  auth_empty_dfrac_valid.mpr valid_own_one

@[rocq_alias gset_bij_auth_dfrac_op_valid]
theorem auth_dfrac_op_valid {dq₁ dq₂ : DFrac} {L₁ L₂ : S} :
    ✓ (auth dq₁ L₁ • auth dq₂ L₂) ↔
      ✓ (dq₁ • dq₂) ∧ L₁ = L₂ ∧ Bijective L₁ := by
  constructor
  · intro hvalid
    have heq : L₁ = L₂ := congrArg DiscreteO.car <|
      View.eq_of_valid_auth <| CMRA.valid_op_left <|
        op_op_op_comm.valid.mp hvalid
    subst L₂
    simpa using auth_dfrac_valid.mp (auth_dfrac_op.valid.mp hvalid)
  · rintro ⟨hvalid, rfl, hbij⟩
    exact auth_dfrac_op.valid.mpr <| auth_dfrac_valid.mpr ⟨hvalid, hbij⟩

@[rocq_alias gset_bij_auth_op_valid]
theorem auth_op_valid {L₁ L₂ : S} :
    ✓ (auth (.own 1) L₁ • auth (.own 1) L₂) ↔ False :=
  by grind [auth_dfrac_op_valid, DFrac.valid_own_op]

@[rocq_alias bij_both_dfrac_valid]
theorem both_dfrac_valid {dq : DFrac} {L : S} {a : α} {b : β} :
    ✓ (auth dq L • elem a b) ↔
      ✓ dq ∧ Bijective L ∧ (a, b) ∈ L := by
  rw [auth, elem, ← CMRA.assoc_L, ← View.frag_op_eq,
    (LeibnizSet.op_union _ _).to_eq, View.auth_op_frag_valid_iff]
  simp only [rel, forall_const, union_singleton_subset_iff,
    and_comm, and_left_comm]

@[rocq_alias bij_both_valid]
theorem both_valid {L : S} {a : α} {b : β} :
    ✓ (auth (.own 1) L • elem a b) ↔ Bijective L ∧ (a, b) ∈ L :=
  both_dfrac_valid.trans ⟨And.right, fun h => ⟨valid_own_one, h⟩⟩

@[rocq_alias gset_bij_elem_agree]
theorem elem_agree {a₁ : α} {b₁ : β} {a₂ : α} {b₂ : β}
    (h : ✓ (elem (S := S) a₁ b₁ • elem a₂ b₂)) :
    a₁ = a₂ ↔ b₁ = b₂ := by
  unfold elem at h
  rw [← View.frag_op_eq, (LeibnizSet.op_union _ _).to_eq,
    View.frag_valid_iff] at h
  obtain ⟨bijL, hsub, hbij⟩ := h 0
  exact bijective_pair <| bijective_of_subset hbij hsub

@[rocq_alias bij_view_included]
theorem elem_included {dq : DFrac} {L : S} {a : α} {b : β}
    (h : (a, b) ∈ L) :
    elem a b ≼ auth dq L := by
  unfold elem auth
  refine CMRA.inc_trans (View.frag_inc_of_inc ?_) (CMRA.inc_op_right _ _)
  refine (LeibnizSet.included_iff_subset _ _).mpr fun x hx => ?_
  simpa [mem_singleton.mp hx] using h

@[rocq_alias gset_bij_auth_extend]
theorem auth_extend {L : S} {a : α} {b : β} (ha : ∀ {b'}, (a, b') ∉ L)
    (hb : ∀ {a'}, (a', b) ∉ L) :
    auth (.own 1) L ~~> auth (.own 1) ({(a, b)} ∪ L) := by
  unfold auth
  refine View.auth_one_op_frag_update fun _ bf hrel => ?_
  obtain ⟨Lf⟩ := bf
  exact ⟨fun x hx => (mem_union.mp hx).elim id fun hx =>
    mem_union.mpr <| .inr <| hrel.1 x <| mem_union.mpr <| .inr hx,
    bijective_extend hrel.2 ha hb⟩

end GSetBij

end Iris
