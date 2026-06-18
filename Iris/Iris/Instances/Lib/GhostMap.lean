/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.Instances.IProp
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode

@[expose] public section

namespace Iris

open Std HeapView PartialMap Iris.Algebra CMRA BI ProofMode

@[rocq_alias ghost_mapG]
class GhostMapG (GF : BundledGFunctors)
    (K V : Type _) (H : outParam <| Type _ → Type _)
    [LawfulFiniteMap H K] where
  elem : ElemG GF (constOF (HeapView K (Agree (LeibnizO V)) H))

attribute [reducible, instance] GhostMapG.elem

section definitions

variable [LawfulFiniteMap H K] [GhostMapG GF K V H]

@[rocq_alias ghost_map_auth]
public def ghost_map_auth (γ : GName) (dq : DFrac) (m : H V) : IProp GF :=
  iOwn (E := GhostMapG.elem) γ (Auth dq (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

#rocq_ignore ghost_map_auth_def "Not needed"
#rocq_ignore ghost_map_auth_aux "Not needed"
#rocq_ignore ghost_map_auth_unseal "Not needed"

@[rocq_alias ghost_map_elem]
public def ghost_map_elem (γ : GName) (dq : DFrac) (k : K) (v : V) : IProp GF :=
  iOwn (E := GhostMapG.elem) γ (Frag k dq (toAgree ⟨v⟩))

#rocq_ignore ghost_map_elem_def "Not needed"
#rocq_ignore ghost_map_elem_aux "Not needed"
#rocq_ignore ghost_map_elem_unseal "Not needed"

#rocq_ignore «ghost_mapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_ghost_mapΣ» "Subsumed by BundledGFunctors typeclass synthesis"

end definitions

notation γ " ↪●MAP{" dq "} " m => ghost_map_auth γ dq m
notation γ " ↪●MAP " m => ghost_map_auth γ (DFrac.own 1) m
notation γ " ↪◯MAP[" k "]{" dq "} " v => ghost_map_elem γ dq k v
notation γ " ↪◯MAP[" k "] " v => ghost_map_elem γ (DFrac.own 1) k v

section lemmas

variable {K V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H K]
variable [GhostMapG GF K V H]

open LawfulPartialMap

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName) (k : K) (dq : DFrac) (v : V) :
    Timeless (PROP := IProp GF) (γ ↪◯MAP[k]{dq} v) := by
  unfold ghost_map_elem
  infer_instance

@[rocq_alias ghost_map_elem_persistent]
instance (γ : GName) (k : K) (v : V) : Persistent (PROP := IProp GF) (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  infer_instance

@[rocq_alias ghost_map_elem_fractional]
instance ghost_map_elem_fractional (γ : GName) (k : K) (v : V) :
    Fractional (PROP := IProp GF) (fun q : Qp => γ ↪◯MAP[k]{.own q} v) where
  fractional p q := by
    unfold ghost_map_elem
    refine .trans ?_ iOwn_op
    refine equiv_iff.mp ?_
    refine .trans ?_ (iOwn_ne.eqv frag_add_op_eqv)
    refine OFE.NonExpansive.eqv (OFE.NonExpansive.eqv ?_)
    exact Agree.idemp.symm

@[rocq_alias ghost_map_elem_as_fractional]
instance (γ : GName) (k : K) (v : V) : AsFractional (PROP := IProp GF) (γ ↪◯MAP[k]{.own q} v)
    (fun q => γ ↪◯MAP[k]{.own q} v) q where
  as_fractional := IProp.ext_iff.mp rfl
  as_fractional_fractional := ghost_map_elem_fractional γ k v

@[rocq_alias ghost_map_elems_unseal]
theorem ghost_map_elems_unseal [DecidableEq K] γ (m : H V) dq :
    ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{dq} v) ==∗
    iOwn (GF := GF) (E := GhostMapG.elem) γ ([^ op map] k ↦ v ∈ m,
      Frag k dq (toAgree (⟨v⟩: LeibnizO V))) := by
  iintro H
  by_cases h : m ≡ₘ ∅
  · iapply OFE.NonExpansive.eqv <| OFE.NonExpansive.eqv (BigOpM.bigOpM_eqv_of_perm _ h)
    simp only [BigOpM.bigOpM_empty]
    iapply iOwn_unit (γ := γ) (ε := unit)
  · imodintro
    iapply bigOpM_iOwn _ _ _ h
    unfold ghost_map_elem
    iexact H

@[rocq_alias ghost_map_elem_valid]
theorem ghost_map_elem_valid (γ : GName) (k : K) (dq : DFrac) (v : V) :
    (γ ↪◯MAP[k]{dq} v) ⊢@{IProp GF} internalCmraValid dq := by
  refine iOwn_cmraValid.trans ?_
  iintro %h
  ipureintro
  exact (frag_valid_iff.mp h).left

@[rocq_alias ghost_map_elem_valid_2]
theorem ghost_map_elem_valid_2 (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF}
      internalCmraValid (dq1 • dq2) ∧ ⌜v1 = v2⌝ := by
  unfold ghost_map_elem
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  obtain ⟨vdq, va⟩ := frag_op_valid_iff.mp H
  ipureintro
  exact ⟨vdq, congrArg (·.car) (toAgree_op_valid_iff_eq.mp va)⟩

@[rocq_alias ghost_map_elem_agree]
theorem ghost_map_elem_agree (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF} ⌜v1 = v2⌝ := by
  iintro H
  icases ghost_map_elem_valid_2 $$ H with ⟨-, $⟩

@[rocq_alias ghost_map_elem_combine_gives]
instance ghost_map_elem_combine_gives γ (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepGives (PROP := IProp GF)
      (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    iintro H
    icases ghost_map_elem_valid_2 $$ H with %H
    itrivial

@[rocq_alias ghost_map_elem_combine]
theorem ghost_map_elem_combine (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    ⊢@{IProp GF}(γ ↪◯MAP[k]{dq1} v1) -∗ (γ ↪◯MAP[k]{dq2} v2) -∗
      (γ ↪◯MAP[k]{dq1 • dq2} v1) ∗ ⌜v1 = v2⌝ := by
  iintro Hl1 Hl2
  icases ghost_map_elem_agree $$ [$Hl1 $Hl2] with #%heq
  iframe %heq; subst heq
  unfold ghost_map_elem
  icombine Hl1 Hl2 as $

@[rocq_alias ghost_map_elem_combine_as]
instance ghost_map_elem_combine_as (γ : GName) (k : K) (dq1 dq2 : DFrac) (v1 v2 : V) :
    CombineSepAs (PROP := IProp GF)
      (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
      (γ ↪◯MAP[k]{dq1 • dq2} v1) where
  combine_sep_as := by
    iintro ⟨Hl1, Hl2⟩
    icases ghost_map_elem_combine $$ Hl1 Hl2 with ⟨H, -⟩
    iframe

@[rocq_alias ghost_map_elem_frac_ne]
theorem ghost_map_elem_frac_ne γ (k1 k2 : K) (dq1 dq2 : DFrac) (v1 v2 : V) (Hk : ¬ ✓ (dq1 • dq2)) :
    ⊢@{IProp GF} (γ ↪◯MAP[k1]{dq1} v1) -∗ (γ ↪◯MAP[k2]{dq2} v2) -∗ ⌜k1 ≠ k2⌝ := by
  iintro Hl1 Hl2
  iintro %Heq; subst Heq
  icombine Hl1 Hl2 gives ⟨%_, %_⟩
  trivial

@[rocq_alias ghost_map_elem_ne]
theorem ghost_map_elem_ne γ (k1 k2 : K) (dq : DFrac) (v1 v2 : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k1] v1) -∗ (γ ↪◯MAP[k2]{dq} v2) -∗ ⌜k1 ≠ k2⌝ := by
  iintro H G
  iapply ghost_map_elem_frac_ne $$ H G
  intro HContra
  exact absurd (DFrac.valid_own_op HContra) (by have : (1 : Qp).val = 1 := rfl; grind)

/-- Make an element read-only. -/
@[rocq_alias ghost_map_elem_persist]
theorem ghost_map_elem_persist (γ : GName) (k : K) (dq : DFrac) (v : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k]{dq} v) ==∗ (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  iintro H
  iapply iOwn_update $$ H
  exact update_frag_discard

/-- Recover fractional ownership for a read-only element. -/
@[rocq_alias ghost_map_elem_unpersist]
theorem ghost_map_elem_unpersist (γ : GName) (k : K) (v : V) :
    ⊢@{IProp GF} (γ ↪◯MAP[k]{.discard} v) ==∗ ∃ q, (γ ↪◯MAP[k]{.own q} v) := by
  unfold ghost_map_elem
  iintro H
  imod iOwn_updateP update_frag_acquire $$ H with ⟨%a, %Heq, G⟩
  obtain ⟨q, Heq⟩ := Heq
  iexists q; subst Heq
  iframe

/-! ### Lemmas about `ghost_map_auth` -/

@[rocq_alias ghost_map_alloc_strong]
theorem ghost_map_alloc_strong [DecidableEq K] (P : GName → Prop) (m : H V) :
  (∀ N, ∃ k, N ≤ k ∧ P k) →
  ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  unfold ghost_map_elem ghost_map_auth
  iintro %Hinf
  imod iOwn_alloc_strong (E := GhostMapG.elem)
    (Auth (DFrac.own 1) (V := Agree (LeibnizO V)) (∅ : H _)) P Hinf with ⟨%γ, %HP, G⟩
  · simpa only [auth_valid_iff] using DFrac.valid_own_one
  · iexists γ; iframe %HP
    iapply BIUpdate.mono <| sep_mono_right <| bigOpM_iOwn_entail γ _ m
    iapply BIUpdate.mono <| iOwn_op.mp
    iapply iOwn_update $$ G
    refine Update.equiv_right ?_
      (update_big_alloc _ (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m) _
        (disjoint_empty_right _) DFrac.valid_own_one
        (all_map fun _ _ => Agree.toAgree_valid))
    refine CMRA.op_eqv ?_ (BigOpM.bigOpM_map_eqv _ _ _)
    exact OFE.NonExpansive.eqv (PartialMap.eqv_of_Equiv union_empty_right)

@[rocq_alias ghost_map_alloc_strong_empty]
theorem ghost_map_alloc_strong_empty [DecidableEq K] (P : GName → Prop)
    (Hinf : ∀ N, ∃ k, N ≤ k ∧ P k) :
    ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP (∅ : H V)) := by
  imod ghost_map_alloc_strong P (∅ : H V) Hinf with ⟨%γ, H1, H2, -⟩
  iexists γ
  iframe

@[rocq_alias ghost_map_alloc]
theorem ghost_map_alloc [DecidableEq K] (m : H V) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  imod (ghost_map_alloc_strong (fun _ => True) m) with ⟨%γ, -, H1, H2⟩
  · intro N; exists N; simp
  · iexists γ
    iframe H1 H2

@[rocq_alias ghost_map_alloc_empty]
theorem ghost_map_alloc_empty [DecidableEq K] : ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP (∅ : H V)) := by
  imod ghost_map_alloc (∅ : H V) with ⟨%γ, _, -⟩
  imodintro
  iexists γ
  iassumption

@[rocq_alias ghost_map_auth_timeless]
instance (m : H V) : Timeless (PROP := IProp GF) (γ ↪●MAP{dq} m) := by
  unfold ghost_map_auth
  infer_instance

@[rocq_alias ghost_map_persistent]
instance (m : H V) : Timeless (PROP := IProp GF) (γ ↪●MAP{.discard} m) := by
  unfold ghost_map_auth
  infer_instance

@[rocq_alias ghost_map_auth_fractional]
instance ghost_map_auth_fractional (m : H V) :
    Fractional (PROP := IProp GF) (fun q => γ ↪●MAP{.own q} m) where
  fractional p q := by
    unfold ghost_map_auth
    refine .trans ?_ iOwn_op
    refine equiv_iff.mp ?_
    refine .trans ?_ (iOwn_ne.eqv auth_dfrac_op_eqv)
    rfl

@[rocq_alias ghost_map_auth_as_fractional]
instance (γ : GName) (m : H V) (q : Qp) :
    AsFractional (PROP := IProp GF) (γ ↪●MAP{.own q} m) (fun q => γ ↪●MAP{.own q} m) q where
  as_fractional := IProp.ext_iff.mp rfl
  as_fractional_fractional := ghost_map_auth_fractional m

@[rocq_alias ghost_map_auth_valid]
theorem ghost_map_auth_valid γ (dq : DFrac) (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ ⌜✓ dq⌝ := by
  unfold ghost_map_auth
  iintro _
  refine iOwn_cmraValid.trans ?_
  iintro %H; ipureintro
  apply auth_valid_iff.mp H

@[rocq_alias ghost_map_auth_valid_2]
theorem ghost_map_auth_valid_2 {γ} {dq1 dq2 : DFrac} {m1 m2 : H V} :
    ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜✓ (dq1 • dq2) ∧ m1 ≡ₘ m2⌝ := by
  unfold ghost_map_auth
  iintro H1 H2
  icombine H1 H2 gives %G
  ipureintro
  have ⟨h₁, h₂⟩ := auth_op_auth_valid_iff.mp G
  refine ⟨h₁, fun k => ?_⟩
  have h := h₂ k
  simp only [get?_map, Option.map] at h
  cases h₁ : get? m1 k <;> cases h₂ : get? m2 k <;>
    grind [OFE.not_none_eqv_some, OFE.not_some_eqv_none,
      → Agree.toAgree_inj, LeibnizO.eqv_inj, OFE.some_eqv_some, Option.some.injEq]

@[rocq_alias ghost_map_auth_agree]
theorem ghost_map_auth_agree γ (dq1 dq2 : DFrac) (m1 m2 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜m1 ≡ₘ m2⌝ := by
  iintro H₁ H₂
  ihave ⟨_, $⟩ := ghost_map_auth_valid_2 $$ H₁ H₂

@[rocq_alias ghost_map_auth_persist]
theorem ghost_map_auth_persist γ dq (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) ==∗ γ ↪●MAP{.discard} m := by
  unfold ghost_map_auth
  iapply iOwn_update auth_dfrac_discard

@[rocq_alias ghost_map_auth_unpersist]
theorem ghost_map_auth_unpersist γ (m : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{.discard} m) ==∗ ∃ q, γ ↪●MAP{.own q} m := by
  unfold ghost_map_auth
  iintro H
  imod iOwn_updateP auth_dfrac_acquire $$ H with ⟨%a, %Heq, G⟩
  obtain ⟨q, Heq⟩ := Heq
  iexists q; subst Heq
  iframe

/-! ### Lemmas about the interaction of `ghost_map_auth` with the elements -/

@[rocq_alias ghost_map_lookup]
theorem ghost_map_lookup {γ dq} {m : H V} {k : K} {dq' v} :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ (γ ↪◯MAP[k]{dq'} v) -∗ ⌜get? m k = some v⌝ := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  icombine H1 H2 gives %G
  ipureintro
  have ⟨av', _, _, h_av', _, h⟩ := auth_op_frag_valid_total_discrete_iff G
  cases h₂ : get? m k <;> grind [get?_map,Agree.toAgree_included, OFE.leibniz]

@[rocq_alias ghost_map_lookup_combine_gives_1]
instance ghost_map_lookup_combine_gives_1 γ (m : H V) (k : K) (dq1 dq2 : DFrac) (v : V) :
  CombineSepGives (PROP := IProp GF)
    (γ ↪●MAP{dq1} m) (γ ↪◯MAP[k]{dq2} v)
    iprop(⌜get? m k = .some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ H G with %H
    itrivial

@[rocq_alias ghost_map_lookup_combine_gives_2]
instance ghost_map_lookup_combine_gives_2 γ (m : H V) (k : K) (dq dq' : DFrac) (v : V) :
  CombineSepGives (PROP := IProp GF)
    (γ ↪◯MAP[k]{dq} v) (γ ↪●MAP{dq'} m)
    iprop(⌜get? m k = .some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ G H with %H
    itrivial

@[rocq_alias ghost_map_insert]
theorem ghost_map_insert {γ} {m : H V} (k : K) (v : V) (Heq : get? m k = .none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro H
  imod iOwn_update (update_one_alloc (k := k) (v1 := toAgree ⟨v⟩)
    (by simp [get?_map, Heq])
    DFrac.valid_own_one
    Agree.toAgree_valid) $$ H with H
  icases H with ⟨H, $⟩
  imodintro
  iapply iOwn_mono $$ H
  exact auth_inc_of_pmap_eqv _ map_insert

@[rocq_alias ghost_map_insert_persist]
theorem ghost_map_insert_persist {γ} {m : H V} (k : K) (v : V) (Heq : get? m k = .none) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ (γ ↪◯MAP[k]{.discard} v) := by
  iintro H
  imod ghost_map_insert k v Heq $$ H with ⟨$, G⟩
  iapply ghost_map_elem_persist $$ G

@[rocq_alias ghost_map_delete]
theorem ghost_map_delete {γ} {m : H V} (k : K) (v : V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ γ ↪●MAP delete m k := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  icombine H1 H2 as G
  imod iOwn_update (update_one_delete (k := k) (v1 := toAgree (⟨v⟩ : LeibnizO V))) $$ G with G
  iapply iOwn_mono $$ G
  exact auth_inc_of_pmap_eqv _ map_delete

-- TODO: Make these implicit

@[rocq_alias ghost_map_update]
theorem ghost_map_update {γ} {m : H V} (k : K) (v : V) (w : V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ (γ ↪●MAP insert m k w) ∗ γ ↪◯MAP[k] w := by
  iintro auth_m frag_kv
  ihave >aux := ghost_map_delete $$ auth_m frag_kv
  ihave >⟨aux, $⟩ := ghost_map_insert _ w (get?_delete_eq rfl) $$ aux
  imodintro
  unfold ghost_map_auth
  iapply iOwn_mono $$ aux
  refine auth_inc_of_pmap_eqv _ ?_
  intro i
  rw [get?_map, get?_map, insert_delete i]

/-! ### Big-op versions of the above lemmas -/

@[rocq_alias ghost_map_lookup_big]
theorem ghost_map_lookup_big {γ dq} {m : H V} {dq'} m0 :
    ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k]{dq'} v) -∗ ⌜m0 ⊆ m⌝ := by
  iintro H1 H2
  simp only [Subset, submap]
  iintro %k %v %Heq
  iapply ghost_map_lookup $$ H1 [H2]
  iapply BigSepM.bigSepM_lookup Heq $$ H2

@[rocq_alias ghost_map_insert_big]
theorem ghost_map_insert_big [DecidableEq K] {γ m} (m' : H V) (Hdisj : m' ##ₘ m) :
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗
  (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro H
  by_cases h : m' ≡ₘ ∅
  · imodintro
    isplitl [H]
    · iapply iOwn_mono $$ H
      exact auth_inc_of_pmap_eqv _ (map_equiv ((union_equiv h .refl).trans union_empty_left))
    · iapply (BigSepM.bigSepM_eqv_empty h).mpr; itrivial
  · rw [←(bigOpM_iOwn γ _ _ h).to_eq, ←iOwn_op.to_eq]
    imod iOwn_update (E := GhostMapG.elem) (update_big_alloc _
        (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m') (DFrac.own 1)
        (disjoint_map Hdisj) DFrac.valid_own_one
        (all_map fun _ _ => Agree.toAgree_valid)) $$ H with H
    icases H with ⟨H1, H2⟩
    imodintro
    isplitl [H1]
    · iapply iOwn_mono $$ H1
      exact auth_inc_of_pmap_eqv _ map_union
    · iapply iOwn_mono $$ H2
      exact inc_of_inc_of_eqv .rfl (BigOpM.bigOpM_map_eqv _ _ _).symm

@[rocq_alias ghost_map_insert_persist_big]
theorem ghost_map_insert_persist_big [DecidableEq K] {γ m} (m' : H V) (Hdisj : m' ##ₘ m) :
    ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k]{.discard} v := by
  iintro H
  imod ghost_map_insert_big m' Hdisj $$ H with ⟨$, H⟩
  iapply BigSepM.bigSepM_bupd
  iapply BigSepM.bigSepM_impl $$ H
  iintro !> %k %v %Heq H
  iapply ghost_map_elem_persist $$ H

@[rocq_alias ghost_map_delete_big]
theorem ghost_map_delete_big [DecidableEq K] {γ m} (m0 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗ (γ ↪●MAP (m \ m0)) := by
  iintro H1 H2
  imod ghost_map_elems_unseal $$ H2 with H2
  unfold ghost_map_auth
  iapply iOwn_update_op $$ [$H1 $H2]
  refine Update.equiv_left (CMRA.op_right_eqv _ (BigOpM.bigOpM_map_eqv _ _ m0)) ?_
  refine (update_big_delete _ _).trans ?_
  refine Update.equiv_right ?_ .id
  exact OFE.NonExpansive.eqv (PartialMap.eqv_of_Equiv map_difference_map)

@[rocq_alias ghost_map_update_big]
theorem ghost_map_update_big [DecidableEq K] {γ m} (m0 m1 : H V) (Heq : dom m0 = dom m1) :
    ⊢@{IProp GF} (γ ↪●MAP m) -∗ ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗
    (γ ↪●MAP (m1 ∪ m)) ∗ [∗map] k ↦ v ∈ m1, γ ↪◯MAP[k] v := by
  iintro H1 H2
  imod ghost_map_elems_unseal $$ H2 with H2
  by_cases h : m1 ≡ₘ ∅
  · imodintro
    isplitl [H1]
    · unfold ghost_map_auth
      iapply iOwn_mono $$ H1
      exact auth_inc_of_pmap_eqv _ (map_equiv ((union_equiv h .refl).trans union_empty_left))
    · iapply (BigSepM.bigSepM_eqv_empty h).mpr; itrivial
  · unfold ghost_map_elem ghost_map_auth
    icombine H1 H2 as H
    rw [←(bigOpM_iOwn γ _ _ h).to_eq, ←iOwn_op.to_eq]
    iapply iOwn_update $$ H
    refine Update.equiv_left (CMRA.op_right_eqv _ (BigOpM.bigOpM_map_eqv _ _ m0)) ?_
    have Heq' : dom (Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m0) =
        dom (Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m1) := by
      rw [dom_map, dom_map, Heq]
    refine (update_big_replace _ _ _ Heq'
      (all_map fun _ _ => Agree.toAgree_valid)).trans ?_
    refine Update.equiv_right ?_ .id
    refine CMRA.op_eqv ?_ (BigOpM.bigOpM_map_eqv _ _ _)
    exact OFE.NonExpansive.eqv (PartialMap.eqv_of_Equiv map_union.symm)

end lemmas

end Iris

end
