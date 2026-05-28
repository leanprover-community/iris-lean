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
class GhostMapG (GF : BundledGFunctors) (F : outParam <| Type _)
    (K V : Type _) (H : outParam <| Type _ → Type _)
    [UFraction F] [LawfulFiniteMap H K] where
  elem : ElemG GF (constOF (HeapView F K (Agree (LeibnizO V)) H))

attribute [reducible, instance] GhostMapG.elem

section definitions

variable [UFraction F] [LawfulFiniteMap H K] [GhostMapG GF F K V H]

@[rocq_alias ghost_map_auth]
public def ghost_map_auth (γ : GName) (dq : DFrac F) (m : H V) : IProp GF :=
  iOwn (E := GhostMapG.elem) γ
    (Auth dq (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

#rocq_ignore ghost_map_auth_def "Not needed"
#rocq_ignore ghost_map_auth_aux "Not needed"
#rocq_ignore ghost_map_auth_unseal "Not needed"

@[rocq_alias ghost_map_elem]
public def ghost_map_elem (γ : GName) (dq : DFrac F) (k : K) (v : V) : IProp GF :=
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

variable {F K V : Type _} {H : Type _ → Type _} [UFraction F] [LawfulFiniteMap H K]
variable [GhostMapG GF F K V H]

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName) (k : K) (dq : DFrac F) (v : V) :
    Timeless (PROP := IProp GF) (γ ↪◯MAP[k]{dq} v) := by
  unfold ghost_map_elem
  infer_instance

@[rocq_alias ghost_map_elem_persistent]
instance (γ : GName) (k : K) (v : V) :
    Persistent (PROP := IProp GF) (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  infer_instance

@[rocq_alias ghost_map_elem_fractional]
instance ghost_map_elem_fractional (γ : GName) (k : K) (v : V)
    : Fractional (PROP := IProp GF) (fun q : F => γ ↪◯MAP[k]{.own q} v) where
  fractional p q := by
    unfold ghost_map_elem
    refine .trans ?_ iOwn_op
    refine equiv_iff.mp ?_
    refine .trans ?_ (iOwn_ne.eqv frag_add_op_equiv)
    refine OFE.NonExpansive.eqv (OFE.NonExpansive.eqv ?_)
    exact Agree.idemp.symm

@[rocq_alias ghost_map_elem_as_fractional]
instance (γ : GName) (k : K) (v : V)
    : AsFractional (PROP := IProp GF) (γ ↪◯MAP[k]{.own q} v)
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
  · iapply OFE.NonExpansive.eqv <| OFE.NonExpansive.eqv (BigOpM.bigOpM_equiv_of_perm _ h)
    simp [BigOpM.bigOpM_empty]
    iapply iOwn_unit (γ := γ) (ε := unit)
  · imodintro
    iapply bigOpM_iOwn _ _ _ (fun c => h c)
    unfold ghost_map_elem
    iexact H

@[rocq_alias ghost_map_elem_valid]
theorem ghost_map_elem_valid (γ : GName) (k : K) (dq : DFrac F) (v : V) :
    (γ ↪◯MAP[k]{dq} v) ⊢@{IProp GF} internalCmraValid dq := by
  refine iOwn_cmraValid.trans ?_
  iintro h
  ipure h; ipure_intro
  exact (frag_valid_iff.mp h).left

@[rocq_alias ghost_map_elem_valid_2]
theorem ghost_map_elem_valid_2 (γ : GName) (k : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF}
      internalCmraValid (dq1 • dq2) ∧ ⌜v1 = v2⌝ := by
  unfold ghost_map_elem
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  obtain ⟨vdq, va⟩ := frag_op_valid_iff.mp H
  ipure_intro
  exact ⟨vdq, congrArg (·.car) (toAgree_op_valid_iff_eq.mp va)⟩

@[rocq_alias ghost_map_elem_agree]
theorem ghost_map_elem_agree (γ : GName) (k : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF} ⌜v1 = v2⌝ := by
  iintro H
  icases ghost_map_elem_valid_2 $$ H with ⟨-, $⟩

@[rocq_alias ghost_map_elem_combine_gives]
instance ghost_map_elem_combine_gives γ (k : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
  CombineSepGives (PROP := IProp GF)
    (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
    iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    iintro H
    icases ghost_map_elem_valid_2 $$ H with %H
    imodintro; ipure_intro; assumption

@[rocq_alias ghost_map_elem_combine]
theorem ghost_map_elem_combine (γ : GName) (k : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
    ⊢@{IProp GF}(γ ↪◯MAP[k]{dq1} v1) -∗ (γ ↪◯MAP[k]{dq2} v2)
      -∗ (γ ↪◯MAP[k]{dq1 • dq2} v1) ∗ ⌜v1 = v2⌝ := by
  iintro Hl1 Hl2
  icases ghost_map_elem_agree $$ [$Hl1 $Hl2] with #%heq
  iframe %heq; subst heq
  icombine Hl1 Hl2 as Hl
  unfold ghost_map_elem
  icombine H1 H2 as $

@[rocq_alias ghost_map_elem_combine_as]
instance ghost_map_elem_combine_as (γ : GName) (k : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
  CombineSepAs (PROP := IProp GF)
    (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
    (γ ↪◯MAP[k]{dq1 • dq2} v1) where
  combine_sep_as := by
    iintro ⟨Hl1, Hl2⟩
    icases ghost_map_elem_combine $$ Hl1 Hl2 with ⟨H, -⟩
    iframe

@[rocq_alias ghost_map_elem_frac_ne]
theorem ghost_map_elem_frac_ne γ (k1 k2 : K) (dq1 dq2 : DFrac F) (v1 v2 : V) :
   ¬ ✓ (dq1 • dq2) →
    ⊢@{IProp GF} (γ ↪◯MAP[k1]{dq1} v1) -∗ (γ ↪◯MAP[k2]{dq2} v2) -∗ ⌜k1 ≠ k2⌝ := by
  iintro %Hcontra Hl1 Hl2
  iintro %Heq; subst Heq
  icombine Hl1 Hl2 gives ⟨%_, %_⟩
  trivial

@[rocq_alias ghost_map_elem_ne]
theorem ghost_map_elem_ne γ (k1 k2 : K) (dq : DFrac F) (v1 v2 : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k1] v1) -∗ (γ ↪◯MAP[k2]{dq} v2) -∗ ⌜k1 ≠ k2⌝ := by
  iintro H G
  iapply ghost_map_elem_frac_ne $$ H G
  intro HContra
  exact Fraction.Whole.not_fractional UFraction.one_whole (DFrac.valid_own_op HContra)

/-- Make an element read-only. -/
@[rocq_alias ghost_map_elem_persist]
theorem ghost_map_elem_persist (γ : GName) (k : K) (dq : DFrac F) (v : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq} v) ==∗ (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  iintro H
  iapply iOwn_update $$ H
  exact update_frag_discard

/-- Recover fractional ownership for a read-only element. -/
@[rocq_alias ghost_map_elem_unpersist]
theorem ghost_map_elem_unpersist [IsHalfFraction F] (γ : GName) (k : K) (v : V) :
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
    (Auth (DFrac.own 1) (K := K) (V := (Agree (LeibnizO V))) (Std.PartialMap.map (fun x => toAgree ⟨x⟩) ∅)) P Hinf with ⟨%γ, %HP, G⟩
  · simpa only [auth_valid_iff] using DFrac.valid_own_one
  · iexists γ; iframe %HP
    iapply BIUpdate.mono <| sep_mono_r <|
      bigOpM_iOwn_entail (F := constOF (HeapView F K (Agree (LeibnizO V)) H))
        (E := GhostMapG.elem) γ _ m
    iapply BIUpdate.mono <| iOwn_op.mp
    iapply iOwn_update $$ G
    refine Update.equiv_right ?_ (update_big_alloc (F:= F) (K := K) (V := (Agree (LeibnizO V)))
      (Std.PartialMap.map (fun x => toAgree { car := x }) ∅)
      (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m) (DFrac.own 1) ?_ ?_ ?_)
    · refine CMRA.op_eqv ?_ (BigOpM.bigOpM_map_equiv _ _ _)
      refine OFE.NonExpansive.eqv <| eqv_of_Equiv ?_
      refine .trans ?_ LawfulPartialMap.union_empty_right
      refine LawfulPartialMap.union_equiv PartialMap.equiv.refl LawfulPartialMap.map_empty
    · simp only [EmptyCollection.emptyCollection, disjoint_iff, LawfulPartialMap.get?_map,
      Option.map_eq_none_iff, get?_empty, Option.map_none, _root_.or_true, implies_true]
    · exact DFrac.valid_own_one
    · -- TODO: golf
      rw [LawfulFiniteMap.all_iff_toList]
      intro ⟨k, v⟩
      rw [toList_get, LawfulPartialMap.get?_map]
      simp only [Option.map_eq_some_iff, forall_exists_index, and_imp]
      rintro x Hx ⟨⟩
      simp only [Agree.valid_def, Agree.valid]
      intro; exact True.intro

@[rocq_alias ghost_map_alloc_strong_empty]
theorem ghost_map_alloc_strong_empty [DecidableEq K] (P : GName → Prop) :
  (∀ N, ∃ k, N ≤ k ∧ P k) →
  ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP (∅ : H V)) := by
  iintro %Hinf
  imod ghost_map_alloc_strong P (∅ : H V) Hinf with ⟨%γ, H1, H2, -⟩
  iexists γ
  iframe

@[rocq_alias ghost_map_alloc]
theorem ghost_map_alloc [DecidableEq K] (m : H V) :
  ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP m) ∗
    [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := by
  imod (ghost_map_alloc_strong (fun _ => True) m) with ⟨%γ, -, H1, H2⟩
  · intro N; exists N; simp
  · iexists γ
    iframe H1 H2

@[rocq_alias ghost_map_alloc_empty]
theorem ghost_map_alloc_empty [DecidableEq K] :
  ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP (∅ : H V)) := by
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
    refine .trans ?_ (iOwn_ne.eqv auth_dfrac_op_equiv)
    rfl

@[rocq_alias ghost_map_auth_as_fractional]
instance (γ : GName) (m : H V) (q : F)
    : AsFractional (PROP := IProp GF) (γ ↪●MAP{.own q} m)
      (fun q => γ ↪●MAP{.own q} m) q where
  as_fractional := IProp.ext_iff.mp rfl
  as_fractional_fractional := ghost_map_auth_fractional m

@[rocq_alias ghost_map_auth_valid]
theorem ghost_map_auth_valid γ (dq : DFrac F) (m : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ ⌜✓ dq⌝ := by
    unfold ghost_map_auth
    iintro _
    refine iOwn_cmraValid.trans ?_
    iintro %H; ipure_intro
    apply auth_valid_iff.mp H

@[rocq_alias ghost_map_auth_valid_2]
theorem ghost_map_auth_valid_2 {γ} {dq1 dq2 : DFrac F} {m1 m2 : H V} :
    ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜✓ (dq1 • dq2) ∧ m1 ≡ₘ m2⌝ := by
  unfold ghost_map_auth
  iintro H1 H2
  icombine H1 H2 gives %G
  ipure_intro
  have ⟨h₁, h₂⟩ := auth_op_auth_valid_iff.mp G
  refine ⟨h₁, fun k => ?_⟩
  have h := h₂ k
  simp only [LawfulPartialMap.get?_map, Option.map] at h
  cases h₁ : get? m1 k <;> cases h₂ : get? m2 k
    <;> grind [OFE.not_none_eqv_some, OFE.not_some_eqv_none,
      → Agree.toAgree_inj, LeibnizO.eqv_inj, OFE.some_eqv_some, Option.some.injEq]

@[rocq_alias ghost_map_auth_agree]
theorem ghost_map_auth_agree γ (dq1 dq2 : DFrac F) (m1 m2 : H V) :
    ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜m1 ≡ₘ m2⌝ := by
  iintro H₁ H₂
  ihave ⟨_, $⟩ := ghost_map_auth_valid_2 $$ H₁ H₂

@[rocq_alias ghost_map_auth_persist]
theorem ghost_map_auth_persist γ dq (m : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) ==∗ γ ↪●MAP{.discard} m := by
  unfold ghost_map_auth
  iapply iOwn_update auth_dfrac_discard

@[rocq_alias ghost_map_auth_unpersist]
theorem ghost_map_auth_unpersist [IsHalfFraction F] γ (m : H V) :
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
  ipure_intro
  have ⟨av', _, _, h_av', _, h⟩ := auth_op_frag_valid_total_discrete_iff G
  cases h₂ : get? m k <;> grind [Std.LawfulPartialMap.get?_map,Agree.toAgree_included, OFE.leibniz]

@[rocq_alias ghost_map_lookup_combine_gives_1]
instance ghost_map_lookup_combine_gives_1 γ (m : H V) (k : K) (dq1 dq2 : DFrac F) (v : V) :
  CombineSepGives (PROP := IProp GF)
    (γ ↪●MAP{dq1} m) (γ ↪◯MAP[k]{dq2} v)
    iprop(⌜get? m k = .some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ H G with %H
    ipure_intro; assumption

@[rocq_alias ghost_map_lookup_combine_gives_2]
instance ghost_map_lookup_combine_gives_2 γ (m : H V) (k : K) (dq dq' : DFrac F) (v : V) :
  CombineSepGives (PROP := IProp GF)
    (γ ↪◯MAP[k]{dq} v) (γ ↪●MAP{dq'} m)
    iprop(⌜get? m k = .some v⌝) where
  combine_sep_gives := by
    iintro ⟨H, G⟩
    icases ghost_map_lookup $$ G H with %H
    ipure_intro; assumption

@[rocq_alias ghost_map_insert]
theorem ghost_map_insert {γ} {m : H V} (k : K) (v : V) :
  get? m k = .none →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro %Heq H
  imod iOwn_update (update_one_alloc (k := k) (v1 := toAgree (⟨v⟩ : LeibnizO V))
    (by simp [LawfulPartialMap.get?_map, Heq])
    DFrac.valid_own_one
    (by simp [Agree.valid_def, Agree.valid, Agree.validN, toAgree])) $$ H with H
  icases H with ⟨H, $⟩
  imodintro
  iapply iOwn_mono $$ H
  refine inc_of_inc_of_eqv .rfl ?_
  refine OFE.NonExpansive.eqv ?_
  intro i
  by_cases H : k = i
    <;> simp [H, LawfulPartialMap.get?_map, get?_insert_ne, get?_insert_eq]

@[rocq_alias ghost_map_insert_persist]
theorem ghost_map_insert_persist {γ} {m : H V} (k : K) (v : V) :
  get? m k = .none →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ (γ ↪◯MAP[k]{.discard} v) := by
  iintro %Heq H
  imod ghost_map_insert k v Heq $$ H with ⟨$, G⟩
  iapply ghost_map_elem_persist $$ G

@[rocq_alias ghost_map_delete]
theorem ghost_map_delete {γ} {m : H V} (k : K) (v : V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ γ ↪●MAP delete m k := by
  unfold ghost_map_auth ghost_map_elem
  iintro H1 H2
  icombine H1 H2 as G
  imod iOwn_update (update_one_delete (k := k) (v1 := toAgree (⟨v⟩ : LeibnizO V)))
    $$ G with G
  iapply iOwn_mono $$ G
  refine inc_of_inc_of_eqv .rfl ?_
  refine OFE.NonExpansive.eqv ?_
  intro i
  by_cases H : k = i
    <;> simp [H, LawfulPartialMap.get?_map, get?_delete_eq, get?_delete_ne]

@[rocq_alias ghost_map_update]
theorem ghost_map_update {γ} {m : H V} (k : K) (v : V) (w : V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ (γ ↪●MAP insert m k w) ∗ γ ↪◯MAP[k] w := by
  iintro auth_m frag_kv
  ihave >aux := ghost_map_delete $$ auth_m frag_kv
  ihave >⟨aux, $⟩ := ghost_map_insert _ w (get?_delete_eq rfl) $$ aux
  imodintro
  unfold ghost_map_auth
  iapply iOwn_mono $$ aux
  refine inc_of_inc_of_eqv .rfl ?_
  refine OFE.NonExpansive.eqv ?_
  intro i
  refine eqv_of_Equiv ?_ i
  simp [Std.PartialMap.map, LawfulPartialMap.get?_insert_delete_same,
    get?_bindAlter, get?_bindAlter]

/-! ### Big-op versions of the above lemmas -/

@[rocq_alias ghost_map_lookup_big]
theorem ghost_map_lookup_big {γ dq} {m : H V} {dq'} m0 :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗
  ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k]{dq'} v) -∗
  ⌜m0 ⊆ m⌝ := by
  iintro H1 H2
  simp only [Subset, submap]
  iintro %k %v %Heq
  iapply ghost_map_lookup $$ H1 [H2]
  iapply BigSepM.bigSepM_lookup Heq $$ H2

@[rocq_alias ghost_map_insert_big]
theorem ghost_map_insert_big [DecidableEq K] {γ m} (m' : H V) :
  (m' ##ₘ m) →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗
  (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k] v := by
  unfold ghost_map_auth ghost_map_elem
  iintro %Hdisj H
  by_cases h : m' ≡ₘ ∅
  · imodintro
    isplitl [H]
    · iapply iOwn_mono $$ H
      refine inc_of_inc_of_eqv .rfl ?_
      refine OFE.NonExpansive.eqv (fun i => ?_)
      simp [LawfulPartialMap.get?_map, Union.union, get?_merge, h i,
        EmptyCollection.emptyCollection, get?_empty]
    · simp only [bigSepM]
      refine (BI.equiv_iff.mp ?_).mpr
      refine (BigOpM.bigOpM_equiv_of_perm _ h).trans ?_
      simp [BigOpM.bigOpM_empty]
  rw [←IProp.ext (bigOpM_iOwn γ _ _ h), ←IProp.ext iOwn_op]
  imod iOwn_update (E := GhostMapG.elem) (update_big_alloc _
      (Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m') (DFrac.own 1)
      ?_ DFrac.valid_own_one ?_) $$ H with H
  · intro i
    specialize Hdisj i; simp only [not_and, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at Hdisj
    grind [LawfulPartialMap.get?_map]
  · rw [LawfulFiniteMap.all_iff_toList]
    intro ⟨k, v⟩
    rw [toList_get, LawfulPartialMap.get?_map]
    simp only [Option.map_eq_some_iff, forall_exists_index, and_imp]
    rintro x Hx ⟨⟩
    simp [Agree.valid_def, Agree.valid, Agree.validN, toAgree]
  · icases H with ⟨H1, H2⟩
    imodintro
    isplitl [H1]
    · iapply iOwn_mono $$ H1
      refine inc_of_inc_of_eqv .rfl ?_
      refine OFE.NonExpansive.eqv (fun i => ?_)
      simp only [Std.PartialMap.map, Union.union, union, get?_bindAlter, get?_merge, Option.merge]
      split <;> simp_all
    · iapply iOwn_mono $$ H2
      refine inc_of_inc_of_eqv .rfl ?_
      refine .trans ?_ (BigOpM.bigOpM_map_equiv _ _ _).symm
      exact .rfl

@[rocq_alias ghost_map_insert_persist_big]
theorem ghost_map_insert_persist_big [DecidableEq K] {γ m} (m' : H V) :
  m' ##ₘ m →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗
  (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k]{.discard} v := by
  iintro %Hdisj H
  imod ghost_map_insert_big m' Hdisj $$ H with ⟨$, H⟩
  iapply BigSepM.bigSepM_bupd
  iapply BigSepM.bigSepM_impl $$ H
  iintro !> %k %v %Heq H
  iapply ghost_map_elem_persist $$ H

@[rocq_alias ghost_map_delete_big]
theorem ghost_map_delete_big [DecidableEq K] {γ m} (m0 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗
  ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗
  (γ ↪●MAP (m \ m0)) := by
  iintro H1 H2
  imod ghost_map_elems_unseal $$ H2 with H2
  unfold ghost_map_auth
  iapply iOwn_update_op $$ [$H1 $H2]
  refine Update.equiv_left
    (CMRA.op_right_eqv _
      (BigOpM.bigOpM_map_equiv
        (fun x : V => toAgree (LeibnizO.mk x))
        (fun k v => Frag k (DFrac.own 1) v) m0))
    ?_
  refine (update_big_delete _ _).trans ?_
  refine Update.equiv_right ?_ .id
  refine OFE.NonExpansive.eqv (fun i => ?_)
  simp only [LawfulPartialMap.get?_difference, LawfulPartialMap.get?_map, Option.isSome_map]
  split <;> simp

@[rocq_alias ghost_map_update_big]
theorem ghost_map_update_big [DecidableEq K] {γ m} (m0 m1 : H V) :
  dom m0 = dom m1 →
  ⊢@{IProp GF} (γ ↪●MAP m) -∗
  ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗
  (γ ↪●MAP (m1 ∪ m)) ∗ [∗map] k ↦ v ∈ m1, γ ↪◯MAP[k] v := by
  iintro %Heq H1 H2
  imod ghost_map_elems_unseal $$ H2 with H2
  by_cases h : m1 ≡ₘ ∅
  · imodintro
    isplitl [H1]
    · unfold ghost_map_auth
      iapply iOwn_mono $$ H1
      refine inc_of_inc_of_eqv .rfl ?_
      refine OFE.NonExpansive.eqv (fun i => ?_)
      simp [LawfulPartialMap.get?_map, Union.union, get?_merge, h i,
        EmptyCollection.emptyCollection, get?_empty]
    · simp only [bigSepM]
      iclear H2
      refine (BI.equiv_iff.mp ?_).mpr
      refine (BigOpM.bigOpM_equiv_of_perm _ h).trans ?_
      simp [BigOpM.bigOpM_empty]
  unfold ghost_map_elem ghost_map_auth
  icombine H1 H2 as H
  rw [←IProp.ext (bigOpM_iOwn γ _ _ h), ←IProp.ext iOwn_op]
  iapply iOwn_update $$ H
  refine Update.equiv_left
    (CMRA.op_right_eqv _
      (BigOpM.bigOpM_map_equiv
        (fun x : V => toAgree (LeibnizO.mk x))
        (fun k v => Frag k (DFrac.own 1) v) m0))
    ?_
  have Heq' : dom (Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m0)
    = dom (Std.PartialMap.map (fun x : V => toAgree (LeibnizO.mk x)) m1) := by
    ext k
    simp only [PartialMap.dom, LawfulPartialMap.get?_map]
    have Heq' := congrFun Heq k
    simp only [PartialMap.dom] at Heq'
    simp [Heq']
  refine (update_big_replace _ _ _ Heq' ?_).trans ?_
  · rw [LawfulFiniteMap.all_iff_toList]
    intro ⟨k, v⟩
    rw [toList_get, LawfulPartialMap.get?_map]
    simp only [Option.map_eq_some_iff, forall_exists_index, and_imp]
    rintro x Hx ⟨⟩
    simp [Agree.valid_def, Agree.valid, Agree.validN, toAgree]
  · refine Update.equiv_right ?_ .id
    refine CMRA.op_eqv ?_ ?_
    · refine OFE.NonExpansive.eqv (fun i => ?_)
      simp only [LawfulPartialMap.get?_map, Union.union, union, get?_merge]
      cases (get? m1 i) <;> cases (get? m i) <;> simp [Option.merge]
    · refine .trans (BigOpM.bigOpM_map_equiv _ _ _) ?_
      exact .rfl

end lemmas

end Iris

end
