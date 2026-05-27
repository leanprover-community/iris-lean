/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.Instances.IProp
public import Iris.Std.HeapInstances
public import Iris.BI.Lib.Fractional
public import Iris.Algebra.BigOp
public import Iris.BI.BigOp.BigOp

namespace Iris

open Iris Std HeapView PartialMap Iris.Algebra CMRA BI

class GhostMapG (GF : BundledGFunctors) (F: outParam (Type _))
    (K V: Type _)(H : outParam <| Type _ → Type _)
    [UFraction F] [LawfulFiniteMap H K] where
  elem: ElemG GF (constOF (HeapView F K (Agree (LeibnizO V)) H))

section definitions

variable [UFraction F][LawfulFiniteMap H K][hgm: GhostMapG GF F K V H]

public def ghost_map_auth (γ : GName) (dq : DFrac F) (m : H V): IProp GF :=
  iOwn (E := hgm.elem) γ
    (Auth dq (Iris.Std.PartialMap.map (fun x ↦ toAgree ⟨x⟩) m))

public def ghost_map_elem (γ : GName) (dq : DFrac F) (k: K) (v: V): IProp GF :=
  iOwn (E := hgm.elem) γ (Frag k dq (toAgree ⟨v⟩))

end definitions

notation γ " ↪●MAP{" dq "} " m => ghost_map_auth γ dq m
notation γ " ↪●MAP " m => ghost_map_auth γ (DFrac.own 1) m
notation γ " ↪◯MAP[" k "]{" dq "} " v => ghost_map_elem γ dq k v
notation γ " ↪◯MAP[" k "] " v => ghost_map_elem γ (DFrac.own 1) k v

section lemmas

variable (F K V : Type _) (H : Type _ → Type _) [UFraction F] [LawfulFiniteMap H K]
variable [hgm: GhostMapG GF F K V H]

@[rocq_alias ghost_map_elem_timeless]
instance (γ : GName)(k: K)(dq: DFrac F)(v: V): Timeless (PROP := IProp GF) (γ ↪◯MAP[k]{dq} v) :=
  iOwn_timeless (E := hgm.elem)

@[rocq_alias ghost_map_elem_persistent]
instance (γ : GName)(k: K)(v: V): Persistent (PROP := IProp GF) (γ ↪◯MAP[k]{.discard} v) := by
  unfold ghost_map_elem
  infer_instance

@[rocq_alias ghost_map_elem_fractional]
instance ghost_map_elem_fractional (γ : GName)(k: K)(v: V)
    : Fractional (PROP := IProp GF) (fun q: F => γ ↪◯MAP[k]{.own q} v) where
  fractional p q := by
    -- If using `refine`/`apply` instead of stating facts with `have`,
    -- it's possible to eliminate some of implicit annotations.
    unfold ghost_map_elem
    refine .trans ?_ (iOwn_op (E := hgm.elem))
    refine equiv_iff.mp ?_
    refine .trans ?_ ((iOwn_ne (E := hgm.elem)).eqv frag_add_op_equiv)
    refine OFE.NonExpansive.eqv (OFE.NonExpansive.eqv ?_)
    exact Agree.idemp.symm

@[rocq_alias ghost_map_elem_as_fractional]
instance (γ : GName) (k: K) (v: V)
    : AsFractional (PROP := IProp GF) (γ ↪◯MAP[k]{.own q} v)
      (fun q => γ ↪◯MAP[k]{.own q} v) q where
  as_fractional := IProp.ext_iff.mp rfl
  as_fractional_fractional := ghost_map_elem_fractional F K V H γ k v

@[rocq_alias ghost_map_elems_unseal]
theorem ghost_map_elems_unseal γ (m : H V) dq :
  ([∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{dq} v) ==∗
  iOwn (E := hgm.elem) γ ([^ op map] k ↦ v ∈ m,
    Frag k dq (toAgree ⟨v⟩)) := by
  iintro H
  by_cases h : m = ∅
  · subst h
    simp only [BigOpM.bigOpM_empty]
    iapply iOwn_unit (E := hgm.elem)
  · -- Either via `BigOpM.bigOpM_weak_hom` or wait a bit, until there are `iOwn_bigOp_*` lemmas.
    -- Zongyuan kindly agreed to port them.
    sorry

@[rocq_alias ghost_map_elem_valid]
theorem ghost_map_elem_valid (γ : GName) (k : K) (dq: DFrac F) (v: V) :
    (γ ↪◯MAP[k]{dq} v) ⊢@{IProp GF} internalCmraValid dq := by
  refine (iOwn_cmraValid (E := hgm.elem)).trans ?_
  iintro h
  ipure h; ipure_intro
  exact (frag_valid_iff.mp h).left

#check iOwn_op
#check frag_op_valid_iff
#check Iris.Agree.op
#check toAgree_op_valid_iff_eq

@[rocq_alias ghost_map_elem_valid_2]
theorem ghost_map_elem_valid_2 (γ : GName) (k : K) (dq1: DFrac F) (dq2: DFrac F) (v1: V) (v2: V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF}
      internalCmraValid (dq1 • dq2) ∧ ⌜v1 = v2⌝ := by
  -- To use `iOwn_*` family of lemmas in the proof mode,
  -- the wrappers should be first unfolded (or be abbrevs, but definitions are probably better).
  unfold ghost_map_elem
  iintro H
  icases iOwn_op (E := hgm.elem) $$ H with H
  icases iOwn_cmraValid (E := hgm.elem) $$ H with %H
  obtain ⟨vdq, va⟩ := frag_op_valid_iff.mp H
  ipure_intro
  exact ⟨vdq, congrArg (·.car) (toAgree_op_valid_iff_eq.mp va)⟩

@[rocq_alias ghost_map_elem_agree]
theorem ghost_map_elem_agree (γ : GName) (k : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2) ⊢@{IProp GF} ⌜v1 = v2⌝ := by
  -- Notation difference with the Rocq version: if you have a hypothesis of shape `H : A ∧ B`,
  -- in Iris you can't derive both `H1 : A` and `H2 : B` at the same time,
  -- `⟨-, T⟩` destruction pattern allows to drop the first one
  -- `$` tries to iframe it immediately.
  iintro H
  icases ghost_map_elem_valid_2 $$ H with ⟨-, $⟩

-- Global Instance ghost_map_elem_combine_gives γ k v1 dq1 v2 dq2 :
--   CombineSepGives (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
--     ⌜✓ (dq1 • dq2) ∧ v1 = v2⌝ := sorry

#check frag_op_equiv
#check BI.equiv_iff
#check Agree.op
#check Agree.toAgree_op_valid_iff_equiv
#check View.frag_ne

@[rocq_alias ghost_map_elem_combine]
theorem ghost_map_elem_combine (γ : GName) (k : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
    (γ ↪◯MAP[k]{dq1} v1) ∗ (γ ↪◯MAP[k]{dq2} v2)
    ⊢@{IProp GF} (γ ↪◯MAP[k]{dq1 • dq2} v1) ∗ ⌜v1 = v2⌝ := by
  iintro H
  -- If the conclusion of icases is persistent/plain/pure, it is possible to
  -- get the result without losing the input hypothesis.
  icases ghost_map_elem_agree $$ H with #%heq
  iframe %heq; subst heq
  -- Here it is indeed a bit annoying to work with rewriting.
  -- Perhaps, there's a better way.
  unfold ghost_map_elem
  icases iOwn_op (E := hgm.elem) $$ H with H
  iapply iOwn_mono (E := hgm.elem) $$ H
  refine inc_of_inc_of_eqv ?_ frag_op_equiv
  refine inc_of_inc_of_eqv .rfl ?_
  refine OFE.NonExpansive.eqv ?_
  exact Agree.idemp.symm

-- Global Instance ghost_map_elem_combine_as (γ : GName) (k : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
--   CombineSepAs (γ ↪◯MAP[k]{dq1} v1) (γ ↪◯MAP[k]{dq2} v2)
--                 (γ ↪◯MAP[k]{dq1 • dq2} v1) | 60 := sorry

@[rocq_alias ghost_map_elem_frac_ne]
theorem ghost_map_elem_frac_ne γ (k1 : K) (k2 : K) (dq1 : DFrac F) (dq2 : DFrac F) (v1 : V) (v2 : V) :
   ¬ ✓ (dq1 • dq2) →
     (γ ↪◯MAP[k1]{dq1} v1) ∗ (γ ↪◯MAP[k2]{dq2} v2) ⊢@{IProp GF} ⌜k1 ≠ k2⌝ := by
  iintro %Hcontra H
  by_cases Heq : k1 = k2
  · subst Heq
    -- Same here, patterns can help a lot, while allowing to stay in the proof mode
    -- for longer, which in turn helps with implicit arguments.
    icases ghost_map_elem_valid_2 $$ H with ⟨%G, -⟩
    exact (Hcontra G).elim
  · ipure_intro; exact Heq

@[rocq_alias ghost_map_elem_ne]
theorem ghost_map_elem_ne γ (k1 : K) (k2 : K) (dq2 : DFrac F) (v1 : V) (v2 : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k1] v1) -∗ (γ ↪◯MAP[k2]{dq2} v2) -∗ ⌜k1 ≠ k2⌝ := sorry

--  Make an element read-only.
theorem ghost_map_elem_persist (γ : GName) (k : K) (dq : DFrac F) (v : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{dq} v) ==∗ (γ ↪◯MAP[k]{.discard} v) := sorry

--  Recover fractional ownership for read-only element.
theorem ghost_map_elem_unpersist (γ : GName) (k : K) (v : V) :
  ⊢@{IProp GF} (γ ↪◯MAP[k]{.discard} v) ==∗ ∃ q, (γ ↪◯MAP[k]{.own q} v) := sorry

-- * lemmas about [ghost_map_auth]

@[rocq_alias ghost_map_alloc_strong]
theorem ghost_map_alloc_strong (P : GName → Prop) (m : H V) :
  (hP : ∀ N, ∃ k, N ≤ k ∧ P k) →
  ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := sorry

@[rocq_alias ghost_map_alloc_strong_empty]
theorem ghost_map_alloc_strong_empty (P : GName → Prop) :
  (hP : ∀ N, ∃ k, N ≤ k ∧ P k) →
  ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MAP (∅ : H V)) := sorry

@[rocq_alias ghost_map_alloc]
theorem ghost_map_alloc (m : H V) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP m) ∗
      [∗map] k ↦ v ∈ m, γ ↪◯MAP[k] v := sorry

@[rocq_alias ghost_map_alloc_empty]
theorem ghost_map_alloc_empty :
  ⊢@{IProp GF} |==> ∃ γ, (γ ↪●MAP (∅ : H V)) := sorry

-- Global Instance ghost_map_auth_timeless γ dq m :
@[rocq_alias ghost_map_auth_timeless]
instance (m : H V): BI.Timeless (PROP := IProp GF) (γ ↪●MAP{dq} m) := sorry

@[rocq_alias ghost_map_persistent]
instance (m : H V): BI.Timeless (PROP := IProp GF) (γ ↪●MAP{.discard} m) := sorry

@[rocq_alias ghost_map_auth_fractional]
instance (m : H V): Fractional (PROP := IProp GF) (fun q => γ ↪●MAP{.own q} m) := sorry

-- Global Instance ghost_map_auth_as_fractional γ q m :
--   AsFractional (γ ↪●MAP{.own q} m) (λ q, γ ↪●MAP{.own q} m)%I q := sorry

@[rocq_alias ghost_map_auth_valid]
theorem ghost_map_auth_valid γ (dq : DFrac F) (m : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ ⌜✓ dq⌝ := sorry

@[rocq_alias ghost_map_auth_valid_2]
theorem ghost_map_auth_valid_2 γ (dq1 : DFrac F) (dq2 : DFrac F) (m1 : H V) (m2 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜✓ (dq1 • dq2) ∧ m1 = m2⌝ := sorry

@[rocq_alias ghost_map_auth_agree]
theorem ghost_map_auth_agree γ (dq1 : DFrac F) (dq2 : DFrac F) (m1 : H V) (m2 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq1} m1) -∗ (γ ↪●MAP{dq2} m2) -∗ ⌜m1 = m2⌝ := sorry

@[rocq_alias ghost_map_auth_persist]
theorem ghost_map_auth_persist γ dq (m : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) ==∗ γ ↪●MAP{.discard} m := sorry

@[rocq_alias ghost_map_auth_unpersist]
theorem ghost_map_auth_unpersist γ (m : H V) :
  ⊢@{IProp GF} (γ ↪●MAP{.discard} m) ==∗ ∃ q, γ ↪●MAP{.own q} m := sorry

-- * lemmas about the interaction of [ghost_map_auth] with the elements

@[rocq_alias ghost_map_lookup]
theorem ghost_map_lookup {γ dq} {m : H V} {k : K} {dq' v} :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗ (γ ↪◯MAP[k]{dq'} v) -∗ ⌜get? m k = some v⌝ := sorry

-- Global Instance ghost_map_lookup_combine_gives_1 {γ dq m k dq' v} :
--   CombineSepGives (γ ↪●MAP{dq} m) (γ ↪◯MAP[k]{dq'} v) ⌜get? m k = .some v⌝ := sorry

-- Global Instance ghost_map_lookup_combine_gives_2 {γ dq m k dq' v} :
--   CombineSepGives (γ ↪◯MAP[k]{dq} v) (γ ↪●MAP{dq'} m) ⌜get? m k = .some v⌝ := sorry

@[rocq_alias ghost_map_insert]
theorem ghost_map_insert {γ} {m: H V} (k: K) (v: V) :
  get? m k = None →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ γ ↪◯MAP[k] v := sorry

@[rocq_alias ghost_map_insert_persist]
theorem ghost_map_insert_persist {γ} {m: H V} (k: K) (v: V) :
  get? m k = None →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗ (γ ↪●MAP insert m k v) ∗ (γ ↪◯MAP[k]{.discard} v) := sorry

@[rocq_alias ghost_map_delete]
theorem ghost_map_delete {γ} {m: H V} (k: K) (v: V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ γ ↪●MAP delete m k := sorry

@[rocq_alias ghost_map_update]
theorem ghost_map_update {γ} {m: H V} (k: K) (v: V) (w: V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗ (γ ↪◯MAP[k] v) ==∗ (γ ↪●MAP insert m k w) ∗ γ ↪◯MAP[k] w := sorry

--  Big-op versions of above lemmas
theorem ghost_map_lookup_big {γ dq} {m : H V} {dq'} m0 :
  ⊢@{IProp GF} (γ ↪●MAP{dq} m) -∗
  ([∗map] k ↦ v ∈ m0, γ ↪◯MAP[k]{dq'} v) -∗
  ⌜m0 ⊆ m⌝ := sorry

@[rocq_alias ghost_map_insert_big]
theorem ghost_map_insert_big {γ m} (m' : H V) :
  (m' ##ₘ m) →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗
  (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k] v := sorry

@[rocq_alias ghost_map_insert_persist_big]
theorem ghost_map_insert_persist_big {γ m} (m' : H V) :
  m' ##ₘ m →
  ⊢@{IProp GF} (γ ↪●MAP m) ==∗
  (γ ↪●MAP (m' ∪ m)) ∗ [∗map] k ↦ v ∈ m', γ ↪◯MAP[k]{.discard} v := sorry

@[rocq_alias ghost_map_delete_big]
theorem ghost_map_delete_big {γ m} (m0 : H V) :
  ⊢@{IProp GF} (γ ↪●MAP m) -∗
  ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗
  (γ ↪●MAP (m \ m0)) := sorry

@[rocq_alias ghost_map_update_big]
theorem ghost_map_update_big {γ m} (m0 m1 : H V) :
  dom m0 = dom m1 →
  ⊢@{IProp GF} (γ ↪●MAP m) -∗
  ([∗map] k ↦v ∈ m0, γ ↪◯MAP[k] v) ==∗
  (γ ↪●MAP (m1 ∪ m)) ∗ [∗map] k ↦ v ∈ m1, γ ↪◯MAP[k] v := sorry

end lemmas
