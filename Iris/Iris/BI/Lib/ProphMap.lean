/-
Copyright (c) Markus de Medeiros 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Instances.Lib.GhostMap
public import Iris.Std.GenSets

@[expose] public section

namespace Iris

open Std PartialMap LawfulPartialMap LawfulSet Iris.Algebra CMRA BI ProofMode

/-! This file defines prophecy-variable bookkeeping.
A prophecy map associates to each (used) prophecy `p : P` the list of values it
will be resolved to.  The list of resolutions still to come is recorded as a
`proph_val_list`, a list of `(prophecy, value)` pairs.  The state interpretation
`proph_map_interp` keeps the ghost map in sync with that list. -/

/-- The list of `(prophecy, value)` resolutions, as recorded by the operational
semantics. -/
@[rocq_alias proph_val_list]
abbrev ProphValList (P V : Type _) := List (P × V)

@[rocq_alias proph_mapGpreS]
class prophMapPreS (P V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)
    [LawfulFiniteMap H P] where
  inG : GhostMapG GF P (List V) H

attribute [reducible, instance] prophMapPreS.inG

@[rocq_alias proph_mapGS]
class prophMapGS (P V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [LawfulFiniteMap H P]
    extends prophMapPreS P V GF H where
  prophMapName : GName

#rocq_ignore «proph_mapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_proph_mapGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

section definitions

variable {GF : BundledGFunctors} {P V : Type _}
variable {H : outParam <| Type _ → Type _} [LawfulFiniteMap H P]
variable {S : Type _} [LawfulSet S P]

/-- The list of resolutions for `p` in `pvs`. -/
@[rocq_alias proph_list_resolves]
def prophListResolves [DecidableEq P] (pvs : ProphValList P V) (p : P) : List V :=
  match pvs with
  | [] => []
  | (q, v) :: pvs => if p = q then v :: prophListResolves pvs p else prophListResolves pvs p

/-- `R` resolves consistently with `pvs`: every recorded resolution list agrees
with the one computed from `pvs`. -/
@[rocq_alias proph_resolves_in_list]
def prophResolvesInList [DecidableEq P] (R : H (List V)) (pvs : ProphValList P V) : Prop :=
  ∀ p vs, get? R p = some vs → vs = prophListResolves pvs p

variable [G : prophMapGS P V GF H]

/-- State interpretation for the prophecy map.  Owns the ghost map `R` of
recorded resolutions, asserting that it resolves consistently with `pvs` and
that its domain is contained in the set `ps` of used prophecies. -/
@[rocq_alias proph_map_interp]
def prophMapInterp [DecidableEq P] (pvs : ProphValList P V) (ps : S) : IProp GF := iprop%
  ∃ R : H (List V), ⌜prophResolvesInList R pvs ∧ (∀ p, dom R p → p ∈ ps)⌝ ∗
    (prophMapGS.prophMapName ↪●MAP R)

/-- Ownership of the prophecy `p`, asserting that it will be resolved to the
list of values `vs`. -/
@[rocq_alias proph]
def proph (p : P) (vs : List V) : IProp GF := prophMapGS.prophMapName ↪◯MAP[p] vs

#rocq_ignore proph_def "Not needed"
#rocq_ignore proph_aux "Not needed"
#rocq_ignore proph_unseal "Not needed"

end definitions

section listResolves

variable {P V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H P] [DecidableEq P]

-- NOTE: p ∉ dom R in the Rocq version is unused.
@[rocq_alias resolves_insert]
theorem resolves_insert {pvs : ProphValList P V} {p : P} {R : H (List V)}
    (Hinlist : prophResolvesInList R pvs) :
    prophResolvesInList (insert R p (prophListResolves pvs p)) pvs := by
  intro q vs HEq
  by_cases h : p = q
  · subst h
    rw [get?_insert_eq rfl] at HEq
    exact (Option.some_inj.mp HEq).symm
  · rw [get?_insert_ne h] at HEq
    exact Hinlist q vs HEq

end listResolves

namespace ProphMap

@[rocq_alias proph_map_init]
theorem init {GF : BundledGFunctors} {P V : Type _}
    {H : Type _ → Type _} [LawfulFiniteMap H P] [DecidableEq P] {S : Type _} [LawfulSet S P]
    [prophMapPreS P V GF H] (pvs : ProphValList P V) (ps : S) :
    ⊢ |==> ∃ G : prophMapGS P V GF H, prophMapInterp (G := G) pvs ps := by
  imod (ghost_map_alloc_empty (K := P) (V := List V) (H := H)) with ⟨%γ, Hh⟩
  imodintro
  iexists (⟨γ⟩ : prophMapGS P V GF H)
  unfold prophMapInterp
  iexists (∅ : H (List V))
  iframe
  ipureintro
  refine ⟨fun p vs h => ?_, fun p h => ?_⟩
  · rw [get?_empty] at h
    cases h
  · simp [dom, get?_empty] at h

end ProphMap

section lemmas

variable {GF : BundledGFunctors} {P V : Type _}
variable {H : outParam <| Type _ → Type _} [LawfulFiniteMap H P]
variable {S : Type _} [LawfulSet S P]
variable [prophMapGS P V GF H]

/-! ### General properties of `proph` -/

@[rocq_alias proph_timeless]
instance instTimelessProph (p : P) (vs : List V) : Timeless (PROP := IProp GF) (proph p vs) :=
  inferInstanceAs (Timeless (prophMapGS.prophMapName ↪◯MAP[p] vs))

@[rocq_alias proph_exclusive]
theorem proph_exclusive (p : P) (vs1 vs2 : List V) :
    proph p vs1 -∗ proph p vs2 -∗ False := by
  unfold proph
  iintro Hp1 Hp2
  icases ghost_map_elem_ne $$ Hp1 Hp2 with %hne
  exact (hne rfl).elim

namespace ProphMap

@[rocq_alias proph_map_new_proph]
theorem new_proph [DecidableEq P] (p : P) (ps : S) (pvs : ProphValList P V) (Hp : p ∉ ps) :
    prophMapInterp pvs ps
      ==∗ (prophMapInterp pvs ({p} ∪ ps) ∗ proph p (prophListResolves pvs p)) := by
  unfold prophMapInterp proph
  iintro ⟨%R, ⟨%Hres, %Hdom⟩, Hauth⟩
  have Hfresh : get? R p = none := by
    rcases h : get? R p with _ | _
    · rfl
    · exact (Hp (Hdom p (by simp [dom, h]))).elim
  imod ghost_map_insert p (prophListResolves pvs p) Hfresh $$ Hauth with ⟨Hauth, Hfrag⟩
  imodintro
  iframe Hfrag
  iexists (insert R p (prophListResolves pvs p))
  iframe Hauth
  ipureintro
  refine ⟨resolves_insert Hres, fun q hq => ?_⟩
  rcases dom_insert_iff.mp hq with rfl | hq
  · exact mem_union.mpr (.inl (mem_singleton.mpr rfl))
  · exact mem_union.mpr (.inr (Hdom q hq))

@[rocq_alias proph_map_resolve_proph]
theorem resolve_proph [DecidableEq P] (p : P) (v : V) (pvs : ProphValList P V) (ps : S)
    (vs : List V) :
    prophMapInterp ((p, v) :: pvs) ps ∗ proph p vs
      ==∗ (∃ vs', ⌜vs = v :: vs'⌝ ∗ prophMapInterp pvs ps ∗ proph p vs') := by
  unfold prophMapInterp proph
  iintro ⟨⟨%R, ⟨%Hres, %Hdom⟩, Hauth⟩, Hp⟩
  icombine Hauth Hp gives %HR
  have Hvs : vs = v :: prophListResolves pvs p := by
    rw [Hres p vs HR, prophListResolves, if_pos rfl]
  subst Hvs
  imod ghost_map_update (prophListResolves pvs p) $$ Hauth Hp with ⟨Hauth, Hfrag⟩
  imodintro
  iexists (prophListResolves pvs p)
  iframe Hfrag; isplit
  · itrivial
  iexists (insert R p (prophListResolves pvs p))
  iframe Hauth
  ipureintro
  refine ⟨fun q ws HEq => ?_, fun q hq => ?_⟩
  · by_cases h : p = q
    · subst h
      rw [get?_insert_eq rfl] at HEq
      exact (Option.some_inj.mp HEq).symm
    · rw [get?_insert_ne h] at HEq
      rw [Hres q ws HEq, prophListResolves, if_neg (Ne.symm h)]
  · have hp : p ∈ ps := Hdom p (by simp [dom, HR])
    rcases dom_insert_iff.mp hq with rfl | hq
    · exact hp
    · exact Hdom q hq

@[rocq_alias proph_map_agree]
theorem agree [DecidableEq P] (pvs : ProphValList P V) (ps : S) (p : P) (vs : List V) :
    prophMapInterp pvs ps ∗ proph p vs
      -∗ ⌜p ∈ ps ∧ vs = prophListResolves pvs p⌝ := by
  unfold prophMapInterp proph
  iintro ⟨⟨%R, ⟨%Hres, %Hdom⟩, Hauth⟩, Hp⟩
  icombine Hauth Hp gives %Hlookup
  ipureintro
  exact ⟨Hdom p (by simp [dom, Hlookup]), Hres p vs Hlookup⟩

end ProphMap

end lemmas

end Iris

end
