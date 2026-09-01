/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Excl
public import Iris.BI.Lib.GenHeap
public import Iris.Instances.Lib.Invariants

@[expose] public section

namespace Iris

open Std Std.PartialMap Std.LawfulPartialMap Iris.Algebra CMRA BI ProofMode
open Agree Auth BigSepM Excl Heap

@[rocq_alias inv_heapN]
def invHeapN : Namespace := nroot.@"inv_heap"

@[rocq_alias inv_heap_mapUR]
abbrev InvHeapMapUR (V : Type _) (H : Type _ → Type _) : Type _ :=
  H (Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop)))

section toInvHeap

variable {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]

@[rocq_alias to_inv_heap]
def toInvHeap (h : H (V × (V → Prop))) : InvHeapMapUR V H :=
  map (fun p => (some (.excl ⟨p.1⟩), toAgree ⟨p.2⟩)) h

@[rocq_alias lookup_to_inv_heap_None]
theorem get?_toInvHeap_none {h : H (V × (V → Prop))} {l : L} (hl : get? h l = none) :
    get? (toInvHeap h) l = none := by
  rw [toInvHeap, get?_map, hl, Option.map_none]

@[rocq_alias lookup_to_inv_heap_Some]
theorem get?_heap_some_toInvHeap {h : H (V × (V → Prop))} {l : L} {v : V} {I : V → Prop}
    (hl : get? h l = some (v, I)) :
    get? (toInvHeap h) l = some (some (.excl ⟨v⟩), toAgree ⟨I⟩) := by
  rw [toInvHeap, get?_map, hl, Option.map_some]

@[rocq_alias lookup_to_inv_heap_Some_2]
theorem get?_toInvHeap_some {h : H (V × (V → Prop))} {l : L}
    {v' : Option (Excl (DiscreteO V))} {I' : Agree (DiscreteO (V → Prop))}
    (hl : get? (toInvHeap h) l = some (v', I')) :
    ∃ v I, v' = some (.excl ⟨v⟩) ∧ I' = toAgree ⟨I⟩ ∧ get? h l = some (v, I) := by
  rw [toInvHeap, get?_map] at hl
  rcases hh : get? h l with _ | ⟨v, I⟩ <;> rw [hh] at hl <;> simp_all

/-- The invariant-heap store is classical: its order is its extension inclusion. -/
private theorem invHeap_incExtN_of_incN {n} {x y : InvHeapMapUR V H} (h : x ≼{n} y) :
    x ≼ₑ{n} y :=
  Heap.lookup_incN.mpr fun i =>
    Option.incExtN_of_incN
      (Prod.incExtN_of_incN (Option.incExtN_of_incN fun h => h) fun h => h) (h i)

private theorem singleton_inc_toInvHeap {h : H (V × (V → Prop))} {l : L} {I : V → Prop}
    {mv : Option (Excl (DiscreteO V))}
    (hinc : ({[l := (mv, toAgree ⟨I⟩)]} : InvHeapMapUR V H) ≼ toInvHeap h) :
    ∃ v, get? h l = some (v, I) ∧ mv ≼ some (excl ⟨v⟩) := by
  replace hinc := Heap.lookup_inc.mpr fun i =>
    Option.incExt_of_inc
      (Prod.incExt_of_inc (Option.incExt_of_inc fun h => h) fun h => h) (hinc i)
  obtain ⟨⟨_, _⟩, hy, hinc⟩ := singleton_incExt_iff.mp hinc
  obtain ⟨v, I', rfl, rfl, hh⟩ := get?_toInvHeap_some hy
  obtain ⟨hv, hI⟩ := Prod.incExt_def.mp (Option.some_incExt_some_iff_is_total.mp hinc)
  cases DiscreteO.eqv_inj (toAgree_included.mp hI)
  exact ⟨v, hh, CMRA.inc_of_incExt hv⟩

@[rocq_alias to_inv_heap_valid]
theorem toInvHeap_valid (h : H (V × (V → Prop))) : ✓ toInvHeap h := fun l => by
  rcases hh : get? h l with _ | ⟨v, I⟩
  · rw [get?_toInvHeap_none hh]; trivial
  · exact get?_heap_some_toInvHeap hh ▸ ⟨trivial, toAgree_valid⟩

@[rocq_alias to_inv_heap_singleton]
theorem toInvHeap_singleton [DecidableEq L] (l : L) (v : V) (I : V → Prop) :
    toInvHeap (H := H) {[l := (v, I)]} = {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]} := by
  rw [PartialMap.singleton, toInvHeap, map_insert, map_empty]; rfl

@[rocq_alias to_inv_heap_insert]
theorem toInvHeap_insert [DecidableEq L] (l : L) (v : V) (I : V → Prop) (h : H (V × (V → Prop))) :
    toInvHeap (insert h l (v, I)) = insert (toInvHeap h) l (some (.excl ⟨v⟩), toAgree ⟨I⟩) :=
  map_insert

end toInvHeap

@[rocq_alias inv_heapGpreS]
class invHeapPreS (L V : Type _) (GF : BundledGFunctors) (H : outParam <| Type _ → Type _)
    [LawfulFiniteMap H L] where
  invHeap : ElemG GF (constOF (Auth (InvHeapMapUR V H)))

attribute [reducible, instance] invHeapPreS.invHeap

@[rocq_alias inv_heapGS]
class invHeapGS (L V : outParam <| Type _) (GF : outParam <| BundledGFunctors)
    (H : outParam <| Type _ → Type _) [LawfulFiniteMap H L]
    extends invHeapPreS L V GF H where
  invHeapName : GName

#rocq_ignore «inv_heapΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_inv_heapGpreS» "Subsumed by BundledGFunctors typeclass synthesis"

open invHeapGS

section definitions

variable {GF : BundledGFunctors} {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
variable [InvGS_gen hlc GF] [genHeapGS L V GF H] [invHeapGS L V GF H]

@[reducible, rocq_alias inv_heap_inv_P]
def invHeapInvP : IProp GF := iprop%
  ∃ h : H (V × (V → Prop)),
    iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) ∗
    [∗map] l ↦ p ∈ h, ⌜p.2 p.1⌝ ∗ l ↦ p.1

@[rocq_alias inv_heap_inv]
def invHeapInv : IProp GF := inv invHeapN invHeapInvP

@[rocq_alias inv_pointsto_own]
def invPointsToOwn (l : L) (v : V) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (◯ {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]})

@[rocq_alias inv_pointsto]
def invPointsTo (l : L) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (◯ {[l := (none, toAgree ⟨I⟩)]})

end definitions

notation:50 l:50 " ↦_" I:max v:50 => invPointsToOwn l v I
notation:50 l:50 " ↦_" I:max "□" => invPointsTo l I

section lemmas

variable {GF : BundledGFunctors} {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]
variable [InvGS_gen hlc GF] [invHeapGS L V GF H]

@[rocq_alias inv_pointsto_lookup_Some]
theorem invPointsTo_get?_some (l : L) (h : H (V × (V → Prop))) (I : V → Prop) :
    l ↦_I □ -∗ iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) -∗
      ⌜∃ v I', get? h l = some (v, I') ∧ I = I'⌝ := by
  iintro Hl Hauth
  unfold invPointsTo
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨v, hh, -⟩ := singleton_inc_toInvHeap (auth_both_valid_discrete.mp Hvalid).1
  exact ⟨v, I, hh, rfl⟩

@[rocq_alias inv_pointsto_own_lookup_Some]
theorem invPointsToOwn_get?_some (l : L) (v : V) (h : H (V × (V → Prop))) (I : V → Prop) :
    l ↦_I v -∗ iOwn (E := invHeapPreS.invHeap) invHeapName (● toInvHeap h) -∗
      ⌜∃ I', get? h l = some (v, I') ∧ I = I'⌝ := by
  iintro Hl Hauth
  unfold invPointsToOwn
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨v', hh, hv⟩ := singleton_inc_toInvHeap (auth_both_valid_discrete.mp Hvalid).1
  cases DiscreteO.eqv_inj (excl_included.mp hv)
  exact ⟨I, hh, rfl⟩

#rocq_ignore inv_pointsto_own_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `funext`/`propext`; congruence is `congrArg`."
#rocq_ignore inv_pointsto_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `funext`/`propext`; congruence is `congrArg`."

@[rocq_alias inv_pointsto_persistent]
instance instPersistentInvPointsTo (l : L) (I : V → Prop) : Persistent (l ↦_I □) := by
  haveI : CoreId (none : Option (Excl (DiscreteO V))) := unit_CoreId
  unfold invPointsTo
  infer_instance

@[rocq_alias inv_pointsto_timeless]
instance instTimelessInvPointsTo (l : L) (I : V → Prop) : Timeless (l ↦_I □) := by
  unfold invPointsTo
  infer_instance

@[rocq_alias inv_pointsto_own_timeless]
instance instTimelessInvPointsToOwn (l : L) (I : V → Prop) v : Timeless (l ↦_I v) := by
  unfold invPointsToOwn
  infer_instance

@[rocq_alias inv_heap_inv_persistent]
instance instPersistentInvHeapInv [genHeapGS L V GF H] :
    Persistent invHeapInv := by
  unfold invHeapInv
  infer_instance

@[rocq_alias inv_pointsto_own_inv]
theorem invPointsToOwn_inv (l : L) (v : V) (I : V → Prop) :
    l ↦_I v -∗ l ↦_I □ := by
  iintro Hl
  unfold invPointsToOwn invPointsTo
  iapply iOwn_mono $$ Hl
  refine CMRA.inc_of_incExt (frag_incExt_of_incExt (singleton_incExt_singleton_mono ?_))
  exact ⟨(some (.excl ⟨v⟩), toAgree ⟨I⟩), Prod.ext rfl Agree.idemp.symm⟩

variable [genHeapGS L V GF H]

local instance instTimelessInvHeapInvP : Timeless invHeapInvP :=
  @exists_timeless _ _ _ _ fun _ => inferInstance

@[rocq_alias inv_pointsto_acc]
theorem invPointsTo_acc {E : CoPset} {l : L} {I : V → Prop} (hN : ↑invHeapN ⊆ E) :
    invHeapInv -∗ l ↦_I □ ={E, E \ ↑invHeapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E \ ↑invHeapN, E}=∗ ⌜True⌝) := by
  unfold invHeapInv
  iintro #Hinv Hl_inv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsTo_get?_some l h I $$ Hl_inv Hauth with %⟨v, I', hh, rfl⟩
  icases bigSepM_lookup_acc hh $$ HsepM with ⟨⟨%hIv, Hl⟩, HsepM⟩
  iexists v
  iframe Hl %hIv
  iintro Hl
  imod Hclose $$ [Hauth HsepM Hl] with -
  · iexists h
    iframe Hauth
    iapply HsepM
    iframe Hl %hIv
  · imodintro; itrivial

variable [DecidableEq L]

@[rocq_alias make_inv_pointsto]
theorem make_invPointsTo {l : L} {v : V} {I : V → Prop} {E : CoPset} (hN : ↑invHeapN ⊆ E)
    (hI : I v) : invHeapInv -∗ l ↦ v ={E}=∗ l ↦_I v := by
  unfold invHeapInv
  iintro #Hinv Hl
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  icases HP with ⟨%h, Hauth, HsepM⟩
  rcases hlk : get? h l with _ | ⟨v', I'⟩
  · imod iOwn_update (auth_update_alloc_of_localUpdate invHeap_incExtN_of_incN (alloc_singleton_local_update
      (x := ((some (.excl ⟨v⟩), toAgree ⟨I⟩) :
        Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop))))
      (get?_toInvHeap_none hlk) ⟨trivial, toAgree_valid⟩)) $$ Hauth with ⟨Hauth, Hfrag⟩
    imod Hclose $$ [Hauth HsepM Hl] with -
    · iexists insert h l (v, I)
      rw [toInvHeap_insert]
      iframe Hauth
      iapply bigSepM_insert hlk
      iframe Hl HsepM %hI
    · imodintro
      unfold invPointsToOwn
      iexact Hfrag
  · icases bigSepM_lookup hlk $$ HsepM with ⟨-, Hl'⟩
    icases pointsTo_ne $$ Hl Hl' with %hne
    exact absurd rfl hne

@[rocq_alias inv_pointsto_own_acc_strong]
theorem invPointsToOwn_acc_strong {E : CoPset} (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv ={E, E \ ↑invHeapN}=∗ ∀ (l : L) (v : V) (I : V → Prop), l ↦_I v -∗
      ⌜I v⌝ ∗ l ↦ v ∗ ∀ w, ⌜I w⌝ -∗ l ↦ w ==∗ l ↦_I w ∗ |={E \ ↑invHeapN, E}=> True := by
  unfold invHeapInv
  iintro #Hinv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  iintro %l %v %I Hl_inv
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsToOwn_get?_some $$ Hl_inv Hauth with %⟨I', hh, rfl⟩
  iunfold invPointsToOwn at Hl_inv
  icases bigSepM_delete hh $$ HsepM with ⟨⟨$, $⟩, HsepM⟩
  iintro %w %hIw Hl
  imod iOwn_update_op (auth_update_of_localUpdate invHeap_incExtN_of_incN (singleton_local_update
      (get?_heap_some_toInvHeap hh)
      (LocalUpdate.prod_1 _ _ (LocalUpdate.option (LocalUpdate.exclusive (x' := excl ⟨w⟩) trivial)))))
    $$ [$Hauth $Hl_inv] with ⟨Hauth, Hfrag⟩
  iunfold invPointsToOwn
  iframe Hfrag
  iapply Hclose $$ [Hauth HsepM Hl]
  iexists insert h l (w, I)
  rw [toInvHeap_insert]
  iframe Hauth
  iapply bigSepM_insert_delete
  iframe Hl HsepM %hIw

@[rocq_alias inv_pointsto_own_acc]
theorem invPointsToOwn_acc {E : CoPset} {l : L} {v : V} {I : V → Prop} (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv -∗ l ↦_I v ={E, E \ ↑invHeapN}=∗
      ⌜I v⌝ ∗ l ↦ v ∗ ∀ w, ⌜I w⌝ -∗ l ↦ w ={E \ ↑invHeapN, E}=∗ l ↦_I w := by
  iintro #Hinv Hl
  imod invPointsToOwn_acc_strong hN $$ Hinv with Hacc
  icases Hacc $$ %l %v %I Hl with ⟨$, $, Hclose⟩
  iintro !> %w %hIw Hl
  imod Hclose $$ %w [//] Hl with ⟨Hfrag, >-⟩
  iexact Hfrag

end lemmas

@[rocq_alias inv_heap_init]
theorem invHeap_init (L V : Type _) {GF : BundledGFunctors} {H : Type _ → Type _}
    [LawfulFiniteMap H L] [DecidableEq L] [InvGS_gen hlc GF] [genHeapGS L V GF H]
    [invHeapPreS L V GF H] (E : CoPset) :
    ⊢ |==> ∃ _ : invHeapGS L V GF H, |={E}=> invHeapInv := by
  imod (iOwn_alloc (E := invHeapPreS.invHeap)
    (● toInvHeap (∅ : H (V × (V → Prop)))) (auth_valid.mpr (toInvHeap_valid ∅)))
    with ⟨%γ, Hauth⟩
  letI G : invHeapGS L V GF H := ⟨γ⟩
  imodintro
  iexists G
  unfold invHeapInv
  iapply inv_alloc invHeapN E invHeapInvP $$ [Hauth]
  inext
  iexists ∅
  iframe Hauth
  iapply bigSepM_empty; itrivial

end Iris
