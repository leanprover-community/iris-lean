/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
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

/-! An "invariant" location is a location that has some invariant about its value
attached to it, and that can never be deallocated explicitly by the program.  It
provides a persistent witness that will always allow reading the location,
guaranteeing that the value read will satisfy the invariant.

This is useful for data structures like RDCSS that need to read locations long
after their ownership has been passed back to the client, but do not care *what*
it is that they are reading in that case.  In that extreme case, the invariant may
just be `True`.

Since invariant locations cannot be deallocated, they only make sense when modeling
languages with garbage collection.  HeapLang can be used to model either language by
choosing whether or not to use the `Free` operation.  By using a separate assertion
`invPointsToOwn` for "invariant" locations, we can keep all the other proofs that do
not need it conservative.

Where Rocq uses the discrete-function OFE `V -d> PropO`, whose equivalence is
pointwise `Iff`, we use `DiscreteO (V → Prop)`, whose equivalence is Lean equality.
By `propext` and `funext` these agree, so the Rocq statements that conclude
`∀ w, I w ↔ I' w` conclude `I = I'` here. -/

@[rocq_alias inv_heapN]
def invHeapN : Namespace := nroot.@"inv_heap"

/-- The per-location entry: the exclusively-owned current value paired with the
agreed-upon invariant. -/
@[rocq_alias inv_heap_mapUR]
abbrev InvHeapMapUR (V : Type _) (H : Type _ → Type _) : Type _ :=
  H (Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop)))

section toInvHeap

variable {L V : Type _} {H : Type _ → Type _} [LawfulFiniteMap H L]

@[rocq_alias to_inv_heap]
def toInvHeap (h : H (V × (V → Prop))) : InvHeapMapUR V H :=
  Std.PartialMap.map
    (fun (p : V × (V → Prop)) => ((some (.excl ⟨p.1⟩), toAgree ⟨p.2⟩) :
      Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop)))) h

@[rocq_alias lookup_to_inv_heap_None]
theorem get?_toInvHeap_none {h : H (V × (V → Prop))} {l : L} (hl : get? h l = none) :
    get? (toInvHeap h) l = none := by
  rw [toInvHeap, get?_map, hl, Option.map_none]

@[rocq_alias lookup_to_inv_heap_Some]
theorem get?_toInvHeap_some {h : H (V × (V → Prop))} {l : L} {v : V} {I : V → Prop}
    (hl : get? h l = some (v, I)) :
    get? (toInvHeap h) l = some (some (.excl ⟨v⟩), toAgree ⟨I⟩) := by
  rw [toInvHeap, get?_map, hl, Option.map_some]

@[rocq_alias lookup_to_inv_heap_Some_2]
theorem get?_toInvHeap_some_2 {h : H (V × (V → Prop))} {l : L}
    {v' : Option (Excl (DiscreteO V))} {I' : Agree (DiscreteO (V → Prop))}
    (hl : get? (toInvHeap h) l = some (v', I')) :
    ∃ v I, v' = some (.excl ⟨v⟩) ∧ I' = toAgree ⟨I⟩ ∧ get? h l = some (v, I) := by
  rw [toInvHeap, get?_map] at hl
  rcases hh : get? h l with _ | ⟨v, I⟩ <;> rw [hh] at hl <;> simp_all

@[rocq_alias to_inv_heap_valid]
theorem toInvHeap_valid (h : H (V × (V → Prop))) : ✓ toInvHeap (H := H) h := by
  intro l
  rcases hh : get? h l with _ | ⟨v, I⟩
  · rw [get?_toInvHeap_none hh]; trivial
  · rw [get?_toInvHeap_some hh]; exact ⟨trivial, Agree.toAgree_valid⟩

@[rocq_alias to_inv_heap_singleton]
theorem toInvHeap_singleton [DecidableEq L] (l : L) (v : V) (I : V → Prop) :
    toInvHeap (H := H) {[l := (v, I)]} = {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]} := by
  rw [PartialMap.singleton, toInvHeap, map_insert, map_empty]
  rfl

@[rocq_alias to_inv_heap_insert]
theorem toInvHeap_insert [DecidableEq L] (l : L) (v : V) (I : V → Prop)
    (h : H (V × (V → Prop))) :
    toInvHeap (insert h l (v, I)) =
      insert (toInvHeap h) l (some (.excl ⟨v⟩), toAgree ⟨I⟩) :=
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

section definitions

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : outParam <| Type _ → Type _} [LawfulFiniteMap H L]
variable [InvGS_gen hlc GF] [genHeapGS L V GF H] [G : invHeapGS L V GF H]

open invHeapGS

@[rocq_alias inv_heap_inv_P]
def invHeapInvP : IProp GF := iprop(
  ∃ h : H (V × (V → Prop)),
    iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (● toInvHeap h) ∗
    [∗map] l ↦ p ∈ h, ⌜p.2 p.1⌝ ∗ l ↦ p.1)

@[rocq_alias inv_heap_inv]
def invHeapInv : IProp GF := inv invHeapN invHeapInvP

@[rocq_alias inv_pointsto_own]
def invPointsToOwn (l : L) (v : V) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName
    (◯ {[l := (some (.excl ⟨v⟩), toAgree ⟨I⟩)]})

@[rocq_alias inv_pointsto]
def invPointsTo (l : L) (I : V → Prop) : IProp GF :=
  iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName
    (◯ {[l := ((none : Option (Excl (DiscreteO V))), toAgree ⟨I⟩)]})

end definitions

notation:50 l:50 " ↦_" I:max v:50 => invPointsToOwn l v I
notation:50 l:50 " ↦_" I:max "□" => invPointsTo l I

section lemmas

variable {GF : BundledGFunctors} {L V : Type _}
variable {H : Type _ → Type _} [LawfulFiniteMap H L] [DecidableEq L]
variable [InvGS_gen hlc GF] [genHeapGS L V GF H] [G : invHeapGS L V GF H]

open invHeapGS

/-! ### Helpers -/

omit [DecidableEq L] [genHeapGS L V GF H] in
@[rocq_alias inv_pointsto_lookup_Some]
theorem invPointsTo_get?_some (l : L) (h : H (V × (V → Prop))) (I : V → Prop) :
    invPointsTo l I -∗
      iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (● toInvHeap h) -∗
      ⌜∃ v I', get? h l = some (v, I') ∧ I = I'⌝ := by
  unfold invPointsTo
  iintro Hl Hauth
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨hinc, -⟩ := Auth.auth_both_valid_discrete.mp Hvalid
  obtain ⟨⟨y₁, y₂⟩, hy, hyinc⟩ := Heap.singleton_inc_iff.mp hinc
  obtain ⟨v', I', rfl, rfl, hh⟩ := get?_toInvHeap_some_2 hy
  obtain ⟨⟨_, z₂⟩, hz⟩ := (Option.some_inc_some_iff.mp hyinc).elim
    (fun heq => ⟨(none, toAgree ⟨I⟩), heq.symm.trans (Prod.ext rfl Agree.idemp.symm)⟩) id
  exact ⟨v', I', hh, DiscreteO.eqv_inj (Agree.toAgree_included.mp ⟨z₂, congrArg Prod.snd hz⟩)⟩

omit [DecidableEq L] [genHeapGS L V GF H] in
@[rocq_alias inv_pointsto_own_lookup_Some]
theorem invPointsToOwn_get?_some (l : L) (v : V) (h : H (V × (V → Prop))) (I : V → Prop) :
    invPointsToOwn l v I -∗
      iOwn (E := invHeapPreS.invHeap (L := L)) invHeapName (● toInvHeap h) -∗
      ⌜∃ I', get? h l = some (v, I') ∧ I = I'⌝ := by
  unfold invPointsToOwn
  iintro Hl Hauth
  icombine Hauth Hl gives %Hvalid
  ipureintro
  obtain ⟨hinc, -⟩ := Auth.auth_both_valid_discrete.mp Hvalid
  obtain ⟨⟨y₁, y₂⟩, hy, hyinc⟩ := Heap.singleton_inc_iff.mp hinc
  obtain ⟨v', I', rfl, rfl, hh⟩ := get?_toInvHeap_some_2 hy
  obtain ⟨⟨z₁, z₂⟩, hz⟩ := (Option.some_inc_some_iff.mp hyinc).elim
    (fun heq => ⟨(none, toAgree ⟨I⟩), heq.symm.trans (Prod.ext rfl Agree.idemp.symm)⟩) id
  obtain rfl : v = v' := DiscreteO.eqv_inj (Excl.excl_included.mp ⟨z₁, congrArg Prod.fst hz⟩)
  exact ⟨I', hh, DiscreteO.eqv_inj (Agree.toAgree_included.mp ⟨z₂, congrArg Prod.snd hz⟩)⟩

/-! ### Typeclass instances -/

#rocq_ignore inv_pointsto_own_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `propext`; congruence is definitional."
#rocq_ignore inv_pointsto_proper
  "Pointwise `Iff` on `V → Prop` is Lean equality by `propext`; congruence is definitional."

/-- Rocq gets this from typeclass search on the unfolded body of `inv_heap_inv_P`; in Lean
instance search neither unfolds `invHeapInvP` nor applies `BI.exists_timeless`, so the
instance that `inv_acc_timeless` needs is spelled out here. -/
instance instTimelessInvHeapInvP : Timeless (invHeapInvP (L := L) (V := V) (H := H)) := by
  unfold invHeapInvP
  refine @BI.exists_timeless _ _ _ _ ?_
  intro h
  infer_instance

@[rocq_alias inv_heap_inv_persistent]
instance instPersistentInvHeapInv : Persistent (invHeapInv (L := L) (V := V) (H := H)) := by
  unfold invHeapInv
  infer_instance

/-- The `none` in the exclusive component is the unit of `Option`, but instance search
does not see through `UCMRA.unit`, so the `CoreId` witness is supplied by hand. -/
@[rocq_alias inv_pointsto_persistent]
instance instPersistentInvPointsTo (l : L) (I : V → Prop) :
    Persistent (PROP := IProp GF) (invPointsTo l I) := by
  have : CoreId (none : Option (Excl (DiscreteO V))) := unit_CoreId
  unfold invPointsTo
  infer_instance

@[rocq_alias inv_pointsto_timeless]
instance instTimelessInvPointsTo (l : L) (I : V → Prop) :
    Timeless (PROP := IProp GF) (invPointsTo l I) := by
  unfold invPointsTo
  infer_instance

@[rocq_alias inv_pointsto_own_timeless]
instance instTimelessInvPointsToOwn (l : L) (v : V) (I : V → Prop) :
    Timeless (PROP := IProp GF) (invPointsToOwn l v I) := by
  unfold invPointsToOwn
  infer_instance

/-! ### Public lemmas -/

@[rocq_alias make_inv_pointsto]
theorem make_invPointsTo {l : L} {v : V} {I : V → Prop} {E : CoPset}
    (hN : (↑invHeapN : CoPset) ⊆ E) (hI : I v) :
    invHeapInv (L := L) (V := V) (H := H) -∗ l ↦ v ={E}=∗ invPointsToOwn l v I := by
  unfold invHeapInv
  iintro #Hinv Hl
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  iunfold invHeapInvP at HP
  icases HP with ⟨%h, Hauth, HsepM⟩
  rcases hlk : get? h l with _ | ⟨v', I'⟩
  · imod iOwn_update (Auth.auth_update_alloc (Heap.alloc_singleton_local_update
      (x := ((some (.excl ⟨v⟩), toAgree ⟨I⟩) :
        Option (Excl (DiscreteO V)) × Agree (DiscreteO (V → Prop))))
      (get?_toInvHeap_none hlk) ⟨trivial, Agree.toAgree_valid⟩)) $$ Hauth with ⟨Hauth, Hfrag⟩
    ihave HP : invHeapInvP $$ [Hauth HsepM Hl]
    · unfold invHeapInvP
      iexists (insert h l (v, I))
      rw [toInvHeap_insert]
      iframe Hauth
      iapply (BigSepM.bigSepM_insert hlk)
      ieval (dsimp only)
      iframe Hl HsepM %hI
    imod Hclose $$ HP with -
    imodintro
    unfold invPointsToOwn
    iexact Hfrag
  · icases (BigSepM.bigSepM_lookup hlk) $$ HsepM with ⟨-, Hl'⟩
    icases pointsTo_ne $$ Hl Hl' with %hne
    exact absurd rfl hne

omit [DecidableEq L] [genHeapGS L V GF H] in
@[rocq_alias inv_pointsto_own_inv]
theorem invPointsToOwn_inv (l : L) (v : V) (I : V → Prop) :
    invPointsToOwn (GF := GF) l v I -∗ invPointsTo l I := by
  have hinc : ((none : Option (Excl (DiscreteO V))), toAgree (⟨I⟩ : DiscreteO (V → Prop))) ≼
      (some (.excl ⟨v⟩), toAgree ⟨I⟩) :=
    ⟨(some (.excl ⟨v⟩), toAgree ⟨I⟩), Prod.ext rfl Agree.idemp.symm⟩
  unfold invPointsToOwn invPointsTo
  iintro Hl
  iapply iOwn_mono (Auth.frag_inc_of_inc (Heap.singleton_inc_singleton_mono hinc)) $$ Hl

/-- An accessor to make use of `invPointsToOwn`.  This opens the invariant *before*
consuming `invPointsToOwn`, so that it can be used before opening an atomic update
that provides `invPointsToOwn`. -/
@[rocq_alias inv_pointsto_own_acc_strong]
theorem invPointsToOwn_acc_strong {E : CoPset} (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv (L := L) (V := V) (H := H) ={E, E \ ↑invHeapN}=∗
      ∀ (l : L) (v : V) (I : V → Prop), invPointsToOwn l v I -∗
        (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w⌝ -∗ l ↦ w ==∗
          invPointsToOwn l w I ∗ |={E \ ↑invHeapN, E}=> True)) := by
  unfold invHeapInv
  iintro #Hinv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  iintro %l %v %I Hl_inv
  iunfold invHeapInvP at HP
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsToOwn_get?_some l v h I $$ Hl_inv Hauth with %⟨I', hh, rfl⟩
  unfold invPointsToOwn
  icases (BigSepM.bigSepM_delete hh) $$ HsepM with ⟨⟨%hIv, Hl⟩, HsepM⟩
  iframe Hl %hIv
  iintro %w %hIw Hl
  imod iOwn_update_op (Auth.auth_update (Heap.singleton_local_update
      (get?_toInvHeap_some hh)
      (LocalUpdate.prod_1 _ _
        (LocalUpdate.option (LocalUpdate.exclusive (x' := Excl.excl ⟨w⟩) trivial)))))
    $$ [$Hauth $Hl_inv] with ⟨Hauth, Hfrag⟩
  ihave HP : invHeapInvP $$ [Hauth HsepM Hl]
  · unfold invHeapInvP
    iexists (insert h l (w, I))
    rw [toInvHeap_insert]
    iframe Hauth
    iapply BigSepM.bigSepM_insert_delete
    ieval (dsimp only)
    iframe Hl HsepM %hIw
  imodintro
  iframe Hfrag
  iapply Hclose $$ HP

/-- A more standard accessor, derived from `invPointsToOwn_acc_strong`. -/
@[rocq_alias inv_pointsto_own_acc]
theorem invPointsToOwn_acc {E : CoPset} {l : L} {v : V} {I : V → Prop}
    (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv (L := L) (V := V) (H := H) -∗ invPointsToOwn l v I ={E, E \ ↑invHeapN}=∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w⌝ -∗ l ↦ w ={E \ ↑invHeapN, E}=∗ invPointsToOwn l w I)) := by
  iintro #Hinv Hl
  imod invPointsToOwn_acc_strong hN $$ Hinv with Hacc
  icases Hacc $$ %l %v %I Hl with ⟨%hIv, Hl, Hclose⟩
  imodintro
  iframe Hl %hIv
  iintro %w %hIw Hl
  imod Hclose $$ %w [//] Hl with ⟨Hfrag, Hcl⟩
  imod Hcl with -
  imodintro
  iexact Hfrag

omit [DecidableEq L] in
@[rocq_alias inv_pointsto_acc]
theorem invPointsTo_acc {E : CoPset} {l : L} {I : V → Prop}
    (hN : (↑invHeapN : CoPset) ⊆ E) :
    invHeapInv (L := L) (V := V) (H := H) -∗ invPointsTo l I ={E, E \ ↑invHeapN}=∗
      ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E \ ↑invHeapN, E}=∗ ⌜True⌝) := by
  unfold invHeapInv
  iintro #Hinv Hl_inv
  imod inv_acc_timeless hN $$ Hinv with ⟨HP, Hclose⟩
  imodintro
  iunfold invHeapInvP at HP
  icases HP with ⟨%h, Hauth, HsepM⟩
  icases invPointsTo_get?_some l h I $$ Hl_inv Hauth with %⟨v, I', hh, rfl⟩
  icases (BigSepM.bigSepM_lookup_acc hh) $$ HsepM with ⟨⟨%hIv, Hl⟩, HsepM⟩
  iexists v
  iframe Hl %hIv
  iintro Hl
  ihave HP : invHeapInvP $$ [Hauth HsepM Hl]
  · unfold invHeapInvP
    iexists h
    iframe Hauth
    iapply HsepM
    ieval (dsimp only)
    iframe Hl %hIv
  imod Hclose $$ HP with -
  imodintro
  itrivial

end lemmas

@[rocq_alias inv_heap_init]
theorem invHeap_init (L V : Type _) {GF : BundledGFunctors} {H : Type _ → Type _}
    [LawfulFiniteMap H L] [DecidableEq L] [InvGS_gen hlc GF] [genHeapGS L V GF H]
    [invHeapPreS L V GF H] (E : CoPset) :
    ⊢ |==> ∃ _ : invHeapGS L V GF H, |={E}=> invHeapInv (L := L) (V := V) (H := H) := by
  imod (iOwn_alloc (E := invHeapPreS.invHeap (L := L))
    (● toInvHeap (∅ : H (V × (V → Prop)))) (Auth.auth_valid.mpr (toInvHeap_valid ∅)))
    with ⟨%γ, Hauth⟩
  letI G : invHeapGS L V GF H := ⟨γ⟩
  imodintro
  iexists G
  unfold invHeapInv
  ihave HP : invHeapInvP $$ [Hauth]
  · unfold invHeapInvP
    iexists (∅ : H (V × (V → Prop)))
    iframe Hauth
    iapply BigSepM.bigSepM_empty
    itrivial
  iapply inv_alloc invHeapN E invHeapInvP $$ [HP]
  inext
  iexact HP

end Iris
