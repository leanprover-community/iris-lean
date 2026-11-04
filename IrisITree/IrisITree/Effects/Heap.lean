/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang, Michael Sammler
-/

module

public import IrisITree.Effects.State
public import IrisITree.Effects.Demonic
public import IrisITree.Effects.Fail
public import ITree.Effects.Heap
public import Iris.BI.BigOp.BigSepList
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.Lib.Invariants
public import Iris.Std.HeapInstances

public section

-- A heap, represented as a [gmap] of [option val]s, with [None] representing deallocated locations.

namespace IrisITree

open Iris BI ITree Effects

/--
  `Loc` and `Val` must live in `Type`: `GhostMapG` needs its map type to land in `Type`
  (upstream `constOF (B : Type)`), and `heap_inv` needs `InvGS_gen hlc GF`, which fixes
  `GF : BundledGFunctors.{0, 0, 0}`.
-/
class heapHGpreS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_ghost_varG : GhostMapG GF Loc (Option Val) (Std.ExtTreeMap Loc · compare)

attribute [reducible, instance] heapHGpreS.heapH_ghost_varG

class heapHGS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_inG : heapHGpreS GF Loc Val
  heapH_heap_name : GName
  heapH_inv_name_postfix : String

attribute [reducible, instance] heapHGS.heapH_inG

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
variable [G : heapHGS GF Loc Val]
local notation "γheap" => heapHGS.heapH_heap_name GF Loc Val

def heapH_inv_name : Namespace :=
  (nroot.@"heapH").@G.heapH_inv_name_postfix

def pointsto (l : Loc) (v : Option Val) (dq : DFrac) : IProp GF :=
  ghost_map_elem (G.heapH_heap_name) dq l v

notation:50 l:50 " ↦? " v:50 => pointsto l v (DFrac.own 1)
notation:50 l:50 " ↦{" dq "}? " v:50 => pointsto l v dq
notation:50 l:50 " ↦ " v:50 => pointsto l (some v) (DFrac.own 1)
notation:50 l:50 " ↦{" dq "} " v:50 => pointsto l (some v) dq

section handler

-- Half of the authoritative view of the current heap into an invariant
-- so that we can know that someone else won't change it while we have control
def heap_inv : IProp GF :=
  inv (heapH_inv_name (G := G)) iprop(
    ∃ σ, ghost_map_auth (K := Loc) (V := Option Val)
      G.heapH_heap_name (DFrac.own <| Qp.half 1) σ
  )

instance heap_inv_persistent : Persistent (heap_inv (G := G)) := by
  unfold heap_inv
  infer_instance

def stateInterp_heap (σ : heapE.T Loc Val) : IProp GF := iprop(
  ghost_map_auth (K := Loc) (V := Option Val)
    G.heapH_heap_name (DFrac.own <| Qp.half 1) σ
  ∧ heap_inv (G := G)
)

def heapH : IHandler (IProp GF) (heapE Loc Val) :=
  stateH stateInterp_heap

end handler

section initialization

variable [Gpre : heapHGpreS GF Loc Val] [DecidableEq Loc]

/-- The heap's map type as a functor in the value type. Typing a heap as
  `heapF Loc (Option Val)` lets `[∗map]` infer the map type (like upstream's `HeapF`). -/
abbrev heapF (Loc : Type) [Ord Loc] : Type → Type := (Std.ExtTreeMap Loc · compare)

omit G in
theorem heapH_init (σ : heapF Loc (Option Val)) :
    ⊢ |={∅}=> ∃ G : heapHGS GF Loc Val,
      heap_inv (G := G) ∗
      stateInterp_heap σ ∗
      [∗map] k ↦ v ∈ σ, k ↦? v := by
  icases (ghost_map_alloc (K := Loc) (V := Option Val) σ) with Hgmap
  imod Hgmap; icases Hgmap with ⟨%γ, ⟨⟨Hauth, Hauth'⟩, Hfrag⟩⟩
  imod (inv_alloc ((nroot.@"heapH").@"") ∅
    (∃ σ, ghost_map_auth (K := Loc) (V := Option Val) γ (.own <| .half 1) σ)) $$ [Hauth] with #Hinv
  · inext; iframe
  · imodintro; iexists ⟨Gpre, γ, ""⟩
    unfold heap_inv heapH_inv_name stateInterp_heap pointsto
    iframe Hinv Hfrag Hauth'
    unfold heap_inv heapH_inv_name
    iassumption

end initialization

section wpi_rules

variable {E : Effect} {H : IHandler (IProp GF) E}
variable [heapE Loc Val -< E] [InH (heapH (G := G)) H]

theorem wpi_storeOpt' Ms Me (l : Loc) (v v' : Option Val) (Φ : Option Val → IProp GF) :
   ↑(heapH_inv_name (G := G)) ⊆ Ms →
    l ↦? v -∗
    (l ↦? v' -∗ |={Ms, Me}=> Φ v) -∗
    WPi (storeOpt l v') @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto storeOpt
  iapply wpi_bind' (Ms \ ↑(heapH_inv_name (G := G)))
  iapply wpi_get; unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩
  iinv Hinv with >⟨%σinv, HauthInv⟩ Hclose
  ihave %Heq := ghost_map_auth_agree $$ HauthInv Hauth; subst σinv
  imodintro; iframe Hinv HauthInv

  /- Replace look up and insert operations. -/
  ihave %Hlookup := ghost_map_lookup $$ Hauth Hpt
  have Hlookup : σ[l]? = some v := by
    simpa [Iris.Std.get?] using Hlookup
  have Hinsert : σ.insert l v' = Std.insert  (M := (Std.ExtTreeMap Loc · compare)) σ l v' := by
    apply Std.ExtTreeMap.ext_getElem?; intro k
    simp only [Iris.Std.insert, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]
  rw [Hlookup, Hinsert]

  iapply wpi_bind' Ms; iapply wpi_set
  unfold stateInterp_heap heap_inv
  iintro %σ' ⟨HauthState, -⟩
  ihave %Heq := ghost_map_auth_agree $$ Hauth HauthState; subst σ'
  icombine Hauth HauthState as Hauth
  imod ghost_map_update v' $$ Hauth Hpt with ⟨⟨Hauth, Hauth'⟩, Hpt⟩
  imod Hclose $$ [Hauth'] with -
  · iframe
  imodintro; isplitl [Hauth]
  · isplit <;> itrivial
  iapply wpi_pure'; simp only [Option.join_some]
  iapply Hwand $$ [$]

theorem wpi_storeOpt M (l : Loc) (v v' : Option Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦? v' -∗ Φ v) -∗
    WPi (storeOpt l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand
  iapply wpi_storeOpt' M M _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply Hwand $$ [$]

theorem wpi_store?' Ms Me (l : Loc) (v : Option Val) (v' : Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    l ↦? v -∗
    (l ↦ v' -∗ |={Ms, Me}=> Φ v) -∗
    WPi (store? l v') @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold store?
  iapply wpi_storeOpt' _ _ _ _ _ _ Hmask $$ Hpt Hwand

theorem wpi_store? M (l : Loc) (v : Option Val) (v' : Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store? l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand
  iapply wpi_store?' M M _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply Hwand $$ [$]

theorem wpi_load?' Ms Me (l : Loc) (v : Val) (dq : DFrac) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ |={Ms,Me}=> Φ (some v)) -∗
    WPi (load? l) @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto load?
  iapply wpi_bind; iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩

  ihave %Hlookup := ghost_map_lookup $$ Hauth Hpt
  have Hlookup : σ[l]? = some (some v) := by
    simpa [Iris.Std.get?] using Hlookup
  rw [Hlookup]; simp only [Option.join_some]

  iframe Hauth Hinv
  imodintro; iapply wpi_pure'
  iapply Hwand $$ [$]

theorem wpi_load? M (l : Loc) (v : Val) (dq : DFrac) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ (some v)) -∗
    WPi (load? l) @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand
  iapply wpi_load?' M M _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply Hwand $$ [$]

section fail

variable [failE -< E]

theorem wpi_store!' Ms Me (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    l ↦ v -∗
    (l ↦ v' -∗ |={Ms,Me}=> Φ v) -∗
    WPi (store! l v') @> H; Ms, Me {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold store!
  iapply wpi_bind; iapply wpi_store?' _ _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply wpi_pure'
  iapply Hwand $$ [$]

theorem wpi_store! M (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦ v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store! l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand
  iapply wpi_store!' M M _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply Hwand $$ [$]

theorem wpi_load!' Ms Me (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ |={Ms,Me}=> Φ v) -∗
    WPi (load! l) @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold load!
  iapply wpi_bind; iapply wpi_load?' _ _ _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply wpi_pure'
  iapply Hwand $$ Hpt

theorem wpi_load! M (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ v) -∗
    WPi (load! l) @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand
  iapply wpi_load!' M M _ _ _ _ Hmask $$ Hpt
  iintro Hpt !>; iapply Hwand $$ [$]

end fail

section alloc

variable [demonicE Loc -< E] [InH (demonicH (PROP := IProp GF) Loc) H]
variable [LawfulLoc Loc]

private theorem extTreeMap_insertMany_eq_ofList_union {K : Type _} {V : Type _}
    [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] [DecidableEq K]
    (m : Std.ExtTreeMap K V compare) (entries : List (K × V))
    (Hnodup : Iris.Std.NoDupKeys entries) :
    m.insertMany entries = Std.PartialMap.union (M := (Std.ExtTreeMap K · compare))
      (Std.PartialMap.ofList (M := (Std.ExtTreeMap K · compare)) entries) m := by
  apply Std.ExtTreeMap.ext_getElem?; intro k
  simp [Iris.Std.PartialMap.union, Iris.Std.merge]
  by_cases Hmem : ∃ w, (k, w) ∈ entries
  · rcases Hmem with ⟨w, Hw⟩
    rw [Std.ExtTreeMap.getElem?_insertMany_list_of_mem ?_
      ((List.pairwise_map.mp
          (List.nodup_iff_pairwise_ne.mp Hnodup)).imp fun Hne Heq =>
            Hne (Std.LawfulEqOrd.compare_eq_iff_eq.mp Heq)) Hw]
    change some w = Option.merge _ (Iris.Std.get? (M := (Std.ExtTreeMap K · compare)) _ k) _
    simp only [Iris.Std.LawfulPartialMap.get?_ofList_some Hw Hnodup]
    cases m[k]? <;> rfl
    simp
  · rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false ?_]
    change m[k]? = Option.merge _
      (Iris.Std.get? (M := (Std.ExtTreeMap K · compare)) _ k) _
    simp only [Iris.Std.LawfulPartialMap.get?_ofList_none Hmem Hnodup]
    cases m[k]? <;> rfl
    rw [← Bool.not_eq_true]
    intro Hcontains
    rcases List.mem_map.mp (List.contains_iff_mem.mp Hcontains) with
      ⟨⟨k', w⟩, Hw, Hk⟩
    apply Hmem; exact ⟨w, Hk ▸ Hw⟩

omit [Std.TransOrd Loc] in
private theorem loc_add_nat_injective (l : Loc) :
    Function.Injective (fun (i : Nat) => l + (i : Int)) := by
  have Hne (i j : Nat) (Hlt : i < j) : l + (i : Int) ≠ l + (j : Int) := by
    intro Heq
    have Hgap : (j : Int) = (i : Int) + (1 + ((j - i - 1 : Nat) : Int)) := by omega
    have Hgt := LawfulLoc.add_pos_gt (l + (i : Int)) (j - i - 1)
    rw [LawfulLoc.add_nat_inj, ← Hgap, Heq] at Hgt
    simp at Hgt
  intro i j Heq
  rcases Nat.lt_trichotomy i j with Hlt | Heq' | Hgt
  · exact False.elim (Hne i j Hlt Heq)
  · exact Heq'
  · exact False.elim (Hne j i Hgt Heq.symm)

theorem wpi_allocN' Ms Me (n : Nat) (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    (∀ l : Loc, ([∗list] i ∈ .range n, (l + Int.ofNat i) ↦ v) -∗ |={Ms,Me}=> Φ l) -∗
    WPi (allocN n v) @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hwand; unfold allocN
  iapply wpi_bind' (Ms \ ↑(heapH_inv_name (G := G)))
  iapply wpi_get; unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩
  iinv Hinv with >⟨%σinv, HauthInv⟩ Hclose
  ihave %Heq := ghost_map_auth_agree $$ HauthInv Hauth; subst σinv
  imodintro; iframe Hauth Hinv
  iapply wpi_bind; iapply wpi_demonic
  iintro %⟨l, Hfree⟩; simp only
  iapply wpi_bind' Ms; iapply wpi_set
  unfold stateInterp_heap heap_inv
  iintro %σ' ⟨Hauth', -⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv Hauth'; subst σ'
  icombine HauthInv Hauth' as Hauth

  -- We do not need to care about the orders
  let entries := (List.range n).map fun m => (l + Int.ofNat m, some v)
  let σnew := Std.PartialMap.ofList (M := (Std.ExtTreeMap Loc · compare)) entries
  let σsum := Std.PartialMap.union (M := (Std.ExtTreeMap Loc · compare)) σnew σ

  -- New added entries do not have duplicated elements and the unioned hold the same elements
  have Hnodup : Std.NoDupKeys entries := by
    unfold Iris.Std.NoDupKeys entries
    simp [List.map_map]
    refine List.nodup_map_of_injective
      (loc_add_nat_injective l) List.nodup_range
  have HinsertMany : σ.insertMany entries = σsum := by
    simpa only [σnew] using extTreeMap_insertMany_eq_ofList_union σ entries Hnodup
  have HinsertMany' :
      σ.insertMany ((List.range n).map fun (i : Nat) => (l + (i : Int), some v)) = σsum := by
    simpa [entries, σsum] using HinsertMany

  imod ghost_map_insert_big σnew $$ Hauth with ⟨⟨HauthInv, HauthState⟩, Hpts⟩
  · -- Prove σnew ##ₘ σ
    unfold Std.PartialMap.disjoint; intro k Hk
    rcases Option.isSome_iff_exists.mp Hk.1 with ⟨w, Hw⟩
    have Hmem := Iris.Std.LawfulFiniteMap.mem_of_mem_ofList Hw
    simp only [entries, List.mem_map] at Hmem
    rcases Hmem with ⟨i, Hi, Hki⟩
    have Hkey : l + Int.ofNat i = k := congrArg Prod.fst Hki
    rw [← Hkey] at Hk
    apply Hfree i <| List.mem_range.mp Hi
    simpa [Iris.Std.get?] using Hk.2
  imod Hclose $$ [HauthInv] with -
  · iexists σ.insertMany entries;
    rw [HinsertMany]; itrivial
  imodintro; isplitl [HauthState]
  · rw [HinsertMany']; iframe HauthState Hinv
  iapply wpi_pure'; iapply Hwand
  unfold pointsto
  iapply (equiv_iff.mp (BigSepL.bigSepL_map
    (Φ := fun _ kv => ghost_map_elem _ _ kv.1 kv.2)
    (l + Int.ofNat ·, some v)))
  iapply (BigSepM.bigSepM_ofList (M := (Std.ExtTreeMap Loc · compare))) $$ Hpts
  exact Hnodup

theorem wpi_allocN M (n : Nat) (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    (∀ l : Loc, ([∗list] i ∈ .range n, (l + Int.ofNat i) ↦ v) -∗ Φ l) -∗
    WPi (allocN n v) @> H; M {{ Φ }} := by
  iintro %Hmask Hwand
  iapply wpi_allocN' M M _ _ _ Hmask
  iintro %loc Hl !>; iapply Hwand $$ [$]

theorem wpi_alloc' Ms Me (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ Ms →
    (∀ l, l ↦ v -∗ |={Ms,Me}=> Φ l) -∗
    WPi (alloc v) @> H; Ms,Me {{ Φ }} := by
  iintro %Hmask Hwand; unfold alloc
  iapply wpi_allocN' Ms Me 1 v Φ Hmask
  iintro %l Hpts; simp; icases Hpts with ⟨Hpt, -⟩
  rw [LawfulLoc.add_zero l]
  iapply Hwand $$ [$]

theorem wpi_alloc M (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    (∀ l, l ↦ v -∗ Φ l) -∗
    WPi (alloc v) @> H; M {{ Φ }} := by
  iintro %Hmask Hwand
  iapply wpi_alloc' M M _ _ Hmask
  iintro %loc Hloc !>; iapply Hwand $$ [$]

end alloc

end wpi_rules

end IrisITree
