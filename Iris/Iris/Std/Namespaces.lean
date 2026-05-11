/-
Copyright (c) 2026 Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Seassau, Markus de Medeiros, Sergei Stepanenko
-/
module

public import Iris.Std.CoPset
public import Iris.Std.Positives
public import Iris.Std.GenSets

@[expose] public section

abbrev Namespace := List Pos

instance : DecidableEq Namespace := by infer_instance

instance : Pos.Countable Namespace := by infer_instance

def nroot : Namespace := List.nil

def ndot [Pos.Countable A] (N : Namespace) (x : A) : Namespace :=
  (Pos.Countable.encode x) :: N

def nclose (N : Namespace) : CoPset :=
  CoPset.suffixes ((Pos.flatten N))

instance : CoeOut Namespace CoPset where coe := nclose

infix:80 ".@" => ndot

instance ndisjoint : Iris.Std.Disjoint Namespace where
  disjoint N1 N2 := nclose N1 ## nclose N2

theorem nclose_root : ↑nroot = CoPset.full := by rfl

theorem nclose_subseteq [Pos.Countable A] N (x : A) : (↑N.@x : CoPset) ⊆ (↑N : CoPset) := by
  intros p
  simp only [nclose, CoPset.elem_suffixes]
  rintro ⟨q, rfl⟩
  obtain ⟨q', Heq⟩ := Pos.flatten_suffix N (ndot N x) (by exists [Pos.Countable.encode x])
  exists q ++ q'
  rewrite [Pos.app_assoc.assoc, <- Heq]
  rfl

theorem nclose_subseteq' [Pos.Countable A] {N : Namespace} (x : A) (Hs : (↑N : CoPset) ⊆ E) :
    (↑(N.@x) : CoPset) ⊆ E :=
  CoPset.subseteq_trans (nclose_subseteq _ _) Hs

theorem ndot_ne_disjoint [Pos.Countable A] (N : Namespace) {x y : A} (Hxy : x ≠ y) :
    N.@x ## N.@y := by
  intros p
  simp only [nclose, CoPset.elem_suffixes]
  rintro ⟨⟨qx, Heqx⟩, ⟨qy, Heqy⟩⟩
  apply Hxy
  have := Pos.flatten_suffix_eq (by simp [ndot]) (Heqx ▸ Heqy)
  simpa only [ndot, List.cons.injEq, Pos.encode_inj, Function.Injective.eq_iff, and_true]

theorem ndot_preserve_disjoint_l [Pos.Countable A] {N : Namespace} {E : CoPset} (x : A)
    (Hdisj : ↑N ## E) : ↑(N.@x) ## E :=
  fun p c => Hdisj p ⟨nclose_subseteq N x _ c.left, c.right⟩

theorem ndot_preserve_disjoint_r [Pos.Countable A] {N : Namespace} {E : CoPset} (x : A)
    (Hdisj : E ## ↑N) : E ## ↑(N.@x) :=
   Iris.Std.LawfulSet.disjoint_comm.mp <| ndot_preserve_disjoint_l x <| Iris.Std.LawfulSet.disjoint_comm.mp Hdisj

theorem nclose_not_finite (N : Namespace) : ¬CoPset.isFinite (↑N) := by
  simp only [nclose]
  exact CoPset.suffixes_not_finite (Pos.flatten N)

theorem fresh_name {S : Type _} [Iris.Std.LawfulFiniteSet S Pos] (E : S) (N : Namespace) :
  ∃ i, i ∉ E ∧ i ∈ (↑N : CoPset) := by
  exists (CoPset.pick (↑N \ set_to_coPset E))
  have hne : ↑N \ set_to_coPset E ≠ ∅ := by
    apply Iris.Std.LawfulSet.diff_not_finite_finite_ne_empty
    · simp [Iris.Std.LawfulSet.setInfinite]
      intro l
      have : ¬CoPset.isFinite (↑N) := nclose_not_finite N
      rw [isFinite_setFinite] at this
      simp [Iris.Std.LawfulSet.setFinite] at this
      exact this l
    · rw [← isFinite_setFinite]
      exact set_to_coPset_finite E
  have ⟨hiN, hiE⟩ := CoPset.in_diff.mp (CoPset.mem_pick (↑N \ set_to_coPset E) hne)
  constructor
  · intro hE
    rw [← mem_set_to_coPset] at hE
    exact hiE hE
  · exact hiN

open Iris.Std in
attribute [grind unfold] instDisjoint in
theorem CoPset.difference_difference (X1 X2 X3 Y : CoPset) :
    (X1 \ X2) \ X3 ## Y -> X1 \ (X2 ∪ X3) ## Y := by
  grind [LawfulSet.mem_diff, LawfulSet.mem_union, Disjoint.disjoint]
