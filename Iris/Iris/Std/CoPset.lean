/-
Copyright (c) 2026 Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Seassau, Markus de Medeiros, Sergei Stepanenko
-/
module

public import Iris.Std.Positives
public import Iris.Std.Classes
public import Iris.Std.GenSets
import Iris.Std.List

@[expose] public section

/- This file implements an abstract type [CoPset] of (possibly infinite) sets
of positive binary natural numbers ([Pos]). This type supports the
following operations:

· the empty set;
· a singleton set;
· the full set;
· union, intersection, and complement;
· picking an element in an infinite set;
· splitting a set into two disjoint subsets in such a way that if the original
  set is infinite then both parts are infinite;
· the (infinite) set of all numbers that have a certain suffix;
· conversions to and from other representations of sets.
-/

/-- The raw tree data structure -/

/- [coPset.leaf false] is the empty set; [coPset.leaf true] is the full set. -/
/- In [coPset.node b l r], the Boolean flag [b] indicates whether the number
1 is a member of the set, while the subtrees [l] and [r] must be
consulted to determine whether a number of the form [2i] or [2i+1]
is a member of the set. -/

inductive CoPsetRaw where
  | leaf : Bool → CoPsetRaw
  | node : Bool → CoPsetRaw → CoPsetRaw → CoPsetRaw
  deriving DecidableEq

/-- The type of raw trees (above) offers several representations of the
empty set and several representations of the full set. In order to
achieve extensional equality, this redundancy must be eliminated.
This is achieved by imposing a well-formedness criterion on trees. -/
def coPsetWf (t : CoPsetRaw) : Bool :=
  match t with
  | .leaf _ => true
  | .node true (.leaf true) (.leaf true) => false
  | .node false (.leaf false) (.leaf false) => false
  | .node _ l r => coPsetWf l && coPsetWf r

theorem node_wf_l {b l r} : coPsetWf (.node b l r) -> coPsetWf l := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPsetWf]

theorem node_wf_r {b l r} : coPsetWf (.node b l r) -> coPsetWf r := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPsetWf]

/-- The smart constructor [node'] preserves well-formedness. -/
def CoPsetRaw.node' (b : Bool) (l r : CoPsetRaw) : CoPsetRaw :=
  match b, l, r with
  | true, .leaf true, .leaf true => .leaf true
  | false, .leaf false, .leaf false => .leaf false
  | _, _, _ => .node b l r

theorem node'_wf {b l r} : coPsetWf l -> coPsetWf r -> coPsetWf (CoPsetRaw.node' b l r) := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp [CoPsetRaw.node', coPsetWf] <;> exact (⟨·, ·⟩)

open CoPsetRaw

/-- The membership test. -/
@[simp] def CoPsetRaw.ElemOf : Pos → CoPsetRaw → Bool
  | _, leaf b => b
  | .xH, node b _ _ => b
  | p~0, node _ l _ => CoPsetRaw.ElemOf p l
  | p~1, node _ _ r => CoPsetRaw.ElemOf p r

instance : Membership Pos CoPsetRaw  where
  mem := fun t p => CoPsetRaw.ElemOf p t

theorem elem_of_node b l r (p : Pos) :
  (CoPsetRaw.ElemOf p (CoPsetRaw.node' b l r)) = (CoPsetRaw.ElemOf p (CoPsetRaw.node b l r)) := by
  cases p <;> cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp [node', CoPsetRaw.ElemOf]

/-- Singleton. -/
@[simp] def CoPsetRaw.Singleton : Pos → CoPsetRaw
  | .xH => node true (leaf false) (leaf false)
  | p~0 => node' false (Singleton p) (leaf false)
  | p~1 => node' false (leaf false) (Singleton p)

/-- Union -/
@[simp] def CoPsetRaw.Union : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf false, t => t
  | t, leaf false => t
  | leaf true, _ => leaf true
  | _, leaf true => leaf true
  | node b1 l1 r1, node b2 l2 r2 => node' (b1 || b2) (Union l1 l2) (Union r1 r2)

instance : Union CoPsetRaw where union := CoPsetRaw.Union

/-- Intersection -/
@[simp] def CoPsetRaw.Intersection : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf true, t => t
  | t, leaf true => t
  | leaf false, _ => leaf false
  | _, leaf false => leaf false
  | node b1 l1 r1, node b2 l2 r2 => node' (b1 && b2) (Intersection l1 l2) (Intersection r1 r2)

instance : Inter CoPsetRaw where inter := CoPsetRaw.Intersection

/-- Complement -/
@[simp] def CoPsetRaw.Complement : CoPsetRaw → CoPsetRaw
  | leaf b => leaf (!b)
  | node b l r => node' (!b) (Complement l) (Complement r)

/-- Well-formedness for the above operations -/

theorem coPsetSingleton_wf p : coPsetWf (CoPsetRaw.Singleton p) := by
  induction p <;> simp_all only [CoPsetRaw.Singleton, coPsetWf]
  · apply node'_wf; simp only [coPsetWf]; assumption
  · apply node'_wf; assumption; simp [coPsetWf]
  · simp

theorem coPsetUnion_wf t1 t2 : coPsetWf t1 -> coPsetWf t2 -> coPsetWf (t1 ∪ t2) := by
  induction t1 generalizing t2 with
  | leaf b =>
    intros Hwf1 Hwf2; cases b <;> simp only [Union.union, CoPsetRaw.Union]
    · assumption
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Union, coPsetWf]
  | node b l r IH1 IH2 =>
    intros Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _ <;> simp only [Union.union, CoPsetRaw.Union, coPsetWf]
    · assumption
    · refine node'_wf ?_ ?_
      · exact IH1 _ (node_wf_l Hwf1) (node_wf_l Hwf2)
      · exact IH2 _ (node_wf_r Hwf1) (node_wf_r Hwf2)

theorem coPsetIntersection_wf t1 t2 :
  coPsetWf t1 -> coPsetWf t2 -> coPsetWf (t1 ∩ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b
    <;> simp only [Inter.inter, CoPsetRaw.Intersection]
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Intersection, coPsetWf]
    · assumption
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _
    <;> simp only [Inter.inter, CoPsetRaw.Intersection, coPsetWf]
    · assumption
    · refine node'_wf ?_ ?_
      · exact IH1 _ (node_wf_l Hwf1) (node_wf_l Hwf2)
      · exact IH2 _ (node_wf_r Hwf1) (node_wf_r Hwf2)

theorem coPsetComplement_wf t : coPsetWf (CoPsetRaw.Complement t) := by
  induction t with
  | leaf b => cases b <;> simp [CoPsetRaw.Complement, coPsetWf]
  | node b l r => cases b <;> simp only [CoPsetRaw.Complement] <;>
    apply node'_wf <;> assumption

/-- The abstract type [CoPset] -/
/- A set is a well-formed tree. -/
structure CoPset where
  tree : CoPsetRaw
  wf : coPsetWf tree = true

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

namespace CoPset

/-- Helper: if a well-formed tree has uniform membership, it must be a leaf.
    Corresponds to `coPLeaf_wf` in Rocq Iris. -/
theorem coPsetLeaf_wf {t : CoPsetRaw} {b : Bool} (Hwf : coPsetWf t = true)
    (Hall : ∀ p, ElemOf p t = b) : t = .leaf b := by
  cases t with
  | leaf b' => exact congrArg _ (Hall .xH)
  | node b' l r =>
    suffices Hwf : (coPsetWf (node b (leaf b) (leaf b))) by cases b <;> simp [coPsetWf] at Hwf
    rw [← Hwf]
    congr
    · exact Hall .xH |>.symm
    · exact coPsetLeaf_wf (node_wf_l Hwf) (Hall <| .xO ·) |>.symm
    · exact coPsetLeaf_wf (node_wf_r Hwf) (Hall <| .xI ·) |>.symm

/-- Two CoPsetRaw trees are equal if they have the same membership function
    and both are well-formed. -/
theorem coPsetRaw_eq {t1 t2 : CoPsetRaw} (Ht : ∀ p, ElemOf p t1 = ElemOf p t2)
    (Hwf1 : coPsetWf t1 = true) (Hwf2 : coPsetWf t2 = true) : t1 = t2 := by
  match t1, t2 with
  | .leaf b1, .leaf b2 => congr 1; exact Ht .xH
  | .leaf b1, .node b2 l2 r2 =>
    simp only [ElemOf] at Ht
    exact coPsetLeaf_wf Hwf2 (fun p => .symm (Ht p)) |>.symm
  | .node b1 l1 r1, .leaf b2 =>
    simp only [ElemOf] at Ht
    exact (coPsetLeaf_wf Hwf1 Ht)
  | .node b1 l1 r1, .node b2 l2 r2 =>
    congr
    · exact Ht .xH
    · exact coPsetRaw_eq (Ht <| .xO ·) (node_wf_l Hwf1) (node_wf_l Hwf2)
    · exact coPsetRaw_eq (Ht <| .xI ·) (node_wf_r Hwf1) (node_wf_r Hwf2)

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

/-- All operations are refined at the level of [CoPset] -/

@[ext]
theorem ext {X Y : CoPset} (H : ∀ p, p ∈ X <-> p ∈ Y) : X = Y := by
  rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩
  simp only [Membership.mem, Bool.coe_iff_coe] at H
  congr 1
  exact coPsetRaw_eq H xwf ywf

def empty : CoPset := ⟨CoPsetRaw.leaf false, rfl⟩

instance : EmptyCollection CoPset where emptyCollection := CoPset.empty

def full : CoPset := ⟨CoPsetRaw.leaf true, rfl⟩

instance : Iris.Std.Top CoPset where top := CoPset.full

@[simp] def singleton (p : Pos) : CoPset := ⟨CoPsetRaw.Singleton p, coPsetSingleton_wf p⟩

instance : Singleton Pos CoPset where
  singleton := CoPset.singleton

def union (X Y : CoPset) : CoPset := ⟨CoPsetRaw.Union X.tree Y.tree, coPsetUnion_wf _ _ X.wf Y.wf⟩

instance : Union CoPset where union := CoPset.union

def inter (X Y : CoPset) : CoPset :=
  ⟨CoPsetRaw.Intersection X.tree Y.tree, coPsetIntersection_wf _ _ X.wf Y.wf⟩

instance : Inter CoPset where inter := CoPset.inter

def complement (X : CoPset) : CoPset := ⟨CoPsetRaw.Complement X.tree, coPsetComplement_wf _⟩

def diff (X Y : CoPset) : CoPset := X ∩ (complement Y)

def mem (p : Pos) (X : CoPset) : Bool := CoPsetRaw.ElemOf p X.tree

instance : HasSubset CoPset where
  Subset t1 t2 := ∀ (p : Pos), p ∈ t1 -> p ∈ t2

instance : SDiff CoPset where
  sdiff := CoPset.diff

theorem mem_empty {p : Pos} : p ∉ (∅ : CoPset) := by
  simp only [Membership.mem, EmptyCollection.emptyCollection, CoPset.empty]
  cases p <;> simp [CoPsetRaw.ElemOf]

theorem mem_full {p : Pos} : p ∈ full := by
  simp only [Membership.mem, full, CoPsetRaw.ElemOf]

theorem in_singleton {p q : Pos} : p ∈ ({q} : CoPset) ↔ p = q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Singleton.singleton, Membership.mem] at h
    induction q generalizing p with
    | xH => cases p <;> simp at h <;> rfl
    | xO q' IH =>
      cases p with
      | xH => simp [elem_of_node] at h
      | xO p' => simp [elem_of_node] at h;  rw [IH h]
      | xI p' => simp [elem_of_node] at h
    | xI q' IH =>
      cases p with
      | xH => simp [elem_of_node] at h
      | xO p' => simp [elem_of_node] at h
      | xI p' => simp [elem_of_node] at h;  rw [IH h]
  · subst h
    simp only [Singleton.singleton, Membership.mem]
    induction p with
    | xH => simp
    | xO p' IH => simpa [elem_of_node]
    | xI p' IH => simpa [elem_of_node]


theorem in_inter {p : Pos} {X Y : CoPset} : p ∈ X ∩ Y <-> p ∈ X ∧ p ∈ Y := by
  simp only [Inter.inter, inter, Membership.mem]
  constructor
  · rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩; dsimp
    induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp only [Intersection] <;> intros Hnin <;> simp_all [CoPsetRaw.ElemOf]
      refine IH _ (node_wf_r xwf) _ (node_wf_r ywf) ?_
      rewrite [elem_of_node] at Hnin
      simp_all [ElemOf]
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp only [Intersection] <;> intros Hnin <;> simp_all [CoPsetRaw.ElemOf]
      refine IH _ (node_wf_l xwf) _ (node_wf_l ywf) ?_
      rewrite [elem_of_node] at Hnin
      simp_all [ElemOf]
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [Intersection, ElemOf, elem_of_node]
  · rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩; simp []
    induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      exact (IH _ (node_wf_r xwf) _ (node_wf_r ywf))
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      exact (IH _ (node_wf_l xwf) _ (node_wf_l ywf))
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [ElemOf, elem_of_node, Intersection]
      exact (⟨·, ·⟩)

theorem in_complement {X : CoPset} : p ∈ complement X <-> p ∉ X := by
  rcases X with ⟨X, xwf⟩
  simp only [complement, Membership.mem, Bool.not_eq_true, Bool.coe_true_iff_false]
  induction p generalizing X with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;>
      simp only [CoPsetRaw.Complement, CoPsetRaw.ElemOf, elem_of_node]
      exact IH _ (node_wf_r xwf)
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;>
      simp only [CoPsetRaw.Complement, CoPsetRaw.ElemOf, elem_of_node]
      exact IH _ (node_wf_l xwf)
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> simp only [CoPsetRaw.Complement, CoPsetRaw.ElemOf, elem_of_node]

theorem in_diff {p} {X Y : CoPset} : p ∈ X \ Y <-> p ∈ X ∧ p ∉ Y := by
  refine ⟨fun Hnin => ?_, fun ⟨Hx, Hy⟩ => ?_⟩
  · obtain ⟨Hx, Hy⟩ := in_inter |>.mp Hnin
    exact ⟨Hx, in_complement.mp Hy⟩
  · simpa only [SDiff.sdiff, CoPset.diff, in_inter] using ⟨Hx, in_complement.mpr Hy⟩

theorem in_union {X Y : CoPset} : p ∈ X ∪ Y <-> p ∈ X ∨ p ∈ Y := by
  rcases X with ⟨X, xwf⟩; rcases Y with ⟨Y, ywf⟩
  simp only [Membership.mem]
  constructor
  · induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, elem_of_node]
      exact IH _ (node_wf_r xwf) _ (node_wf_r ywf)
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, elem_of_node]
      exact IH _ (node_wf_l xwf) _ (node_wf_l ywf)
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]
  · induction p generalizing X Y with
    | xI p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]
      exact IH _ (node_wf_r xwf) _ (node_wf_r ywf)
    | xO p IH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]
      exact IH _ (node_wf_l xwf) _ (node_wf_l ywf)
    | xH =>
      rcases X with ⟨⟨⟩⟩ | _ <;> rcases Y with ⟨⟨⟩⟩ | _ <;>
      simp_all [Union.union, union, CoPsetRaw.Union, ElemOf, elem_of_node]

theorem not_in_union {p} {X1 X2 : CoPset} : ¬ p ∈ X1 ∪ X2 <-> ¬ p ∈ X1 ∧ ¬ p ∈ X2 := by
  refine ⟨fun Hu => ?_, fun ⟨H1, H2⟩ Hu => ?_⟩
  · exact ⟨(Hu <| in_union.mpr <| .inl ·), (Hu <| in_union.mpr <| .inr ·)⟩
  · exact in_union.mp Hu |>.elim H1 H2

theorem subseteq_trans {X Y Z : CoPset} (Hxy : X ⊆ Y) (Hyz : Y ⊆ Z) : X ⊆ Z :=
  fun p => (Hyz p) ∘ (Hxy p)

def CoPsetRaw.isFinite : CoPsetRaw → Bool
  | CoPsetRaw.leaf b => !b
  | CoPsetRaw.node _ l r => isFinite l && isFinite r

def isFinite (X : CoPset) : Bool :=
  CoPsetRaw.isFinite X.tree

/-- Picking an element out of an infinite set -/

/- Provided that the set [X] is infinite, [pick X] yields an element of
this set. Note that [pick] is implemented by depth-first search, so
using it repeatedly to obtain elements [x] and inserting these elements
[x] into some set [Y] will give rise to a very unbalanced tree. -/

def CoPsetRaw.pickRaw : CoPsetRaw → Option Pos
  | CoPsetRaw.leaf true => some Pos.P1
  | CoPsetRaw.node true _ _ => some Pos.P1
  | CoPsetRaw.leaf false => none
  | CoPsetRaw.node false l r =>
    match pickRaw l with
    | some i => some (i~0)
    | none => Option.map (λ i => i~1) (pickRaw r)

def pick (X : CoPset) : Pos :=
  (CoPsetRaw.pickRaw X.tree).getD Pos.P1

theorem CoPsetRaw.pickRaw_elem_of (t : CoPsetRaw) (i : Pos) :
    CoPsetRaw.pickRaw t = some i → CoPsetRaw.ElemOf i t := by
  induction t generalizing i with
  | leaf b =>
    cases b <;> simp [CoPsetRaw.pickRaw, CoPsetRaw.ElemOf]
  | node b l r ihl ihr =>
    cases b
    · simp only [pickRaw]
      intro h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [ElemOf]
        apply ihl
        assumption
      · simp only [Option.map] at h
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp only [ElemOf]
          apply ihr
          assumption
        · simp at h
    · simp only [pickRaw, Option.some.injEq]
      intro h
      subst h
      rfl

theorem CoPsetRaw.pickRaw_none (t : CoPsetRaw) (i : Pos) :
    CoPsetRaw.pickRaw t = none → ¬(CoPsetRaw.ElemOf i t) := by
  induction t generalizing i with
  | leaf b =>
    cases b <;> simp [CoPsetRaw.pickRaw, CoPsetRaw.ElemOf]
  | node b l r ihl ihr =>
    cases b
    · simp only [CoPsetRaw.pickRaw, Bool.not_eq_true]
      intro h
      split at h
      · simp at h
      · cases i with
        | xH => simp [CoPsetRaw.ElemOf]
        | xO p =>
          simp only [ElemOf]
          rw [Bool.eq_false_iff]
          apply ihl; assumption
        | xI p =>
          simp only [ElemOf]
          rw [Bool.eq_false_iff]
          apply ihr
          simp only [Option.map] at h
          split at h
          · simp at h
          · assumption
    · simp [CoPsetRaw.pickRaw]

theorem mem_pick (X : CoPset) : X ≠ ∅ → pick X ∈ X := by
  cases X with | mk tree wf =>
  intro hne
  simp only [Membership.mem, pick]
  cases h : CoPsetRaw.pickRaw tree with
  | some i => exact CoPsetRaw.pickRaw_elem_of tree i h
  | none =>
    exfalso
    apply hne
    ext p
    simp only [Membership.mem, EmptyCollection.emptyCollection, empty, ElemOf, Bool.false_eq_true,
      iff_false, Bool.not_eq_true]
    rw [Bool.eq_false_iff]
    exact CoPsetRaw.pickRaw_none tree p h

-- Inverse suffix closure

/-- [suffixes q] is the set of all numbers [p] such that [q] is a suffix
of [p], when these numbers are viewed as sequences of bits. In other words, it
is the set of all numbers that have the suffix [q]. It is always an infinite
set. -/
def CoPsetRaw.suffixesRaw : Pos → CoPsetRaw
  | .xH => .leaf true
  | p~0 => CoPsetRaw.node' false (suffixesRaw p) (.leaf false)
  | p~1 => CoPsetRaw.node' false (.leaf false) (suffixesRaw p)

theorem coPsetSuffixes_wf p : coPsetWf (CoPsetRaw.suffixesRaw p) := by
  induction p <;> simp [CoPsetRaw.suffixesRaw, coPsetWf] <;>
  apply node'_wf <;> simp_all [coPsetWf]

def suffixes (p : Pos) : CoPset :=
  ⟨CoPsetRaw.suffixesRaw p, coPsetSuffixes_wf p⟩

theorem elem_suffixes {p q} : p ∈ suffixes q <-> ∃ q', p = q' ++ q := by
  constructor
  · induction q generalizing p with
    | xI q IH =>
      simp only [suffixes, CoPsetRaw.suffixesRaw, Membership.mem, elem_of_node]
      intros Hin
      cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      obtain ⟨q', rfl⟩ := IH Hin
      exact ⟨q', rfl⟩
    | xO q IH =>
      simp only [suffixes, CoPsetRaw.suffixesRaw, Membership.mem, elem_of_node]
      intros Hin
      cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      obtain ⟨q', rfl⟩ := IH Hin
      exact ⟨q', rfl⟩
    | xH => intro _; exists p
  · rintro ⟨q', rfl⟩
    simp only [suffixes, Membership.mem]
    induction q <;>
    simp_all [CoPsetRaw.suffixesRaw, elem_of_node, HAppend.hAppend, Pos.app, CoPsetRaw.ElemOf]

theorem suffixesRaw_not_finite (p : Pos) : ¬CoPsetRaw.isFinite (CoPsetRaw.suffixesRaw p) := by
  induction p with
  | xH => simp [CoPsetRaw.suffixesRaw, CoPsetRaw.isFinite]
  | xO p ih | xI p ih =>
    simp only [CoPsetRaw.suffixesRaw, node']
    split
    · simp [CoPsetRaw.isFinite]
    · simp [show CoPsetRaw.suffixesRaw p = leaf false by assumption, CoPsetRaw.isFinite] at ih
    · simp [CoPsetRaw.isFinite, ih]

theorem suffixes_not_finite (p : Pos) : ¬isFinite (suffixes p) := by
  simp only [isFinite, suffixes]
  exact suffixesRaw_not_finite p

/-- Splitting a set -/

/- Every infinite [X : CoPset] can be split into two disjoint parts, which are
infinite sets. Use the functions [splitLeft] and [splitRight] if you
need a constructive witness. -/

def leftRaw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node true (CoPsetRaw.leaf true) (CoPsetRaw.leaf false)
  | CoPsetRaw.node b l r => CoPsetRaw.node' b (leftRaw l) (leftRaw r)

def rightRaw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node false (CoPsetRaw.leaf false) (CoPsetRaw.leaf true)
  | CoPsetRaw.node _ l r => CoPsetRaw.node' false (rightRaw l) (rightRaw r)

theorem left_wf t : coPsetWf (leftRaw t) := by
  induction t with
  | leaf b => cases b <;> simp [leftRaw, coPsetWf]
  | node b l r => simp only [leftRaw]; apply node'_wf <;> assumption

theorem right_wf t : coPsetWf (rightRaw t) := by
  induction t with
  | leaf b => cases b <;> simp [rightRaw, coPsetWf]
  | node b l r => simp only [rightRaw]; apply node'_wf <;> assumption

def splitLeft (X : CoPset) : CoPset := ⟨leftRaw X.tree, left_wf _⟩

def splitRight (X : CoPset) : CoPset := ⟨rightRaw X.tree, right_wf _⟩

def split (X : CoPset) : CoPset × CoPset := (splitLeft X, splitRight X)

end CoPset

section Instances

open Iris Std CoPset

instance : Set CoPset Pos where

instance : LawfulSet CoPset Pos where
  ext h := CoPset.ext h
  mem_empty := CoPset.mem_empty
  mem_singleton := CoPset.in_singleton
  mem_union := CoPset.in_union
  mem_inter := CoPset.in_inter
  mem_diff := CoPset.in_diff

instance : DecidableEq CoPset := by
  rintro ⟨X⟩ ⟨Y⟩
  rw [CoPset.mk.injEq]
  infer_instance

end Instances

section Set

open Iris Std CoPset

def set_to_coPset {S : Type _} [LawfulFiniteSet S Pos] (X : S) : CoPset :=
  LawfulSet.ofList (toList X)

theorem mem_set_to_coPset {S : Type _} [LawfulFiniteSet S Pos] (X : S) i
  : i ∈ set_to_coPset X ↔ i ∈ X := by
  simp only [set_to_coPset]
  rw [←LawfulSet.mem_ofList, ←mem_toList]
  rfl

theorem isFinite_setFinite {X : CoPset} : isFinite X ↔ LawfulSet.setFinite X := by
  cases X with | mk tx wx =>
  simp only [isFinite, LawfulSet.setFinite]
  induction tx with
  | leaf b =>
    simp only [CoPsetRaw.isFinite, Bool.not_eq_eq_eq_not, Bool.not_true, Membership.mem, ElemOf]
    constructor
    · rintro ⟨⟩; exists []; intro _ H; cases H
    · rintro ⟨l, Hl⟩
      cases b
      · rfl
      · simp at Hl
        exact ((List.fresh l).choose_spec (Hl (List.fresh l).choose)).elim
  | node b l r IHl IHr =>
    simp only [CoPsetRaw.isFinite, Bool.and_eq_true]; constructor
    · intro ⟨H1, H2⟩
      obtain ⟨l1, Hl1⟩ := (IHl (node_wf_l wx)).mp H1
      obtain ⟨l2, Hl2⟩ := (IHr (node_wf_r wx)).mp H2
      refine ⟨(if b then [Pos.xH] else []) ++ l1.map (·~0) ++ l2.map (·~1), fun x Hx => ?_⟩
      simp only [List.mem_append, List.mem_map]; simp only [Membership.mem] at Hx Hl1 Hl2
      cases x with
      | xH => cases b; simp [CoPsetRaw.ElemOf] at Hx; left; simp
      | xO p => simp only [ElemOf] at Hx; left; right; exact ⟨_, Hl1 _ Hx, rfl⟩
      | xI p => simp only [ElemOf] at Hx; right; exact ⟨_, Hl2 _ Hx, rfl⟩
    · rintro ⟨k, Hk⟩
      rw [IHl (node_wf_l wx), IHr (node_wf_r wx)]
      simp only [Membership.mem] at Hk ⊢
      constructor
      · exists k.filterMap (fun x => match x with | Pos.xO q => some q | _ => none)
        intro p Hp
        have Hmem : (p~0) ∈ k := Hk (p~0) Hp
        clear Hk IHl IHr Hp
        induction k with
        | nil => cases Hmem
        | cons x xs IH =>
          simp only [List.filterMap]
          cases Hmem with
          | head => apply List.mem_cons.mpr; left; rfl
          | tail _ Hmem' =>
            cases x with
            | xH => exact IH Hmem'
            | xO q => right; exact IH Hmem'
            | xI q => exact IH Hmem'
      · exists k.filterMap (fun x => match x with | Pos.xI q => some q | _ => none)
        intro p Hp
        have Hmem : (p~1) ∈ k := Hk (p~1) Hp
        clear Hk IHl IHr Hp
        induction k with
        | nil => cases Hmem
        | cons x xs IH =>
          simp only [List.filterMap]
          cases Hmem with
          | head => apply List.mem_cons.mpr; left; rfl
          | tail _ Hmem' =>
            cases x with
            | xH => exact IH Hmem'
            | xO q => exact IH Hmem'
            | xI q => right; exact IH Hmem'

theorem not_isFinite_setInfinite {X : CoPset} : ¬isFinite X ↔ LawfulSet.setInfinite X := by
  rw [isFinite_setFinite, LawfulSet.not_finite_infinite]

theorem set_to_coPset_finite {S : Type _} [LawfulFiniteSet S Pos] (X : S)
  : isFinite (set_to_coPset X) := by
    simp only [set_to_coPset]
    induction (toList X) with
    | nil => simp only [LawfulSet.ofList_nil, isFinite_setFinite]; exact LawfulSet.empty_finite
    | cons x xs IH =>
      simp only [LawfulSet.ofList_cons, LawfulSet.insert_union, isFinite_setFinite]
      exact LawfulSet.union_finite LawfulSet.singleton_finite (isFinite_setFinite.mp IH)

end Set
