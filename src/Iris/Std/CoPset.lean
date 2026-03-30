/-
Copyright (c) 2026 Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Remy Seassau, Markus de Medeiros, Sergei Stepanenko
-/
module

public import Iris.Std.Positives
import Iris.Std.Classes

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
def CoPsetRaw.ElemOf : Pos → CoPsetRaw → Bool
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
def CoPsetRaw.Singleton : Pos → CoPsetRaw
  | .xH => node true (leaf false) (leaf false)
  | p~0 => node' false (Singleton p) (leaf false)
  | p~1 => node' false (leaf false) (Singleton p)

/-- Union -/
def CoPsetRaw.Union : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf false, t => t
  | t, leaf false => t
  | leaf true, _ => leaf true
  | _, leaf true => leaf true
  | node b1 l1 r1, node b2 l2 r2 => node' (b1 || b2) (Union l1 l2) (Union r1 r2)

instance : Union CoPsetRaw where union := CoPsetRaw.Union

/-- Intersection -/
def CoPsetRaw.Intersection : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf true, t => t
  | t, leaf true => t
  | leaf false, _ => leaf false
  | _, leaf false => leaf false
  | node b1 l1 r1, node b2 l2 r2 => node' (b1 && b2) (Intersection l1 l2) (Intersection r1 r2)

instance : Inter CoPsetRaw where inter := CoPsetRaw.Intersection

/-- Complement -/
def CoPsetRaw.Complement : CoPsetRaw → CoPsetRaw
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

/-- All operations are refined at the level of [CoPset] -/

def empty : CoPset := ⟨CoPsetRaw.leaf false, rfl⟩

instance : EmptyCollection CoPset where emptyCollection := CoPset.empty

def full : CoPset := ⟨CoPsetRaw.leaf true, rfl⟩

def singleton (p : Pos) : CoPset := ⟨CoPsetRaw.Singleton p, coPsetSingleton_wf p⟩

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

theorem in_inter p (X Y : CoPset) : p ∈ X ∩ Y <-> p ∈ X ∧ p ∈ Y := by
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
  · obtain ⟨Hx, Hy⟩ := in_inter p X (complement Y) |>.mp Hnin
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

def CoPset.pick (X : CoPset) : Pos :=
  (CoPsetRaw.pickRaw X.tree).getD Pos.P1


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

instance : Iris.Std.Disjoint CoPset where
  disjoint s t := ∀ p, p ∈ s -> p ∈ t -> False

@[symm]
theorem disj_symm (E1 E2 : CoPset) :
  E1 ## E2 -> E2 ## E1 := by
  exact fun Hdisj p HE1 HE2 => Hdisj p HE2 HE1
