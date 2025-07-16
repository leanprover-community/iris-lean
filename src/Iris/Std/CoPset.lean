import Iris.Std.Positives
import Iris.Std.Classes

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

/- [coPLeaf false] is the empty set; [coPLeaf true] is the full set. -/
/- In [coPNode b l r], the Boolean flag [b] indicates whether the number
1 is a member of the set, while the subtrees [l] and [r] must be
consulted to determine whether a number of the form [2i] or [2i+1]
is a member of the set. -/

private inductive CoPsetRaw where
  | leaf : Bool → CoPsetRaw
  | node : Bool → CoPsetRaw → CoPsetRaw → CoPsetRaw
deriving DecidableEq

/-- The type of raw trees (above) offers several representations of the
empty set and several representations of the full set. In order to
achieve extensional equality, this redundancy must be eliminated.
This is achieved by imposing a well-formedness criterion on trees. -/
def coPset_wf (t : CoPsetRaw) : Bool :=
  match t with
  | .leaf _ => true
  | .node true (.leaf true) (.leaf true) => false
  | .node false (.leaf false) (.leaf false) => false
  | .node _ l r => coPset_wf l && coPset_wf r

theorem node_wf_l b l r : coPset_wf (.node b l r) -> coPset_wf l := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPset_wf]
theorem node_wf_r b l r : coPset_wf (.node b l r) -> coPset_wf r := by
  cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp_all [coPset_wf]

/-- The smart constructor [node'] preserves well-formedness. -/
def CoPsetRaw.node' (b : Bool) (l r : CoPsetRaw) : CoPsetRaw :=
  match b, l, r with
  | true, .leaf true, .leaf true => .leaf true
  | false, .leaf false, .leaf false => .leaf false
  | _, _, _ => .node b l r

theorem node'_wf b l r :
  coPset_wf l -> coPset_wf r -> coPset_wf (CoPsetRaw.node' b l r) := by
  cases b <;> rcases l with ⟨ ⟨⟩ ⟩ | _ <;> rcases r with ⟨ ⟨⟩ ⟩ | _ <;>
  simp [CoPsetRaw.node', coPset_wf] <;> exact fun a_6 a_7 => ⟨a_6, a_7⟩

open CoPsetRaw

/-- The membership test. -/
def CoPsetRaw.ElemOf : Pos → CoPsetRaw → Bool
  | _, leaf b => b
  | P1, node b _ _ => b
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
  | P1 => node true (leaf false) (leaf false)
  | p~0 => node' false (Singleton p) (leaf false)
  | p~1 => node' false (leaf false) (Singleton p)

/-- Union -/
def CoPsetRaw.Union : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf false, t => t
  | t, leaf false => t
  | leaf true, _ => leaf true
  | _, leaf true => leaf true
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 || b2) (Union l1 l2) (Union r1 r2)
instance : Union CoPsetRaw where union := CoPsetRaw.Union

/-- Intersection -/
def CoPsetRaw.Intersection : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf true, t => t
  | t, leaf true => t
  | leaf false, _ => leaf false
  | _, leaf false => leaf false
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 && b2) (Intersection l1 l2) (Intersection r1 r2)
instance : Inter CoPsetRaw where inter := CoPsetRaw.Intersection

/-- Complement -/
def CoPsetRaw.Complement : CoPsetRaw → CoPsetRaw
  | leaf b => leaf (!b)
  | node b l r => node' (!b) (Complement l) (Complement r)

/-- Well-formedness for the above operations -/

theorem coPsetSingleton_wf p : coPset_wf (CoPsetRaw.Singleton p) := by
  induction p <;> simp_all [CoPsetRaw.Singleton, coPset_wf]
  · apply node'_wf; simp [coPset_wf]; assumption
  · apply node'_wf; assumption; simp [coPset_wf]

theorem coPsetUnion_wf t1 t2 :
  coPset_wf t1 -> coPset_wf t2 -> coPset_wf (t1 ∪ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b <;> simp [Union.union, CoPsetRaw.Union]
    · assumption
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Union, coPset_wf]
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [Union.union, CoPsetRaw.Union, coPset_wf]
    · assumption
    · apply node'_wf
      · apply IH1; exact node_wf_l b l r Hwf1
        (expose_names; exact node_wf_l a a_1 a_2 Hwf2)
      · apply IH2; exact node_wf_r b l r Hwf1
        (expose_names; exact node_wf_r a a_1 a_2 Hwf2)

theorem coPsetIntersection_wf t1 t2 :
  coPset_wf t1 -> coPset_wf t2 -> coPset_wf (t1 ∩ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b <;> simp [Inter.inter, CoPsetRaw.Intersection]
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [CoPsetRaw.Intersection, coPset_wf]
    · assumption
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [Inter.inter, CoPsetRaw.Intersection, coPset_wf]
    · assumption
    · apply node'_wf
      · apply IH1; exact node_wf_l b l r Hwf1
        (expose_names; exact node_wf_l a a_1 a_2 Hwf2)
      · apply IH2; exact node_wf_r b l r Hwf1
        (expose_names; exact node_wf_r a a_1 a_2 Hwf2)

theorem coPsetComplement_wf t : coPset_wf (CoPsetRaw.Complement t) := by
  induction t with
  | leaf b => cases b <;> simp [CoPsetRaw.Complement, coPset_wf]
  | node b l r => cases b <;> simp [CoPsetRaw.Complement, coPset_wf] <;>
    apply node'_wf <;> assumption

/-- The abstract type [CoPset] -/
/- A set is a well-formed tree. -/
structure CoPset where
  tree : CoPsetRaw
  wf : coPset_wf tree = true

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

namespace CoPset

/-- All operations are refined at the level of [CoPset] -/

def empty : CoPset := ⟨CoPsetRaw.leaf false, rfl⟩
instance : EmptyCollection CoPset where emptyCollection := CoPset.empty

def full : CoPset := ⟨CoPsetRaw.leaf true, rfl⟩

def singleton (p : Pos) : CoPset :=
  ⟨CoPsetRaw.Singleton p, coPsetSingleton_wf p⟩

def union (X Y : CoPset) : CoPset :=
  ⟨CoPsetRaw.Union X.tree Y.tree, coPsetUnion_wf _ _ X.wf Y.wf⟩
instance : Union CoPset where union := CoPset.union

def inter (X Y : CoPset) : CoPset :=
  ⟨CoPsetRaw.Intersection X.tree Y.tree, coPsetIntersection_wf _ _ X.wf Y.wf⟩
instance : Inter CoPset where inter := CoPset.inter

def diff (X Y : CoPset) : CoPset :=
  ⟨CoPsetRaw.Intersection X.tree (CoPsetRaw.Complement Y.tree), coPsetIntersection_wf _ _ X.wf (coPsetComplement_wf _)⟩

def mem (p : Pos) (X : CoPset) : Bool :=
  CoPsetRaw.ElemOf p X.tree

def complement (X : CoPset) : CoPset :=
  ⟨CoPsetRaw.Complement X.tree, coPsetComplement_wf _⟩

instance : HasSubset CoPset where
  Subset t1 t2 := ∀ (p : Pos), p ∈ t1 -> p ∈ t2

theorem subseteq_trans (X Y Z : CoPset) :
  X ⊆ Y ->
  Y ⊆ Z ->
  X ⊆ Z := by
  intros Hxy Hyz p Hx
  exact Hyz p (Hxy p Hx)

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
  | CoPsetRaw.leaf true => some P1
  | CoPsetRaw.node true _ _ => some P1
  | CoPsetRaw.leaf false => none
  | CoPsetRaw.node false l r =>
    match pickRaw l with
    | some i => some (i~0)
    | none => Option.map (λ i => i~1) (pickRaw r)

def CoPset.pick (X : CoPset) : Pos :=
  (CoPsetRaw.pickRaw X.tree).getD P1


-- Inverse suffix closure

/-- [suffixes q] is the set of all numbers [p] such that [q] is a suffix
of [p], when these numbers are viewed as sequences of bits. In other words, it
is the set of all numbers that have the suffix [q]. It is always an infinite
set. -/
def CoPsetRaw.suffixesRaw : Pos → CoPsetRaw
  | P1 => .leaf true
  | p~0 => CoPsetRaw.node' false (suffixesRaw p) (.leaf false)
  | p~1 => CoPsetRaw.node' false (.leaf false) (suffixesRaw p)

theorem coPsetSuffixes_wf p : coPset_wf (CoPsetRaw.suffixesRaw p) := by
  induction p <;> simp [CoPsetRaw.suffixesRaw, coPset_wf] <;>
  apply node'_wf <;> simp_all [coPset_wf]

def suffixes (p : Pos) : CoPset :=
  ⟨CoPsetRaw.suffixesRaw p, coPsetSuffixes_wf p⟩
theorem elem_suffixes p q : p ∈ suffixes q <-> ∃ q', p = q' ++ q := by
  constructor
  · induction q generalizing p with
    | xI q IH =>
      simp [suffixes, CoPsetRaw.suffixesRaw]
      simp_all [Membership.mem]; rewrite [elem_of_node]
      intros Hin; cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      specialize (IH _ Hin)
      rcases IH with ⟨ q', Heq ⟩
      exists q'; rewrite [Heq]; simp [HAppend.hAppend, Pos.app]
    | xO q IH =>
      simp [suffixes, CoPsetRaw.suffixesRaw]
      simp_all [Membership.mem]; rewrite [elem_of_node]
      intros Hin; cases p <;> simp [CoPsetRaw.ElemOf] at Hin
      specialize (IH _ Hin)
      rcases IH with ⟨ q', Heq ⟩
      exists q'; rewrite [Heq]; simp [HAppend.hAppend, Pos.app]
    | xH =>
      simp [suffixes, CoPsetRaw.suffixesRaw]
      simp [Membership.mem, CoPsetRaw.ElemOf]
      simp [HAppend.hAppend, Pos.app]
  · intros Heq; rcases Heq with ⟨ q', Heq ⟩; rewrite [Heq]
    simp [suffixes, Membership.mem]
    induction q generalizing p <;> simp [CoPsetRaw.suffixesRaw] <;> try rewrite [elem_of_node] <;>
    simp_all [HAppend.hAppend, Pos.app, CoPsetRaw.ElemOf]
    cases q' <;> simp [CoPsetRaw.ElemOf]

/-- Splitting a set -/

/- Every infinite [X : CoPset] can be split into two disjoint parts, which are
infinite sets. Use the functions [splitLeft] and [splitRight] if you
need a constructive witness. -/

def l_raw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node true (CoPsetRaw.leaf true) (CoPsetRaw.leaf false)
  | CoPsetRaw.node b l r => CoPsetRaw.node' b (l_raw l) (l_raw r)

def r_raw : CoPsetRaw → CoPsetRaw
  | CoPsetRaw.leaf false => CoPsetRaw.leaf false
  | CoPsetRaw.leaf true => CoPsetRaw.node false (CoPsetRaw.leaf false) (CoPsetRaw.leaf true)
  | CoPsetRaw.node _ l r => CoPsetRaw.node' false (r_raw l) (r_raw r)

theorem l_wf t : coPset_wf (l_raw t) := by
  induction t with
  | leaf b => cases b <;> simp [l_raw, coPset_wf]
  | node b l r => simp [l_raw]; apply node'_wf <;> assumption

theorem r_wf t : coPset_wf (r_raw t) := by
  induction t with
  | leaf b => cases b <;> simp [r_raw, coPset_wf]
  | node b l r => simp [r_raw]; apply node'_wf <;> assumption

def splitLeft (X : CoPset) : CoPset :=
  ⟨l_raw X.tree, l_wf _⟩

def splitRight (X : CoPset) : CoPset :=
  ⟨r_raw X.tree, r_wf _⟩

def split (X : CoPset) : CoPset × CoPset :=
  (splitLeft X, splitRight X)

end CoPset

instance : Iris.Std.Disjoint CoPset where
  disjoint s t := ∀ p, p ∈ s -> p ∈ t -> False

@[symm]
theorem disj_symm (E1 E2 : CoPset) :
  E1 ## E2 -> E2 ## E1 := by
  exact fun Hdisj p HE1 HE2 => Hdisj p HE2 HE1
