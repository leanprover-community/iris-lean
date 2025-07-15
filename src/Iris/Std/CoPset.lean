import Iris.Std.Positives

inductive CoPsetRaw where
  | leaf : Bool → CoPsetRaw
  | node : Bool → CoPsetRaw → CoPsetRaw → CoPsetRaw
deriving DecidableEq

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

def CoPsetRaw.node' (b : Bool) (l r : CoPsetRaw) : CoPsetRaw :=
  match b, l, r with
  | true, .leaf true, .leaf true => .leaf true
  | false, .leaf false, .leaf false => .leaf false
  | _, _, _ => .node b l r

theorem node'_wf b l r :
  coPset_wf l -> coPset_wf r -> coPset_wf (.node' b l r) := by
  cases b <;> rcases l with ⟨ ⟨⟩ ⟩ | _ <;> rcases r with ⟨ ⟨⟩ ⟩ | _ <;> simp [CoPsetRaw.node', coPset_wf]
  · exact fun a_6 a_7 => ⟨a_6, a_7⟩
  · exact fun a_6 a_7 => ⟨a_6, a_7⟩

open CoPsetRaw

def coPsetElemOfRaw : Pos → CoPsetRaw → Bool
  | _, leaf b => b
  | P1, node b _ _ => b
  | p~0, node _ l _ => coPsetElemOfRaw p l
  | p~1, node _ _ r => coPsetElemOfRaw p r
instance : Membership Pos CoPsetRaw  where
  mem := fun t p => coPsetElemOfRaw p t

theorem elem_of_node b l r (p : Pos) :
  (coPsetElemOfRaw p (CoPsetRaw.node' b l r)) = (coPsetElemOfRaw p (CoPsetRaw.node b l r)) := by
  cases p <;> cases b <;> rcases l with ⟨⟨⟩⟩ | _ <;> rcases r with ⟨⟨⟩⟩ | _ <;>
  simp [node', coPsetElemOfRaw]

def coPsetSingletonRaw : Pos → CoPsetRaw
  | P1 => node true (leaf false) (leaf false)
  | p~0 => node' false (coPsetSingletonRaw p) (leaf false)
  | p~1 => node' false (leaf false) (coPsetSingletonRaw p)

def coPsetUnionRaw : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf false, t => t
  | t, leaf false => t
  | leaf true, _ => leaf true
  | _, leaf true => leaf true
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 || b2) (coPsetUnionRaw l1 l2) (coPsetUnionRaw r1 r2)
instance : Union CoPsetRaw where union := coPsetUnionRaw

def coPsetIntersectionRaw : CoPsetRaw → CoPsetRaw → CoPsetRaw
  | leaf true, t => t
  | t, leaf true => t
  | leaf false, _ => leaf false
  | _, leaf false => leaf false
  | node b1 l1 r1, node b2 l2 r2 =>
    node' (b1 && b2) (coPsetIntersectionRaw l1 l2) (coPsetIntersectionRaw r1 r2)
instance : Inter CoPsetRaw where inter := coPsetIntersectionRaw

def coPsetComplementRaw : CoPsetRaw → CoPsetRaw
  | leaf b => leaf (!b)
  | node b l r => node' (!b) (coPsetComplementRaw l) (coPsetComplementRaw r)

theorem coPsetSingleton_wf p : coPset_wf (coPsetSingletonRaw p) := by
  induction p <;> simp_all [coPsetSingletonRaw, coPset_wf]
  · apply node'_wf; simp [coPset_wf]; assumption
  · apply node'_wf; assumption; simp [coPset_wf]

theorem coPsetUnion_wf t1 t2 :
  coPset_wf t1 -> coPset_wf t2 -> coPset_wf (t1 ∪ t2) := by
  revert t2; induction t1 with
  | leaf b =>
    intros t2 Hwf1 Hwf2; cases b <;> simp [Union.union, coPsetUnionRaw]
    · assumption
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [coPsetUnionRaw, coPset_wf]
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [Union.union, coPsetUnionRaw, coPset_wf]
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
    intros t2 Hwf1 Hwf2; cases b <;> simp [Inter.inter, coPsetIntersectionRaw]
    · rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [coPsetIntersectionRaw, coPset_wf]
    · assumption
  | node b l r IH1 IH2 =>
    intros t2 Hwf1 Hwf2; rcases t2 with ⟨⟨⟩⟩ | _ <;> simp [Inter.inter, coPsetIntersectionRaw, coPset_wf]
    · assumption
    · apply node'_wf
      · apply IH1; exact node_wf_l b l r Hwf1
        (expose_names; exact node_wf_l a a_1 a_2 Hwf2)
      · apply IH2; exact node_wf_r b l r Hwf1
        (expose_names; exact node_wf_r a a_1 a_2 Hwf2)

theorem coPsetComplement_wf t : coPset_wf (coPsetComplementRaw t) := by
  induction t with
  | leaf b => cases b <;> simp [coPsetComplementRaw, coPset_wf]
  | node b l r => cases b <;> simp [coPsetComplementRaw, coPset_wf] <;>
    apply node'_wf <;> assumption

structure CoPset where
  tree : CoPsetRaw
  wf : coPset_wf tree = true

instance : Membership Pos CoPset where mem E p := p ∈ E.tree

namespace CoPset

def empty : CoPset := ⟨CoPsetRaw.leaf false, rfl⟩
instance : EmptyCollection CoPset where emptyCollection := CoPset.empty

def full : CoPset := ⟨CoPsetRaw.leaf true, rfl⟩

def singleton (p : Pos) : CoPset :=
  ⟨coPsetSingletonRaw p, coPsetSingleton_wf p⟩

def union (X Y : CoPset) : CoPset :=
  ⟨coPsetUnionRaw X.tree Y.tree, coPsetUnion_wf _ _ X.wf Y.wf⟩
instance : Union CoPset where union := CoPset.union

def inter (X Y : CoPset) : CoPset :=
  ⟨coPsetIntersectionRaw X.tree Y.tree, coPsetIntersection_wf _ _ X.wf Y.wf⟩
instance : Inter CoPset where inter := CoPset.inter

def diff (X Y : CoPset) : CoPset :=
  ⟨coPsetIntersectionRaw X.tree (coPsetComplementRaw Y.tree), coPsetIntersection_wf _ _ X.wf (coPsetComplement_wf _)⟩

def mem (p : Pos) (X : CoPset) : Bool :=
  coPsetElemOfRaw p X.tree

def complement (X : CoPset) : CoPset :=
  ⟨coPsetComplementRaw X.tree, coPsetComplement_wf _⟩

instance : HasSubset CoPset where
  Subset t1 t2 := ∀ (p : Pos), p ∈ t1 -> p ∈ t2

theorem subseteq_trans (X Y Z : CoPset) :
  X ⊆ Y ->
  Y ⊆ Z ->
  X ⊆ Z := by
  intros Hxy Hyz p Hx
  exact Hyz p (Hxy p Hx)

def isFiniteRaw : CoPsetRaw → Bool
  | CoPsetRaw.leaf b => !b
  | CoPsetRaw.node _ l r => isFiniteRaw l && isFiniteRaw r

def isFinite (X : CoPset) : Bool :=
  isFiniteRaw X.tree

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

def suffixesRaw : Pos → CoPsetRaw
  | P1 => .leaf true
  | p~0 => .node' false (suffixesRaw p) (.leaf false)
  | p~1 => .node' false (.leaf false) (suffixesRaw p)

theorem coPsetSuffixes_wf p : coPset_wf (suffixesRaw p) := by
  induction p <;> simp [suffixesRaw, coPset_wf] <;>
  apply node'_wf <;> simp_all [coPset_wf]

def suffixes (p : Pos) : CoPset :=
  ⟨suffixesRaw p, coPsetSuffixes_wf p⟩
theorem elem_suffixes p q : p ∈ suffixes q <-> ∃ q', p = q' ++ q := by
  constructor
  · induction q generalizing p with
    | xI q IH =>
      simp [suffixes, suffixesRaw]
      simp_all [Membership.mem]; rewrite [elem_of_node]
      intros Hin; cases p <;> simp [coPsetElemOfRaw] at Hin
      specialize (IH _ Hin)
      rcases IH with ⟨ q', Heq ⟩
      exists q'; rewrite [Heq]; simp [HAppend.hAppend, Pos.app]
    | xO q IH =>
      simp [suffixes, suffixesRaw]
      simp_all [Membership.mem]; rewrite [elem_of_node]
      intros Hin; cases p <;> simp [coPsetElemOfRaw] at Hin
      specialize (IH _ Hin)
      rcases IH with ⟨ q', Heq ⟩
      exists q'; rewrite [Heq]; simp [HAppend.hAppend, Pos.app]
    | xH =>
      simp [suffixes, suffixesRaw]
      simp [Membership.mem, coPsetElemOfRaw]
      simp [HAppend.hAppend, Pos.app]
  · intros Heq; rcases Heq with ⟨ q', Heq ⟩; rewrite [Heq]
    simp [suffixes, Membership.mem]
    induction q generalizing p <;> simp [suffixesRaw] <;> try rewrite [elem_of_node] <;>
    simp_all [HAppend.hAppend, Pos.app, coPsetElemOfRaw]
    cases q' <;> simp [coPsetElemOfRaw]

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

class Disjoint (α : Type u) where
  disjoint : α -> α -> Prop

infix:70 " ## " => Disjoint.disjoint

instance : Disjoint CoPset where
  disjoint s t := ∀ p, p ∈ s -> p ∈ t -> False
