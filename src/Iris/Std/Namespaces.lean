import Iris.Std.CoPset
import Iris.Std.Positives

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
  simp [nclose, ndot]
  rewrite [CoPset.elem_suffixes]; rewrite [CoPset.elem_suffixes]
  rintro ⟨ q, Heq ⟩; rewrite [Heq]
  obtain ⟨ q', Heq ⟩ :=
    (Pos.flatten_suffix N (ndot N x) (by exists [Pos.Countable.encode x]))
  exists (q ++ q')
  rewrite [Pos.app_assoc_l.assoc, <- Heq]
  rfl

theorem nclose_subseteq' [Pos.Countable A] E (N : Namespace) (x : A) : (↑N : CoPset) ⊆ E -> (↑(N.@x) : CoPset) ⊆ E := by
  intro Hsubset
  apply CoPset.subseteq_trans
  apply nclose_subseteq
  assumption

theorem ndot_ne_disjoint [Pos.Countable A] (N : Namespace) (x y : A) :
  x ≠ y -> N.@x ## N.@y := by
  intros Hxy p; simp [nclose];
  rewrite [CoPset.elem_suffixes]; rewrite [CoPset.elem_suffixes]
  rintro ⟨ qx, Heqx ⟩; rintro ⟨ qy, Heqy ⟩
  rewrite [Heqx] at Heqy
  have := Pos.flatten_suffix_eq qx qy (N.@x) (N.@y) (by simp [ndot, List.length]) Heqy
  simp [ndot, Pos.Countable.encode] at this
  have := (Pos.encode_inj.inj _ _ this)
  exact Hxy this

theorem ndot_preserve_disjoint_l [Pos.Countable A] (N : Namespace) (E : CoPset) (x : A) :
  ↑N ## E → ↑(N.@x) ## E := by
  have := nclose_subseteq N x
  simp [Iris.Std.disjoint]; simp [Subset] at this
  intros Hdisj p; exact fun a_1 => Hdisj p (this p a_1)

theorem ndot_preserve_disjoint_r [Pos.Countable A] (N : Namespace) (E : CoPset) (x : A) :
  E ## ↑N → E ## ↑(N.@x) := by
  intros
  symm
  apply ndot_preserve_disjoint_l
  symm; assumption

theorem CoPset.difference_difference (X1 X2 X3 Y : CoPset) :
  (X1 \ X2) \ X3 ## Y -> X1 \ (X2 ∪ X3) ## Y := by
  -- Long term, this should be solvable with one automatic tactic
  intros Hdisj p Hnin Hin
  apply (Hdisj p _ Hin)
  obtain ⟨ HX1, HXU ⟩ := (in_diff p X1 (X2 ∪ X3)).1 Hnin
  obtain ⟨ HX2, HX3 ⟩ := (not_in_union p X2 X3).1 HXU
  simp [in_diff]; simp [*]
