import Iris.Std.CoPset
import Iris.Std.Positives

class Countable (A : Type) where
  encode : A -> Pos
  decode : Pos -> Option A
  decode_encode x : decode (encode x) = some x

instance some_inj {A} : Iris.Std.Injective (@some A) where
  inj := by intros x y; rintro ⟨⟩; rfl

instance encode_inj [c : Countable A] : Iris.Std.Injective (c.encode) where
  inj := by
    intros x y Hxy; apply some_inj.inj
    rewrite [<- c.decode_encode x, Hxy, c.decode_encode]
    rfl

instance [Countable A] : Countable (List A) where
  encode xs := positives_flatten (List.map Countable.encode xs)
  decode p := Option.bind (positives_unflatten p)
              (fun positives => List.mapM Countable.decode positives)
  decode_encode := by
    intros xs
    rewrite [positives_unflatten_flatten]; simp
    induction xs
    · rfl
    · simp [List.map]; rename_i a aa aaa aaaa; rewrite [aaaa];
      rewrite [Countable.decode_encode]; simp

instance : Countable Pos where
  encode := id
  decode := some
  decode_encode _ := rfl

abbrev Namespace := List Pos

instance : DecidableEq Namespace := by infer_instance
instance : Countable Namespace := by infer_instance

def nroot : Namespace := List.nil

def ndot [Countable A] (N : Namespace) (x : A) : Namespace :=
  (Countable.encode x) :: N

def nclose (N : Namespace) : CoPset :=
  CoPset.suffixes ((positives_flatten N))

instance : CoeOut Namespace CoPset where coe := nclose

infix:80 ".@" => ndot

instance ndisjoint : Iris.Std.Disjoint Namespace where
  disjoint N1 N2 := nclose N1 ## nclose N2

theorem nclose_root : ↑nroot = CoPset.full := by rfl

theorem nclose_subseteq [Countable A] N (x : A) : (↑N.@x : CoPset) ⊆ (↑N : CoPset) := by
  intros p
  simp [nclose, ndot]
  rewrite [CoPset.elem_suffixes]; rewrite [CoPset.elem_suffixes]
  rintro ⟨ q, Heq ⟩; rewrite [Heq]
  obtain ⟨ q', Heq ⟩ :=
    (positives_flatten_suffix N (ndot N x) (by exists [Countable.encode x]))
  exists (q ++ q')
  rewrite [app_assoc_l.assoc, <- Heq]
  rfl

theorem nclose_subseteq' [Countable A] E (N : Namespace) (x : A) : (↑N : CoPset) ⊆ E -> (↑(N.@x) : CoPset) ⊆ E := by
  intro Hsubset
  apply CoPset.subseteq_trans
  apply nclose_subseteq
  assumption

theorem ndot_ne_disjoint [Countable A] (N : Namespace) (x y : A) :
  x ≠ y -> N.@x ## N.@y := by
  intros Hxy p; simp [nclose];
  rewrite [CoPset.elem_suffixes]; rewrite [CoPset.elem_suffixes]
  rintro ⟨ qx, Heqx ⟩; rintro ⟨ qy, Heqy ⟩
  rewrite [Heqx] at Heqy
  have := positives_flatten_suffix_eq qx qy (N.@x) (N.@y) (by simp [ndot, List.length]) Heqy
  simp [ndot, Countable.encode] at this
  have := (encode_inj.inj _ _ this)
  exact Hxy this

theorem ndot_preserve_disjoint_l [Countable A] (N : Namespace) (E : CoPset) (x : A) :
  ↑N ## E → ↑(N.@x) ## E := by
  have := nclose_subseteq N x
  simp [Iris.Std.disjoint]; simp [Subset] at this
  intros Hdisj p; exact fun a_1 => Hdisj p (this p a_1)

theorem ndot_preserve_disjoint_r [Countable A] (N : Namespace) (E : CoPset) (x : A) :
  E ## ↑N → E ## ↑(N.@x) := by
  intros
  symm
  apply ndot_preserve_disjoint_l
  symm; assumption

theorem CoPset.difference_difference (X1 X2 X3 Y : CoPset) :
  (X1 \ X2) \ X3 ## Y -> X1 \ (X2 ∪ X3) ## Y := by
  -- Long term, this should be solvable with one automatic tactic
  intros Hdisj p Hnin Hin
  simp [SDiff.sdiff, CoPset.diff] at Hnin
  apply (Hdisj p _ Hin)
  obtain ⟨ HX1, HXU ⟩ := (in_diff p X1 (X2 ∪ X3)).1 Hnin
  obtain ⟨ HX2, HX3 ⟩ := (not_in_union p X2 X3).1 HXU
  simp [in_diff]; simp [*]
