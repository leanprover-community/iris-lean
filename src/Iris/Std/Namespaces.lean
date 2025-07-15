import Iris.Std.CoPset
import Iris.Std.Positives

class Countable (A : Type) where
  encode : A -> Pos
  decode : Pos -> Option A
  decode_encode x : decode (encode x) = some x

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
  Pos.ofNat (Countable.encode x) :: N

def nclose (N : Namespace) : CoPset :=
  CoPset.suffixes ((positives_flatten N))

instance : CoeOut Namespace CoPset where coe := nclose

infix:70 ".@" => ndot

instance ndisjoint : Disjoint Namespace where
  disjoint N1 N2 := nclose N1 ## nclose N2

theorem nclose_root : ↑nroot = CoPset.full := by rfl

theorem nclose_subseteq [Countable A] N (x : A) : (↑N.@x : CoPset) ⊆ (↑N : CoPset) := by
  intros p
  simp [nclose, ndot]
  rewrite [CoPset.elem_suffixes]; rewrite [CoPset.elem_suffixes]
  rintro ⟨ q, Heq ⟩; rewrite [Heq]
  exists (q ++ Pos.ofNat (Countable.encode x))
