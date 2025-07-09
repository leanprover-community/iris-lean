import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.Updates

abbrev discrete_fun_insert [DecidableEq A] {B : A → Type}
  (x : A) (y : B x) (f : ∀ a, B a) : ∀ a, B a := λ x' =>
  if h : (x = x') then Eq.ndrec y h else f x'

class unit (A : Type) where ε : A

def discrete_fun_singleton [DecidableEq A] {B : A -> Type} [i : ∀ a, Iris.UCMRA (B a)] (x : A) (y : B x) :
  ∀ a, B a := discrete_fun_insert x y (λ a => (i a).unit)
