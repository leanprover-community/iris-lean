namespace Iris.Std

abbrev Relation (α : Type) := α → α → Prop

class Equiv (α : Type) where
  equiv : Relation α

infix:50 " ≡ " => Equiv.equiv

class Reflexive (R : Relation α) where
  reflexivity : ∀ x : α, R x x

class Transitive (R : Relation α) where
  transitivity : ∀ {x y z}, R x y → R y z → R x z

class PreOrder (R : Relation α) extends Reflexive R, Transitive R

end Iris.Std
