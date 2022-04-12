namespace Iris.Std.Classes

abbrev relation (A : Type) := A → A → Prop

class Equiv (A : Type) where
  equiv : relation A

infix:50 " ≡ " => Equiv.equiv

class Reflexive (R : relation A) where
  reflexivity : ∀ x : A, R x x

class Transitive (R : relation A) where
  transitivity : ∀ {x y z}, R x y → R y z → R x z

class PreOrder (R : relation A) extends Reflexive R, Transitive R

end Iris.Std.Classes
