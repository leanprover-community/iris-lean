namespace Iris.Std

abbrev Relation (α : Type) := α → α → Prop


class Reflexive (R : Relation α) where
  reflexivity {x : α} : R x x
export Reflexive (reflexivity)

class Transitive (R : Relation α) where
  transitivity {x y z : α} : R x y → R y z → R x z
export Transitive (transitivity)

class PreOrder (R : Relation α) extends Reflexive R, Transitive R


class Comm (R : Relation α) (f : β → β → α) : Prop where
  comm {x y : β} : R (f x y) (f y x)
export Comm (comm)

class LeftId (R : Relation α) (i : α) (f : α → α → α) : Prop where
  left_id {x : α} : R (f i x) x
export LeftId (left_id)

class RightId (R : Relation α) (i : α) (f : α → α → α) : Prop where
  right_id {x : α} : R (f x i) x
export RightId (right_id)

class Assoc (R : Relation α) (f : α → α → α) : Prop where
  assoc {x y z : α} : R (f x (f y z)) (f (f x y) z)
export Assoc (assoc)

class AntiSymm (R S : Relation α) : Prop where
  anti_symm {x y : α} : S x y → S y x → R x y
export AntiSymm (anti_symm)

end Iris.Std
