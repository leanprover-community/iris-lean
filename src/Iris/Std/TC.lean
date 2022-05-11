namespace Iris.Std

set_option checkBinderAnnotations false

class inductive TCFalse


class inductive TCTrue
  | t

instance : TCTrue := TCTrue.t


class inductive TCOr (T U : Sort _)
  | l : [T] → TCOr T U
  | r : [U] → TCOr T U

instance [t : T] : TCOr T U := @TCOr.l T U t
instance [u : U] : TCOr T U := @TCOr.r T U u


/-- Type class instances search requires `c` to be fully reduced. -/
class inductive TCIte (c : Bool) (T U : Sort _)
  | t : (_ : c = true) → [T] → TCIte c T U
  | e : (_ : c = false) → [U] → TCIte c T U

instance [t : T] : TCIte true T U := @TCIte.t true T U (by rfl) t
instance [u : U] : TCIte false T U := @TCIte.e false T U (by rfl) u

end Iris.Std
