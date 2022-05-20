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


/-- Type class instances search requires the condition to be fully reduced. -/
class inductive TCIte : Bool → Sort u → Sort v → Sort (max (u + 1) (v + 1))
  | t [t : T] : TCIte true T U
  | e [u : U] : TCIte false T U

instance [t : T] : TCIte true T U := TCIte.t (t := t)
instance [u : U] : TCIte false T U := TCIte.e (u := u)

end Iris.Std
