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

-- `no_index` and the `unif_hint`s are a workaround for non-reducible boolean operations
instance [t : T] : TCIte (no_index true) T U := TCIte.t (t := t)
instance [u : U] : TCIte (no_index false) T U := TCIte.e (u := u)

unif_hint (b : Bool) where
  |- false || b ≟ b
unif_hint (b : Bool) where
  |- true || b ≟ true
unif_hint (b : Bool) where
  |- false && b ≟ false
unif_hint (b : Bool) where
  |- true && b ≟ b

end Iris.Std
