namespace Iris.Std

set_option checkBinderAnnotations false

/-- Type class version of `False`, i.e. a type class with no instances. -/
class inductive TCFalse


/-- Type class version of `True`, i.e. a type class with a trivial instance without arguments. -/
class inductive TCTrue
  | t

instance : TCTrue := TCTrue.t


/-- Type class version of `Or`, i.e. a type class for which an instance exists if an instance of any
of the listed type classes is present. -/
class inductive TCOr (T U : Sort _)
  | l : [T] → TCOr T U
  | r : [U] → TCOr T U

instance [t : T] : TCOr T U := @TCOr.l T U t
instance [u : U] : TCOr T U := @TCOr.r T U u


/-- Type class version of `Ite`, i.e. a type class for which an instance exists if the boolean
condition is `true` and an instance of `T` is present or the condition is `false` and an instance
of `U` is present.

Note that type class instance search requires the condition to be fully reduced. -/
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
