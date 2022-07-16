namespace Prod

def allSome? : Option α × Option β → Option (α × β)
  | (some x, some y) => some (x, y)
  | _                => none

def mapAll (f : α → β) : α × α → β × β
  | (x, y) => (f x, f y)

def mapAllM [Monad M] (f : α → M β) : α × α → M (β × β)
  | (x, y) => do return (← f x, ← f y)

end Prod
