namespace Prod

def mapAllM [Monad M] (f : α → M β) : α × α → M (β × β)
  | (x, y) => do return (← f x, ← f y)

end Prod
