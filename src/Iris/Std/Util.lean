namespace List

@[specialize]
def foldl1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | a :: l => l.foldl f a

@[specialize]
def foldr1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | [a]    => a
  | a :: l => f a (foldr1 f alt l)

end List
