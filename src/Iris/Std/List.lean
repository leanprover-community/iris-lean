namespace List

@[reducible]
def isEmptyR : List α → Bool
  | []     => true
  | _ :: _ => false

@[reducible]
def eraseIdxR : List α → Nat → List α
  | [], _          => []
  | _ :: as, 0     => as
  | a :: as, n + 1 => a :: eraseIdxR as n

@[specialize]
def foldl1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | a :: l => l.foldl f a

@[specialize]
def foldr1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | [a]    => a
  | a :: l => f a (foldr1 f alt l)

@[reducible]
def getR : (as : List α) → Fin as.length → α
  | a::as, ⟨0, _⟩ => a
  | a::as, ⟨Nat.succ i, h⟩ => getR as ⟨i, Nat.le_of_succ_le_succ h⟩

end List
