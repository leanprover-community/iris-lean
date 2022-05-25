namespace List

@[reducible]
def isEmptyR : List α → Bool
  | []     => true
  | _ :: _ => false

@[reducible]
def eraseIdxR : (as : List α) → Fin as.length → List α
  | _ :: as, ⟨0, _⟩     => as
  | a :: as, ⟨i + 1, h⟩ => a :: eraseIdxR as ⟨i, Nat.le_of_succ_le_succ h⟩

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
  | a :: _ , ⟨0, _⟩     => a
  | a :: as, ⟨i + 1, h⟩ => getR as ⟨i, Nat.le_of_succ_le_succ h⟩

@[specialize]
def partitionIndices (as : List α) (p : Nat → Bool) : List α × List α :=
  go as 0
where
  go (as : List α) (idx : Nat) : List α × List α :=
    match as with
    | []      => ([], [])
    | a :: as =>
      let as' := go as (idx + 1)
      if p idx then
        as'.map (a :: ·) (·)
      else
        as'.map (·) (a :: ·)

end List
