inductive Pos where
| xI : Pos -> Pos
| xO : Pos -> Pos
| xH : Pos
deriving Repr, DecidableEq

notation "P1" => Pos.xH

syntax term " ~1" : term
syntax term " ~0" : term

macro_rules
  | `($p ~1) => `(Pos.xI $p)
  | `($p ~0) => `(Pos.xO $p)

def Pos.toNat : Pos → Nat
  | Pos.xH     => 1
  | Pos.xO p   => 2 * p.toNat
  | Pos.xI p   => 2 * p.toNat + 1

instance : CoeOut Pos Nat where coe := Pos.toNat

instance : LT Pos where
  lt a b := a.toNat < b.toNat

instance : LE Pos where
  le a b := a.toNat ≤ b.toNat

def Pos.compare (a b : Pos) : Ordering :=
  Ord.compare (a.toNat) (b.toNat)

def Pos.succ : Pos → Pos
  | p~1     => (succ p)~0
  | p~0   => p~1
  | P1   => P1~0

def Pos.ofNat (n : Nat) : Pos :=
match n with
| 0 => P1
| 1 => P1
| (n + 1) => Pos.succ (.ofNat n)

instance : OfNat Pos n where ofNat := Pos.ofNat n

mutual
def Pos.add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (.add p q)~1
    | p~1, P1 => (.succ p)~0
    | p~0, q~1 => (.add p q)~1
    | p~0, q~0 => (.add p q)~0
    | p~0, P1 => p~1
    | P1, q~1 => (.succ q)~0
    | P1, q~0 => q~1
    | P1, P1 => P1~0

def add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, P1 => (.succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (.add p q)~1
    | p~0, P1 => (.succ p)~0
    | P1, q~1 => (.succ q)~1
    | P1, q~0 => (.succ q)~0
    | P1, P1 => P1~1
end

instance : Add Pos where add := Pos.add

def Pos.mul : Pos → Pos → Pos
  | P1,     q       => q
  | p~0,   q       => .xO (.mul p q)
  | p~1,   q       => .add (.xO (.mul p q)) q

instance : Mul Pos where mul := Pos.mul

def Pos.app (p1 p2 : Pos) : Pos :=
  match p2 with
  | P1 => p1
  | p2~0 => (.app p1 p2)~0
  | p2~1 => (.app p1 p2)~1

instance : HAppend Pos Pos Pos where hAppend := Pos.app

instance app_assoc_l : @Std.Associative Pos (.++.) where
  assoc _ _ p := by induction p <;> simp_all [HAppend.hAppend, Pos.app]

instance app_1_l : @Std.LawfulLeftIdentity Pos Pos (Pos.app) P1 where
  left_id p := by induction p <;> simp [Pos.app] <;> assumption

def reverse_go (p1 p2 : Pos) : Pos :=
  match p2 with
  | P1 => p1
  | p2~0 => reverse_go (p1~0) p2
  | p2~1 => reverse_go (p1~1) p2
def Pos.reverse : Pos → Pos := reverse_go P1

theorem reverse_go_app (p1 p2 p3 : Pos) :
  reverse_go p1 (p2 ++ p3) = reverse_go p1 p3 ++ reverse_go P1 p2 := by
  have helper : ∀ p1 p2 p3, reverse_go (p2 ++ p3) p1 = p2 ++ (reverse_go p3 p1) := by
    intro p1
    induction p1 with
    | xI p1 IH =>
      intro p2 p3
      apply (IH _ (_~1))
    | xO p1 IH =>
      intro p2 p3
      apply (IH _ (_~0))
    | xH =>
      intro p2 p3; rfl

  induction p3 generalizing p1 p2 with
  | xI p3 IH =>
    simp [reverse_go, HAppend.hAppend, Pos.app]
    exact IH (p1~1) p2
  | xO p3 IH =>
    simp [reverse_go, HAppend.hAppend, Pos.app]
    exact IH (p1~0) p2
  | xH =>
    simp [reverse_go]
    rewrite [<- helper]
    simp [HAppend.hAppend, Pos.app]

theorem reverse_app (p1 p2 : Pos) :
  Pos.reverse (p1 ++ p2) = .reverse p2 ++ .reverse p1 := by
  simp [Pos.reverse]; apply reverse_go_app
theorem reverse_x0 p : .reverse (p~0) = (P1~0) ++ .reverse p := by
  apply (reverse_app p (P1~0))
theorem reverse_xI p : .reverse (p~1) = (P1~1) ++ .reverse p := by
  apply (reverse_app p (P1~1))

def Pos.dup  : Pos -> Pos
| P1 => P1
| p~0 => (dup p)~0~0
| p~1 => (dup p)~1~1

def positives_flatten_go (xs : List Pos) (acc : Pos) : Pos :=
  match xs with
  | [] => acc
  | x :: xs => positives_flatten_go xs (acc~1~0 ++ Pos.reverse (Pos.dup x))
def positives_flatten (xs : List Pos) : Pos :=
  positives_flatten_go xs P1

def positives_unflatten_go
        (p : Pos)
        (acc_xs : List Pos)
        (acc_elm : Pos)
  : Option (List Pos) :=
  match p with
  | P1 => some acc_xs
  | p'~0~0 => positives_unflatten_go p' acc_xs (acc_elm~0)
  | p'~1~1 => positives_unflatten_go p' acc_xs (acc_elm~1)
  | p'~1~0 => positives_unflatten_go p' (acc_elm :: acc_xs) P1
  | _ => none

def positives_unflatten (p : Pos) : Option (List Pos) :=
  positives_unflatten_go p [] P1

theorem positives_flatten_go_app xs acc :
    positives_flatten_go xs acc = acc ++ positives_flatten_go xs P1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs IH =>
    simp [positives_flatten_go]
    rewrite [IH]
    rewrite [IH ((Pos.xI P1).xO ++ x.dup.reverse)]
    ac_nf
    rewrite [<- app_assoc_l.assoc]
    rewrite [<- app_assoc_l.assoc]
    rewrite [<- app_assoc_l.assoc]
    simp [HAppend.hAppend, Pos.app]

theorem positives_unflatten_go_app (p : Pos) suffix xs acc :
  positives_unflatten_go (suffix ++ Pos.reverse (Pos.dup p)) xs acc =
  positives_unflatten_go suffix xs (acc ++ p) := by
  induction p generalizing suffix acc with
  | xI p IH =>
    simp [Pos.dup]
    rewrite [reverse_xI]; rewrite [reverse_xI]
    rewrite [<- app_assoc_l.assoc]; rewrite [<- app_assoc_l.assoc]
    rewrite [IH]
    rfl
  | xO p IH =>
    simp [Pos.dup]
    rewrite [reverse_x0]; rewrite [reverse_x0]
    rewrite [<- app_assoc_l.assoc]; rewrite [<- app_assoc_l.assoc]
    rewrite [IH]
    rfl
  | xH => rfl

theorem positives_unflatten_flatten_go suffix xs acc :
  positives_unflatten_go (suffix ++ positives_flatten_go xs P1) acc P1 =
  positives_unflatten_go suffix (xs ++ acc) P1 := by
  revert suffix acc
  induction xs with
  | nil => intros suff acc; rfl
  | cons x xs IH =>
    simp [positives_flatten_go]
    intros suff acc
    rewrite [positives_flatten_go_app]
    rewrite [<- app_assoc_l.assoc]
    rewrite [IH]
    rewrite [<- app_assoc_l.assoc]
    rewrite [positives_unflatten_go_app]
    simp [HAppend.hAppend, Pos.app]
    rewrite [app_1_l.left_id]
    rfl

theorem positives_unflatten_flatten xs :
  positives_unflatten (positives_flatten xs) = some xs := by
  unfold positives_flatten; unfold positives_unflatten
  rewrite [<- (app_1_l.left_id (positives_flatten_go xs P1))]
  have := positives_unflatten_flatten_go P1 xs []
  simp [HAppend.hAppend] at this
  rewrite [this]
  simp [Append.append]
  rfl

theorem positives_flatten_app xs ys :
  positives_flatten (xs ++ ys) = positives_flatten xs ++ positives_flatten ys := by
  unfold positives_flatten
  induction xs generalizing ys with
  | nil =>
    simp [positives_flatten_go]; simp [HAppend.hAppend]
    rewrite [app_1_l.left_id (positives_flatten_go ys P1)]; rfl
  | cons x xs IH =>
    simp [positives_flatten_go]
    rewrite [positives_flatten_go_app]; rewrite [positives_flatten_go_app xs]
    rewrite [IH]
    simp [app_assoc_l.assoc]

theorem positives_flatten_suffix (l k : List Pos) :
  l <:+ k -> ∃ q, positives_flatten k = q ++ positives_flatten l := by
  rintro ⟨ l', Heq ⟩; rewrite [<- Heq]
  exists (positives_flatten l')
  apply positives_flatten_app
