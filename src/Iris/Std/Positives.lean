import Iris.Std.Classes
/-- [Pos] is a datatype representing the strictly positive integers
   in a binary way. Starting from 1 (represented by [xH]), one can
   add a new least significant digit via [xO] (digit 0) or [xI] (digit 1). -/

inductive Pos where
| xI : Pos -> Pos
| xO : Pos -> Pos
| xH : Pos
deriving Repr, DecidableEq

namespace Pos

/- Postfix notation for positive numbers, which allows mimicking
    the position of bits in a big-endian representation.
    For instance, we can write [P1~1~0] instead of [(xO (xI xH))]
    for the number 6 (which is 110 in binary notation). -/

notation "P1" => xH

syntax term "~1" : term
syntax term "~0" : term

macro_rules
  | `($p ~1) => `(xI $p)
  | `($p ~0) => `(xO $p)

@[app_unexpander xI]
def unexpand_Pos_xI : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `($p~1)
  | _ => throw ()

@[app_unexpander xO]
def unexpand_Pos_x0 : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `($p~0)
  | _ => throw ()

-- Operations over positive numbers

/-- Successor -/
def succ : Pos → Pos
  | p~1     => (succ p)~0
  | p~0   => p~1
  | P1   => P1~0

mutual
/-- Addition -/
def add x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, P1 => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, P1 => p~1
    | P1, q~1 => (succ q)~0
    | P1, q~0 => q~1
    | P1, P1 => P1~0

def add_carry x y :=
  match x, y with
    | p~1, q~1 => (add_carry p q)~1
    | p~1, q~0 => (add_carry p q)~0
    | p~1, P1 => (succ p)~1
    | p~0, q~1 => (add_carry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, P1 => (succ p)~0
    | P1, q~1 => (succ q)~1
    | P1, q~0 => (succ q)~0
    | P1, P1 => P1~1
end

instance : Add Pos where add := Pos.add

/-- Multiplication -/
def mul : Pos → Pos → Pos
  | P1,     q       => q
  | p~0,   q       => xO (mul p q)
  | p~1,   q       => add (xO (mul p q)) q

instance : Mul Pos where mul := Pos.mul


/-- Coercions to and from Nat -/

def toNat : Pos → Nat
  | xH     => 1
  | xO p   => 2 * p.toNat
  | xI p   => 2 * p.toNat + 1

instance : CoeOut Pos Nat where coe := Pos.toNat

def compare (a b : Pos) : Ordering :=
  Ord.compare (a.toNat) (b.toNat)

/- 0%nat gets mapped to 1%pos. -/
def ofNat (n : Nat) : Pos :=
match n with
| 0 => P1
| 1 => P1
| (n + 1) => succ (ofNat n)

instance : OfNat Pos n where ofNat := Pos.ofNat n


/- Since [Pos] represents lists of bits, we define list operations
  on it. These operations are in reverse, as positives are treated as snoc
  lists instead of cons lists. -/
def app (p1 p2 : Pos) : Pos :=
  match p2 with
  | P1 => p1
  | p2~0 => (app p1 p2)~0
  | p2~1 => (app p1 p2)~1

@[reducible]
instance : HAppend Pos Pos Pos where hAppend := Pos.app

instance app_assoc_l : @Std.Associative Pos (.++.) where
  assoc _ _ p := by induction p <;> simp_all [HAppend.hAppend, app]

@[simp]
theorem app_1_left_id (p : Pos) : app P1 p = p := by
  induction p <;> simp [HAppend.hAppend, app] <;> assumption

instance app_1_l : @Std.LawfulLeftIdentity Pos Pos (app) P1 where
  left_id p := app_1_left_id p

def reverse_go (p1 p2 : Pos) : Pos :=
  match p2 with
  | P1 => p1
  | p2~0 => reverse_go (p1~0) p2
  | p2~1 => reverse_go (p1~1) p2
def reverse : Pos → Pos := reverse_go P1

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
    simp [reverse_go, HAppend.hAppend, app]
    exact IH (p1~1) p2
  | xO p3 IH =>
    simp [reverse_go, HAppend.hAppend, app]
    exact IH (p1~0) p2
  | xH =>
    simp [reverse_go]
    rewrite [<- helper]
    simp [HAppend.hAppend, app]

theorem reverse_app (p1 p2 : Pos) :
  reverse (p1 ++ p2) = reverse p2 ++ reverse p1 := by
  simp [reverse]; apply reverse_go_app
theorem reverse_x0 p : reverse (p~0) = (P1~0) ++ reverse p := by
  apply (reverse_app p (P1~0))
theorem reverse_xI p : reverse (p~1) = (P1~1) ++ reverse p := by
  apply (reverse_app p (P1~1))

/-- Duplicate the bits of a positive, i.e. 1~0~1 -> 1~0~0~1~1 and
      1~1~0~0 -> 1~1~1~0~0~0~0 -/
def dup  : Pos -> Pos
| P1 => P1
| p~0 => (dup p)~0~0
| p~1 => (dup p)~1~1


/-- These next functions allow to efficiently encode lists of positives (bit
strings) into a single positive and go in the other direction as well. This is
for example used for the countable instance of lists and in namespaces.
The main functions are [flatten] and [unflatten]. -/

def flatten_go (xs : List Pos) (acc : Pos) : Pos :=
  match xs with
  | [] => acc
  | x :: xs => flatten_go xs (acc~1~0 ++ reverse (dup x))

/-- Flatten a list of positives into a single positive by duplicating the bits
of each element, so that:

- [0 -> 00]
- [1 -> 11]

and then separating each element with [10]. -/
def flatten (xs : List Pos) : Pos :=
  flatten_go xs P1

def unflatten_go
        (p : Pos)
        (acc_xs : List Pos)
        (acc_elm : Pos)
  : Option (List Pos) :=
  match p with
  | P1 => some acc_xs
  | p'~0~0 => unflatten_go p' acc_xs (acc_elm~0)
  | p'~1~1 => unflatten_go p' acc_xs (acc_elm~1)
  | p'~1~0 => unflatten_go p' (acc_elm :: acc_xs) P1
  | _ => none

/-- Unflatten a positive into a list of positives, assuming the encoding
used by [flatten]. -/
def unflatten (p : Pos) : Option (List Pos) :=
  unflatten_go p [] P1

theorem flatten_go_app xs acc :
    flatten_go xs acc = acc ++ flatten_go xs P1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs IH =>
    simp [flatten_go]
    rewrite [IH]
    rewrite [IH (P1~1~0 ++ x.dup.reverse)]
    simp only [<- app_assoc_l.assoc]
    simp [HAppend.hAppend, app]

theorem unflatten_go_app (p : Pos) suffix xs acc :
  unflatten_go (suffix ++ reverse (dup p)) xs acc =
  unflatten_go suffix xs (acc ++ p) := by
  induction p generalizing suffix acc with
  | xI p IH =>
    simp [dup]
    rewrite [reverse_xI]; rewrite [reverse_xI]
    simp only [<- app_assoc_l.assoc]
    rewrite [IH]
    rfl
  | xO p IH =>
    simp [dup]
    rewrite [reverse_x0]; rewrite [reverse_x0]
    simp only [<- app_assoc_l.assoc]
    rewrite [IH]
    rfl
  | xH => rfl

theorem unflatten_flatten_go suffix xs acc :
  unflatten_go (suffix ++ flatten_go xs P1) acc P1 =
  unflatten_go suffix (xs ++ acc) P1 := by
  revert suffix acc
  induction xs with
  | nil => intros suff acc; rfl
  | cons x xs IH =>
    simp [flatten_go]
    intros suff acc
    rewrite [flatten_go_app]
    rewrite [<- app_assoc_l.assoc]
    rewrite [IH]
    rewrite [<- app_assoc_l.assoc]
    rewrite [unflatten_go_app]
    simp [HAppend.hAppend, app]
    rfl

theorem unflatten_flatten xs :
  unflatten (flatten xs) = some xs := by
  unfold flatten; unfold unflatten
  rewrite [<- (app_1_l.left_id (flatten_go xs P1))]
  have := unflatten_flatten_go P1 xs []
  simp [HAppend.hAppend] at this
  simp [this, Append.append]
  rfl

theorem flatten_app xs ys :
  flatten (xs ++ ys) = flatten xs ++ flatten ys := by
  unfold flatten
  induction xs generalizing ys with
  | nil =>
    simp [flatten_go, HAppend.hAppend]; rfl
  | cons x xs IH =>
    simp [flatten_go]
    rewrite [flatten_go_app]; rewrite [flatten_go_app xs]
    rewrite [IH]
    simp [app_assoc_l.assoc]

theorem flatten_cons x xs :
  flatten (x :: xs)
  = P1~1~0 ++ reverse (dup x) ++ flatten xs := by
  have heq : x :: xs = [x] ++ xs := rfl
  rw [heq]
  apply flatten_app

theorem flatten_suffix (l k : List Pos) :
  l <:+ k -> ∃ q, flatten k = q ++ flatten l := by
  rintro ⟨ l', Heq ⟩; rewrite [<- Heq]
  exists (flatten l')
  apply flatten_app

instance app_inj (p : Pos) : Iris.Std.Injective (.++ p) where
  inj := by
    intros a a' Heq
    induction p <;> simp_all [HAppend.hAppend, app]

theorem reverse_involutive p : reverse (reverse p) = p := by
  induction p with
  | xI p IH =>
    rewrite [reverse_xI, reverse_app, IH]; rfl
  | xO p IH =>
    rewrite [reverse_x0, reverse_app, IH]; rfl
  | xH => rfl

instance rev_inj : Iris.Std.Injective reverse where
  inj := by
    intros p q Heq
    rewrite [<- reverse_involutive p]
    rewrite [<- reverse_involutive q]
    simp [Heq]

theorem dup_app p q : dup (p ++ q) = dup p ++ dup q := by
  induction q generalizing p <;>
  simp_all [HAppend.hAppend, app, dup]

theorem reverse_dup (p : Pos) :
  reverse (dup p) = dup (reverse p) := by
  have hdup := dup_app
  have hassoc := app_assoc_l.assoc
  simp [HAppend.hAppend, app] at hdup hassoc
  induction p with
  | xI p IH =>
    simp [dup]
    simp [reverse_xI, HAppend.hAppend, app]
    rewrite [<- hassoc, IH, hdup]
    rfl
  | xO p IH =>
    simp [dup]
    simp [reverse_x0, HAppend.hAppend, app]
    rewrite [<- hassoc, IH, hdup]
    rfl
  | xH => rfl

theorem dup_suffix_eq p q s1 s2 :
  s1~1~0 ++ dup p = s2~1~0 ++ dup q -> p = q := by
  induction p generalizing q with
  | xI p IH =>
    intros Heq
    cases q <;> simp_all [HAppend.hAppend, app, dup] <;> rename Pos => q
    rewrite [IH q]; rfl; simp [Heq]
  | xO p IH =>
    intros Heq
    cases q <;> simp_all [HAppend.hAppend, app, dup] <;> rename Pos => q
    rewrite [IH q]; rfl; simp [Heq]
  | xH => cases q <;> simp [HAppend.hAppend, app, dup]

theorem flatten_suffix_eq p1 p2 (xs ys : List Pos) :
  List.length xs = List.length ys ->
  p1 ++ flatten xs = p2 ++ flatten ys ->
  xs = ys := by
  induction xs generalizing p1 p2 ys with
  | nil => simp; intros Hlen _; apply List.eq_nil_of_length_eq_zero; symm; assumption
  | cons x xs IH =>
    rcases ys with _ | ⟨ y, ys ⟩; intros Hlen _; simp [List.length] at Hlen;
    rewrite [flatten_cons]
    rewrite [<- app_assoc_l.assoc]; rewrite [<- app_assoc_l.assoc]
    rewrite [flatten_cons]
    rewrite [<- app_assoc_l.assoc]; rewrite [<- app_assoc_l.assoc]
    intros Hlen Hl
    have Heq : xs = ys := by apply IH; simp_all []; apply Hl
    rewrite [Heq]; congr; rewrite [Heq] at Hl
    replace Hl := (app_inj (flatten ys)).inj _ _ Hl
    rewrite [reverse_dup] at Hl
    rewrite [reverse_dup] at Hl
    replace Hl := (dup_suffix_eq _ _ p1 p2 Hl)
    apply (rev_inj.inj _ _ Hl)


class Countable (A : Type) where
  encode : A -> Pos
  decode : Pos -> Option A
  decode_encode x : decode (encode x) = some x

instance some_inj {A} : Iris.Std.Injective (@some A) where
  inj := by intros x y; rintro ⟨⟩; rfl

instance encode_inj [c : Countable A] : Iris.Std.Injective (c.encode) where
  inj := by
    intros x y Hxy; apply some_inj.inj
    rewrite [<- c.decode_encode x, Hxy, c.decode_encode]
    rfl

instance [Countable A] : Countable (List A) where
  encode xs := Pos.flatten (List.map Countable.encode xs)
  decode p := do
    let positives ← (Pos.unflatten p);
    List.mapM Countable.decode positives
  decode_encode := by
    intros xs
    rewrite [Pos.unflatten_flatten]; simp
    induction xs with
    | nil => rfl
    | cons x xs IH =>
      simp [List.map]; rewrite [IH]; rewrite [Countable.decode_encode]; simp

instance : Countable Pos where
  encode := id
  decode := some
  decode_encode _ := rfl

end Pos
