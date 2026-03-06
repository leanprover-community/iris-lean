/-
Copyright (c) 2026 Remy Seassau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

abbrev P1 : Pos := xH
syntax term "~1" : term
syntax term "~0" : term

macro_rules
  | `($p ~1) => `(xI $p)
  | `($p ~0) => `(xO $p)

@[app_unexpander xI]
def unexpandPosXI : Lean.PrettyPrinter.Unexpander
  | `($_ $p) => `($p~1)
  | _ => throw ()

@[app_unexpander xO]
def unexpandPosXO : Lean.PrettyPrinter.Unexpander
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
    | p~1, q~1 => (addCarry p q)~0
    | p~1, q~0 => (add p q)~1
    | p~1, xH => (succ p)~0
    | p~0, q~1 => (add p q)~1
    | p~0, q~0 => (add p q)~0
    | p~0, xH => p~1
    | xH, q~1 => (succ q)~0
    | xH, q~0 => q~1
    | xH, xH => P1~0

def addCarry x y :=
  match x, y with
    | p~1, q~1 => (addCarry p q)~1
    | p~1, q~0 => (addCarry p q)~0
    | p~1, xH => (succ p)~1
    | p~0, q~1 => (addCarry p q)~0
    | p~0, q~0 => (add p q)~1
    | p~0, xH => (succ p)~0
    | xH, q~1 => (succ q)~1
    | xH, q~0 => (succ q)~0
    | xH, xH => P1~1
end

instance : Add Pos where add := Pos.add

/-- Multiplication -/
def mul : Pos → Pos → Pos
  | xH,    q       => q
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
  | xH => p1
  | p2~0 => (app p1 p2)~0
  | p2~1 => (app p1 p2)~1

@[reducible]
instance : HAppend Pos Pos Pos where hAppend := Pos.app

instance app_assoc : @Std.Associative Pos (.++.) where
  assoc _ _ p := by induction p <;> simp_all [HAppend.hAppend, app]

@[simp]
theorem app_1_left_id (p : Pos) : app P1 p = p := by
  induction p <;> simp [app] <;> assumption

@[simp]
theorem app_1_right_id (p : Pos) : app p P1 = p := by
  induction p <;> simp [app] <;> assumption

instance app_1_l : @Std.LawfulLeftIdentity Pos Pos (.++.) P1 where
  left_id p := app_1_left_id p

def reverseGo (p1 p2 : Pos) : Pos :=
  match p2 with
  | xH => p1
  | p2~0 => reverseGo (p1~0) p2
  | p2~1 => reverseGo (p1~1) p2
def reverse : Pos → Pos := reverseGo P1

theorem reverse_go_app (p1 p2 p3 : Pos) :
  reverseGo p1 (p2 ++ p3) = reverseGo p1 p3 ++ reverseGo P1 p2 := by
  have helper : ∀ p1 p2 p3, reverseGo (p2 ++ p3) p1 = p2 ++ (reverseGo p3 p1) := by
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
    exact IH (p1~1) p2
  | xO p3 IH =>
    exact IH (p1~0) p2
  | xH =>
    rewrite [<- helper]
    rfl

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
| xH => P1
| p~0 => (dup p)~0~0
| p~1 => (dup p)~1~1


/-- These next functions allow to efficiently encode lists of positives (bit
strings) into a single positive and go in the other direction as well. This is
for example used for the countable instance of lists and in namespaces.
The main functions are [flatten] and [unflatten]. -/

def flattenGo (xs : List Pos) (acc : Pos) : Pos :=
  match xs with
  | [] => acc
  | x :: xs => flattenGo xs (acc~1~0 ++ reverse (dup x))

/-- Flatten a list of positives into a single positive by duplicating the bits
of each element, so that:

- [0 -> 00]
- [1 -> 11]

and then separating each element with [10]. -/
def flatten (xs : List Pos) : Pos :=
  flattenGo xs P1

def unflattenGo
        (p : Pos)
        (acc_xs : List Pos)
        (acc_elm : Pos)
  : Option (List Pos) :=
  match p with
  | xH => some acc_xs
  | p'~0~0 => unflattenGo p' acc_xs (acc_elm~0)
  | p'~1~1 => unflattenGo p' acc_xs (acc_elm~1)
  | p'~1~0 => unflattenGo p' (acc_elm :: acc_xs) P1
  | _ => none

/-- Unflatten a positive into a list of positives, assuming the encoding
used by [flatten]. -/
def unflatten (p : Pos) : Option (List Pos) :=
  unflattenGo p [] P1

theorem flatten_go_app xs acc :
    flattenGo xs acc = acc ++ flattenGo xs P1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs IH =>
    simp [flattenGo]
    rewrite [IH]
    rewrite [IH (P1~1~0 ++ x.dup.reverse)]
    simp only [<- app_assoc.assoc]
    rfl

theorem unflatten_go_app (p : Pos) suffix xs acc :
  unflattenGo (suffix ++ reverse (dup p)) xs acc =
  unflattenGo suffix xs (acc ++ p) := by
  induction p generalizing suffix acc with
  | xI p IH =>
    simp [dup]
    rewrite [reverse_xI]; rewrite [reverse_xI]
    simp only [<- app_assoc.assoc]
    rewrite [IH]
    rfl
  | xO p IH =>
    simp [dup]
    rewrite [reverse_x0]; rewrite [reverse_x0]
    simp only [<- app_assoc.assoc]
    rewrite [IH]
    rfl
  | xH => rfl

theorem unflatten_flatten_go suffix xs acc :
  unflattenGo (suffix ++ flattenGo xs P1) acc P1 =
  unflattenGo suffix (xs ++ acc) P1 := by
  revert suffix acc
  induction xs with
  | nil => intros suff acc; rfl
  | cons x xs IH =>
    intros suff acc
    simp only [flattenGo]
    rewrite [List.cons_append, flatten_go_app]
    rewrite [<- app_assoc.assoc, IH, <- app_assoc.assoc]
    rewrite [unflatten_go_app]
    rewrite [app_1_l.left_id]
    rfl

theorem unflatten_flatten xs :
  unflatten (flatten xs) = some xs := by
  unfold flatten; unfold unflatten
  rewrite [<- (app_1_l.left_id (flattenGo xs P1))]
  rewrite [unflatten_flatten_go P1 xs [], List.append_nil]
  rfl

theorem flatten_app xs ys :
  flatten (xs ++ ys) = flatten xs ++ flatten ys := by
  unfold flatten
  induction xs generalizing ys with
  | nil =>
    simp only [flattenGo]
    rewrite [app_1_l.left_id]
    rfl
  | cons x xs IH =>
    rewrite [List.cons_append]
    simp only [flattenGo]
    rewrite [flatten_go_app (xs ++ ys), flatten_go_app xs]
    rewrite [IH]
    rewrite [<-app_assoc.assoc]
    rfl

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
  have hassoc := app_assoc.assoc
  simp at hdup hassoc
  induction p with
  | xI p IH =>
    simp only [dup, reverse_xI]
    rewrite [<- hassoc, IH, hdup]
    rfl
  | xO p IH =>
    simp only [dup, reverse_x0]
    rewrite [<- hassoc, IH, hdup]
    rfl
  | xH => rfl

theorem dup_suffix_eq p q s1 s2 :
  s1~1~0 ++ dup p = s2~1~0 ++ dup q -> p = q := by
  induction p generalizing q with
  | xI p IH =>
    intros Heq
    cases q <;> simp_all [HAppend.hAppend, app, dup] <;> rename Pos => q
    rewrite [IH q] <;> rfl
  | xO p IH =>
    intros Heq
    cases q <;> simp_all [HAppend.hAppend, app, dup] <;> rename Pos => q
    rewrite [IH q] <;> rfl
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
    rewrite [<- app_assoc.assoc, <- app_assoc.assoc]
    rewrite [flatten_cons]
    rewrite [<- app_assoc.assoc, <- app_assoc.assoc]
    intros Hlen Hl
    have Heq : xs = ys := by apply IH; simp_all []; apply Hl
    rewrite [Heq]; congr; rewrite [Heq] at Hl
    replace Hl := (app_inj (flatten ys)).inj _ _ Hl
    rewrite [reverse_dup, reverse_dup] at Hl
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
    rewrite [Pos.unflatten_flatten]
    rewrite [Option.bind_eq_bind, Option.bind_some, List.mapM_map]
    induction xs with
    | nil => rfl
    | cons x xs IH =>
      rewrite [List.mapM_cons, Function.comp_apply, Option.pure_def, Option.bind_eq_bind]
      rewrite [IH, Countable.decode_encode]
      rfl

instance : Countable Pos where
  encode := id
  decode := some
  decode_encode _ := rfl

end Pos
