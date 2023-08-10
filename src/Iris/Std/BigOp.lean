/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/

namespace Iris.Std

/-- Fold a binary operator `f` over a list of `PROP`s. If the list is empty, `unit` is returned. -/
def bigOp (f : PROP → PROP → PROP) (unit : PROP) : List PROP → PROP
  | []      => unit
  | [P]     => P
  | P :: Ps => f P (bigOp f unit Ps)

class LawfulBigOp (f : PROP → PROP → PROP) (unit : outParam PROP)
    (eq : outParam (PROP → PROP → Prop)) where
  refl : eq a a
  symm : eq a b → eq b a
  trans : eq a b → eq b c → eq a c
  comm : eq (f a b) (f b a)
  assoc : eq (f (f a b) c) (f a (f b c))
  left_id : eq (f unit a) a
  congr_l : eq a a' → eq (f a b) (f a' b)

theorem LawfulBigOp.right_id [LawfulBigOp (PROP := PROP) f unit eq] : eq (f a unit) a :=
  trans f comm left_id

theorem LawfulBigOp.congr_r [LawfulBigOp (PROP := PROP) f unit eq]
    (h : eq b b') : eq (f a b) (f a b') :=
  trans f comm <| trans f (congr_l h) comm

open LawfulBigOp

theorem bigOp_nil {f : PROP → PROP → PROP} {unit : PROP} : bigOp f unit [] = unit := rfl

theorem bigOp_cons {f : PROP → PROP → PROP} {unit : PROP} [LawfulBigOp f unit eq] :
    eq (bigOp f unit (P :: Ps)) (f P (bigOp f unit Ps)) :=
  match Ps with
  | [] => symm f right_id
  | _ :: _ => refl f
