/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Qq
import Iris.BI
import Iris.Std.Expr

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr Lean.Meta Qq

def nameAnnotation := `name

def parseName? : Expr → Option (Name × Expr)
  | .mdata d e => do
    let .true := d.size == 1 | none
    let some (DataValue.ofName v) := d.find nameAnnotation | none
    some (v, e)
  | _ => none

def mkNameAnnotation (name : Name) (e : Expr) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName name)]⟩ e

inductive Hyps {prop : Q(Type)} (bi : Q(BI $prop)) : (e : Q($prop)) → Type where
  | emp (_ : $e =Q emp) : Hyps bi e
  | sep (tm elhs erhs : Q($prop)) (_ : $e =Q iprop($elhs ∗ $erhs))
        (lhs : Hyps bi elhs) (rhs : Hyps bi erhs) : Hyps bi e
  | hyp (tm : Q($prop)) (name : Name) (p : Q(Bool)) (ty : Q($prop))
        (_ : $e =Q iprop(□?$p $ty)) : Hyps bi e

def Hyps.tm : @Hyps prop bi s → Q($prop)
  | .emp _ => s
  | .sep tm .. | .hyp tm .. => tm

def Hyps.mkEmp {prop : Q(Type)} (bi : Q(BI $prop)) (e := q(BI.emp : $prop)) : Hyps bi e := .emp ⟨⟩

def Hyps.mkSep {prop : Q(Type)} {bi : Q(BI $prop)} {elhs erhs}
    (lhs : Hyps bi elhs) (rhs : Hyps bi erhs) (e := q(BI.sep $elhs $erhs)) : Hyps bi e :=
  .sep q(BI.sep $(lhs.tm) $(rhs.tm) : $prop) elhs erhs ⟨⟩ lhs rhs

def isTrue (p : Q(Bool)) : Bool := p.constName! == ``true

def matchBool (p : Q(Bool)) : ($p =Q true) ⊕' ($p =Q false) :=
  if isTrue p then .inl ⟨⟩ else .inr ⟨⟩

def mkIntuitionisticIf {prop : Q(Type)} (_bi : Q(BI $prop))
    (p : Q(Bool)) (e : Q($prop)) : {A : Q($prop) // $A =Q iprop(□?$p $e)} :=
  match matchBool p with
  | .inl _ => ⟨q(iprop(□ $e)), ⟨⟩⟩
  | .inr _ => ⟨e, ⟨⟩⟩

def Hyps.mkHyp {prop : Q(Type)} (bi : Q(BI $prop))
    (name : Name) (p : Q(Bool)) (ty : Q($prop)) (e := q(iprop(□?$p $ty))) : Hyps bi e :=
  .hyp (mkIntuitionisticIf bi p (mkNameAnnotation name ty)) name p ty ⟨⟩

partial def parseHyps? {prop : Q(Type)} (bi : Q(BI $prop)) (expr : Expr) :
    Option ((s : Q($prop)) × Hyps bi s) := do
  if let some #[_, _, P, Q] := appM? expr ``sep then
    let ⟨elhs, lhs⟩ ← parseHyps? bi P
    let ⟨erhs, rhs⟩ ← parseHyps? bi Q
    some ⟨q(BI.sep $elhs $erhs), .sep expr elhs erhs ⟨⟩ lhs rhs⟩
  else if expr.isAppOfArity ``emp 2 then
    some ⟨expr, .emp ⟨⟩⟩
  else if let some #[_, (_ : Q(BIBase $prop)), P] := appM? expr ``intuitionistically then
    let (name, (ty : Q($prop))) ← parseName? P
    some ⟨q(iprop(□ $ty)), .hyp expr name q(true) ty ⟨⟩⟩
  else
    let (name, ty) ← parseName? expr
    some ⟨ty, .hyp expr name q(false) ty ⟨⟩⟩

/-- This is the same as `Entails`, but it takes a `BI` instead.
This constant is used to detect iris proof goals. -/
abbrev Entails' [BI PROP] : PROP → PROP → Prop := Entails

structure IrisGoal where
  prop : Q(Type)
  bi : Q(BI $prop)
  e : Q($prop)
  hyps : Hyps bi e
  goal : Q($prop)

def isIrisGoal (expr : Expr) : Bool := isAppOfArity expr ``Entails' 4

def parseIrisGoal? (expr : Expr) : Option IrisGoal := do
  let some #[prop, bi, P, goal] := expr.appM? ``Entails' | none
  let ⟨e, hyps⟩ ← parseHyps? bi P
  some { prop, bi, e, hyps, goal }

def IrisGoal.toExpr : IrisGoal → Expr
  | { hyps, goal, .. } => q(Entails' $(hyps.tm) $goal)

def IrisGoal.strip : IrisGoal → Expr
  | { e, goal, .. } => q(Entails $e $goal)
