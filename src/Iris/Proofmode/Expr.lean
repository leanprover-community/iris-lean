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

/-- Kind of hypotheses. -/
inductive HypothesisKind where
  | intuitionistic | spatial
  deriving BEq

inductive Hyps (prop : Q(Type)) where
  | emp (tm : Q($prop))
  | sep (tm strip : Q($prop)) (lhs rhs : Hyps prop)
  | hyp (tm strip : Q($prop)) (kind : HypothesisKind) (name : Name) (ty : Q($prop))

def Hyps.tm : Hyps prop → Q($prop)
  | .emp tm | .sep tm .. | .hyp tm .. => tm

def Hyps.strip {prop : Q(Type)} : Hyps prop → Q($prop)
  | .emp tm | .sep _ tm .. | .hyp _ tm .. => tm

inductive PathElem | left | right

def Hyps.mkEmp {prop : Q(Type)} (_bi : Q(BI $prop)) : Hyps prop :=
  .emp q(BI.emp : $prop)

def Hyps.mkSep {prop : Q(Type)} (_bi : Q(BI $prop)) (lhs rhs : Hyps prop) : Hyps prop :=
  .sep q(BI.sep $(lhs.tm) $(rhs.tm) : $prop) q(BI.sep $(lhs.strip) $(rhs.strip) : $prop) lhs rhs

def Hyps.mkHyp {prop : Q(Type)} (_bi : Q(BI $prop))
    (kind : HypothesisKind) (name : Name) (ty : Q($prop)) : Hyps prop :=
  have e : Q($prop) := mkNameAnnotation name ty
  match kind with
  | .intuitionistic =>
    .hyp q(iprop(□ $e)) q(iprop(□ $ty)) kind name ty
  | .spatial => .hyp e ty kind name ty

def Hyps.find? (name : Name) : Hyps prop → Option (List PathElem × HypothesisKind × Q($prop))
  | .emp _ => none
  | .sep _ _ lhs rhs =>
    match rhs.find? name with
    | some (ctx, r) => some (.right :: ctx, r)
    | none => match lhs.find? name with
      | some (ctx, r) => some (.left :: ctx, r)
      | none => none
  | .hyp _ _ kind name' ty => if name == name' then some ([], kind, ty) else none

partial def parseHyps? (prop : Q(Type)) (expr : Expr) : Option <| Hyps prop := do
  if let some #[_, (_ : Q(BIBase $prop)), P, Q] := appM? expr ``sep then
    let lhs ← parseHyps? prop P
    let rhs ← parseHyps? prop Q
    some (.sep expr q(BI.sep $(lhs.strip) $(rhs.strip) : $prop) lhs rhs)
  else if expr.isAppOfArity ``emp 2 then
    some (.emp expr)
  else if let some #[_, (_ : Q(BIBase $prop)), P] := appM? expr ``intuitionistically then
    let (name, (ty : Q($prop))) ← parseName? P
    some (.hyp expr q(iprop(□ $ty)) .intuitionistic name ty)
  else
    let (name, ty) ← parseName? expr
    some (.hyp expr ty .spatial name ty)

/-- This is the same as `Entails`, but it takes a `BI` instead.
This constant is used to detect iris proof goals. -/
abbrev Entails' [BI PROP] : PROP → PROP → Prop := Entails

structure IrisGoal where
  prop : Q(Type)
  bi : Q(BI $prop)
  hyps : Hyps prop
  goal : Q($prop)

def isIrisGoal (expr : Expr) : Bool := isAppOfArity expr ``Entails' 4

def parseIrisGoal? (expr : Expr) : Option IrisGoal := do
  let some #[prop, bi, P, goal] := expr.appM? ``Entails' | none
  let hyps ← parseHyps? prop P
  some { prop, bi, hyps, goal }

def IrisGoal.toExpr : IrisGoal → Expr
  | { hyps, goal, .. } => q(Entails' $(hyps.tm) $goal)

def IrisGoal.strip : IrisGoal → Expr
  | { hyps, goal, .. } => q(Entails $(hyps.strip) $goal)
