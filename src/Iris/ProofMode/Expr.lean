/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Qq
import Iris.BI
import Iris.Std.Expr

namespace Iris.ProofMode
open Iris.BI
open Lean Lean.Expr Lean.Meta Qq

@[match_pattern] def nameAnnotation := `name
@[match_pattern] def uniqAnnotation := `uniq

def parseName? : Expr → Option (Name × Name × Expr)
  | .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e => do
    some (name, uniq, e)
  | _ => none

def mkNameAnnotation (name uniq : Name) (e : Expr) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ e

inductive Hyps {prop : Q(Type)} (bi : Q(BI $prop)) : (e : Q($prop)) → Type where
  | emp (_ : $e =Q emp) : Hyps bi e
  | sep (tm elhs erhs : Q($prop)) (_ : $e =Q iprop($elhs ∗ $erhs))
        (lhs : Hyps bi elhs) (rhs : Hyps bi erhs) : Hyps bi e
  | hyp (tm : Q($prop)) (name uniq : Name) (p : Q(Bool)) (ty : Q($prop))
        (_ : $e =Q iprop(□?$p $ty)) : Hyps bi e

instance : Inhabited (Hyps bi s) := ⟨.emp ⟨⟩⟩

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
    (name uniq : Name) (p : Q(Bool)) (ty : Q($prop)) (e := q(iprop(□?$p $ty))) : Hyps bi e :=
  .hyp (mkIntuitionisticIf bi p (mkNameAnnotation name uniq ty)) name uniq p ty ⟨⟩

partial def parseHyps? {prop : Q(Type)} (bi : Q(BI $prop)) (expr : Expr) :
    Option ((s : Q($prop)) × Hyps bi s) := do
  if let some #[_, _, P, Q] := appM? expr ``sep then
    let ⟨elhs, lhs⟩ ← parseHyps? bi P
    let ⟨erhs, rhs⟩ ← parseHyps? bi Q
    some ⟨q(BI.sep $elhs $erhs), .sep expr elhs erhs ⟨⟩ lhs rhs⟩
  else if expr.isAppOfArity ``emp 2 then
    some ⟨expr, .emp ⟨⟩⟩
  else if let some #[_, _, P] := appM? expr ``intuitionistically then
    let (name, uniq, (ty : Q($prop))) ← parseName? P
    some ⟨q(iprop(□ $ty)), .hyp expr name uniq q(true) ty ⟨⟩⟩
  else
    let (name, uniq, ty) ← parseName? expr
    some ⟨ty, .hyp expr name uniq q(false) ty ⟨⟩⟩

partial def Hyps.find? {prop bi} (name : Name) : ∀ {s}, @Hyps prop bi s → Option (Name × Q(Bool) × Q($prop))
  | _, .emp _ => none
  | _, .hyp _ name' uniq p ty _ => if name == name' then (uniq, p, ty) else none
  | _, .sep _ _ _ _ lhs rhs => rhs.find? name <|> lhs.find? name

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

/-- This is only used for display purposes, so that we can render context variables that appear
to have type `A : PROP` even though `PROP` is not a type. -/
def HypMarker {PROP : Type} (_A : PROP) : Prop := True

def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ()) fun _ =>
    return Sum.inl <| Elab.Info.ofTermInfo
      { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder }

def addHypInfo (stx : Syntax) (name uniq : Name) (prop : Q(Type)) (ty : Q($prop))
    (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let ty := q(HypMarker $ty)
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨uniq⟩ name ty) (.fvar ⟨uniq⟩) ty isBinder

def Hyps.findWithInfo {prop bi} (hyps : @Hyps prop bi s) (name : Ident) : MetaM Name := do
  let some (uniq, _, ty) := hyps.find? name.getId | throwError "unknown hypothesis"
  addHypInfo name name.getId uniq prop ty
  pure uniq
