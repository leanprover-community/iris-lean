/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Lib.Fixpoint

/-! Stub fixpoint commands. The fixpoint itself and its unfolding theorem are `sorry`; the proof
clauses are parsed and ignored. See `FIXPOINT_PLAN.md` for the planned implementation. -/

namespace Iris.Fixpoint
open Lean Elab Command

/-- Placeholder for the fixpoint of `f`. -/
public def stubFixpoint {α : Sort _} (_f : α → α) : α := sorry

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat nonexpClause
syntax "nonexp_by " Lean.Parser.Tactic.tacticSeq : nonexpClause

declare_syntax_cat contractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : contractiveClause

/-- Arity of the first application of `name` in `stx`. -/
meta partial def recursiveArity (name : Name) (stx : Syntax) : Option Nat :=
  match stx with
  | `($f:ident $args*) =>
    if f.getId == name then some args.size
    else (stx.getArgs.filterMap (recursiveArity name))[0]?
  | _ =>
    if stx.isIdent && stx.getId == name then some 0
    else (stx.getArgs.filterMap (recursiveArity name))[0]?

/-- Split `binders` into a prefix and a suffix made of the last `arity` explicit parameters. -/
meta def splitBinders (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (arity : Nat) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ×
      Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut pre := binders
  let mut suffix := #[]
  let mut needed := arity
  while needed > 0 do
    let some b := pre.back? | throwError "fixpoint stub: recursive arity {arity} exceeds the parameters"
    pre := pre.pop
    let `(bracketedBinder| ($ids* : $t)) := b
      | throwErrorAt b "fixpoint stub: recursive parameters must be trailing explicit binders"
    if ids.size ≤ needed then
      suffix := #[b] ++ suffix
      needed := needed - ids.size
    else
      let keep := ids.extract 0 (ids.size - needed)
      let take := ids.extract (ids.size - needed) ids.size
      pre := pre.push (← `(bracketedBinder| ($keep* : $t)))
      suffix := #[← `(bracketedBinder| ($take* : $t))] ++ suffix
      needed := 0
  return (pre, suffix)

/-- Names of the explicit parameters bound by `binders`. -/
meta def explicitArgs (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) : Array Term :=
  binders.foldl (init := #[]) fun acc b =>
    match b with
    | `(bracketedBinder| ($ids* : $_)) => acc ++ ids.map fun i => ⟨i.raw⟩
    | _ => acc

/-- Names of the leading implicit (not instance) binders of `type`. -/
meta partial def leadingImplicitNames (type : Expr) : Array Name :=
  match type with
  | .forallE n _ body bi =>
    if bi == .default then #[]
    else (if bi == .instImplicit then #[] else #[n]) ++ leadingImplicitNames body
  | _ => #[]

/-- Emit `name.pre`, a placeholder definition of `name`, and a `sorry` unfolding theorem. -/
meta def elabStub (mods : TSyntax ``Lean.Parser.Command.declModifiers) (name : Ident)
    (binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (contractive : Bool) : CommandElabM Unit := do
  let arity := (recursiveArity name.getId body).getD 0
  let (pre, suffix) ← splitBinders binders arity
  let selfType ← if suffix.isEmpty then pure ty else `(∀ $suffix*, $ty)
  let preArgs := explicitArgs pre
  let preName := mkIdentFrom name (name.getId ++ `pre)
  let unfoldName := mkIdentFrom name (name.getId ++ `unfold)
  elabCommand (← `(command| def $preName:ident $pre* ($name : $selfType) $suffix* : $ty := $body))
  -- Pin the implicit parameters of `name.pre` that its explicit arguments do not determine.
  let preType := (← getConstInfo ((← getCurrNamespace) ++ preName.getId)).type
  let implicitArgs : Array Term ← (leadingImplicitNames preType).mapM fun n => do
    return ⟨(← `(Lean.Parser.Term.namedArgument| ($(mkIdent n) := $(mkIdent n)))).raw⟩
  let preApp ← `($preName:ident $preArgs* $implicitArgs*)
  elabCommand (← `(command|
    $mods:declModifiers def $name:ident $pre* : $selfType := stubFixpoint $preApp))
  elabCommand (← `(command|
    theorem $unfoldName:ident $pre* : $name $preArgs* $implicitArgs* = $preApp ($name $preArgs*) :=
      sorry))
  if contractive then
    let contractiveName := mkIdentFrom name (name.getId ++ `pre ++ `contractive)
    elabCommand (← `(command|
      instance $contractiveName:ident $pre* : OFE.Contractive $preApp := sorry))

/-- Least Iris fixpoint (stub). -/
elab "ifix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    (monotoneClause)? nonexpClause : command => do
  elabStub (← `(declModifiers|)) name binders ty body false

/-- Greatest Iris fixpoint (stub). -/
elab "icofix " name:ident binders:bracketedBinder* " : " ty:term " := " body:term
    (monotoneClause)? nonexpClause : command => do
  elabStub (← `(declModifiers|)) name binders ty body false

/-- Guarded Iris fixpoint (stub). -/
elab mods:declModifiers "iguarded " name:ident binders:bracketedBinder* " : " ty:term
    " := " body:term (contractiveClause)? : command =>
  elabStub mods name binders ty body true

end Iris.Fixpoint
