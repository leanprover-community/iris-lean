/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.ProofMode.Tactics.Contractive

namespace Iris

open Lean Elab Command Meta Term

/-- Syntax category for binder groups, e.g. `(x y : T)`. -/
declare_syntax_cat guardedExplicitBinder
syntax "(" ident+ " : " term ")" : guardedExplicitBinder

declare_syntax_cat guardedContractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : guardedContractiveClause

/-- Determines the (syntactic) arity of the first application of `name`. -/
meta partial def guardedSelfArity (name : Name) (stx : Syntax) : Option Nat :=
  match stx with
  | `($f:ident $args*) =>
    if f.getId == name then some args.size
    else ((stx.getArgs.map (guardedSelfArity name)).filterMap id)[0]?
  | _ =>
    if stx.isIdent && stx.getId == name then some 0
    else ((stx.getArgs.map (guardedSelfArity name)).filterMap id)[0]?

/-- Binder names that are neither explicit not instance-implicit. -/
meta partial def guardedLeadingAutoBoundNames (e : Expr) : Array Name :=
  match e with
  | .forallE name _ body bi =>
    (if bi == .default then #[]
     else (if bi == .instImplicit then #[] else #[name]) ++ guardedLeadingAutoBoundNames body)
  | _ => #[]

/-- Builds a `(i : t)` explicit binder group. -/
meta def guardedMkExplicitBinder (i : Ident) (t : Term)
    : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
  `(bracketedBinder| ($i : $t))

/-- Recursive definition via the guarded fixpoint. -/
elab mods:declModifiers "guarded " name:ident binders:guardedExplicitBinder*
    " : " ty:term " := " body:term contractiveBy:(guardedContractiveClause)? : command => do
  let mut names : Array Ident := #[]
  let mut types : Array Term := #[]
  for b in binders do
    let `(guardedExplicitBinder| ($ids* : $t)) := b | throwUnsupportedSyntax
    for id in ids do
      names := names.push id
      types := types.push t

  -- Determine the arity at which `name` recurses
  let some arity := guardedSelfArity name.getId body
    | throwErrorAt name "guarded fixpoint def: no recursive occurrence of '{name.getId}' found in the body"

  if arity > names.size then
    throwErrorAt name
      "guarded fixpoint def: recursive call arity {arity} exceeds the parameter count {names.size}"

  -- Split the arguments - prefixes are the arguments that stay fixed
  -- (e.g. for `wp`, the prefixes would be just `s : Stuckness`)
  let splitPoint := names.size - arity
  let prefixNames := names.extract 0 splitPoint
  let prefixTypes := types.extract 0 splitPoint
  let suffixNames := names.extract splitPoint names.size
  let suffixTypes := types.extract splitPoint names.size

  let prefixBinders ← (prefixNames.zip prefixTypes).mapM fun (i, t) => guardedMkExplicitBinder i t
  let suffixBinders ← (suffixNames.zip suffixTypes).mapM fun (i, t) => guardedMkExplicitBinder i t
  let selfType ← suffixTypes.foldrM (fun t acc => `($t → $acc)) ty
  let selfBinder ← guardedMkExplicitBinder name selfType

  -- pre-definition: the original body but with self-reference as an argument
  let preName := mkIdentFrom name (name.getId ++ `pre)
  let declPre ← `(command|
    def $preName:ident $prefixBinders* $selfBinder $suffixBinders* : $ty := $body)
  elabCommand declPre

  let preFullName := (← getCurrNamespace) ++ preName.getId
  let some preInfo := (← getEnv).find? preFullName
    | throwErrorAt name "guarded fixpoint def: could not find generated declaration {preFullName}"

  -- apply prefix arguments and leading implicit arguments
  let autoBoundNames := guardedLeadingAutoBoundNames preInfo.type
  let autoArgs : Array Term ← autoBoundNames.mapM fun n => do
    let s ← `(Lean.Parser.Term.namedArgument| ($(mkIdent n) := $(mkIdent n)))
    return ⟨s.raw⟩
  let prefixArgs : Array Term := prefixNames.map fun i => ⟨i.raw⟩
  let preApp ← `($preName:ident $prefixArgs* $autoArgs*)

  -- contractivity instance
  let contractiveTac ← match contractiveBy with
    | some clause =>
      let `(guardedContractiveClause| contractive_by $ts) := clause | throwUnsupportedSyntax
      pure ts
    | none => `(Lean.Parser.Tactic.tacticSeq| contractive)
  let contractiveName := mkIdentFrom name (name.getId ++ `pre ++ `contractive)
  let declContr ← `(command| instance $contractiveName:ident $prefixBinders* :
                  OFE.Contractive $preApp where distLater_dist := by $contractiveTac)
  elabCommand declContr

  -- definition: fixpoint of the pre-definition
  let defName := mkIdentFrom name (name.getId)
  let declDef ← `(command|
    $mods:declModifiers def $defName:ident $prefixBinders* : $selfType := fixpoint $preApp)
  elabCommand declDef

end Iris
