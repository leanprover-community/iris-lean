/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.ProofMode.Tactics.Contractive
public meta import Iris.ProofMode.Tactics.Monotone
public meta import Iris.BI.Lib.Fixpoint

namespace Iris

open Lean Elab Command Meta Term

/-- Syntax category for binder groups, e.g. `(x y : T)`, and instances. -/
declare_syntax_cat fixpointBinder
syntax "(" ident+ " : " term ")" : fixpointBinder
syntax "[" term "]" : fixpointBinder

/-- Determines the (syntactic) arity of the first application of `name`. -/
meta partial def fixpointSelfArity (name : Name) (stx : Syntax) : Option Nat :=
  match stx with
  | `($f:ident $args*) =>
    if f.getId == name then some args.size
    else ((stx.getArgs.map (fixpointSelfArity name)).filterMap id)[0]?
  | _ =>
    if stx.isIdent && stx.getId == name then some 0
    else ((stx.getArgs.map (fixpointSelfArity name)).filterMap id)[0]?

/-- Peels off the leading implicit binders, returning their
names together with the remaining expression. -/
meta partial def fixpointPeelLeading (e : Expr) : Array Name × Expr :=
  match e with
  | .forallE name _ body bi =>
    if bi == .default then (#[], e)
    else
      let (ns, rest) := fixpointPeelLeading body
      (#[name] ++ ns, rest)
  | _ => (#[], e)

/-- Builds a `(i : t)` explicit binder group. -/
meta def fixpointMkExplicitBinder (i : Ident) (t : Term)
    : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
  `(bracketedBinder| ($i : $t))

meta def elabFixpointDef (fixpoint : Name) (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (name : Ident) (binders : Array (TSyntax `fixpointBinder)) (ty : Term) (body : Term)
    : CommandElabM Unit := do
  let mut names : Array Ident := #[]
  let mut types : Array Term := #[]
  let mut instBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for b in binders do
    match b with
    | `(fixpointBinder| ($ids* : $t)) =>
      for id in ids do
        names := names.push id
        types := types.push t
    | `(fixpointBinder| [$t]) =>
      instBinders := instBinders.push (← `(bracketedBinder| [$t]))
    | _ => throwUnsupportedSyntax

  -- Determine the arity at which `name` recurses
  let some arity := fixpointSelfArity name.getId body
    | throwErrorAt name "monotone fixpoint def: no recursive occurrence of '{name.getId}' found in the body"

  if arity > names.size then
    throwErrorAt name
      "monotone fixpoint def: recursive call arity {arity} exceeds the parameter count {names.size}"

  -- Split the arguments - prefixes are the arguments that stay fixed
  -- (e.g. for `twp`, the prefixes would be just `s : Stuckness`)
  let splitPoint := names.size - arity
  let prefixNames := names.extract 0 splitPoint
  let prefixTypes := types.extract 0 splitPoint
  let suffixNames := names.extract splitPoint names.size
  let suffixTypes := types.extract splitPoint names.size

  let prefixBinders ← (prefixNames.zip prefixTypes).mapM fun (i, t) => fixpointMkExplicitBinder i t
  let suffixBinders ← (suffixNames.zip suffixTypes).mapM fun (i, t) => fixpointMkExplicitBinder i t
  let selfType ← suffixTypes.foldrM (fun t acc => `($t → $acc)) ty
  let selfBinder ← fixpointMkExplicitBinder name selfType

  -- Build tuples of arguments for uncurried application
  let mut argPair : Term := suffixNames[0]!
  for i in suffixNames[1:] do
    argPair ← `(($argPair, $i))

  let mut domTy : Term := suffixTypes[0]!
  for t in suffixTypes[1:] do
    domTy ← `($domTy × $t)

  -- pre-definition: the original body but with self-reference as an argument
  let preName := mkIdentFrom name (name.getId ++ `pre)
  let declPre ← `(command|
    $mods:declModifiers def $preName:ident $prefixBinders* $selfBinder $suffixBinders* : $ty := $body)
  elabCommand declPre

  let preFullName := (← getCurrNamespace) ++ preName.getId
  let some preInfo := (← getEnv).find? preFullName
    | throwErrorAt name "monotone fixpoint def: could not find generated declaration {preFullName}"

  -- Find the names of leading implicit arguments and (explicit) prefix arguments
  let (leadingNames, _) := fixpointPeelLeading preInfo.type
  let leadingArgs : Array Term := leadingNames.map fun n => mkIdent n
  let prefixArgs : Array Term := prefixNames.map id

  -- pre'-definition: the pre-definition, uncurried into a single argument
  let selfParamBinder ← fixpointMkExplicitBinder name (← `($domTy → $ty))

  let mut curriedSelf : Term := name
  for _ in [:suffixNames.size - 1] do
    curriedSelf ← `(Function.curry $curriedSelf)

  let preNameFull := mkIdentFrom name preFullName
  let preApp ← `(@$preNameFull:ident $leadingArgs* $prefixArgs* $curriedSelf)
  let mut pre'Body : Term := preApp
  for _ in [:suffixNames.size - 1] do
    pre'Body ← `(Function.uncurry $pre'Body)

  let pre'Name := mkIdentFrom name (name.getId ++ `pre')
  let declPre' ← `(command|
    def $pre'Name:ident $prefixBinders* $selfParamBinder := $pre'Body)
  elabCommand declPre'

  -- monotonicity instance
  let preMonoName := mkIdentFrom name (name.getId ++ `pre_mono')
  let monoBinders := instBinders ++ prefixBinders
  let pre'App ← `(@$pre'Name:ident $leadingArgs* $prefixArgs*)
  let declMono ← `(command|
    instance $preMonoName:ident $monoBinders* : BIMonoPred $pre'App where
      mono_pred := by monotone
      mono_pred_ne := by nonexp)
  elabCommand declMono

  -- definition: fixpoint of the uncurried pre-definition
  let defName := mkIdentFrom name (name.getId ++ `def)
  let defBinders := instBinders ++ prefixBinders ++ suffixBinders
  let declDef ← `(command|
    def $defName:ident $defBinders* : $ty := $(mkIdent fixpoint) ($pre'Name $prefixArgs*) $argPair)
  elabCommand declDef

/-- Recursive definition via the least fixpoint. -/
elab mods:declModifiers "leastfix " name:ident binders:fixpointBinder*
    " : " ty:term " := " body:term : command =>
  elabFixpointDef ``bi_least_fixpoint mods name binders ty body

/-- Recursive definition via the greatest fixpoint. -/
elab mods:declModifiers "greatestfix " name:ident binders:fixpointBinder*
    " : " ty:term " := " body:term : command =>
  elabFixpointDef ``bi_greatest_fixpoint mods name binders ty body

end Iris
