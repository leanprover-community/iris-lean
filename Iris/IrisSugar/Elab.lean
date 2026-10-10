/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Elab.App
public import IrisSugar.Registry

/-!
# `local stepindex` and its elaborator

The meta code behind `local stepindex T` (see the module docs of `Iris.Algebra.StepIndex`): the
`stepindex` command, and the scoped elaborator and delaborator of `Iris.StepIndexSugar` that fill in
and hide the step index of `@[indexed]` declarations. The elaborator runs on every application and
identifier of a sugared section, so its common path (an identifier that cannot name an `@[indexed]`
declaration) is a single name-set lookup.
-/

namespace Iris.StepIndexSugar

open Lean Elab Term

/-- The constants that `f` names (unless `f` is a local variable), with their `@[indexed]` data. -/
meta def indexedHeads (f : Ident) : TermElabM (List (Name × Option IndexedInfo)) := do
  let table := indexedExt.getState (← getEnv)
  -- fast path: no `@[indexed]` declaration has this last name component
  let .str _ last := f.getId.eraseMacroScopes | return []
  unless table.lasts.contains (.mkSimple last) do return []
  if (← isLocalIdent? f).isSome then return []
  return (← resolveGlobalName f.getId).filterMap fun (n, fields) =>
    if fields.isEmpty then some (n, table.decls.find? n) else none

/-- `f args` with the step index of the section filled in, or `none` when it is given (positionally
or by name) or not reached by a partial application. -/
meta def fillSI (i : IndexedInfo) (f : Syntax) (args : Array Syntax) : TermElabM (Option Syntax) := do
  let isNamed (a : Syntax) := a.isOfKind ``Parser.Term.namedArgument
  if args.any fun a => isNamed a && a[1].getId == i.name then return none
  -- filled in already (this is an alternative of an overloaded `C args` coming back)
  if args.any fun a => a.getAtomVal == "stepindex%" || a[0].getAtomVal == "stepindex%" then
    return none
  let si ← `(stepindex%)
  match i.explicitPos with
  | none =>
    let named ← `(Parser.Term.namedArgument| ($(mkIdent i.name) := $si))
    return some (Syntax.mkApp ⟨f⟩ (args.push named |>.map (⟨·⟩)))
  | some p =>
    let posIdx := (List.range args.size).filter fun j =>
      !(isNamed args[j]! || args[j]!.isOfKind ``Parser.Term.ellipsis)
    -- fewer positional arguments than reach the step index: a partial application before it;
    -- as many as all explicit arguments: the step index is given
    unless p ≤ posIdx.length && posIdx.length < i.arity do return none
    -- in a generic section, its step index variable written in place (`C SI F` partially applied):
    -- given. (Not for a constant like `Nat`, which may well be an ordinary argument.)
    let secSI := siExt.getState (← getEnv)
    if h : p < posIdx.length ∧ ((← getLCtx).findFromUserName? secSI).isSome then
      let a := args[posIdx[p]]!
      if a.isIdent && a.getId == secSI then return none
    let k := if h : p < posIdx.length then posIdx[p] else args.size
    return some (Syntax.mkApp ⟨f⟩ ((args.insertIdx! k si.raw).map (⟨·⟩)))

/-- The identifier of a head `C` or `C.{u, …}`. -/
meta def headIdent? (f : Syntax) : Option Ident :=
  if f.isIdent then some ⟨f⟩
  else if f.isOfKind ``Parser.Term.explicitUniv && f[0].isIdent then some ⟨f[0]⟩
  else none

/-- `stx` (`C args`, `C` or `C.{u, …}`) with the step index of the section filled in, when `C` is
`@[indexed]`. When `C` is overloaded, each reading becomes an alternative (with the step index filled
in for the `@[indexed]` ones), and overload resolution picks among them as usual. -/
meta def elabIndexed (stx : Syntax) (head : Syntax) (args : Array Syntax)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let some f := headIdent? head | throwUnsupportedSyntax
  let heads ← indexedHeads f
  unless heads.any (·.2.isSome) do throwUnsupportedSyntax
  -- the head, naming the constant `n` unambiguously
  let headFor (n : Name) : Syntax :=
    let c := mkCIdentFrom f n
    if head.isIdent then c else head.setArg 0 c
  let mut alts : Array Syntax := #[]
  for (n, i?) in heads do
    let h := if heads.length == 1 then head else headFor n
    match i? with
    | some i =>
      let some s ← fillSI i h args | throwUnsupportedSyntax
      alts := alts.push s
    | none => alts := alts.push (if args.isEmpty then h else Syntax.mkApp ⟨h⟩ (args.map (⟨·⟩)))
  let stx' := if h : alts.size = 1 then alts[0] else mkNode choiceKind alts
  -- the default elaborators, not `elabTerm` on `C args`: the result is again `C args`, and must not
  -- come back here (a partial application would get a second step index)
  withMacroExpansion stx stx' <|
    if stx'.isOfKind choiceKind then elabTerm stx' expectedType? else Lean.Elab.Term.elabApp stx' expectedType?

/-- In a `local stepindex` section, `C args` for an `@[indexed]` `C` elaborates with the step index
filled in (see `Iris.Algebra.StepIndex`). -/
@[scoped term_elab app] public meta def elabIndexedApp : TermElab := fun stx expectedType? =>
  elabIndexed stx stx[0] stx[1].getArgs expectedType?

/-- A bare `C` (or `C.{u, …}`) for an `@[indexed]` `C`: `C stepindex%` (or `C (SI := stepindex%)`). -/
@[scoped term_elab ident] public meta def elabIndexedIdent : TermElab := fun stx expectedType? =>
  elabIndexed stx stx #[] expectedType?

@[scoped term_elab explicitUniv, inherit_doc elabIndexedIdent]
public meta def elabIndexedExplicitUniv : TermElab := fun stx expectedType? =>
  elabIndexed stx stx #[] expectedType?

/-- Whether `si` is the step index of the section (set by `local stepindex`). -/
public meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- In a `local stepindex` section, `C SI args` for an `@[indexed]` `C` with an explicit step index
prints as `C args` when `SI` is the step index of the section. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).decls.find? c | failure
  let some p := i.explicitPos | failure
  guard (e.getAppNumArgs > i.argIdx)
  unless ← isSectionSI (← withNaryArg i.argIdx delab) do failure
  let stx : Term ← Lean.PrettyPrinter.Delaborator.delabApp
  let `($f $args*) := stx | return stx
  unless p < args.size do return stx
  if args.size == 1 then return f
  return ⟨Syntax.mkApp f (args.eraseIdx! p)⟩

end Iris.StepIndexSugar

namespace Iris

public section
open Lean Parser in
/-- `local stepindex T` makes `T` the step index of the current section: the `@[indexed]`
declarations take it when their step index is not given, and print without it (see the module docs
of `Iris.Algebra.StepIndex`).

```
local stepindex Nat
variable [CMRA α]          -- CMRA Nat α
example (x : α) : ✓ x → ✓ x := id
```
-/
syntax (name := stepindexCmd) Term.attrKind &"stepindex " term : command
end

open Lean Elab Command in
@[command_elab stepindexCmd]
public meta def elabStepindex : CommandElab := fun stx => do
  let `(command| $k:attrKind stepindex $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`stepindex` must be `local`: it sets the step index of the current section"
  unless T.raw.isIdent do
    throwError "`stepindex` expects an identifier, but got{indentD T}\n\n\
      Introduce an abbreviation first, e.g. `abbrev MySI := ...` then `local stepindex MySI`."
  runTermElabM fun _ => do
    let Te ← Term.elabType T
    unless (← Meta.trySynthInstance (← Meta.mkAppM `Iris.SIdx #[Te])) matches .some _ do
      throwError "`stepindex` requires a `SIdx` instance for{indentExpr Te}"
  siExt.add T.raw.getId .local
  elabCommand (← `(command| open scoped Iris.StepIndexSugar))

end Iris
