/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import IrisSugar.Registry

/-!
# Step-index notation support

The meta code behind `local stepindex T` (see the module docs of `Iris.Algebra.StepIndex`): the
`stepindex` command and the scoped delaborator that hides the section's step index.
`@[indexed]` generates name and application notations in `IrisSugar.Registry`; ordinary
applications and identifiers use Lean's standard elaborators.
-/

namespace Iris.StepIndexSugar

open Lean Elab Term

/-- Whether `si` is the step index of the section (set by `local stepindex`). -/
public meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- In a `local stepindex` section, `C SI args` for an `@[indexed]` `C` with an explicit step index
prints as `C args` when `SI` is the step index of the section. -/
@[scoped delab app] public meta def delabIndexedApp : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let table := indexedExt.getState (← getEnv)
  let some i := table.decls.find? c | failure
  guard (e.getAppNumArgs > i.argIdx)
  let si ← withNaryArg i.argIdx delab
  let stx ← Lean.PrettyPrinter.Delaborator.delabApp
  let (f, args) : Term × Array Syntax := match stx with
    | `($f $args*) => (f, args.map (·.raw))
    | _ => (stx, #[])
  let head := if f.raw.isOfKind ``Parser.Term.explicitUniv then f.raw[0] else f.raw
  -- Fully qualified names are the explicit API: their positional index must stay visible.
  guard (head.isIdent && table.notations.contains head.getId)
  let mut args := args
  if let some p := i.explicitPos then
    guard (p < args.size)
    args := args.eraseIdx! p
  if ← isSectionSI si then
    if i.explicitPos.isNone then failure
  else
    -- A different index needs a named override; a positional index would be another argument
    -- to the notation. This also makes implicit indices visible when they differ from the section.
    let named ← `(Parser.Term.namedArgument| ($(mkIdent i.name) := $si))
    args := #[named] ++ args
  return ⟨applyIndexedNotationArgs f args⟩

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
