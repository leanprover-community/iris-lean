/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.AuxDef
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Iris.Std.StepIndex.Registry

/-!
# `@[indexed]`, `local stepindex`, and their notations

`@[indexed]` gives each declaration `C` a scoped macro (in `Iris.StepIndex`) that rewrites `C args`
to `C (SI := stepindex%) args`, so that the step index is known before instance search runs.
`local stepindex T` opens these macros, together with a delaborator that prints `C T args` as
`C args`.
-/

namespace Iris.StepIndex

open Lean

/-- The identifier of a head `C` or `C.{u, …}`. -/
meta def headIdent? (f : Syntax) : Option Ident :=
  if f.isIdent then some ⟨f⟩
  else if f.isOfKind ``Parser.Term.explicitUniv && f[0].isIdent then some ⟨f[0]⟩
  else none

/-- Whether the last components of `a` and `b` agree: a fast check that `a` cannot name `b`. -/
meta def sameLast (a b : Name) : Bool :=
  match a, b with
  | .str _ s, .str _ t => s == t
  | _, _ => false

/-- The declarations that `f` names, not counting field accesses `C.f`. A notation or macro
pre-resolves its identifiers. -/
meta def resolveHead (f : Ident) : MacroM (List Name) := do
  if let .ident _ _ _ pre := f.raw then
    let ns := pre.filterMap fun | .decl n [] => some n | _ => none
    unless ns.isEmpty do return ns
  return (← Macro.resolveGlobalName f.getId).filterMap fun (n, fields) =>
    if fields.isEmpty then some n else none

/--
Expands `C args`, or a bare `C`, to `C (si := stepindex%) args` when `C` names `decl`, an
`@[indexed]` declaration with step index binder `si`. Each `@[indexed]` declaration registers this
as its scoped macro.

* It does nothing when `args` already name `si`: this is how the step index is given explicitly,
  and it stops the macro from firing again on its own output.
* When `C` is overloaded, the other declarations it names stay as alternatives of a choice node.
* A macro cannot see local variables: a local that shadows `decl` is rewritten too, and then fails
  on the named argument.
-/
public meta def expandIndexed (decl si : Name) : Macro := fun stx => do
  let (head, args) :=
    if stx.isOfKind ``Parser.Term.app then (stx[0], stx[1].getArgs) else (stx, #[])
  let some f := headIdent? head | Macro.throwUnsupported
  unless sameLast f.getId.eraseMacroScopes decl do Macro.throwUnsupported
  let names ← resolveHead f
  unless names.contains decl do Macro.throwUnsupported
  if args.any fun a => a.isOfKind ``Parser.Term.namedArgument &&
      a[1].getId.eraseMacroScopes == si then
    Macro.throwUnsupported
  let siArg ← `(Parser.Term.namedArgument| ($(mkIdent si) := stepindex%))
  let app (h : Syntax) (n : Name) : Term :=
    Syntax.mkApp ⟨h⟩ <| (if n == decl then #[siArg.raw] ++ args else args).map (⟨·⟩)
  if let [_] := names then return app head decl
  -- overloaded: one alternative per declaration, its head resolved to that declaration
  let alts := names.toArray.map fun n =>
    let c := mkCIdentFrom f n
    app (if head.isIdent then c else head.setArg 0 c) n
  return mkNode choiceKind (alts.map (·.raw))

/-- The step index binder of `decl`: its first binder whose type is `stepindex (Type _)`. -/
meta def findIndexedInfo (decl : Name) : MetaM (Option IndexedInfo) := do
  Meta.forallTelescope (← getConstInfo decl).type fun xs _ => do
    let mut expl := 0
    for i in [:xs.size] do
      let d ← xs[i]!.fvarId!.getDecl
      if isStepIndexBinder d.type then
        return some { name := d.userName, argIdx := i,
                      explicitPos := if d.binderInfo.isExplicit then some expl else none }
      if d.binderInfo.isExplicit then expl := expl + 1
    return none

section
open Elab Command

/-- Declares the scoped macro of the `@[indexed]` declaration `decl`, on applications `C args` and
on bare `C` and `C.{u, …}`. -/
meta def addIndexedMacro (decl : Name) (i : IndexedInfo) : CoreM Unit := liftCommandElabM do
  let ns := mkIdent `Iris.StepIndex
  let kind ← `(Parser.Term.attrKind| scoped)
  let attrs ← [``Parser.Term.app, identKind, ``Parser.Term.explicitUniv].toArray.mapM fun k =>
    `(Parser.Term.attrInstance| $kind:attrKind macro $(mkIdent k))
  elabCommand (← `(namespace $ns))
  elabCommand (← `(@[$attrs,*] public aux_def indexed $(mkIdent decl) : Macro :=
    expandIndexed $(quote decl) $(quote i.name)))
  elabCommand (← `(end $ns))

end

/--
`@[indexed]` marks a declaration whose step index (the binder of type `stepindex (Type _)`, explicit
or implicit, possibly a section variable) is filled in by `local stepindex T` sections: there `C a`
elaborates as `C (SI := T) a` and prints back as `C a`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let some i ← (findIndexedInfo decl).run'
      | throwError "`@[indexed]`: `{decl}` has no step index binder of type `stepindex (Type _)`"
    modifyEnv (indexedExt.addEntry · (decl, i))
    addIndexedMacro decl i
}

/-- Whether `si` is the section's step index. -/
public meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C SI args` as `C args` when `SI` is the section's step index. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).find? c | failure
  let some p := i.explicitPos | failure
  guard (e.getAppNumArgs > i.argIdx)
  unless ← isSectionSI (← withNaryArg i.argIdx delab) do failure
  let stx : Term ← Lean.PrettyPrinter.Delaborator.delabApp
  let `($f $args*) := stx | return stx
  return Syntax.mkApp f (args.eraseIdxIfInBounds p)

end Iris.StepIndex

namespace Iris

public section
open Lean Parser in
/-- `local stepindex T` makes `T` the section's step index: `@[indexed]` declarations take it when
theirs is not given, and print without it.

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
  elabCommand (← `(command| open scoped Iris.StepIndex))

end Iris
