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

`@[indexed]` gives a declaration `C` a scoped notation (in `Iris.StepIndex`): the token `C`, alone
or applied, stands for `C (SI := stepindex%)`, so that the step index is known before instance
search runs. `local stepindex T` opens these notations, together with a delaborator that prints
`C T args` back with the notation.

The notation is a token, so inside a `local stepindex` section the raw declaration is written
`«C»`, and `C` cannot be used where an identifier is expected (binders, `namespace`, `open`).

Spellings: a trailing `ᵢ` and a leading `Iris.` are dropped from the declaration name. A type (a
class or structure, or anything else ending in a sort) is spelled by its last component and by its
qualified name; any other declaration only by its qualified name.
-/

namespace Iris.StepIndex

open Lean

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

/-- The notation spellings of `decl` (see the module docstring). -/
meta def spellingsOf (decl : Name) (isType : Bool) : Array String :=
  let strip : Name → Name
    | .str p s => .str p (if s.endsWith "ᵢ" then (s.dropEnd 1).toString else s)
    | n => n
  let n := (strip decl).replacePrefix `Iris .anonymous
  let qualified := n.toString (escape := false)
  match n with
  | .str .anonymous _ => #[qualified]
  | .str _ last => if isType then #[last, qualified] else #[qualified]
  | _ => #[qualified]

/-- The forms of a notation: the token alone, applied, and with explicit universes. -/
inductive NotationForm where
  | atom | app | univ

/-- The syntax kind of the notation `tok` of `decl` in the form `form`. -/
meta def notationKind (decl : Name) (tok : String) : NotationForm → Name
  | .atom => .str `Iris.StepIndex s!"{decl} {tok}"
  | .app => .str `Iris.StepIndex s!"{decl} {tok} app"
  | .univ => .str `Iris.StepIndex s!"{decl} {tok} univ"

/--
Expands the notation of `decl` (step index binder `si`) to `decl (si := stepindex%) args`: from
`tok` (one node), `tok args` (two), or `tok.{us} args` (five).
-/
public meta def expandIndexedNotation (decl si : Name) : Macro := fun stx => do
  let c := mkCIdentFrom stx[0] decl (canonical := true)
  let (head, args) ← match stx.getNumArgs with
    | 1 => pure (c.raw, #[])
    | 2 => pure (c.raw, stx[1].getArgs)
    | 5 => pure (mkNode ``Parser.Term.explicitUniv #[c, stx[1], stx[2], stx[3]], stx[4].getArgs)
    | _ => Macro.throwUnsupported
  let siArg ← `(Parser.Term.namedArgument| ($(mkIdent si) := stepindex%))
  return Syntax.mkApp ⟨head⟩ ((#[siArg.raw] ++ args).map (⟨·⟩))

section
open Elab Command

/-- Declares the scoped notation `tok` of `decl`: `tok` alone, `tok args`, and
`tok.{us} args`. -/
meta def addIndexedNotation (decl : Name) (si : Name) (tok : String) : CoreM Unit :=
  liftCommandElabM do
    let ns := mkIdent `Iris.StepIndex
    let k0 := notationKind decl tok .atom
    let k1 := notationKind decl tok .app
    let k2 := notationKind decl tok .univ
    let tokLit := Syntax.mkStrLit tok
    let kind ← `(Parser.Term.attrKind| scoped)
    let attrs ← #[k0, k1, k2].mapM fun k =>
      `(Parser.Term.attrInstance| $kind:attrKind macro $(mkIdent k))
    elabCommand (← `(namespace $ns))
    elabCommand (← `(scoped syntax:max (name := $(mkIdent (.mkSimple k0.getString!))) $tokLit:str : term))
    elabCommand (← `(scoped syntax:lead (name := $(mkIdent (.mkSimple k1.getString!)))
      $tokLit:str (Lean.Parser.Term.argument)+ : term))
    elabCommand (← `(scoped syntax:lead (name := $(mkIdent (.mkSimple k2.getString!)))
      $tokLit:str noWs ".{" level,+ "}" (Lean.Parser.Term.argument)* : term))
    elabCommand (← `(@[$attrs,*] public aux_def indexed $(mkIdent decl) : Macro :=
      expandIndexedNotation $(quote decl) $(quote si)))
    elabCommand (← `(end $ns))

end

/--
`@[indexed]` marks a declaration whose step index (the binder of type `stepindex (Type _)`, explicit
or implicit, possibly a section variable) is filled in by `local stepindex T` sections: there the
notation `C a` elaborates as `C (SI := T) a` and prints back as `C a`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let some i ← (findIndexedInfo decl).run'
      | throwError "`@[indexed]`: `{decl}` has no step index binder of type `stepindex (Type _)`"
    let isType ← Meta.MetaM.run' <|
      Meta.forallTelescope (← getConstInfo decl).type fun _ b => return b.isSort
    let i := { i with spellings := spellingsOf decl isType }
    modifyEnv (indexedExt.addEntry · (decl, i))
    for tok in i.spellings do
      addIndexedNotation decl i.name tok
}

/-- Whether `si` is the section's step index. -/
public meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- Prints `C SI args` with the notation of `C` when `SI` is the section's step index. -/
@[scoped delab app] public meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).find? c | failure
  let some tok := i.spellings[0]? | failure
  guard (e.getAppNumArgs > i.argIdx)
  unless ← isSectionSI (← withNaryArg i.argIdx delab) do failure
  let stx : Term ← Lean.PrettyPrinter.Delaborator.delabApp
  let args ← match stx with
    | `($_:ident $args*) => pure (args.map (·.raw))
    | `($_:ident) => pure #[]
    | _ => failure
  let args := match i.explicitPos with
    | some p => args.eraseIdxIfInBounds p
    | none => args
  if args.isEmpty then
    return ⟨mkNode (notationKind c tok .atom) #[mkAtom tok]⟩
  return ⟨mkNode (notationKind c tok .app) #[mkAtom tok, mkNullNode args]⟩

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
