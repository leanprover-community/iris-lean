/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean
public import Iris.Init

/-!
# Step Index Registry

The step index type of the current scope, set by `local stepindex T` (see `Iris.Algebra.StepIndex`).
The `Iris.StepIndexSugar` notations read it through `stepindex%`.
-/

open Lean Elab Command Tactic

/-- The step index type of the current scope (`Name.anonymous` when none is set). -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := Name.anonymous
  }

/-- Show the step index type of the current scope. -/
@[expose] elab "#stepindex?" : command => do
  match siExt.getState (← getEnv) with
  | .anonymous => logInfo m!"No step index declared."
  | si => logInfo m!"{si}"

/--
`stepindex%` elaborates to the step index type of the current scope (set by `local stepindex T`).
The `Iris.StepIndexSugar` notations expand to it, so that the step index is read at the use site.
It elaborates to a hole when no step index is set.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous => Term.elabTerm (← `(_)) expectedType?
  | n => Term.elabTerm (mkIdent n) expectedType?

/-- Where an `@[indexed]` declaration takes its step index: the binder whose type is
`stepindex (Type _)`. -/
public structure IndexedInfo where
  /-- The binder name of the step index. -/
  name : Name
  /-- Its position among all arguments. -/
  argIdx : Nat
  /-- Its position among the explicit arguments, or `none` when it is not explicit. -/
  explicitPos : Option Nat
  /-- The number of explicit arguments. -/
  arity : Nat
  deriving Inhabited, Repr

/-- The `@[indexed]` declarations, and the last components of their names (a fast check that an
identifier cannot name one). -/
public meta structure IndexedTable where
  decls : NameMap IndexedInfo := {}
  lasts : NameSet := {}
  deriving Inhabited

/-- Add an `@[indexed]` declaration to the table. -/
public meta def IndexedTable.insert (t : IndexedTable) (n : Name) (i : IndexedInfo) : IndexedTable :=
  { decls := t.decls.insert n i, lasts := t.lasts.insert (.mkSimple n.getString!) }

/-- The `@[indexed]` declarations. -/
public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) IndexedTable ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }

/--
`@[indexed]` marks a declaration whose step index (the binder of type `stepindex (Type _)`, explicit
or implicit, possibly a section variable) is filled in by `local stepindex T` sections: there `C a`
elaborates as `C T a` (or `C (SI := T) a` for an implicit step index) and prints back as `C a`.
-/
meta initialize registerBuiltinAttribute {
  name := `indexed
  descr := "the step index of this declaration is filled in by `local stepindex` sections"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    unless kind == .global do throwError "`@[indexed]` must be global"
    let info ← getConstInfo decl
    let r ← Meta.MetaM.run' <| Meta.forallTelescope info.type fun xs _ => do
      let mut expl := 0
      let mut r : Option IndexedInfo := none
      for i in [:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        if r.isNone && d.type.isAppOfArity `Iris.stepindex 1 then
          r := some { name := d.userName, argIdx := i, arity := 0,
                      explicitPos := if d.binderInfo.isExplicit then some expl else none }
        if d.binderInfo.isExplicit then expl := expl + 1
      return r.map ({ · with arity := expl })
    let some i := r
      | throwError "`@[indexed]`: `{decl}` has no step index binder of type `stepindex (Type _)`"
    modifyEnv (indexedExt.addEntry · (decl, i))
}
