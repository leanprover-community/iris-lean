/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.ScopedEnvExtension
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# Step Index Registry

The step index type of the current scope, set by `local stepindex T` (see `Iris.Std.StepIndex.Elab`).
Notations read it through `stepindex%`.
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
Notations expand to it, so that the step index is read at the use site.
It elaborates to a hole when no step index is set.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous => Term.elabTerm (← `(_)) expectedType?
  | n => Term.elabTerm (mkIdent n) expectedType?

/-- Where an `@[indexed SI]` declaration takes its step index: its binder `SI`. -/
public meta structure IndexedInfo where
  /-- The position of `SI` among all arguments. -/
  argIdx : Nat
  /-- Its position among the explicit arguments, or `none` when it is not explicit. -/
  explicitPos : Option Nat
  /-- The spellings of its notation; the first one is used for printing. -/
  spellings : Array String
  deriving Inhabited, Repr

/-- The `@[indexed]` declarations. -/
public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) (NameMap IndexedInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }
