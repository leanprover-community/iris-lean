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

/--
`SI : stepindex (Type _)` marks `SI` as a step index binder, like `outParam` marks an output:
`@[indexed]` declarations take theirs from the `local stepindex` section. It elaborates to its
argument with a metadata marker (no constant to unfold), so it costs nothing in unification.
-/
@[expose] elab "stepindex " t:term:max : term => do
  let e ← Term.elabType t
  return .mdata (KVMap.empty.insert `iris.stepindex (.ofBool true)) e

/-- Whether a binder type carries the `stepindex` marker. -/
public meta def isStepIndexBinder : Expr → Bool
  | .mdata m _ => m.getBool `iris.stepindex
  | _ => false

/-- Where an `@[indexed]` declaration takes its step index: the binder whose type is
`stepindex (Type _)`. -/
public meta structure IndexedInfo where
  /-- The binder name of the step index. -/
  name : Name
  /-- Its position among all arguments. -/
  argIdx : Nat
  /-- Its position among the explicit arguments, or `none` when it is not explicit. -/
  explicitPos : Option Nat
  /-- The spellings of its notation; the first one is used for printing. -/
  spellings : Array String := #[]
  deriving Inhabited, Repr

/-- The `@[indexed]` declarations. -/
public meta initialize indexedExt :
    SimplePersistentEnvExtension (Name × IndexedInfo) (NameMap IndexedInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun t (n, i) => t.insert n i
    addImportedFn := fun as => as.foldl (fun t a => a.foldl (fun t (n, i) => t.insert n i) t) {}
  }
