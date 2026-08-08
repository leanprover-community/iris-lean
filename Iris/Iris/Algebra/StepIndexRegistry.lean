/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Lean
public meta import Lean

/-!
# Step Index Registry

An attribute holding a default type for step indices that can be registered per-section.
-/

open Lean Elab Command Tactic

/-- Extension used to track the current default type for step indices -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := Name.anonymous
  }

/-- Query the type of step indices -/
@[expose] elab "#stepindex?" : command => do
  match siExt.getState (← getEnv) with
  | Name.anonymous =>  logInfo m!"No step index declared."
  | si =>  logInfo m!"{si}"


/--
`stepindex%` elaborates to the step index type in scope, resolved eagerly as a term.
Use this in macros so that the step index type is calculated based on the default at the use site.
Elaborates to a hole when no default step index is in scope, as to default to whichever `SIdx`
instance is in scope.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous => Term.elabTerm (← `(_)) expectedType?
  | n => Term.elabTerm (mkIdent n) expectedType?
