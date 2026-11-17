/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Iris.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-! # `local bi PROP`: local defaults for PROP types. -/

open Lean Elab Command Term

public meta section

register_option iris.localBi.warnOnOverride : Bool := {
  defValue := true
  descr := "warn when `local bi` overrides an existing default proposition type"
}

end

namespace Iris

public section

/-- Store the proposition type of the current section, as written in `local bi PROP`. -/
meta initialize biExt : SimpleScopedEnvExtension Syntax (Option Syntax) ←
  registerSimpleScopedEnvExtension {
    addEntry _ s := some s
    initial := none
  }

/-- The proposition type set by `local bi`, or a hole when none is set. -/
@[expose] elab "bi%" : term => do
  match biExt.getState (← getEnv) with
  | none => elabTerm (← `(_)) none
  | some T => elabType T

/-- `local bi T` marks `T` as the default proposition type in the section.
Applications must be parenthesized, as in `local bi (IProp GF)`.
Overriding an existing default warns unless `iris.localBi.warnOnOverride` is `false`. -/
syntax (name := biCmd) Lean.Parser.Term.attrKind &"bi " term:max : command

@[command_elab biCmd]
meta def elabBiCmd : CommandElab := fun stx => do
  let `(command| $k:attrKind bi $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`bi` must be `local`: it sets the proposition type of the current section"
  if (biExt.getState (← getEnv)).isSome && iris.localBi.warnOnOverride.get (← getOptions) then
    logWarningAt T "`local bi` overrides an existing default proposition type\n\
      Disable this warning with `set_option iris.localBi.warnOnOverride false`."
  biExt.add T .local

end
end Iris
