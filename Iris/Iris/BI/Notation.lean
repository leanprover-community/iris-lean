/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
module

public meta import Lean.Elab.Term
public meta import Lean.Elab.Quotation.Precheck
public meta import Lean.PrettyPrinter.Delaborator

public meta section

namespace Iris.BI
open Lean Lean.Macro Lean.Elab Lean.Elab.Term

/-- Flag for iprop term elaboration. When set, terms are interpreted as an
iprop.  -/
register_option iris.inIprop : Bool := {
  defValue := false
  descr    := "true when elaborating inside an `iprop(...)` scope"
}

/-- Check whether we are currently inside an `iprop(...)` scope. -/
meta def inIpropScope : TermElabM Bool := do
  return (← getOptions).getBool `iris.inIprop

/-- Run an elaboration action with the iprop flag set. -/
meta def withIpropScope {α} (k : TermElabM α) : TermElabM α := do
  withTheReader Core.Context
    (fun ctx => { ctx with options := ctx.options.setBool `iris.inIprop true })
    k

-- define `iprop` embedding in `term`
syntax:max (name := iprop_scope) "iprop(" term ")" : term
syntax:max "term(" term ")" : term

/-- Term elaborator for `iprop(...)`. Runs only when no `macro_rules` clause
matches the body (macros expand first). Opens the iprop elaboration scope
and elaborates the body, letting flag-checking BI connective elaborators
take over for connectives that no longer have macro_rules. -/
@[term_elab iprop_scope]
meta def elabIpropScope : TermElab := fun stx expectedType? => do
  let body : Term := ⟨stx[1]⟩
  withIpropScope (elabTerm body expectedType?)

/-- Precheck for `iprop(...)` quotations: recurse into the body.

Without this, syntax quotations that produce `iprop(...)` (e.g.
`\`(iprop($P → False))` inside a macro_rules RHS) fail the precheck because
the elaborator-based `iprop_scope` is not a macro and has no default
precheck.

We additionally swallow `unsupportedSyntax` raised by the inner precheck —
that exception bubbles up when an inner BI connective syntax (e.g.
`|={...}[...]▷=> _`) has neither a precheck nor a macro registered. The
original macro-only design accepted this implicitly because the catch-all
`iprop($t) => pure t` macro expanded the body and let standard precheck
take over (which often returned early via `hasQuotedIdent`). Mirroring that
permissiveness here avoids forcing every connective to grow its own
precheck. -/
@[quot_precheck Iris.BI.iprop_scope]
meta def precheckIpropScope : Lean.Elab.Term.Quotation.Precheck := fun stx => do
  try
    Lean.Elab.Term.Quotation.precheck stx[1]
  catch _ =>
    pure ()

-- Escape hatch to unset the iprop flag
macro_rules
  | `(iprop(term($t))) => pure t

-- carry `iprop` over some `term` constructs
macro_rules
  | `(iprop(($P)))                  => ``((iprop($P)))
  | `(iprop(if $c then $t else $e)) => ``(if $c then iprop($t) else iprop($e))
  | `(iprop(($P : $t)))             => ``((iprop($P) : $t))

macro:max "iprop(" P:term " : " t:term ")" : term => `((iprop($P) : $t))

/-- Remove an `iprop` quotation from a `term` syntax object. -/
partial def unpackIprop [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(iprop($P))             => do `($P)
  | `($P:ident)              => do `($P)
  | `(?$P:ident)             => do `(?$P)
  | `(($P))                  => do `(($(← unpackIprop P)))
  | `($P $[ $Q]*)            => do ``($P $[ $Q]*)
  | `(if $c then $t else $e) => do
    let t ← unpackIprop t
    let e ← unpackIprop e
    `(if $c then $t else $e)
  | `(($P : $t))             => do ``(($(← unpackIprop P) : $t))
  | `($t)                    => `($t:term)

end Iris.BI
