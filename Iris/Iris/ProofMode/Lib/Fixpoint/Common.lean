/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public import Iris.ProofMode.Lib.Monotone

/-! # Shared parts of the fixpoint commands -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Meta

/-! ## The clauses -/

declare_syntax_cat monotoneClause
syntax "monotone_by " Lean.Parser.Tactic.tacticSeq : monotoneClause

declare_syntax_cat contractiveClause
syntax "contractive_by " Lean.Parser.Tactic.tacticSeq : contractiveClause

end Iris.Fixpoint

/-! ## Default tactics, for a missing clause -/

public meta section

register_option iris.fixpoint.monotoneDefault : Bool := {
  defValue := true
  descr := "Whether `ifix` and `icofix` without a `monotone_by` clause try the extensible tactic \
    `ifix_monotone_default`, which is `imono` unless extended with `macro_rules`."
}

register_option iris.fixpoint.contractiveDefault : Bool := {
  defValue := true
  descr := "Whether `iguarded` without a `contractive_by` clause tries the extensible tactic \
    `iguarded_contractive_default`, which has no rules unless extended with `macro_rules`."
}

end

namespace Iris.Fixpoint
open Lean Elab Command Meta

/-- Proves monotonicity for `ifix`/`icofix` without `monotone_by`. Extend with `macro_rules`. -/
syntax (name := ifixMonotoneDefault) "ifix_monotone_default" : tactic
macro_rules | `(tactic| ifix_monotone_default) => `(tactic| imono)

/-- Proves contractiveness for `iguarded` without `contractive_by`. Extend with `macro_rules`. -/
syntax (name := iguardedContractiveDefault) "iguarded_contractive_default" : tactic

/-- `fixpoint_default tac "msg"` runs `tac`, prefixing any error with `msg`. -/
syntax (name := fixpointDefault) "fixpoint_default " tactic str : tactic

@[tactic fixpointDefault] meta def evalFixpointDefault : Tactic.Tactic
  | `(tactic| fixpoint_default $tac $msg) => do
    -- Without error recovery, a failure is an exception, not a logged error.
    try Tactic.withoutRecover do Tactic.evalTactic tac; Tactic.done
    catch e => throwError "{msg.getString}\n\n{e.toMessageData}"
  | _ => throwUnsupportedSyntax

/-- The proof for a missing `clause` of `cmd`: the extensible tactic `hook`, unless `opt` is off. -/
meta def defaultTactic (cmd clause opt : Name) (hook : TSyntax `tactic) (what : String) :
    CommandElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  let keyword := hook.raw[0].getAtomVal
  unless (← getOptions).getBool opt true do
    throwError "{cmd}: the default tactic for {what} is off. Provide a proof with `{clause}`, or \
      turn `{opt}` back on."
  let advice := s!"Provide a proof with `{clause}`, or extend `{keyword}` with `macro_rules`."
  let env ← getEnv
  if (macroAttribute.getEntries env hook.raw.getKind).isEmpty &&
      (Tactic.tacticElabAttribute.getEntries env hook.raw.getKind).isEmpty then
    throwError "{cmd}: no default tactic proves {what}. {advice}"
  let msg := Syntax.mkStrLit s!"{cmd}: `{keyword}` did not prove {what}. {advice}"
  `(Lean.Parser.Tactic.tacticSeq| fixpoint_default $hook $msg)

/-! ## Adding declarations -/

/-- The full name of `name`, just declared in the current namespace. Built, not resolved: resolving
could find another constant, and `protected` hides the short name. -/
meta def resolveDeclared (name : Ident) : CommandElabM Name := do
  let id := name.getId
  let ns ← getCurrNamespace
  let full := if id.getRoot == `_root_ then id.replacePrefix `_root_ .anonymous else ns ++ id
  let env ← getEnv
  if env.contains full then return full
  let priv := mkPrivateName env full
  if env.contains priv then return priv
  throwErrorAt name "unknown declaration `{full}`"

/-- Prime binders that shadow a used enclosing binder, so statements print without `x_1`: library
binders (`Φ`, `n`) can shadow parameters, and `name.ne` repeats its argument names. -/
meta def primeShadowed (e : Expr) : Expr :=
  go #[] e
where
  go (scope : Array Name) : Expr → Expr
    | .forallE n t b bi =>
      let n := fresh scope n b; .forallE n (go scope t) (go (scope.push n) b) bi
    | .lam n t b bi => let n := fresh scope n b; .lam n (go scope t) (go (scope.push n) b) bi
    | .app f a => .app (go scope f) (go scope a)
    | .mdata d e => .mdata d (go scope e)
    | e => e
  /-- Whether `b`, the body of a binder, uses an enclosing binder named `n`. -/
  usesName (scope : Array Name) (n : Name) (b : Expr) : Bool :=
    (List.range scope.size).any fun i => scope[scope.size - 1 - i]! == n && b.hasLooseBVar (i + 1)
  /-- `n`, primed until `b` uses no enclosing binder of that name (at most `scope.size` times). -/
  fresh (scope : Array Name) (n : Name) (b : Expr) : Name := Id.run do
    let mut n := n
    for _ in [:scope.size] do
      unless usesName scope n b do break
      n := n.appendAfter "'"
    return n

/-- Add a theorem, letting the kernel check `value` against `type`. -/
meta def emitThm (name : Name) (levels : List Name) (type value : Expr) : TermElabM Unit := do
  addDecl <| .thmDecl {
    name, levelParams := levels
    type := primeShadowed (← instantiateMVars type), value := ← instantiateMVars value }

end Iris.Fixpoint

end
