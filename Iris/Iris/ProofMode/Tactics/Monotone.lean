/-
Copyright (c) 2026 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser
-/
module

public meta import Iris.Instances.Lib.Monotone
public meta import Iris.ProofMode

namespace Iris

open Lean Elab Tactic Meta Iris.Std ProofMode Term Macro

meta partial def etaExpand (e : Expr) : TacticM Unit := do
  let ty ← whnf (← instantiateMVars (← inferType e))
  if ty.isAppOf ``Prod then
    let stx ← PrettyPrinter.delab e
    evalTactic (← `(tactic| rw [← Prod.eta $stx]))
    etaExpand (← mkAppM ``Prod.fst #[e])
    etaExpand (← mkAppM ``Prod.snd #[e])

meta def tryUnfoldFn : TacticM Unit := do
  let _ ← observing? ((← getMainTarget).withApp <| λ _ args => do
    if let some e := args[3]? then e.withApp <| λ _ args => do
      if let some e := args[2]? then match e.getAppFn with
        | .const fn _ => do
          -- don't unfold primitives
          if not <| (`Iris.BI.BIBase).isPrefixOf fn then
            evalTactic <| ← `(tactic|unfold $(mkIdent fn); try simp)
        | _ => return)

elab "monotone" : tactic => do
  let H ← `(icasesPat| H)
  let H' ← `(selPat| H)
  let x ← `(ident| x)

  -- introduce hypotheses
  evalTactic <| ← `(tactic|intros; iintro #$H %$x)

  -- eta-expand the argument
  withMainContext do
    let e := mkFVar (← getFVarId x)
    etaExpand e

  -- unfold twice
  tryUnfoldFn
  tryUnfoldFn

  -- split match
  (← getMainTarget).withApp λ _ args =>
    args[3]!.withApp λ _ args => do
      let d := args[2]!.getAppArgs[2]!
      let stx ← Term.exprToSyntax d
      evalTactic <| ← `(tactic| try cases $stx:term)

  evalTactic <| ← `(tactic|irevert $H' %$x; apply MonotonePred.monotone)
  evalTactic <| ← `(tactic|irevert $H' %$x; apply MonotonePred.monotone)
