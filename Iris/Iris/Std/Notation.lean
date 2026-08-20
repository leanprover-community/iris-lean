/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.Std.DelabRule
public import Iris.Init

namespace Iris.Std
open Lean PrettyPrinter Delaborator

public meta section

/--
  A generic delaborator for `Std.Tele.tforall`, `Std.Tele.texist`,
  `BIBase.forall`, `BIBase.exist`, `BI.tforall` and `BI.texist`.
  Unlike the notations in Iris-Rocq, there is no eta-expansion for
  non-lambda expressions (e.g. `tforall Φ`). This intends to be consistent with Lean.
-/
def delabQuant
    (arity : Nat) (fn : Term → DelabM Term)
    (termCreator : Ident → TSyntaxArray `ident → Term → DelabM Term)
    (collapseFunction : Term → Option (Ident × TSyntaxArray `ident × Term)) : Delab := do
  -- No delaboration when `pp.notation` is set as `false`
  guard <| ← getPPOption getPPNotation
  -- No delaboration when `pp.explicit` is set as `true`
  guard <| !(← getPPOption getPPExplicit)
  withOverApp arity do
    -- No delaboration for non-lambda expressions (e.g., `tforall Φ`)
    guard (← SubExpr.getExpr).appArg!.isLambda
    SubExpr.withAppArg <| withBindingBodyUnusedName fun x => do
      let body ← fn (← delab)
      -- Nested quantifiers are collapsed (e.g. `∀ x, ∀ y, P x y` as `∀ x y, P x y`)
      match collapseFunction body with
      | some (y, ys, Ψ) => termCreator ⟨x⟩ (#[y] ++ ys) Ψ
      | none            => termCreator ⟨x⟩ #[] body
