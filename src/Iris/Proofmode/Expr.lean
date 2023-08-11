/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Proofmode.Environments
import Iris.Std.Expr

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr Lean.Meta

/-- Return whether `expr` is an application of `BIBase.emp`. -/
def isEmp (expr : Expr) : MetaM Bool := do
  let expr ← withReducible <| whnf expr
  return expr.isAppOfArity ``BIBase.emp 2

/-- Return whether `expr` is an application of `EnvsEntails`. -/
def isEnvsEntails (expr : Expr) : MetaM Bool := do
  let expr ← withReducible <| whnf expr
  return expr.isAppOfArity ``EnvsEntails 4

/-- Extract the premise and conclusion from an application of `BIBase.entails`. -/
def extractEntails? (expr : Expr) : MetaM <| Option <| Expr × Expr := do
  let expr ← withReducible <| whnf expr
  let some #[_, _, P, Q] := appM? expr ``Entails
    | return none
  return some (P, Q)

/-- Extract the intuitionistic and spatial context, as well as the goal from an application
of `EnvsEntails`. -/
def extractEnvsEntails? (expr : Expr) : MetaM <| Option <| Expr × Expr × Expr := do
  let expr ← withReducible <| whnf expr
  let some #[_, _, envs, P] := appM? expr ``EnvsEntails
    | return none
  let envs ← withReducible <| whnf envs
  let some #[_, _, Γₚ, Γₛ] := appM? envs ``Envs.mk
    | return none
  return some (Γₚ, Γₛ, P)

/-- Update an application of `EnvsEntails` with a new intuitionistic (`Γₚ`) and spatial (`Γₛ`)
context, as well as with a new goal (`P`). If any part is `none`, the value from the original
expression `expr` is used instead. -/
def modifyEnvsEntails? (expr : Expr) (Γₚ Γₛ P : Option Expr) : MetaM <| Option Expr := do
  let expr ← withReducible <| whnf expr
  let some #[_, _, envs, _] := appM? expr ``EnvsEntails
    | return none
  let envs ← withReducible <| whnf envs
  let some #[_, _, _, _] := appM? envs ``Envs.mk
    | return none
  let envs := modifyAppOptM envs #[none, none, Γₚ, Γₛ]
  let expr := modifyAppOptM expr #[none, none, envs, P]
  return some expr


namespace EnvExpr

/-- Return `true` iff any expression in the environment represented by `env` fulfills the predicate
`pred`. The function returns `none` if `env` is not an application of `Env.cons` and `Env.nil`. -/
partial def any? (env : Expr) (pred : Expr → Bool) : MetaM <| Option Bool := do
  let env ← whnf env
  if let some (_, a, env') := app3? env ``Env.cons then
    if pred a then return true
    else any? env' pred
  else if let some _ := app1? env ``Env.nil then
    return false
  else
    return none

/-- Find the index of the first hypothesis in the environment represented by `env` which fulfills
the predicate `pred`. The function returns `none` if `env` is not an application of `Env.cons`
and `Env.nil` or no hypothesis fulfills the predicate `pred`. -/
partial def findIndexM? [Monad M] [MonadLift MetaM M] (env : Expr) (pred : Expr → M Bool) :
    M <| Option Nat := go env 0
where
  go (env : Expr) (idx : Nat) : M <| Option Nat := do
    let env ← whnf env
    if let some (_, a, env') := app3? env ``Env.cons then
      if ← pred a then pure <| some idx
      else go env' (idx + 1)
    else
      pure none

/-- Find the index of the first hypothesis in the environment represented by `env` which fulfills
the predicate `pred`. The function returns `none` if `env` is not an application of `Env.cons`
and `Env.nil` or no hypothesis fulfills the predicate `pred`. -/
partial def findIndex? (env : Expr) (pred : Expr → Bool) : MetaM <| Option Nat := do
  have : MonadLift MetaM MetaM := { monadLift := id }
  findIndexM? env (return pred ·)

/-- Return the expression representing the hypothesis at index `i` in the environment represented
by `env`. The function returns `none` if `env` is not an application of `Env.cons` and `Env.nil` or
the index is invalid. -/
def get? (env : Expr) (i : Nat) : MetaM <| Option Expr := do
  let env ← whnf env
  match i with
  | 0 =>
    if let some (_, a, _) := app3? env ``Env.cons then
      return a
    else
      return none
  | i + 1 =>
    if let some (_, _, env') := app3? env ``Env.cons then
      get? env' i
    else
      return none

/-- Return the length of the environment represented by `env`. The function returns `none` if `env`
is not an application of `Env.cons` and `Env.nil`. -/
partial def length? (env : Expr) : MetaM <| Option Nat :=
  go env 0
where
  go (env : Expr) (length : Nat) : MetaM <| Option Nat := do
    let env ← whnf env
    if let some (_, _, env') := app3? env ``Env.cons then
      go env' (length + 1)
    else if let some _ := app1? env ``Env.nil then
      return length
    else
      return none

/-- Set the hypothesis represented by `e` at index `i` in the environment represented by `env`. The
function returns `none` if `env` is not an application of `Env.cons` and `Env.nil` or the index
is invalid. -/
def set? (env : Expr) (e : Expr) (i : Nat) : MetaM <| Option Expr := do
  let env ← whnf env
  match i with
  | 0 => do
    let some _ := app3? env ``Env.cons
      | pure none
    return modifyAppOptM env #[none, e, none]
  | i + 1 => do
    let some (_, _, env') := app3? env ``Env.cons
      | pure none
    let some env' ← set? env' e i
      | pure none
    return modifyAppOptM env #[none, none, env']

/-- Turn the representation `env` of an environment with any hypothesis type into an actual
environment with hypotheses of type `Expr`. The hypothesis representations in the returned
environment are the same as in the original representation `env`. -/
partial def toEnv? (env : Expr) : MetaM <| Option <| Env Expr := do
  let env ← whnf env
  if let some (_, a, env') := app3? env ``Env.cons then
    return (← toEnv? env') |>.map (.cons a ·)
  else if let some _ := app1? env ``Env.nil then
    return some .nil
  else
    return none

end EnvExpr
end Iris.Proofmode
