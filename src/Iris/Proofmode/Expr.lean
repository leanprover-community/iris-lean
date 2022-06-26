import Iris.BI
import Iris.Proofmode.Environments
import Iris.Std.Expr

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr Lean.Meta

def isEmp (expr : Expr) : Bool := expr.isAppOfArity ``BIBase.emp 2

def isEnvsEntails (expr : Expr) : Bool := expr.isAppOfArity ``envs_entails 4

def extractEntails? (expr : Expr) : Option (Expr × Expr) := Id.run do
  let some #[_, _, P, Q] := appM? expr ``BIBase.entails
    | none
  some (P, Q)

def extractEnvsEntails? (expr : Expr) : Option (Expr × Expr × Expr) := Id.run do
  let some #[_, _, envs, P] := appM? expr ``envs_entails
    | none
  let some #[_, _, Γₚ, Γₛ] := appM? envs ``Envs.mk
    | none
  some (Γₚ, Γₛ, P)

def modifyEnvsEntails? (expr : Expr) (Γₚ Γₛ P : Option Expr) : Option Expr := Id.run do
  let some #[_, _, envs, _] := appM? expr ``envs_entails
    | none
  let some #[_, _, _, _] := appM? envs ``Envs.mk
    | none
  let envs := modifyAppOptM envs #[none, none, Γₚ, Γₛ]
  let expr := modifyAppOptM expr #[none, none, envs, P]
  some expr


namespace EnvExpr

partial def any? (env : Expr) (pred : Expr → Bool) : MetaM <| Option Bool := do
  let env ← whnf env
  if let some (_, a, env') := app3? env ``Env.cons then
    if pred a then return true
    else any? env' pred
  else if let some _ := app1? env ``Env.nil then
    return false
  else
    return none

partial def findIndexM? [Monad M] [MonadLift MetaM M] (env : Expr) (pred : Expr → M Bool) : M <| Option Nat :=
  go env 0
where
  go (env : Expr) (idx : Nat) : M <| Option Nat := do
    let env ← whnf env
    if let some (_, a, env') := app3? env ``Env.cons then
      if ← pred a then pure <| some idx
      else go env' (idx + 1)
    else
      pure none

partial def findIndex? (env : Expr) (pred : Expr → Bool) : MetaM <| Option Nat := do
  have : MonadLift MetaM MetaM := { monadLift := id }
  findIndexM? env (return pred ·)

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
