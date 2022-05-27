import Iris.BI
import Iris.Proofmode.Environments
import Iris.Std.Expr

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr

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

end Iris.Proofmode
