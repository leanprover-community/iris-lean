import Iris.BI
import Iris.Std.Expr

import Lean.Expr

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr

structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : List PROP
  spatial : List PROP

inductive HypothesisType | intuitionistic | spatial

def of_envs [BI PROP] (Γₚ Γₛ : List PROP) : PROP :=
  match Γₚ, Γₛ with
  | [], [] => `[iprop| emp]
  | _, []  => `[iprop| □ [∧] Γₚ]
  | [], _  => `[iprop| [∗] Γₛ]
  | _, _   => `[iprop| □ [∧] Γₚ ∗ [∗] Γₛ]

def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ.intuitionistic Δ.spatial ⊢ Q


def isEnvsEntails (expr : Expr) : Bool := expr.isAppOfArity ``envs_entails 4

def extractEnvsEntails? (expr : Expr) : Option (Expr × Expr × Expr) := Id.run <| do
  let some #[_, _, envs, P] := appM? expr ``envs_entails
    | none
  let some #[_, _, Γₚ, Γₛ] := appM? envs ``Envs.mk
    | none
  return (Γₚ, Γₛ, P)

def modifyEnvsEntails? (expr : Expr) (Γₚ Γₛ P : Option Expr) : Option Expr := Id.run <| do
  let some #[_, _, envs, _] := appM? expr ``envs_entails
    | none
  let some #[_, _, _, _] := appM? envs ``Envs.mk
    | none
  let envs := modifyAppOptM envs #[none, none, Γₚ, Γₛ]
  let expr := modifyAppOptM expr #[none, none, envs, P]
  return expr

end Iris.Proofmode
