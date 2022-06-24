import Lean.Expr
import Lean.Meta

namespace Lean.Expr
open Lean.Meta

def appM? (e : Expr) (fName : Name) : Option <| Array Expr :=
  if e.isAppOf fName then
    e.getAppArgs
  else
    none

def modifyAppOptM (e : Expr) (args : Array <| Option Expr) : Expr :=
  mkAppN e.getAppFn <| e.getAppArgs.zipWith args (fun a b => if let some b := b then b else a)


partial def asListExpr_any? (list : Expr) (pred : Expr → Bool) : MetaM <| Option Bool := do
  let list ← whnf list
  if let some (_, a, list') := app3? list `List.cons then
    if pred a then return true
    else asListExpr_any? list' pred
  else if let some _ := app1? list `List.nil then
    return false
  else
    return none

partial def asListExpr_findIndexM? [Monad M] [MonadLift MetaM M] (list : Expr) (pred : Expr → M Bool) : M <| Option Nat :=
  go list 0
where
  go (list : Expr) (idx : Nat) : M <| Option Nat := do
    let list ← whnf list
    if let some (_, a, list') := app3? list `List.cons then
      if ← pred a then pure <| some idx
      else go list' (idx + 1)
    else
      pure none

partial def asListExpr_findIndex? (list : Expr) (pred : Expr → Bool) : MetaM <| Option Nat := do
  have : MonadLift MetaM MetaM := { monadLift := id }
  asListExpr_findIndexM? list (return pred ·)

def asListExpr_get? (list : Expr) (i : Nat) : MetaM <| Option Expr := do
  let list ← whnf list
  match i with
  | 0 =>
    if let some (_, a, _) := app3? list `List.cons then
      return a
    else
      return none
  | i + 1 =>
    if let some (_, _, list') := app3? list `List.cons then
      asListExpr_get? list' i
    else
      return none

partial def asListExpr_length? (list : Expr) : MetaM <| Option Nat :=
  go list 0
where
  go (list : Expr) (length : Nat) : MetaM <| Option Nat := do
    let list ← whnf list
    if let some (_, _, list') := app3? list `List.cons then
      go list' (length + 1)
    else if let some _ := app1? list `List.nil then
      return length
    else
      return none

def asListExpr_set? (list : Expr) (e : Expr) (i : Nat) : MetaM <| Option Expr := do
  let list ← whnf list
  match i with
  | 0 => do
    let some _ := app3? list `List.cons
      | pure none
    return modifyAppOptM list #[none, e, none]
  | i + 1 => do
    let some (_, _, list') := app3? list `List.cons
      | pure none
    let some list' ← asListExpr_set? list' e i
      | pure none
    return modifyAppOptM list #[none, none, list']

partial def asListExpr_toList? (list : Expr) : MetaM <| Option <| List Expr := do
  let list ← whnf list
  if let some (_, a, list') := app3? list `List.cons then
    return (← asListExpr_toList? list') |>.map (a :: ·)
  else if let some _ := app1? list `List.nil then
    return some []
  else
    return none


def getMDataName? : Expr → Option Name
  | Expr.mdata md _ _ => md.get? "name"
  | _ => none

def setMDataName? (e : Expr) (name : Name) : Expr := match e with
  | Expr.mdata md e _ =>
    mkMData (md.insert "name" name) e
  | e =>
    mkMData (KVMap.empty.insert "name" name) e

end Lean.Expr
