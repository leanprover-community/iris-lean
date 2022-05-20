import Lean.Expr
import Lean.Meta

namespace Lean.Expr

def appM? (e : Expr) (fName : Name) : Option (Array Expr) :=
  if e.isAppOf fName then
    e.getAppArgs
  else
    none

def modifyAppOptM (e : Expr) (args : Array (Option Expr)) : Expr :=
  mkAppN e.getAppFn <| e.getAppArgs.zipWith args (fun a b => if let some b := b then b else a)

partial def asListExpr_any? (list : Expr) (pred : Expr → Bool) : Option Bool :=
  if let some (_, a, list') := app3? list `List.cons then
    if pred a then true
    else asListExpr_any? list' pred
  else if let some _ := app1? list `List.nil then
    false
  else
    none

partial def asListExpr_findIndexM? [Monad M] (list : Expr) (pred : Expr → M Bool) : M <| Option Nat :=
  go list 0
where
  go (list : Expr) (idx : Nat) : M <| Option Nat := do
    if let some (_, a, list') := app3? list `List.cons then
      if (← pred a) then pure <| some idx
      else go list' (idx + 1)
    else
      pure none

partial def asListExpr_findIndex? (list : Expr) (pred : Expr → Bool) : Option Nat := Id.run <| do
  asListExpr_findIndexM? list pred

def asListExpr_get? (list : Expr) : Nat → Option Expr
  | 0 => Id.run <| do
    let some (_, a, _) := app3? list `List.cons
      | none
    return a
  | n + 1 => Id.run <| do
    let some (_, _, list') := app3? list `List.cons
      | none
    return asListExpr_get? list' n

partial def asListExpr_length? (list : Expr) : Option Nat :=
  go list 0
where
  go (list : Expr) (length : Nat) : Option Nat :=
    if let some (_, _, list') := app3? list `List.cons then
      go list' (length + 1)
    else if let some _ := app1? list `List.nil then
      length
    else
      none

def asListExpr_set? (list : Expr) (e : Expr) : Nat → Option Expr
  | 0 => Id.run <| do
    let some (_, a, _) := app3? list `List.cons
      | none
    return modifyAppOptM list #[none, e, none]
  | n + 1 => Id.run <| do
    let some (_, _, list') := app3? list `List.cons
      | none
    let some list' := asListExpr_set? list' e n
      | none
    return modifyAppOptM list #[none, none, list']

partial def asListExpr_toList? (list : Expr) : Option (List Expr) := Id.run <| do
  if let some (_, a, list') := app3? list `List.cons then
    return asListExpr_toList? list' |>.map (a :: ·)
  else if let some _ := app1? list `List.nil then
    return some []
  else
    return none

def getMDataName? (e : Expr) : Option Name := match e with
  | Expr.mdata md _ _ => md.get? "name"
  | _ => none

def setMDataName? (e : Expr) (name : Name) : Expr := match e with
  | Expr.mdata md e _ =>
    mkMData (md.insert "name" name) e
  | e =>
    mkMData (KVMap.empty.insert "name" name) e

end Lean.Expr
