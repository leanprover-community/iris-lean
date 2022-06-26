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


def getMDataName? : Expr → Option Name
  | Expr.mdata md _ _ => md.get? "name"
  | _ => none

def setMDataName? (e : Expr) (name : Name) : Expr := match e with
  | Expr.mdata md e _ =>
    mkMData (md.insert "name" name) e
  | e =>
    mkMData (KVMap.empty.insert "name" name) e

end Lean.Expr
