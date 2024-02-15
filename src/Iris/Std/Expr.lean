/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Lean.Expr
import Lean.Meta

namespace Lean.Expr
open Lean.Meta

/-- If `e` represents an application of a function with the name `fname`, return the
representations of its arguments. Otherwise return `none`. -/
def appM? (e : Expr) (fName : Name) : Option <| Array Expr :=
  if e.isAppOf fName then
    e.getAppArgs
  else
    none

/-- Modify the arguments of the function application represented by `e`. If an element in `args` is
`none`, then the corresponding argument in the function application remains unchanged. -/
def modifyAppOptM (e : Expr) (args : Array <| Option Expr) : Expr :=
  mkAppN e.getAppFn <| e.getAppArgs.zipWith args (fun a b => if let some b := b then b else a)


/-- Get the `mdata` entry with the key `"name"`, if available. -/
def getMDataName? : Expr → Option Name
  | Expr.mdata md _ => md.get? "name"
  | _ => none

/-- Set the `mdata` entry of `e` with the key `"name"` to `name`. -/
def setMDataName? (e : Expr) (name : Name) : Expr := match e with
  | Expr.mdata md e =>
    mkMData (md.insert "name" name) e
  | e =>
    mkMData (KVMap.empty.insert "name" name) e

end Lean.Expr
