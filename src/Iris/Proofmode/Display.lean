import Iris.BI.Notation
import Iris.Proofmode.Environments
import Iris.Proofmode.Expr

import Lean.PrettyPrinter.Delaborator

namespace Iris.Proofmode
open Iris.BI
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

declare_syntax_cat envs_display
declare_syntax_cat envs_display_line

syntax envs_display_line ppDedent(ppLine envs_display_line)* : envs_display
syntax "Iris Proof Mode" : envs_display_line
syntax "─"+ : envs_display_line
syntax "─"+ " □" : envs_display_line
syntax "─"+ " ∗" : envs_display_line
syntax (ident)? " : " term : envs_display_line

abbrev delab := Lean.PrettyPrinter.delab

@[delab app.Iris.Proofmode.envs_entails]
def delabEnvsEntails : Delab := do
  let expr ← (← getExpr) |> instantiateMVars

  -- extract environment
  let some (Γₚ, Γₛ, P) := extractEnvsEntails? expr
    | failure

  let some Γₚ := extractHypotheses? Γₚ
    | failure
  let some Γₛ := extractHypotheses? Γₛ
    | failure

  -- delaborate
  let Γₚ ← delabHypotheses Γₚ
  let Γₛ ← delabHypotheses Γₛ

  let P ← unpackIprop (← delab P)

  -- build syntax
  `(envs_display| Iris Proof Mode
                  ─────────────────────────────────────
                  $Γₚ:envs_display_line*
                  ───────────────────────────────────── □
                  $Γₛ:envs_display_line*
                  ───────────────────────────────────── ∗
                  $P)
where
  extractHypotheses? (Γ : Expr) : Option <| Array <| Option Name × Expr :=
    Γ.asListExpr_toList?.map (· |>.map (fun h => (h.getMDataName?, h)) |>.toArray)

  delabHypotheses (Γ : Array <| Option Name × Expr) : DelabM <| Array Syntax :=
    Γ.mapM fun (name?, h) => do
      let h ← unpackIprop (← delab h)
      if let some name := name? then
        let name := mkIdent name
        `(envs_display_line| $name:ident : $h)
      else
        `(envs_display_line| : $h)

end Iris.Proofmode
