import Iris.Proofmode.Environments

import Lean.PrettyPrinter.Delaborator

namespace Iris.Proofmode
open Lean Lean.Expr Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

declare_syntax_cat envs_display
declare_syntax_cat envs_display_line

syntax envs_display_line ppDedent(ppLine envs_display_line)* : envs_display
syntax "Iris Proof Mode" : envs_display_line
syntax "─"+ : envs_display_line
syntax "─"+ " □" : envs_display_line
syntax "─"+ " ∗" : envs_display_line
syntax (ident)? " : " iprop : envs_display_line

abbrev delab := Lean.PrettyPrinter.delab

@[delab app.Iris.Proofmode.envs_entails]
def delabEnvsEntails : Delab := do
  let expr ← (← getExpr) |> instantiateMVars

  -- extract environment
  let some (Γₚ, Γₛ, P) := extractEnvsEntails? expr
    | throwError "ill-formed proof environment"

  let some Γₚ := extractHypotheses? Γₚ
    | throwError "ill-formed proof environment"
  let some Γₛ := extractHypotheses? Γₛ
    | throwError "ill-formed proof environment"

  -- delaborate
  let Γₚ ← delabHypotheses Γₚ
  let Γₛ ← delabHypotheses Γₛ

  let P ← delab P

  -- build syntax
  `(envs_display| Iris Proof Mode
                  ─────────────────────────────────────
                  $Γₚ:envs_display_line*
                  ───────────────────────────────────── □
                  $Γₛ:envs_display_line*
                  ───────────────────────────────────── ∗
                  $P)
where
  extractHypotheses? (Γ : Expr) : Option $ Array $ Option Name × Expr :=
    Γ.asListExpr_toList?.map (· |>.map (fun h => (getMDataName? h, h)) |>.toArray)

  delabHypotheses (Γ : Array $ Option Name × Expr) : DelabM $ Array Syntax :=
    Γ.mapM fun (name?, h) => do
      let h ← delab h
      if let some name := name? then
        let name := mkIdent name
        `(envs_display_line| $name:ident : $h)
      else
        `(envs_display_line| : $h)

end Iris.Proofmode
