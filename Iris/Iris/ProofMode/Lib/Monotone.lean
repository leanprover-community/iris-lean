/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Markus de Medeiros
-/
module

public meta import Iris.BI.Lib.Monotone
public meta import Iris.ProofMode

namespace Iris

open Lean Elab Tactic Meta BI

/-- Apply one `IMono` rule for a connective. Extend it with `macro_rules`. -/
syntax "imono_rule" : tactic

macro_rules
  | `(tactic| imono_rule) => `(tactic| first
      | apply IMono.sep | apply IMono.and | apply IMono.or | apply IMono.wand
      | apply IMono.pers_imp | apply IMono.forall | apply IMono.exists
      | apply IMono.persistently | apply IMono.affinely | apply IMono.absorbingly
      | apply IMono.intuitionistically | apply IMono.later | apply IMono.laterN
      | apply IMono.except0 | apply IMono.bupd | apply IMono.fupd | apply IMono.step_fupdN
      | apply IMono.bigSepL | apply IMono.bigAndL | apply IMono.bigOrL | apply IMono.bigSepL2
      | apply IMono.bigSepM | apply IMono.bigSepS | apply IMono.bigSepMS)

/-- Unfold the definition at the head of `P` in a goal `⊢ □ R -∗ P -∗ P'`. -/
elab "imono_unfold" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let unexpected {α} : TacticM α := throwError "imono: unexpected goal{indentExpr target}"
  let_expr BIBase.EmpValid _ _ goal := target | unexpected
  let_expr BIBase.wand _ _ _ body := goal | unexpected
  let_expr BIBase.wand _ _ P _ := body | unexpected
  let some fn := P.getAppFn.constName? | throwError "imono: nothing to unfold in{indentExpr P}"
  if (`Iris.BI.BIBase).isPrefixOf fn || (← getProjectionFnInfo? fn).any (·.fromClass) then
    throwError "imono: no rule for {fn}"
  evalTactic (← `(tactic| unfold $(mkIdent fn):ident))

/-- One step of `imono`, on a goal `⊢ □ R -∗ P -∗ P'`. -/
syntax "imono_step" : tactic

macro_rules
  | `(tactic| imono_step) => `(tactic| first
      | exact IMono.refl
      | (imono_rule <;> intros <;> imono_step)
      | (iintro #H HP; iapply H; iexact HP)
      | (split <;> imono_step)
      | (imono_unfold; imono_step))

/-- Prove that a fixpoint body `F` is monotone, stated as `BIMono F` or with its arguments spelled
out: `∀ Φ Ψ, ⊢ □ (∀ x y, Φ x y -∗ Ψ x y) -∗ ∀ x y, F Φ x y -∗ F Ψ x y`. The body is taken apart one
connective at a time, down to the recursive calls; `match`es are split, and other definitions
unfolded. -/
macro "imono" : tactic => `(tactic| (
  try unfold BIMono
  intro Φ Ψ
  repeat (apply IMono.arg; intro)
  try dsimp only
  imono_step))

end Iris
