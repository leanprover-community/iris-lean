module

import Iris.HeapLang.Omni
import Std.Tactic.Do

open Iris.HeapLang Lean.Order Std.Internal.Do

namespace Iris.HeapLang.VcgenSmoke

/-! ## Approach-1 smoke test: spec-driven evaluation-order for `binop`.

Four `@[spec]` lemmas, all in the internal engine's `pre ⊑ wp` shape:
value, head-redex, right-focus, left-focus. Priorities make the most-evaluated
pattern win, so a nested `binop` tree is walked right-to-left down to leaves. -/

/-- Value form. -/
@[spec high] theorem val_spec (v : Val) (post : Val → State → Prop) (epost : EPost.Nil) :
    post v ⊑ Std.Internal.Do.wp ((.ofVal v : Exp)) post epost := by
  intro σ h; exact wp_val.mpr h

/-- Head redex: both operands are values. -/
@[spec high] theorem binop_redex_spec {op : BinOp} {v1 v2 v' : Val}
    (hop : op.eval v1 v2 = some v') (post : Val → State → Prop) (epost : EPost.Nil) :
    post v' ⊑ Std.Internal.Do.wp (Exp.binop op (.ofVal v1) (.ofVal v2)) post epost := by
  intro σ h; exact wp_binop hop h

/-- Left-focus: right operand already a value, evaluate the left. -/
@[spec] theorem binop_focusL_spec {op : BinOp} {e1 : Exp} {v2 : Val}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e1 (fun v1 => Std.Internal.Do.wp (Exp.binop op (.ofVal v1) (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.binop op e1 (.ofVal v2)) post epost := by
  intro σ h; exact wp_bind_fill [.binOpL op v2] h

/-- Right-focus: evaluate the right operand first (HeapLang is right-to-left). -/
@[spec low] theorem binop_focusR_spec {op : BinOp} {e1 e2 : Exp}
    (post : Val → State → Prop) (epost : EPost.Nil) :
    Std.Internal.Do.wp e2 (fun v2 => Std.Internal.Do.wp (Exp.binop op e1 (.ofVal v2)) post epost) epost
      ⊑ Std.Internal.Do.wp (Exp.binop op e1 e2) post epost := by
  intro σ h; exact wp_bind_fill [.binOpR op e1] h

/-! ## The program `(1 + 2) + (3 + 4)`. -/

/-- `vcgen` executes the nested tree and reduces the goal to the arithmetic VCs. -/
example : (fun _ => True) ⊑ Std.Internal.Do.wp hl((#1 + #2) + (#3 + #4)) (fun r _ => r = .lit (.int 10)) EPost.Nil.mk := by
  vcgen
  -- Order matters here, atm
  case vc3 => rfl
  case vc5 => rfl
  case vc1 => rfl

end Iris.HeapLang.VcgenSmoke
