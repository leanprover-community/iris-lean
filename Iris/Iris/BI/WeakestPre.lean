module

public import Iris.Std.CoPset
public meta import Iris.Std.Rewrite
public import Std
meta import Lean
public import Lean

public section

#check Lean.PrettyPrinter.Unexpander

open Lean

inductive Stuckness where
| NotStuck
| MaybeStuck

namespace Stuckness

@[simp]
instance instLE: LE Stuckness where
  le x y := ¬ (x = .MaybeStuck ∧ y = .NotStuck)

instance : Std.IsPreorder Stuckness where
  le_refl := by
    simp only [LE.le, not_and, forall_eq, reduceCtorEq, not_false_eq_true]
  le_trans := by
    simp only [LE.le]; grind only [Stuckness]

end Stuckness

class Wp (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _) where
  wp : A → CoPset → Expr → (Val → PROP) → PROP

class TotalWP (PROP Expr) (Val : outParam (Type _)) (A : Type _) where
  totalWp : A → CoPset → Expr → (Val → PROP) → PROP

syntax wp_expr :=
    term:max (" @ " term:max (" ; " term:max) <|> ((" ? ")? )) <|> (" ? ")?

declare_syntax_cat wp_postcond_inner
syntax ident ", " term : wp_postcond_inner
syntax term : wp_postcond_inner

declare_syntax_cat wp_postcond
syntax " {{ " wp_postcond_inner " }} " : wp_postcond
syntax " [{ " wp_postcond_inner " }] " : wp_postcond
syntax " ⦃ " wp_postcond_inner " ⦄ " : wp_postcond -- Are spaces outside of parens used in the pp?
syntax " 〖 " wp_postcond_inner " 〗 "  : wp_postcond

syntax (name := wp) "WP " wp_expr wp_postcond : term

/- This section checks whether the syntax is recognized correctly for all combinations -/
section testNotation
set_option trace.Elab.info false

/-- Suppress all `info` level messages from a command -/
elab "#no_info" "in" cmd:command : command => do
  Lean.Elab.Command.elabCommandTopLevel cmd
  modify fun st => {st with
    messages := {st.messages with
      unreported := st.messages.unreported.filter (¬ ·.severity matches MessageSeverity.information)
    }
  }

#no_info in #check_failure WP e @ s ; E {{ Φ }}
#no_info in #check_failure WP e @ E {{ Φ }}
#no_info in #check_failure WP e @ E ? {{ Φ }}
#no_info in #check_failure WP e {{ Φ }}
#no_info in #check_failure WP e ? {{ Φ }}

#no_info in #check_failure WP e @ s ; E {{v,  Φ }}
#no_info in #check_failure WP e @ E {{v,  Φ }}
#no_info in #check_failure WP e @ E ? {{v,  Φ }}
#no_info in #check_failure WP e {{v,  Φ }}
#no_info in #check_failure WP e ? {{v,  Φ }}

#no_info in #check_failure WP e @ s ; E ⦃ Φ ⦄
#no_info in #check_failure WP e @ E ⦃ Φ ⦄
#no_info in #check_failure WP e @ E ? ⦃ Φ ⦄
#no_info in #check_failure WP e ⦃ Φ ⦄
#no_info in #check_failure WP e ? ⦃ Φ ⦄

#no_info in #check_failure WP e @ s ; E ⦃v,  Φ ⦄
#no_info in #check_failure WP e @ E ⦃v,  Φ ⦄
#no_info in #check_failure WP e @ E ? ⦃v,  Φ ⦄
#no_info in #check_failure WP e ⦃v,  Φ ⦄
#no_info in #check_failure WP e ? ⦃v,  Φ ⦄

#no_info in #check_failure WP e @ s ; E [{ Φ }]
#no_info in #check_failure WP e @ E [{ Φ }]
#no_info in #check_failure WP e @ E ? [{ Φ }]
#no_info in #check_failure WP e [{ Φ }]
#no_info in #check_failure WP e ? [{ Φ }]

#no_info in #check_failure WP e @ s ; E [{v,  Φ }]
#no_info in #check_failure WP e @ E [{v,  Φ }]
#no_info in #check_failure WP e @ E ? [{v,  Φ }]
#no_info in #check_failure WP e [{v,  Φ }]
#no_info in #check_failure WP e ? [{v,  Φ }]

#no_info in #check_failure WP e @ s ; E 〖 Φ 〗
#no_info in #check_failure WP e @ E 〖 Φ 〗
#no_info in #check_failure WP e @ E ? 〖 Φ 〗
#no_info in #check_failure WP e 〖 Φ 〗
#no_info in #check_failure WP e ? 〖 Φ 〗

#no_info in #check_failure WP e @ s ; E 〖v,  Φ 〗
#no_info in #check_failure WP e @ E 〖v,  Φ 〗
#no_info in #check_failure WP e @ E ? 〖v,  Φ 〗
#no_info in #check_failure WP e 〖v,  Φ 〗
#no_info in #check_failure WP e ? 〖v,  Φ 〗

end testNotation

open Lean in
meta def parseWpExpr : Lean.TSyntax `wp_expr → Lean.MacroM (TSyntax `term × TSyntax `term × TSyntax `term) := fun
  | `(wp_expr| $e @ $s ; $E) =>
    return (e, s, E)
  | `(wp_expr| $e @ $E) =>
    return (e, ←`(Stuckness.NotStuck), E)
  | `(wp_expr| $e @ $E ?) =>
    return (e, ←`(Stuckness.MaybeStuck), E)
  | `(wp_expr| $e:term) =>
    return (e, ←`(Stuckness.NotStuck), ←`(⊤))
  | `(wp_expr| $e:term ?) =>
    return (e, ←`(Stuckness.MaybeStuck), ←`(⊤))
  | _ => Lean.Macro.throwUnsupported

open Lean in
meta def parseWpPostcondInner (stx : TSyntax `wp_postcond_inner) : MacroM (TSyntax `term) := do
  match stx with
  | `(wp_postcond_inner| $v:ident, $Φ:term) => `(fun $v => $Φ)
  | `(wp_postcond_inner| $Φ:term) => return Φ
  | _ => Macro.throwUnsupported

open Lean in
meta def parseWpPostcond (stx : TSyntax `wp_postcond) : MacroM (TSyntax `term × Bool) := do
  match stx with
  | `(wp_postcond| {{ $inner:wp_postcond_inner }})
  | `(wp_postcond| ⦃ $inner:wp_postcond_inner ⦄) =>
    return (←parseWpPostcondInner inner, false)
  | `(wp_postcond| [{ $inner:wp_postcond_inner }])
  | `(wp_postcond| 〖 $inner:wp_postcond_inner 〗) =>
    return (←parseWpPostcondInner inner, true)
  | _ => Macro.throwUnsupported (α := TSyntax `term × Bool)

@[macro wp]
meta def wpMacro : Lean.Macro := fun stx => do
  match stx with
  | `(WP $expr $postcond) =>
    let (e, s, E) ← parseWpExpr expr
    let (Φ, useTotal?) ← parseWpPostcond postcond
    if useTotal? then
      `(TotalWP.totalWp $s $E $e $Φ)
    else
      `(Wp.wp $s $E $e $Φ)
  | _ => Lean.Macro.throwUnsupported

section testElab
set_option linter.unusedVariables false

variable (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _)
variable [Wp PROP Expr Val A]
variable [Wp PROP Expr Val Stuckness]
variable [TotalWP PROP Expr Val A]
variable [TotalWP PROP Expr Val Stuckness]

variable (e : Expr)(s : A)(E : CoPset)
variable (Φ : PROP)

/-- info: Wp.wp s E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ s ; E {{v,  Φ }}
/-- info: Wp.wp Stuckness.NotStuck E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ E {{ v,  Φ}}
/-- info: Wp.wp Stuckness.NotStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e {{v,  Φ }}
/-- info: Wp.wp Stuckness.MaybeStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e ? {{v,  Φ }}

/-- info: TotalWP.totalWp s E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ s ; E [{v,  Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ E [{ v,  Φ}]
/-- info: TotalWP.totalWp Stuckness.NotStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e [{v,  Φ }]
/-- info: TotalWP.totalWp Stuckness.MaybeStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e ? [{v,  Φ }]

variable (Φ : Val → PROP)

/-- info: Wp.wp s E e Φ : PROP -/
#guard_msgs in #check WP e @ s ; E {{ Φ }}
/-- info: Wp.wp Stuckness.NotStuck E e Φ : PROP -/
#guard_msgs in #check WP e @ E {{  Φ}}
/-- info: Wp.wp Stuckness.NotStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e {{ Φ }}
/-- info: Wp.wp Stuckness.MaybeStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e ? {{ Φ }}

/-- info: TotalWP.totalWp s E e Φ : PROP -/
#guard_msgs in #check WP e @ s ; E [{ Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck E e Φ : PROP -/
#guard_msgs in #check WP e @ E [{  Φ}]
/-- info: TotalWP.totalWp Stuckness.NotStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e [{ Φ }]
/-- info: TotalWP.totalWp Stuckness.MaybeStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e ? [{ Φ }]

end testElab

meta def unexpandWpPostcondInner : TSyntax `term → PrettyPrinter.UnexpandM (TSyntax `wp_postcond_inner)
  | `(fun $v:ident => $Φ:term) => `(wp_postcond_inner|$v:ident, $Φ:term)
  | `($Φ:term) => `(wp_postcond_inner| $Φ:term)

open Lean in
meta def makeWpExpr (s E e : TSyntax `term) : PrettyPrinter.UnexpandM (TSyntax `wp_expr) := do
  match s, E with
  | `(Stuckness.NotStuck), `(⊤) => `(wp_expr| $e:term)
  | `(Stuckness.NotStuck), E => `(wp_expr| $e:term @ $E:term)
  | `(Stuckness.MaybeStuck), `(⊤) => `(wp_expr| $e:term ?)
  | `(Stuckness.MaybeStuck), E => `(wp_expr| $e:term @ $E:term ?)
  | s, E => `(wp_expr| $e:term @ $s:term ; $E:term)

@[app_unexpander Wp.wp]
meta def unexpanderWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $e $Φ) => do
    let wp_expr ← makeWpExpr s E e
    let wp_postcond_inner ← unexpandWpPostcondInner Φ
    `(WP $wp_expr {{ $wp_postcond_inner }})
  | _ => throw ()

@[app_unexpander TotalWP.totalWp]
meta def unexpanderTotalWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $e $Φ) => do
    let wp_expr ← makeWpExpr s E e
    let wp_postcond_inner ← unexpandWpPostcondInner Φ
    `(WP $wp_expr [{ $wp_postcond_inner }])
  | _ => throw ()

section testUnexpand
set_option linter.unusedVariables false

variable (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _)
variable [Wp PROP Expr Val A]
variable [Wp PROP Expr Val Stuckness]
variable [TotalWP PROP Expr Val A]
variable [TotalWP PROP Expr Val Stuckness]

variable (e : Expr)(s : A)(E : CoPset)
variable (Φ : PROP)

/-- info: WP e @ s ; E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E {{v,  Φ }}
/-- info: WP e @ E {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E {{ v,  Φ}}
/-- info: WP e @ E ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? {{ v,  Φ}}
/-- info: WP e {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e {{v,  Φ }}
/-- info: WP e ? {{ v, Φ }} : PROP -/
#guard_msgs in #check WP e ? {{v,  Φ }}

/-- info: WP e @ s ; E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E [{v,  Φ }]
/-- info: WP e @ E [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E [{ v,  Φ}]
/-- info: WP e @ E ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? [{ v,  Φ}]
/-- info: WP e [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e [{v,  Φ }]
/-- info: WP e ? [{ v, Φ }] : PROP -/
#guard_msgs in #check WP e ? [{v,  Φ }]

variable (Φ : Val → PROP)

/-- info: WP e @ s ; E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ s ; E {{ Φ }}
/-- info: WP e @ E {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E {{  Φ}}
/-- info: WP e @ E ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e @ E ? {{  Φ}}
/-- info: WP e {{ Φ }} : PROP -/
#guard_msgs in #check WP e {{ Φ }}
/-- info: WP e ? {{ Φ }} : PROP -/
#guard_msgs in #check WP e ? {{ Φ }}

/-- info: WP e @ s ; E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ s ; E [{ Φ }]
/-- info: WP e @ E [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E [{  Φ}]
/-- info: WP e @ E ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e @ E ? [{  Φ}]
/-- info: WP e [{ Φ }] : PROP -/
#guard_msgs in #check WP e [{ Φ }]
/-- info: WP e ? [{ Φ }] : PROP -/
#guard_msgs in #check WP e ? [{ Φ }]

end testUnexpand
