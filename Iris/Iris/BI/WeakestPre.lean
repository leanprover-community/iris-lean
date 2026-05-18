module

public import Iris.Std.CoPset
public import Iris.BI
public meta import Iris.BI
public import Iris.BI.BIBase
public meta import Iris.Std.Rewrite
public import Std
meta import Lean
public import Lean

public import Iris.BI.BI
public import Iris.BI.Classes
public import Iris.BI.DerivedLaws
public import Iris.BI.DerivedLawsLater
public import Iris.BI.Extensions
public import Iris.BI.SIProp
public meta import Iris.Std.RocqPorting

public section

namespace Iris

open Lean

inductive Stuckness where
| NotStuck
| MaybeStuck

namespace Stuckness

@[simp]
instance instLE: LE Stuckness where
  le x y := ¬ (x = .MaybeStuck ∧ y = .NotStuck)

instance : Std.IsPreorder Stuckness where
  le_refl  := by grind only [Stuckness, LE.le, instLE]
  le_trans := by grind only [Stuckness, LE.le, instLE]

@[simp] theorem le_MaybeStuck {s : Stuckness} : s ≤ MaybeStuck := by cases s <;> grind only [Stuckness, LE.le, instLE]

@[simp] theorem NotSuck_le {s : Stuckness} : NotStuck ≤ s := by cases s <;> grind only [Stuckness, LE.le, instLE]

end Stuckness

class Wp (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _) where
  wp : A → CoPset → Expr → (Val → PROP) → PROP

class TotalWP (PROP Expr) (Val : outParam (Type _)) (A : Type _) where
  totalWp : A → CoPset → Expr → (Val → PROP) → PROP


syntax wpExpr :=
  term:max (" @ " term:max (" ; " term:max) <|> ((" ? ")? )) <|> (" ? ")?

declare_syntax_cat wpPostcondInner
syntax ident ", " term : wpPostcondInner
syntax term : wpPostcondInner

declare_syntax_cat wpPostcond
syntax " {{ " wpPostcondInner " }} " : wpPostcond
syntax " [{ " wpPostcondInner " }] " : wpPostcond
syntax " ⦃ " wpPostcondInner " ⦄ " : wpPostcond -- Are spaces outside of parens used in the pp?
syntax " 〖 " wpPostcondInner " 〗 "  : wpPostcond

syntax (name := wp) "WP " wpExpr wpPostcond : term

syntax texanPostcond := (ident+ ", ")? " RET " term:min "; " term

syntax (name := texanTriple) "{{{ " term " }}} " wpExpr " {{{ " texanPostcond " }}}" : term

/- This section checks whether the syntax is recognized correctly for all combinations -/
section testNotation

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E {{ Φ }}
-/
#guard_msgs in #check_failure WP e @ s ; E {{ Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E {{ Φ }}
-/
#guard_msgs in #check_failure WP e @ E {{ Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? {{ Φ }}
-/
#guard_msgs in #check_failure WP e @ E ? {{ Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e {{ Φ }}
-/
#guard_msgs in #check_failure WP e {{ Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? {{ Φ }}
-/
#guard_msgs in #check_failure WP e ? {{ Φ }}

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E {{ v, Φ }}
-/
#guard_msgs in #check_failure WP e @ s ; E {{v,  Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E {{ v, Φ }}
-/
#guard_msgs in #check_failure WP e @ E {{v,  Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? {{ v, Φ }}
-/
#guard_msgs in #check_failure WP e @ E ? {{v,  Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e {{ v, Φ }}
-/
#guard_msgs in #check_failure WP e {{v,  Φ }}
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? {{ v, Φ }}
-/
#guard_msgs in #check_failure WP e ? {{v,  Φ }}

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E ⦃ Φ ⦄
-/
#guard_msgs in #check_failure WP e @ s ; E ⦃ Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ⦃ Φ ⦄
-/
#guard_msgs in #check_failure WP e @ E ⦃ Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? ⦃ Φ ⦄
-/
#guard_msgs in #check_failure WP e @ E ? ⦃ Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ⦃ Φ ⦄
-/
#guard_msgs in #check_failure WP e ⦃ Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? ⦃ Φ ⦄
-/
#guard_msgs in #check_failure WP e ? ⦃ Φ ⦄

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E ⦃ v, Φ ⦄
-/
#guard_msgs in #check_failure WP e @ s ; E ⦃v,  Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ⦃ v, Φ ⦄
-/
#guard_msgs in #check_failure WP e @ E ⦃v,  Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? ⦃ v, Φ ⦄
-/
#guard_msgs in #check_failure WP e @ E ? ⦃v,  Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ⦃ v, Φ ⦄
-/
#guard_msgs in #check_failure WP e ⦃v,  Φ ⦄
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? ⦃ v, Φ ⦄
-/
#guard_msgs in #check_failure WP e ? ⦃v,  Φ ⦄

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E [{ Φ }]
-/
#guard_msgs in #check_failure WP e @ s ; E [{ Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E [{ Φ }]
-/
#guard_msgs in #check_failure WP e @ E [{ Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? [{ Φ }]
-/
#guard_msgs in #check_failure WP e @ E ? [{ Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e [{ Φ }]
-/
#guard_msgs in #check_failure WP e [{ Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? [{ Φ }]
-/
#guard_msgs in #check_failure WP e ? [{ Φ }]

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E [{ v, Φ }]
-/
#guard_msgs in #check_failure WP e @ s ; E [{v,  Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E [{ v, Φ }]
-/
#guard_msgs in #check_failure WP e @ E [{v,  Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? [{ v, Φ }]
-/
#guard_msgs in #check_failure WP e @ E ? [{v,  Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e [{ v, Φ }]
-/
#guard_msgs in #check_failure WP e [{v,  Φ }]
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? [{ v, Φ }]
-/
#guard_msgs in #check_failure WP e ? [{v,  Φ }]

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E 〖 Φ 〗
-/
#guard_msgs in #check_failure WP e @ s ; E 〖 Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E 〖 Φ 〗
-/
#guard_msgs in #check_failure WP e @ E 〖 Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? 〖 Φ 〗
-/
#guard_msgs in #check_failure WP e @ E ? 〖 Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e 〖 Φ 〗
-/
#guard_msgs in #check_failure WP e 〖 Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? 〖 Φ 〗
-/
#guard_msgs in #check_failure WP e ? 〖 Φ 〗

/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ s ; E 〖 v, Φ 〗
-/
#guard_msgs in #check_failure WP e @ s ; E 〖v,  Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E 〖 v, Φ 〗
-/
#guard_msgs in #check_failure WP e @ E 〖v,  Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e @ E ? 〖 v, Φ 〗
-/
#guard_msgs in #check_failure WP e @ E ? 〖v,  Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e 〖 v, Φ 〗
-/
#guard_msgs in #check_failure WP e 〖v,  Φ 〗
/--
info: elaboration function for `Iris.wp` has not been implemented
  WP e ? 〖 v, Φ 〗
-/
#guard_msgs in #check_failure WP e ? 〖v,  Φ 〗

/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ s ; E {{{ x y, RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ s ; E {{{ x y , RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ E {{{ x y, RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ E {{{ x y , RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ E ? {{{ x y, RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ E ? {{{ x y , RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e {{{ x y, RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e {{{ x y , RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e ? {{{ x y, RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e ? {{{ x y , RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ s ; E {{{ RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ s ; E {{{ RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ E {{{ RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ E {{{ RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e @ E ? {{{ RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e @ E ? {{{ RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e {{{ RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e {{{ RET pat ; Q }}}
/--
info: elaboration function for `Iris.texanTriple` has not been implemented
  {{{ P }}} e ? {{{ RET pat; Q }}}
-/
#guard_msgs in #check_failure {{{ P }}} e ? {{{ RET pat ; Q }}}

end testNotation

open Lean in
meta def parseWpExpr : Lean.TSyntax ``wpExpr → Lean.MacroM (TSyntax `term × TSyntax `term × TSyntax `term) := fun
  | `(wpExpr| $e @ $s ; $E) =>
    return (e, s, E)
  | `(wpExpr| $e @ $E) =>
    return (e, ←`(Stuckness.NotStuck), E)
  | `(wpExpr| $e @ $E ?) =>
    return (e, ←`(Stuckness.MaybeStuck), E)
  | `(wpExpr| $e:term) =>
    return (e, ←`(Stuckness.NotStuck), ←`(⊤))
  | `(wpExpr| $e:term ?) =>
    return (e, ←`(Stuckness.MaybeStuck), ←`(⊤))
  | _ => Lean.Macro.throwUnsupported

open Lean in
meta def parseWpPostcondInner (stx : TSyntax `wpPostcondInner) : MacroM (TSyntax `term) := do
  match stx with
  | `(wpPostcondInner| $v:ident, $Φ:term) => `(fun $v => $Φ)
  | `(wpPostcondInner| $Φ:term) => return Φ
  | _ => Macro.throwUnsupported

open Lean in
meta def parseWpPostcond (stx : TSyntax `wpPostcond) : MacroM (TSyntax `term × Bool) := do
  match stx with
  | `(wpPostcond| {{ $inner:wpPostcondInner }})
  | `(wpPostcond| ⦃ $inner:wpPostcondInner ⦄) =>
    return (←parseWpPostcondInner inner, false)
  | `(wpPostcond| [{ $inner:wpPostcondInner }])
  | `(wpPostcond| 〖 $inner:wpPostcondInner 〗) =>
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

-- syntax (name := underExtraBinders) "underExtraBinders(" term:min ")" : term
-- syntax (name := sourceExtraBinders) "sourceExtraBinders(" term ")" : term

-- private meta partial def findSource : Syntax → Option Syntax
-- | .missing => none
-- | .node _ ``sourceExtraBinders args => do
--   let #[_, inner, _] := args | none
--   return inner
-- | .node _ _ args => do
--   let #[res] := args.filterMap findSource | none
--   return res
-- | .ident _ _ _ _ => none
-- | .atom _ _ => none

-- private meta partial def collectUnresolvedIds : Syntax → Elab.Term.TermElabM (Array Ident)
-- | .missing => return {}
-- | .node _ _ args => do
--   args.flatMapM collectUnresolvedIds
-- | id@(.ident ..) => do
--   try
--     let _ ← Elab.Term.elabIdent id .none
--     return {}
--   catch
--   | .error _ md =>
--     let msg ← md.toString
--     if msg.startsWith "Unknown identifier" then
--       return #[⟨id⟩]
--     else
--       return {}
--   | _ => return {}
-- | .atom _ _ =>
--   return {}

-- elab "sourceExtraBinders(" t:term ")" : term => Elab.Term.elabTerm t .none

-- @[term_elab underExtraBinders]
-- meta def elabUnderExtraBinders: Elab.Term.TermElab := fun stx ty? => do
--   match stx with
--   | `(underExtraBinders( $t:term ) ) =>
--     if let .some s := findSource t then
--       -- logInfo s!"Found! {s.getArgs.size} {repr s}"
--       let ids ← collectUnresolvedIds s
--       logInfo s!"Collected identifiers {ids}"
--       if ids.isEmpty then
--         Elab.Term.elabTerm t ty?
--       else
--         let stx ← `(∀ $ids*, $t)
--         Elab.Term.elabTerm stx ty?
--     else
--       Elab.Term.elabTerm t ty?
--   | _ => unreachable!

-- macro_rules
-- | `(iprop(underExtraBinders($t))) => `(underExtraBinders(iprop($t)))
-- | `(iprop(sourceExtraBinders($t))) => `(sourceExtraBinders(iprop($t)))

-- @[macro texanTriple]
-- meta def wpTexanTriple : Lean.Macro
--   | `({{{ $P:term }}} $expr {{{ $[$[$xs:ident]* ,]? RET $pat ; $Q }}}) => do
--     let k ← match xs with
--             | some xs => `(∀ $xs*, underExtraBinders($Q → Φ sourceExtraBinders($pat)))
--             | none => `($Q:term → Φ $pat)
--     `(iprop(∀ Φ, $P -∗ ▷ $k -∗ (WP $expr {{ Φ }})))
--   | _ => Lean.Macro.throwUnsupported

@[macro texanTriple]
meta def wpTexanTriple : Lean.Macro
  | `({{{ $P:term }}} $wpExpr {{{ $[$[$xs:ident]* ,]? RET $pat ; $Q:term }}}) => do
    -- It seems like `∀ $xs*, Ψ` does not translate to `Ψ`.
    let k ← match xs with
            | some xs => `(∀ $xs*, $Q:term → Φ $pat)
            | none => `($Q:term → Φ $pat)
    `(iprop(∀ Φ, $P -∗ ▷ $k -∗ (WP $wpExpr {{ Φ }})))
  | _ => Lean.Macro.throwUnsupported

section testElab
set_option linter.unusedVariables false

variable (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _)
variable [ι : Iris.BI PROP]
variable [Wp PROP Expr Val A]
variable [Wp PROP Expr Val Stuckness]
variable [TotalWP PROP Expr Val A]
variable [TotalWP PROP Expr Val Stuckness]

variable (e : Expr)(s : A)(E : CoPset)
variable (Φ : PROP)

/-- info: Wp.wp s E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ s ; E {{v,  Φ }}
/-- info: Wp.wp Stuckness.NotStuck E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ E {{ v, Φ }}
/-- info: Wp.wp Stuckness.NotStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e {{v,  Φ }}
/-- info: Wp.wp Stuckness.MaybeStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e ? {{v,  Φ }}

/-- info: TotalWP.totalWp s E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ s ; E [{v,  Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck E e fun v => Φ : PROP -/
#guard_msgs in #check WP e @ E [{ v, Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e [{v,  Φ }]
/-- info: TotalWP.totalWp Stuckness.MaybeStuck ⊤ e fun v => Φ : PROP -/
#guard_msgs in #check WP e ? [{v,  Φ }]

variable (Φ : Val → PROP)

/-- info: Wp.wp s E e Φ : PROP -/
#guard_msgs in #check WP e @ s ; E {{ Φ }}
/-- info: Wp.wp Stuckness.NotStuck E e Φ : PROP -/
#guard_msgs in #check WP e @ E {{ Φ }}
/-- info: Wp.wp Stuckness.NotStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e {{ Φ }}
/-- info: Wp.wp Stuckness.MaybeStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e ? {{ Φ }}

/-- info: TotalWP.totalWp s E e Φ : PROP -/
#guard_msgs in #check WP e @ s ; E [{ Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck E e Φ : PROP -/
#guard_msgs in #check WP e @ E [{ Φ }]
/-- info: TotalWP.totalWp Stuckness.NotStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e [{ Φ }]
/-- info: TotalWP.totalWp Stuckness.MaybeStuck ⊤ e Φ : PROP -/
#guard_msgs in #check WP e ? [{ Φ }]

variable (P : PROP) (Q : PROP) (v : Nat) (s : Stuckness) [Wp PROP Expr Nat Stuckness]

-- Can we do away with the `x .. y` by obtaining the identifiers directly from `RET pat`?

/-- info: iprop(∀ Φ, P -∗ (▷ ∀ x y, Q → Φ (x + 1)) -∗ Wp.wp s E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ s ; E {{{ x y , RET (x+1) ; Q }}}
/-- info: iprop(∀ Φ, P -∗ (▷ ∀ x y, Q → Φ (x + 1)) -∗ Wp.wp Stuckness.NotStuck E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ E {{{ x y , RET (x+1) ; Q }}}
/-- info: iprop(∀ Φ, P -∗ (▷ ∀ x y, Q → Φ (x + 1)) -∗ Wp.wp Stuckness.MaybeStuck E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ E ? {{{ x y , RET (x+1) ; Q }}}
/-- info: iprop(∀ Φ, P -∗ (▷ ∀ x y, Q → Φ (x + 1)) -∗ Wp.wp Stuckness.NotStuck ⊤ e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e {{{ x y , RET (x+1) ; Q }}}
/-- info: iprop(∀ Φ, P -∗ (▷ ∀ x y, Q → Φ (x + 1)) -∗ Wp.wp Stuckness.MaybeStuck ⊤ e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e ? {{{ x y , RET (x+1) ; Q }}}

/-- info: iprop(∀ Φ, P -∗ ▷ (Q → Φ 0) -∗ Wp.wp s E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ s ; E {{{ RET 0 ; Q }}}
/-- info: iprop(∀ Φ, P -∗ ▷ (Q → Φ 0) -∗ Wp.wp Stuckness.NotStuck E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ E {{{ RET 0 ; Q }}}
/-- info: iprop(∀ Φ, P -∗ ▷ (Q → Φ 0) -∗ Wp.wp Stuckness.MaybeStuck E e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e @ E ? {{{ RET 0 ; Q }}}
/-- info: iprop(∀ Φ, P -∗ ▷ (Q → Φ 0) -∗ Wp.wp Stuckness.NotStuck ⊤ e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e {{{ RET 0 ; Q }}}
/-- info: iprop(∀ Φ, P -∗ ▷ (Q → Φ 0) -∗ Wp.wp Stuckness.MaybeStuck ⊤ e Φ) : PROP -/
#guard_msgs in #check {{{ P }}} e ? {{{ RET 0 ; Q }}}

end testElab

meta def unexpandWpPostcondInner : TSyntax `term → PrettyPrinter.UnexpandM (TSyntax `wpPostcondInner)
  | `(fun $v:ident => $Φ:term) => `(wpPostcondInner|$v:ident, $Φ:term)
  | `($Φ:term) => `(wpPostcondInner| $Φ:term)

open Lean in
meta def makeWpExpr (s E e : TSyntax `term) : PrettyPrinter.UnexpandM (TSyntax ``wpExpr) := do
  match s, E with
  | `(Stuckness.NotStuck), `(⊤) => `(wpExpr| $e:term)
  | `(Stuckness.NotStuck), E => `(wpExpr| $e:term @ $E:term)
  | `(Stuckness.MaybeStuck), `(⊤) => `(wpExpr| $e:term ?)
  | `(Stuckness.MaybeStuck), E => `(wpExpr| $e:term @ $E:term ?)
  | s, E => `(wpExpr| $e:term @ $s:term ; $E:term)

@[app_unexpander Wp.wp]
meta def unexpanderWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $e $Φ) => do
    let wpExpr ← makeWpExpr s E e
    let wpPostcondInner ← unexpandWpPostcondInner Φ
    `(WP $wpExpr {{ $wpPostcondInner }})
  | _ => throw ()

@[app_unexpander TotalWP.totalWp]
meta def unexpanderTotalWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $e $Φ) => do
    let wpExpr ← makeWpExpr s E e
    let wpPostcondInner ← unexpandWpPostcondInner Φ
    `(WP $wpExpr [{ $wpPostcondInner }])
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

/-
Notations used in Rocq
For Texan triples, more of the same

{{{ P }}} e @ s ; E {{{  RET pat ; Q }}}
{{{ P ]}} e @ E {{{ RET pat ; Q }}}
{{{ P ]}} e @ E ? {{{  RET pat ; Q }}}
{{{ P ]}} e {{{ RET pat ; Q }}}
{{{ P ]}} e ? {{{ RET pat ; Q }}}

{{{ P }}} e @ s ; E {{{ x .. y , RET pat ; Q }}}
{{{ P }}} e @ E {{{ x .. y , RET pat ; Q }}}
{{{ P }}} e @ E ? {{{ x .. y , RET pat ; Q }}}
{{{ P }}} e {{{ x .. y , RET pat ; Q }}}
{{{ P }}} e ? {{{ x .. y , RET pat ; Q }}}

-/
