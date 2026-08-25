module

public import Iris.Std.CoPset
public import Iris.BI.BI

public section

namespace Iris

open Lean

@[rocq_alias stuckness]
inductive Stuckness where
| NotStuck
| MaybeStuck

namespace Stuckness

@[simp, rocq_alias stuckness_le]
instance instLE: LE Stuckness where
  le x y := ¬ (x = .MaybeStuck ∧ y = .NotStuck)

@[rocq_alias stuckness_le_po]
instance : Std.IsPreorder Stuckness where
  le_refl  := by grind only [Stuckness, LE.le, instLE]
  le_trans := by grind only [Stuckness, LE.le, instLE]

@[simp] theorem le_MaybeStuck {s : Stuckness} : s ≤ MaybeStuck := by
  cases s <;> grind only [Stuckness, LE.le, instLE]

@[simp] theorem NotStuck_le {s : Stuckness} : NotStuck ≤ s := by
  cases s <;> grind only [Stuckness, LE.le, instLE]

end Stuckness

@[rocq_alias Wp]
class Wp (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _) where
  wp : A → CoPset → Expr → (Val → PROP) → PROP

@[rocq_alias Twp]
class TotalWp (PROP Expr) (Val : outParam (Type _)) (A : Type _) where
  totalWp : A → CoPset → Expr → (Val → PROP) → PROP

syntax wpExpr :=
  term:max (" @ " term:max (" ; " term:max) <|> ((" ? ")? )) <|> (" ? ")?

declare_syntax_cat wpPostcondInner
syntax ident ", " term : wpPostcondInner
syntax term : wpPostcondInner

declare_syntax_cat wpPostcond
-- Avoids conflicts with
-- example {a : PUnit.{i}} : PUnit.{i} := a
--                      ^^
-- see: https://github.com/leanprover-community/iris-lean/pull/393
syntax " {" noWs "{ " wpPostcondInner " }" noWs "} " : wpPostcond
syntax " [" noWs "{ " wpPostcondInner " }" noWs "] " : wpPostcond

syntax (name := wp) "WP " wpExpr wpPostcond : term

syntax texanPostcondInner := ((ppSpace (binderIdent <|> bracketedBinder))+ ", ")? " RET " term:min "; " term:min

declare_syntax_cat texanPostcond
syntax " {" noWs "{ " texanPostcondInner " }" noWs "} " : texanPostcond
declare_syntax_cat texanPrecond
syntax " {" noWs "{ " term:min " }" noWs "} " : texanPrecond

syntax (name := texanTriple) texanPrecond wpExpr texanPostcond : term


declare_syntax_cat totalTexanPostcond
syntax " [" noWs "{ " texanPostcondInner " }" noWs "] " : totalTexanPostcond
declare_syntax_cat totalTexanPrecond
syntax " [" noWs "{ " term:min " }" noWs "] " : totalTexanPrecond

syntax (name := totalTexanTriple) totalTexanPrecond wpExpr totalTexanPostcond : term

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
  | `(wpPostcondInner| $v:ident, $Φ:term) => `(fun $v => iprop($Φ))
  | `(wpPostcondInner| $Φ:term) => return iprop(Φ)
  | _ => Macro.throwUnsupported

open Lean in
meta def parseWpPostcond (stx : TSyntax `wpPostcond) : MacroM (TSyntax `term × Bool) := do
  match stx with
  | `(wpPostcond| {{ $inner:wpPostcondInner }}) =>
    return (←parseWpPostcondInner inner, false)
  | `(wpPostcond| [{ $inner:wpPostcondInner }]) =>
    return (←parseWpPostcondInner inner, true)
  | _ => Macro.throwUnsupported (α := TSyntax `term × Bool)

open Lean in
private meta def transformTexanBinders
    (xs : Array (TSyntax [`Lean.binderIdent, `Lean.Parser.Term.bracketedBinder])) :
    MacroM <| TSyntaxArray [`ident, `Lean.Parser.Term.hole,
      `Lean.Parser.Term.bracketedBinder] :=
  xs.mapM fun
    | `(binderIdent|_) => `(hole|_)
    | `(binderIdent|$i:ident) => `(ident|$i)
    | `(bracketedBinder|$x) => `(bracketedBinder|$x)

@[macro wp]
meta def wpMacro : Lean.Macro := fun stx => do
  match stx with
  | `(WP%$tk $expr $postcond) =>
    let (e, s, E) ← parseWpExpr expr
    let (Φ, useTotal?) ← parseWpPostcond postcond
    if useTotal? then
      `(TotalWp.totalWp $s $E $e $Φ)
    else
      `($(BI.wrapIpropSpan tk stx ``Wp.wp) $s $E $e $Φ)
  | _ => Lean.Macro.throwUnsupported

meta def parseTexanTriple : Syntax → MacroM Term
  | `({{ $P:term }} $wpExpr {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) => do
    let k ← match xs with
            | some xs =>
              let xs ← transformTexanBinders xs
              `(iprop(∀ $xs*, $Q:term -∗ Φ $pat))
            | none => `($Q:term -∗ Φ $pat)
    `(∀ Φ, $P -∗ ▷ $k -∗ (WP $wpExpr {{ Φ }}))
  | `([{ $P:term }] $wpExpr [{ $[$[$xs]* ,]? RET $pat ; $Q:term }]) => do
    let k ← match xs with
            | some xs =>
              let xs ← transformTexanBinders xs
              `(iprop(∀ $xs*, $Q:term -∗ Φ $pat))
            | none => `($Q:term -∗ Φ $pat)
    `(∀ Φ, $P -∗ $k -∗ (WP $wpExpr [{ Φ }]))
  | _ => Lean.Macro.throwUnsupported

@[macro Iris.BI.iprop]
meta def wpTexanTriple : Lean.Macro
  | `(iprop($P)) => do `(iprop(□ $(← parseTexanTriple P)))
  | _ => Lean.Macro.throwUnsupported

@[macro texanTriple, macro totalTexanTriple]
meta def wpTexanTripleTerm : Lean.Macro
  | P => do `(⊢ $(← parseTexanTriple P))

meta def unexpandWpPostcondInner : TSyntax `term → PrettyPrinter.UnexpandM (TSyntax `wpPostcondInner)
  | `(fun $v:ident => iprop($Φ:term)) => `(wpPostcondInner|$v:ident, $Φ:term)
  | `(iprop($Φ:term)) => `(wpPostcondInner| $Φ:term)
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

@[app_unexpander TotalWp.totalWp]
meta def unexpanderTotalWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $e $Φ) => do
    let wpExpr ← makeWpExpr s E e
    let wpPostcondInner ← unexpandWpPostcondInner Φ
    `(WP $wpExpr [{ $wpPostcondInner }])
  | _ => throw ()

-- TODO: Consider adding unexpanders for texan triples
