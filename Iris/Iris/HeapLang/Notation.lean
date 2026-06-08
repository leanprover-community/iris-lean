/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Iris.HeapLang.Syntax
public meta import Lean.PrettyPrinter.Parenthesizer

public meta section
namespace Iris.HeapLang

open Lean Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Elab Parser ProgramLogic

declare_syntax_cat hl_exp
declare_syntax_cat hl_binder
declare_syntax_cat hl_match_arm
declare_syntax_cat hl_val

/-- embedding heaplang expressions into terms -/
syntax:max "hl(" hl_exp ")" : term
syntax:min "hl% " hl_exp:min : term
macro_rules
  | `(hl% $t) => `(hl($t))
/-- embedding heaplang binders into terms -/
syntax:max "hl_binder(" hl_binder ")" : term
/-- embedding heaplang values into terms -/
syntax:max "hl_val(" hl_val ")" : term
syntax:min "hl_val% " hl_val:min : term
macro_rules
  | `(hl_val% $t) => `(hl_val($t))

/-- escaping -/
syntax:max "&" term:max : hl_binder
syntax:max binderIdent : hl_binder

/-- escaping -/
syntax:max "&" term:max : hl_val
/-- embedding literals -/
syntax:max "#" term:max : hl_val
/-- pairs -/
syntax:max "(" hl_val ", " hl_val,+ ")" : hl_val
/-- injL -/
syntax:100 "injl(" hl_val ")" : hl_val
/-- injR -/
syntax:100 "injr(" hl_val ")" : hl_val
/-- none and some -/
syntax:100 "none()" : hl_val
syntax:100 "some(" hl_val ")" : hl_val

/-- parenthesis -/
syntax:max "(" hl_exp ")" : hl_exp
/-- embedding values -/
syntax:max "v(" hl_val ")" : hl_exp
/-- escaping -/
syntax:max "&" term:max : hl_exp
/-- embedding literals -/
syntax:max "#" term:max : hl_exp
/-- variables -/
syntax:max ident : hl_exp
-- levels are taken from https://github.com/leanprover/lean4/blob/985f350dcd18fc7814dfa677cac09933f44f3215/src/Init/Notation.lean#L280
/-- addition -/
syntax:65 hl_exp:66 " + " hl_exp:65 : hl_exp
/-- offset -/
syntax:65 hl_exp:66 " +ₗ " hl_exp:65 : hl_exp
/-- subtraction -/
syntax:65 hl_exp:66 " - " hl_exp:65 : hl_exp
/-- multiplication -/
syntax:70 hl_exp:71 " * " hl_exp:70 : hl_exp
/-- division -/
syntax:70 hl_exp:71 " / " hl_exp:70 : hl_exp
/-- modulo -/
syntax:70 hl_exp:71 " % " hl_exp:70 : hl_exp
/-- and -/
syntax:60 hl_exp:61 " &&& " hl_exp:60 : hl_exp
/-- or -/
syntax:55 hl_exp:56 " ||| " hl_exp:55 : hl_exp
/-- xor -/
syntax:58 hl_exp:59 " ^^^ " hl_exp:58 : hl_exp
/-- shiftl -/
syntax:75 hl_exp:76 " <<< " hl_exp:75 : hl_exp
/-- shiftr -/
syntax:75 hl_exp:76 " >>> " hl_exp:75 : hl_exp
/-- le -/
syntax:50 hl_exp:50 " <= " hl_exp:50 : hl_exp
syntax:50 hl_exp:50 " ≤ " hl_exp:50 : hl_exp
/-- lt -/
syntax:50 hl_exp:50 " < " hl_exp:50 : hl_exp
/-- equality -/
syntax:50 hl_exp:50 " = " hl_exp:50 : hl_exp

syntax:35 hl_exp:36 "&&" hl_exp:35 : hl_exp
syntax:30 hl_exp:31 "||" hl_exp:30 : hl_exp

/-- neg -/
syntax:100 "~" hl_exp:100 : hl_exp
/-- minus -/
syntax:75 "-" hl_exp:75 : hl_exp

/-- if -/
syntax:10 "if " hl_exp:10 " then " hl_exp:10 " else " hl_exp:10 : hl_exp

/-- application -/
syntax:100 hl_exp:100 colGt ppSpace hl_exp:101 : hl_exp
/-- let -/
syntax:10 "let " hl_binder " := " hl_exp:10 "; " hl_exp:1 : hl_exp
/-- sequencing -/
syntax:5 hl_exp:6 "; " hl_exp:5 : hl_exp
/-- lambda -/
syntax:10 "λ " hl_binder+ ", " hl_exp:1 : hl_exp
/-- lambda -/
syntax:10 "λ " hl_binder+ ", " hl_exp:1 : hl_val
/-- recursive function -/
syntax:10 "rec " hl_binder ppSpace hl_binder+ " := " hl_exp:1 : hl_exp
/-- recursive function -/
syntax:10 "rec " hl_binder ppSpace hl_binder+ " := " hl_exp:1 : hl_val

/-- pairs -/
syntax:max "(" hl_exp ", " hl_exp,+ ")" : hl_exp
/-- fst -/
syntax:100 "fst(" hl_exp ")" : hl_exp
/-- snd -/
syntax:100 "snd(" hl_exp ")" : hl_exp

/-- injL -/
syntax:100 "injl(" hl_exp ")" : hl_exp
/-- injR -/
syntax:100 "injr(" hl_exp ")" : hl_exp

/-- none and some -/
syntax:100 "none()" : hl_exp
syntax:100 "some(" hl_exp ")" : hl_exp

/-- match -/
syntax:100 "match " hl_exp:5 " with"
  " | " hl_match_arm " => " hl_exp:5
  " | " hl_match_arm " => " hl_exp:5 : hl_exp

syntax "injl(" hl_binder ")" : hl_match_arm
syntax "injr(" hl_binder ")" : hl_match_arm
syntax "some(" hl_binder ")" : hl_match_arm
syntax "none()" : hl_match_arm

/-- heap operations -/
syntax:100 "allocn(" hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "ref(" hl_exp ")" : hl_exp
syntax:100 "free(" hl_exp ")" : hl_exp
syntax:100 "!" hl_exp:100 : hl_exp
syntax:15 hl_exp:16 " ← " hl_exp:15 : hl_exp
syntax:100 "cmpXchg(" hl_exp ", " hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "cas(" hl_exp ", " hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "xchg(" hl_exp ", " hl_exp ")" : hl_exp
syntax:100 "faa(" hl_exp ", " hl_exp ")" : hl_exp

/-- fork -/
syntax:100 "fork(" hl_exp  ")" : hl_exp

/-- assert -/
syntax:100 "assert(" hl_exp  ")" : hl_exp

/-- holes -/
syntax "_" : hl_exp

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer hl_exp]
def hl_exp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `hl_exp false (fun stx => Unhygienic.run `(hl_exp|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `hl_exp prec

partial def unpackHLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `hl_exp)
  | `(hl($e)) => `(hl_exp|$e)
  | `($t) => `(hl_exp|&$t)

partial def unpackHLVal [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `hl_val)
  | `(hl_val($e)) => `(hl_val|$e)
  | `($t) => `(hl_val|&$t)

partial def unpackHLBinder [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `hl_binder)
  | `(hl_binder($e)) => `(hl_binder|$e)
  | `($t) => `(hl_binder|&$t)

/-- elaborating binders -/
macro_rules
  | `(hl_binder(_)) => `(Binder.anon)
  | `(hl_binder($i:ident)) => `(Binder.named $(Syntax.mkStrLit i.getId.toString))
  | `(hl_binder(&$t)) => `($t)

/-- elaborating values -/
macro_rules
  | `(hl_val(& $t)) => pure t
  | `(hl_val(# $n:num)) => `(Val.lit (BaseLit.int $n))
  | `(hl_val(# $e)) => `(Val.lit $e)
  | `(hl_val(rec $f $x := $e)) => do `(Val.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl_val(rec $f $x $xs* := $e)) => do `(hl_val(rec $f $x := λ $xs*, $e))
  | `(hl_val(λ $xs*, $e)) => do `(hl_val(rec _ $xs* := $e))
  | `(hl_val(($e1, $e2))) => `(Val.pair hl_val($e1) hl_val($e2))
  | `(hl_val(($e1, $e2, $e3,*))) => `(hl_val(($e1, ($e2, $e3,*))))
  | `(hl_val(injl($e1))) => `(Val.injL hl_val($e1))
  | `(hl_val(injr($e1))) => `(Val.injR hl_val($e1))
  | `(hl_val(none())) => `(hl_val(injl(#())))
  | `(hl_val(some($e))) => `(hl_val(injr($e)))

/-- elaborating expressions -/
macro_rules
  | `(hl(($e))) => `(hl($e))
  | `(hl(_)) => `(_)
  | `(hl(&$t)) => pure t
  | `(hl(v($e))) => `(@ToVal.ofVal Exp Val instToVal hl_val($e))
  | `(hl(# $e)) => `(hl(v(# $e)))
  | `(hl($i:ident)) => `(Exp.var $(Syntax.mkStrLit i.getId.toString))
  | `(hl($e1 + $e2)) => `(Exp.binop BinOp.plus hl($e1) hl($e2))
  | `(hl($e1 +ₗ $e2)) => `(Exp.binop BinOp.offset hl($e1) hl($e2))
  | `(hl($e1 - $e2)) => `(Exp.binop BinOp.minus hl($e1) hl($e2))
  | `(hl($e1 * $e2)) => `(Exp.binop BinOp.mult hl($e1) hl($e2))
  | `(hl($e1 / $e2)) => `(Exp.binop BinOp.tdiv hl($e1) hl($e2))
  | `(hl($e1 % $e2)) => `(Exp.binop BinOp.tmod hl($e1) hl($e2))
  | `(hl($e1 &&& $e2)) => `(Exp.binop BinOp.and hl($e1) hl($e2))
  | `(hl($e1 ||| $e2)) => `(Exp.binop BinOp.or hl($e1) hl($e2))
  | `(hl($e1 ^^^ $e2)) => `(Exp.binop BinOp.xor hl($e1) hl($e2))
  | `(hl($e1 <<< $e2)) => `(Exp.binop BinOp.shiftl hl($e1) hl($e2))
  | `(hl($e1 >>> $e2)) => `(Exp.binop BinOp.shiftr hl($e1) hl($e2))
  | `(hl($e1 <= $e2)) => `(hl($e1 ≤ $e2))
  | `(hl($e1 ≤ $e2)) => `(Exp.binop BinOp.le hl($e1) hl($e2))
  | `(hl($e1 < $e2)) => `(Exp.binop BinOp.lt hl($e1) hl($e2))
  | `(hl($e1 = $e2)) => `(Exp.binop BinOp.eq hl($e1) hl($e2))
  | `(hl($e1 && $e2)) => `(hl(if $e1 then $e2 else #false))
  | `(hl($e1 || $e2)) => `(hl(if $e1 then #true else $e2))
  | `(hl(~$e1)) => `(Exp.unop UnOp.neg hl($e1))
  | `(hl(-$e1)) => `(Exp.unop UnOp.minus hl($e1))
  | `(hl(if $e1 then $e2 else $e3)) => `(Exp.if hl($e1) hl($e2) hl($e3))
  | `(hl($e1 $e2)) => `(Exp.app hl($e1) hl($e2))
  | `(hl(rec $f $x := $e)) => do `(Exp.rec_ hl_binder($f) hl_binder($x) hl($e))
  | `(hl(rec $f $x $xs* := $e)) => `(hl(rec $f $x := λ $xs*, $e))
  | `(hl(λ $xs*, $e)) => `(hl(rec _ $xs* := $e))
  | `(hl($e1; $e2)) => `(hl(let _ := $e1; $e2))
  | `(hl(let $i := $e1; $e2)) => `(hl((λ $i, $e2) $e1))
  | `(hl(($e1, $e2))) => `(Exp.pair hl($e1) hl($e2))
  | `(hl(($e1, $e2, $e3,*))) => `(hl(($e1, ($e2, $e3,*))))
  | `(hl(fst($e1))) => `(Exp.fst hl($e1))
  | `(hl(snd($e1))) => `(Exp.snd hl($e1))
  | `(hl(match $e1 with | injl($i2) => $e2 | injr($i3) => $e3)) =>
    `(Exp.case hl($e1) hl(λ $i2, $e2) hl(λ $i3, $e3))
  | `(hl(match $e1 with | injr($i2) => $e2 | injl($i3) => $e3)) =>
    `(hl(match $e1 with | injl($i3) => $e3 | injr($i2) => $e2))
  -- TODO: Why does the following not work?
  -- | `(hl_match_arm | none()) => `(hl_match_arm | injl(_))
  -- | `(hl_match_arm | some($i)) => `(hl_match_arm | injr($i))
  | `(hl(match $e1 with | some($i2) => $e2 | none() => $e3)) =>
    `(hl(match $e1 with | injr($i2) => $e2 | injl(_) => $e3))
  | `(hl(match $e1 with | none() => $e2 | some($i3) => $e3)) =>
    `(hl(match $e1 with | injl(_) => $e2 | injr($i3) => $e3))
  | `(hl(injl($e1))) => `(Exp.injL hl($e1))
  | `(hl(injr($e1))) => `(Exp.injR hl($e1))
  | `(hl(none())) => `(hl(injl(#())))
  | `(hl(some($e))) => `(hl(injr($e)))
  | `(hl(allocn($e1, $e2))) => `(Exp.allocN hl($e1) hl($e2))
  | `(hl(ref($e1))) => `(hl(allocn(#1, $e1)))
  | `(hl(free($e1))) => `(Exp.free hl($e1))
  | `(hl(! $e1)) => `(Exp.load hl($e1))
  | `(hl($e1 ← $e2)) => `(Exp.store hl($e1) hl($e2))
  | `(hl(cmpXchg($e1, $e2, $e3))) => `(Exp.cmpXchg hl($e1) hl($e2) hl($e3))
  | `(hl(cas($e1, $e2, $e3))) => `(hl(snd(cmpXchg($e1, $e2, $e3))))
  | `(hl(xchg($e1, $e2))) => `(Exp.xchg hl($e1) hl($e2))
  | `(hl(faa($e1, $e2))) => `(Exp.faa hl($e1) hl($e2))
  | `(hl(fork($e1))) => `(Exp.fork hl($e1))
  | `(hl(assert($e1))) => `(Exp.assert hl($e1))

/-- delaborating Binders -/
@[app_unexpander Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(hl_binder(_))

@[app_unexpander Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(hl_binder($(Lean.mkIdent $ Name.mkSimple s.getString):ident))
  | _ => throw ()

/-- delaborating values -/
@[app_unexpander Val.lit]
def unexpLit : Unexpander
  | `($_ ↑$arg) => `(hl_val(# $arg))
  | `($_ BaseLit.unit) => `(hl_val(# ()))
  | `($_ $arg) => `(hl_val(# $arg))
  | _ => throw ()

partial def unexpLamVal : Term → UnexpandM Term
  | `(hl_val(rec _ $x := $e)) => do
    unexpLamVal $ ← `(hl_val(λ $x, $e))
  | `(hl_val(λ $x, (λ $ys*, $e))) => do
    unexpLamVal $ ← `(hl_val(λ $x $ys*, $e))
  | x => return x

@[app_unexpander Val.rec_]
def unexpRecVal : Unexpander
  | `($_ $f $x $e) => do
    unexpLamVal $ ← `(hl_val(rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e)))
  | _ => throw ()

partial def unexpPairVal' : Term → UnexpandM Term
  | `(hl_val(($e1, ($e2, $e3,*)))) => do
    unexpPairVal' $ ← `(hl_val(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Val.pair]
def unexpPairVal : Unexpander
  | `($_ $e1 $e2) => do
    unexpPairVal' $ ← `(hl_val(($(← unpackHLVal e1), $(← unpackHLVal e2))))
  | _ => throw ()

@[app_unexpander Val.injL]
def unexpInjlVal : Unexpander
  | `($_ $e1) => do `(hl_val(injl($(← unpackHLVal e1))))
  | _ => throw ()

@[app_unexpander Val.injR]
def unexpInjrVal : Unexpander
  | `($_ $e1) => do `(hl_val(injr($(← unpackHLVal e1))))
  | _ => throw ()

/-- delaborating expressions -/
partial def unexpValLit : Term → DelabM Term
  | `(hl(v(# $l))) => do
    unexpValLit $ ← `(hl(# $l))
  | x => return x

@[app_delab ToVal.ofVal]
def unexpVal : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← SubExpr.getExpr
  let_expr ToVal.ofVal exp val _ v := e | failure
  if !exp.isConstOf ``Exp && !val.isConstOf ``Val then failure
  let v ← delab v
  unexpValLit $ ← `(hl(v($(← unpackHLVal v))))

@[app_unexpander Exp.var]
def unexpVar : Unexpander
  | `($_ $e:str) => do `(hl($(Lean.mkIdent $ Name.mkSimple e.getString):ident))
  | _ => throw ()

@[app_unexpander Exp.binop]
def unexpBinop : Unexpander
  | `($_ BinOp.plus $e1 $e2) => do `(hl(($(← unpackHLExp e1) + $(← unpackHLExp e2))))
  | `($_ BinOp.offset $e1 $e2) => do `(hl(($(← unpackHLExp e1) +ₗ $(← unpackHLExp e2))))
  | `($_ BinOp.minus $e1 $e2) => do `(hl(($(← unpackHLExp e1) - $(← unpackHLExp e2))))
  | `($_ BinOp.mult $e1 $e2) => do `(hl(($(← unpackHLExp e1) * $(← unpackHLExp e2))))
  | `($_ BinOp.tdiv $e1 $e2) => do `(hl(($(← unpackHLExp e1) / $(← unpackHLExp e2))))
  | `($_ BinOp.tmod $e1 $e2) => do `(hl(($(← unpackHLExp e1) % $(← unpackHLExp e2))))
  | `($_ BinOp.and $e1 $e2) => do `(hl(($(← unpackHLExp e1) &&& $(← unpackHLExp e2))))
  | `($_ BinOp.or $e1 $e2) => do `(hl(($(← unpackHLExp e1) ||| $(← unpackHLExp e2))))
  | `($_ BinOp.xor $e1 $e2) => do `(hl(($(← unpackHLExp e1) ^^^ $(← unpackHLExp e2))))
  | `($_ BinOp.shiftl $e1 $e2) => do `(hl(($(← unpackHLExp e1) <<< $(← unpackHLExp e2))))
  | `($_ BinOp.shiftr $e1 $e2) => do `(hl(($(← unpackHLExp e1) >>> $(← unpackHLExp e2))))
  | `($_ BinOp.le $e1 $e2) => do `(hl(($(← unpackHLExp e1) ≤ $(← unpackHLExp e2))))
  | `($_ BinOp.lt $e1 $e2) => do `(hl(($(← unpackHLExp e1) < $(← unpackHLExp e2))))
  | `($_ BinOp.eq $e1 $e2) => do `(hl(($(← unpackHLExp e1) = $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.unop]
def unexpUnop : Unexpander
  | `($_ UnOp.neg $e1) => do `(hl((~$(← unpackHLExp e1))))
  | `($_ UnOp.minus $e1) => do `(hl((-$(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.if]
def unexpIf : Unexpander
  | `($_ $e1 $e2 $e3) => do `(hl(if $(← unpackHLExp e1) then $(← unpackHLExp e2) else $(← unpackHLExp e3) ))
  | _ => throw ()

partial def unexpLam : Term → UnexpandM Term
  | `(hl((rec _ $x := $e))) => do
    unexpLam $ ← `(hl((λ $x, $e)))
  | `(hl((λ $x, (λ $ys*, $e)))) => do
    unexpLam $ ← `(hl((λ $x $ys*, $e)))
  | x => return x

@[app_unexpander Exp.rec_]
def unexpRec : Unexpander
  | `($_ $f $x $e) => do
    unexpLam $ ← `(hl((rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e))))
  | _ => throw ()

partial def unexpLet : Term → UnexpandM Term
  | `(hl((λ $f, $e2) $e1)) => do
    unexpLet $ ← `(hl(let $f := $e1; $e2))
  | `(hl(let _ := $e1; $e2)) => do `(hl($e1; $e2))
  | x => return x

@[app_unexpander Exp.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    unexpLet $ ← `(hl($(← unpackHLExp e1) $(← unpackHLExp e2)))
  | _ => throw ()

partial def unexpPair' : Term → UnexpandM Term
  | `(hl(($e1, ($e2, $e3,*)))) => do
    unexpPair' $ ← `(hl(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Exp.pair]
def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' $ ← `(hl(($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.fst]
def unexpFst : Unexpander
  | `($_ $e1) => do `(hl(fst($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.snd]
def unexpSnd : Unexpander
  | `($_ $e1) => do `(hl(snd($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.injL]
def unexpInjl : Unexpander
  | `($_ $e1) => do `(hl(injl($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.injR]
def unexpInjr : Unexpander
  | `($_ $e1) => do `(hl(injr($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.case]
def unexpCase : Unexpander
  | `($_ $e1 hl((λ $i2, $e2)) hl((λ $i3, $e3))) =>
    do `( hl(match $(← unpackHLExp e1) with | injl($i2) => $e2 | injr($i3) => $e3) )
  | _ => throw ()

partial def unexpRef : Term → UnexpandM Term
  | `(hl(allocn(#1, $e2))) => do `(hl(ref($e2)))
  | x => return x

@[app_unexpander Exp.allocN]
def unexpAllocN : Unexpander
  | `($_ $e1 $e2) => do unexpRef $ ← `(hl(allocn($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.free]
def unexpFree : Unexpander
  | `($_ $e1) => do `(hl(free($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.load]
def unexpLoad : Unexpander
  | `($_ $e1) => do `(hl(!$(← unpackHLExp e1)))
  | _ => throw ()

@[app_unexpander Exp.store]
def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(hl($(← unpackHLExp e1) ← $(← unpackHLExp e2)))
  | _ => throw ()

@[app_unexpander Exp.cmpXchg]
def unexpCmpXChg : Unexpander
  | `($_ $e1 $e2 $e3) => do `(hl(cmpXchg($(← unpackHLExp e1), $(← unpackHLExp e2), $(← unpackHLExp e3))))
  | _ => throw ()

@[app_unexpander Exp.xchg]
def unexpXChg : Unexpander
  | `($_ $e1 $e2) => do `(hl(xchg($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.faa]
def unexpFAA : Unexpander
  | `($_ $e1 $e2) => do `(hl(faa($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Exp.fork]
def unexpFork : Unexpander
  | `($_ $e1) => do `(hl(fork($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Exp.assert]
def unexpAssert : Unexpander
  | `($_ $e1) => do `(hl(assert($(← unpackHLExp e1))))
  | _ => throw ()
