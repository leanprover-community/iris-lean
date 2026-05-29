module

public import Iris.HeapLang.Syntax
public import Iris.ProofMode.ProofModeM
public import Lean
public import Qq

namespace Iris.HeapLang

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Qq

def extractEctxItem : Q(Exp) → MetaM (Option Q(Exp.EctxItem) × Q(Exp))
  | ~q(.app $e (.val $v₂)) => return (some q(Exp.EctxItem.app_left $v₂), e)
  | ~q(.app $e₁ $e) => return (some q(Exp.EctxItem.app_right $e), e)
  /-  ‹op› □ -/
  | ~q(.unop $op $e) => return (some q(Exp.EctxItem.unop $op), e)

  /- □ ‹op› v₂ -/
  | ~q(.binop $op $e (.val $v₂)) => return (some q(Exp.EctxItem.binop_left $op $v₂), e)
  /- e₁ ‹op› □ -/
  | ~q(.binop $op $e₁ $e) => return (some q(Exp.EctxItem.binop_right $op $e₁), e)

  /- if □ then e₁ else e₂ -/
  | ~q(.if $e $e₁ $e₂) => return (some q(Exp.EctxItem.if $e₁ $e₂), e)

  /- (□, v₂) -/
  | ~q(.pair $e (.val $v₂)) => return (some q(Exp.EctxItem.pair_left $v₂), e)
  /- (e₁, □) -/
  | ~q(.pair $e₁ $e) => return (some q(Exp.EctxItem.pair_right $e₁), e)

  /- □.fst -/
  | ~q(.fst $e) => return (some q(Exp.EctxItem.fst), e)
  /- □.snd -/
  | ~q(.snd $e) => return (some q(Exp.EctxItem.snd), e)

  /- injL(□) -/
  | ~q(.injL $e) => return (some q(Exp.EctxItem.injL), e)
  /- injR(□) -/
  | ~q(.injR $e) => return (some q(Exp.EctxItem.injR), e)

  /- match □ with | .injL _ => e₁ | .injR _ => e₂  -/
  | ~q(.case $e $e₁ $e₂) => return (some q(Exp.EctxItem.case $e₁ $e₂), e)

  /- allocn(□, v₂) -/
  | ~q(.allocN $e (.val $v₂)) => return (some q(Exp.EctxItem.allocN_left $v₂), e)
  /- allocn(e₁, □) -/
  | ~q(.allocN $e₁ $e) => return (some q(Exp.EctxItem.allocN_right $e₁), e)

  /- free(□) -/
  | ~q(.free $e) => return (some q(Exp.EctxItem.free), e)

  /- ! □ -/
  | ~q(.load $e) => return (some q(Exp.EctxItem.load), e)

  /- □ ← v₂ -/
  | ~q(.store $e (.val $v₂)) => return (some q(Exp.EctxItem.store_left $v₂), e)
  /- e₁ ← □ -/
  | ~q(.store $e₁ $e) => return (some q(Exp.EctxItem.store_right $e₁), e)

  /- xchg(□, v₂) -/
  | ~q(.xchg $e (.val $v₂)) => return (some q(Exp.EctxItem.xchg_left $v₂), e)
  /- xchg(e₁, □) -/
  | ~q(.xchg $e₁ $e) => return (some q(Exp.EctxItem.xchg_right $e₁), e)

  /- cmpXchg(□, v₁, v₂) -/
  | ~q(.cmpXchg $e (.val $v₁) (.val $v₂)) => return (some q(Exp.EctxItem.cmpXchg_left $v₁ $v₂), e)
  /- cmpXchg(e₀, □, v₂) -/
  | ~q(.cmpXchg $e₀ $e (.val $v₂)) => return (some q(Exp.EctxItem.cmpXchg_middle $e₀ $v₂), e)
  /- cmpXchg(e₀, e₁, □) -/
  | ~q(.cmpXchg $e₀ $e₁ $e) => return (some q(Exp.EctxItem.cmpXchg_right $e₀ $e₁), e)

  /- faa(□, v₂) -/
  | ~q(.faa $e (.val $v₂)) => return (some q(Exp.EctxItem.faa_left $v₂), e)
  /- faa(e₁, □) -/
  | ~q(.faa $e₁ $e) => return (some q(Exp.EctxItem.faa_right $e₁), e)
  /- fork(□) -/
  | ~q(.fork $e) => return (some q(Exp.EctxItem.fork), e)

  /- resolve(□, v₁, v₂) -/
  | ~q(.resolve $e (.val $v₁) (.val $v₂)) => return (some q(Exp.EctxItem.resolve_left $v₁ $v₂), e)
  /- resolve(e₀, □, v₂) -/
  | ~q(.resolve $e₀ $e (.val $v₂)) => return (some q(Exp.EctxItem.resolve_middle $e₀ $v₂), e)
  /- resolve(e₀, v₁, □) -/
  | ~q(.resolve $e₀ $e₁ $e) => return (some q(Exp.EctxItem.resolve_right $e₀ $e₁), e)
  | e => return (none, e)


partial
def extractAllEctxItems (e : Q(Exp)) (acc : List Q(Exp.EctxItem) := []) : MetaM (List Q(Exp.EctxItem) × Q(Exp)) := do
  match ← extractEctxItem e with
  | (.some Ki, e') =>
    extractAllEctxItems e' (Ki :: acc)
  | (.none, e) =>
    return (acc, e)
