module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.ProofMode.ProofModeM
public import Lean
public import Iris.ProgramLogic.EctxiLanguage
public import Iris.ProgramLogic.EctxLanguage
public import Iris.HeapLang.Instances
public import Qq

namespace Iris.HeapLang

open Lean hiding Expr
open Lean renaming Expr → LeanExpr
open Qq Iris.ProofMode

open ECtxItem in
meta partial
def extractEctxItem : Q(Exp) → MetaM (Option Q(ECtxItem) × Q(Exp))
  | ~q(.app $e (.val $v₂))                => return (some q(appL $v₂), e)
  | ~q(.app $e₁ $e)                       => return (some q(appR $e₁), e)
  | ~q(.unop $op $e)                      => return (some q(unOp $op), e)
  | ~q(.binop $op $e (.val $v₂))          => return (some q(binOpL $op $v₂), e)
  | ~q(.binop $op $e₁ $e)                 => return (some q(binOpR $op $e₁), e)
  | ~q(.if $e $e₁ $e₂)                    => return (some q(.if $e₁ $e₂), e)
  | ~q(.pair $e (.val $v₂))               => return (some q(pairL $v₂), e)
  | ~q(.pair $e₁ $e)                      => return (some q(pairR $e₁), e)
  | ~q(.fst $e)                           => return (some q(fst), e)
  | ~q(.snd $e)                           => return (some q(snd), e)
  | ~q(.injL $e)                          => return (some q(injL), e)
  | ~q(.injR $e)                          => return (some q(injR), e)
  | ~q(.case $e $e₁ $e₂)                  => return (some q(case $e₁ $e₂), e)
  | ~q(.allocN $e (.val $v₂))             => return (some q(allocNL $v₂), e)
  | ~q(.allocN $e₁ $e)                    => return (some q(allocNR $e₁), e)
  | ~q(.free $e)                          => return (some q(free), e)
  | ~q(.load $e)                          => return (some q(load), e)
  | ~q(.store $e (.val $v₂))              => return (some q(storeL $v₂), e)
  | ~q(.store $e₁ $e)                     => return (some q(storeR $e₁), e)
  | ~q(.xchg $e (.val $v₂))               => return (some q(xchgL $v₂), e)
  | ~q(.xchg $e₁ $e)                      => return (some q(xchgR $e₁), e)
  | ~q(.cmpXchg $e (.val $v₁) (.val $v₂)) => return (some q(cmpXchgL $v₁ $v₂), e)
  | ~q(.cmpXchg $e₀ $e (.val $v₂))        => return (some q(cmpXchgM $e₀ $v₂), e)
  | ~q(.cmpXchg $e₀ $e₁ $e)               => return (some q(cmpXchgR $e₀ $e₁), e)
  | ~q(.faa $e (.val $v₂))                => return (some q(faaL $v₂), e)
  | ~q(.faa $e₁ $e)                       => return (some q(faaR $e₁), e)
  | ~q(.resolve $e (.val $v₁) (.val $v₂)) => extractResolveL q(.resolve $e (.val $v₁) (.val $v₂))
  | ~q(.resolve $e₀ $e (.val $v₂))        => return (some q(resolveM $e₀ $v₂), e)
  | ~q(.resolve $e₀ $e₁ $e)               => return (some q(resolveR $e₀ $e₁), e)
  | e => return (none, e)
where
  extractResolveL : Q(Exp) → MetaM (Option Q(ECtxItem) × Q(Exp))
  | ~q(.resolve $e (.val $v₁) (.val $v₂)) => do
    let (.some K, rest) ← extractResolveL e
      | return (none, e)
    return (.some q(resolveL $K $v₁ $v₂), rest)
  | e =>
    extractEctxItem e

public meta partial
def extractAllEctxItems (e : Q(Exp)) (acc : List Q(ECtxItem) := []) : MetaM (List Q(ECtxItem) × Q(Exp)) := do
  match ← extractEctxItem e with
  | (.some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (.none, e) => return (acc, e)


open ECtxItem in
meta partial
def fillItem (e : Q(Exp)) : Q(ECtxItem) → MetaM Q(Exp)
  | ~q(appL $v₂)            => return q(.app $e (.val $v₂))
  | ~q(appR $e₁)            => return q(.app $e₁ $e)
  | ~q(unOp $op)            => return q(.unop $op $e)
  | ~q(binOpL $op $v₂)      => return q(.binop $op $e (.val $v₂))
  | ~q(binOpR $op $e₁)      => return q(.binop $op $e₁ $e)
  | ~q(.if $e₁ $e₂)         => return q(.if $e $e₁ $e₂)
  | ~q(pairL $v₂)           => return q(.pair $e (.val $v₂))
  | ~q(pairR $e₁)           => return q(.pair $e₁ $e)
  | ~q(fst)                 => return q(.fst $e)
  | ~q(snd)                 => return q(.snd $e)
  | ~q(injL)                => return q(.injL $e)
  | ~q(injR)                => return q(.injR $e)
  | ~q(case $e₁ $e₂)        => return q(.case $e $e₁ $e₂)
  | ~q(allocNL $v₂)         => return q(.allocN $e (.val $v₂))
  | ~q(allocNR $e₁)         => return q(.allocN $e₁ $e)
  | ~q(free)                => return q(.free $e)
  | ~q(load)                => return q(.load $e)
  | ~q(storeL $v₂)          => return q(.store $e (.val $v₂))
  | ~q(storeR $e₁)          => return q(.store $e₁ $e)
  | ~q(xchgL $v₂)           => return q(.xchg $e (.val $v₂))
  | ~q(xchgR $e₁)           => return q(.xchg $e₁ $e)
  | ~q(cmpXchgL $v₁ $v₂)    => return q(.cmpXchg $e (.val $v₁) (.val $v₂))
  | ~q(cmpXchgM $e₀ $v₂)    => return q(.cmpXchg $e₀ $e (.val $v₂))
  | ~q(cmpXchgR $e₀ $e₁)    => return q(.cmpXchg $e₀ $e₁ $e)
  | ~q(faaL $v₂)            => return q(.faa $e (.val $v₂))
  | ~q(faaR $e₁)            => return q(.faa $e₁ $e)
  | ~q(resolveL $K $v₁ $v₂) => return q(.resolve $(←fillItem e K) (.val $v₁) (.val $v₂))
  | ~q(resolveM $e₀ $v₂)    => return q(.resolve $e₀ $e (.val $v₂))
  | ~q(resolveR $e₀ $e₁)    => return q(.resolve $e₀ $e₁ $e)


public meta partial def fill (K : Q(List ECtxItem)) (e : Q(Exp)) : MetaM Q(Exp) :=
  -- K.foldlM fillItem e
  match K with
  | ~q([]) => pure e
  | ~q($Ki :: $K) => do
    fill K (←fillItem e Ki)

public meta partial def fillQ (K: Q(List ECtxItem)) (e : Q(Exp)) : MetaM ((res : Q(Exp)) × PLift ($res =Q ProgramLogic.fill $K $e)):=
  return ⟨←fill K e , .up ⟨⟩⟩

meta def quoteList {α : Q(Type u)}: List Q($α) → Q(List $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

public meta
structure ECtxResultOf (e : Q(Exp)) (α : Type) where unsafeMk ::
  result : α
  K : Q(List ECtxItem)
  e' : Q(Exp)
  heq : ProgramLogic.fill $K $e' =Q $e := ⟨⟩

public meta partial
def findECtx {α : Type _} (ogE : Q(Exp)) (pred : Q(Exp) → ProofModeM α)
  : ProofModeM (Option (ECtxResultOf ogE α)) := do
  let (Kis, inner) ← extractAllEctxItems ogE
  go inner Kis
where
  go (e : Q(Exp)) (Kis : List Q(ECtxItem)) : ProofModeM (Option (ECtxResultOf ogE α)) := do
    if let some a ← observing? <| pred e then
      return some {result := a, K := quoteList Kis, e' := e}
    let Ki :: Kis' := Kis | return none
    go (← fillItem e Ki) Kis'
