module

public import Iris.ProofMode
public import Iris.HeapLang.Tactic
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Language
public import Iris.ProgramLogic.EctxLanguage
public import Iris.ProgramLogic.EctxiLanguage
public import Lean
public import Qq

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang

-- TODO: Is this really needed?
meta def quoteList {α : Q(Type u)}: List Q($α) → Q(List $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

meta
def trySubtractExprFromContextAt(ctx : List Q(ECtxItem)) (e : Q(Exp)) (K : Q(Exp)) (position : Nat) : MetaM (Option (List Q(ECtxItem))) := do
  let (inner_Ks, outer_Ks) := ctx.splitAt position
  trace[wp_bind] s!"Expression context (inner): {← inner_Ks.mapM <| liftM ∘ ppExpr}"
  trace[wp_bind] s!"Expression context (outer): {← outer_Ks.mapM <| liftM ∘ ppExpr}"
  let K' ← HeapLang.fill inner_Ks e
  if ←isDefEq K K' then return .some outer_Ks else return .none

meta partial
def substractExprFromContextMatchingFrom (ctx : List Q(ECtxItem)) (e : Q(Exp)) (K : Q(Exp)) (pt : Nat) : MetaM (List Q(ECtxItem)) :=  do
  if pt <= ctx.length then
    match ← trySubtractExprFromContextAt ctx e K pt with
    | .some outer_Ks => return outer_Ks
    | .none => substractExprFromContextMatchingFrom ctx e K (pt+1)
  else
    throwError s!"Couldn't unify {←ppExpr K} with any possible evaluation context"

meta partial
def substractExprFromContext (ctx : List Q(ECtxItem)) (e : Q(Exp)) (K : Q(Exp)) : MetaM (List Q(ECtxItem)) :=  do
  let (Ks, rad) := (← HeapLang.extractAllEctxItems K)
  let K_depth := Ks.length
  if let .mvar _ := rad then
    -- NOTE: It only makes sense to search for a possibly bigger context if the radical is
    -- a metavariable.
    substractExprFromContextMatchingFrom ctx e K K_depth
  else
    let .some res ← trySubtractExprFromContextAt ctx e K K_depth
      | throwError s!"Couldn't unify {←ppExpr K} with any possible evaluation context"
    return res

elab "wp_bind" K:term : tactic => do
  -- TODO: Do we ask for a function or for a "pattern"?
  let K ← elabTermEnsuringTypeQ K q(HeapLang.Exp)
  trace[bind] s!"Context to bind over: {←ppExpr K}"
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "`wp_bind` only works over `IProp` (at universe level 0)"
    let ~q(IProp $GF) := prop
      | throwError "`wp_bind` only works over `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "`wp_bind` expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    let ~q(Wp.wp (A := Stuckness) (Expr := Exp) (Val := $Val)
      (self := wp.def (Λ := @ProgramLogic.EctxLanguage.instLanguage _ _ _ _ _ (ProgramLogic.EctxItemLanguage.instEctxLanguage (EctxItem := ECtxItem) (Λ := $Λ))) (ι := $ι))
      $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"
    let (ctx, e) ← HeapLang.extractAllEctxItems e
    trace[wp_bind] s!"Expression context: {← ctx.mapM <| liftM ∘ ppExpr}"
    trace[wp_bind] s!"Expression radical: {←ppExpr e}"
    let outer_Ks ← substractExprFromContext ctx e K

    let outer_K := quoteList outer_Ks

    let evctxInst : Q(ProgramLogic.Language.Context (ProgramLogic.fill (Expr := Exp) $outer_K)) := q(ProgramLogic.EctxLanguage.instContextFill ..)
    trace[wp_bind] s!"Evaluation context instance: {←ppExpr evctxInst}"

    let pf := q(wp_bind (GF := $GF) (ProgramLogic.fill _) (κ := $evctxInst) (s := $s) (E := $E) (e := $K) (Φ := $Φ))
    let innerPostcond : Q($Val → IProp $GF) ← Qq.withLocalDeclDQ `v q(Val) fun v => do
      mkLambdaFVars #[v] <| q(Wp.wp (PROP := IProp $GF) $s $E $(←HeapLang.fill outer_Ks q(.val $v)) $Φ)

    -- TODO: Here, we assume that `HeapLang.fill outer_Ks v` properly reflects the semantics of
    -- `ProgramLogic.fill`. It requires us to have a duplicate implementation of `fill`, one in the
    -- object level and one in the meta level, and ensure that these implementations are equivalent.
    -- The reason we use `HeapLang.fill` here is to ensure the context is properly simplified. It
    -- may be preferable to, instead, use `ProgramLogic.fill` everywhere, and simply invoke `simp`
    -- to perform a targetted "constant evaluation" on the produced term.
    have : $innerPostcond =Q fun v : $Val => Wp.wp (PROP := IProp $GF) $s $E (ProgramLogic.fill $outer_K (v : Exp)) $Φ := ⟨⟩

    let newGoal := q(Wp.wp (PROP := IProp $GF) $s $E $K $innerPostcond)

    let newProof ← addBIGoal hyps newGoal
    mvar.assign q($(newProof).trans $pf)

initialize registerTraceClass `wp_bind
