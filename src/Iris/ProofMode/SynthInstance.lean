/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Goals

/- TODO: How to call these functions? ProofMode.synthInstance, ipmSynthInstance, synthIPMInstance, synthInstanceIPM? -/

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

def MessageData.withMCtx (mctx : MetavarContext) (d : MessageData) : MessageData :=
  .lazy λ ctx => return MessageData.withContext {env := ctx.env, mctx := mctx, lctx := ctx.lctx, opts := ctx.opts} d

initialize ipmClassesExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name)  ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

syntax (name := ipm_class) "ipm_class" : attr

/-- This attribute should be used for classes that use the special IPM synthInstance below. -/
initialize registerBuiltinAttribute {
  name := `ipm_class
  descr := "proof mode class"
  add := fun decl stx kind =>
    ipmClassesExt.add decl
}


private partial def synthInstanceMainCore (mvar : Expr) : MetaM (Option Unit) := do
  withIncRecDepth do
    let mvarType  ← inferType mvar
    let mvarType  ← instantiateMVars mvarType
    if !(ipmClassesExt.getState (← getEnv)).contains mvarType.getAppFn.constName then
      return ← withTraceNode `Meta.synthInstance (return m!"{exceptOptionEmoji ·} switch to normal synthInstance") do
        let some e ← synthInstance? mvarType | return none
        mvar.mvarId!.assign e
        return some ()

    let mctx0 ← getMCtx
    withTraceNode `Meta.synthInstance (return m!"{exceptOptionEmoji ·} new goal {MessageData.withMCtx mctx0 m!"{mvarType}"} => {mvarType}") do
    let instances ← SynthInstance.getInstances mvarType
    let mctx      ← getMCtx
    if instances.isEmpty then
      return none
    for inst in instances.reverse do
      let mctx0 ← getMCtx
      let res ← withTraceNode `Meta.synthInstance
        (withMCtx mctx0 do return MessageData.withMCtx mctx0 m!"{exceptOptionEmoji ·} apply {inst.val} to {← instantiateMVars (← inferType mvar)}") do
        setMCtx mctx
        let some (mctx', subgoals) ← withAssignableSyntheticOpaque (SynthInstance.tryResolve mvar inst) | return none
        setMCtx mctx'
        for g in subgoals do
          let some _ ← synthInstanceMainCore g | return none
      if res.isSome then
        return res
    return none

private def synthInstanceMain (type : Expr) (_maxResultSize : Nat) : MetaM (Option Expr) :=
  withCurrHeartbeats do
     let mvar ← mkFreshExprMVar type
     tryCatchRuntimeEx (do
       let some _ ← synthInstanceMainCore mvar | return none
       return mvar)
       fun ex =>
         if ex.isRuntime then
           throwError "failed to synthesize{indentExpr type}\n{ex.toMessageData}{useDiagnosticMsg}"
         else
           throw ex

private def synthInstanceCore? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do
  let opts ← getOptions
  let maxResultSize := maxResultSize?.getD (synthInstance.maxSize.get opts)
  withTraceNode `Meta.synthInstance
    (return m!"IPM: {exceptOptionEmoji ·} {← instantiateMVars type}") do
  withConfig (fun config => { config with isDefEqStuckEx := true, transparency := TransparencyMode.instances,
                                          foApprox := true, ctxApprox := true, constApprox := false, univApprox := false }) do
  withInTypeClassResolution do
    let type ← instantiateMVars type
    -- TODO: Should we run whnf under the ∀ quantifiers of type?
    -- let type ← preprocess type
    -- TODO: should we create mvars for outParams?
    -- let normType ← preprocessOutParam type
    let normType := type
    -- key point: we don't create a new MCtxDepth here such that we can instantiate and create mvars
    let result? ← synthInstanceMain normType maxResultSize
    trace[Meta.synthInstance] "result {result?}"
    return result?

protected def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option (Expr × Std.HashSet MVarId)) := do profileitM Exception "typeclass inference " (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  -- we can be sure that e only depends on the mvars that actually appear in e
  (← synthInstanceCore? type maxResultSize?).mapM λ e => do let e ← instantiateMVars e; return (e, ← e.getMVarDependencies)


protected def trySynthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (LOption (Expr × Std.HashSet MVarId)) := do
  catchInternalId isDefEqStuckExceptionId
    (toLOptionM <| ProofMode.synthInstance? type maxResultSize?)
    (fun _ => pure LOption.undef)

protected def trySynthInstanceQ (α : Q(Sort u)) : MetaM (LOption (Q($α) × Std.HashSet MVarId)) :=
  ProofMode.trySynthInstance α

protected def trySynthInstanceQAddingGoals {prop : Q(Type u)} {bi : Q(BI $prop)} (gs : Goals bi) (α : Q(Sort v)) : MetaM (Option Q($α)) := do
  let LOption.some (e, mvars) ← ProofMode.trySynthInstance α | return none
  mvars.forM gs.addPureGoal
  return some e
