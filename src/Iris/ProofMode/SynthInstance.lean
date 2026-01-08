/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Goals

/-
This file implements a custom typeclass synthesis algorithm that is used for the proof mode typeclasses.
This is necessary since proof mode typeclasses need to be able to instantiate and create new mvars, but the
standard typeclass synthesis does not support this.

See also https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Issues.20with.20typeclasses.20in.20the.20proof.20mode/with/563410548 for discussion.

In addition to the synthInstance family of functions, we provide the following attributes and annotations:

The `ipm_class` attribute marks that a class should use the IPM synthesis defined in this file. For all other classes,
the IPM synthesis falls back to standard synthesis, enabling one to use standard type classes as parameters for IPM type classes.
Note that IPM synthesis is *not* triggered automatically for holes where the class is marked with `ipm_class`. Instead,
the IPM synthesis needs to be explicitly invoked via the functions in this file.

The `ipm_backtrack` attribute on an instance tells the IPM synthesis to backtrack if instance instance can be applied, but
its preconditions fail to synthesize. This is not enabled by default to avoid accidental exponential blow-ups.

The `InOut` type in Classes.lean is used to dynamically determine, which parameters are inputs and which are outputs. IPM synthesis
ignores `outParam` and `semiOutParam` annotations, but it is still recommended to add these annotations as documentation.

The `#imp_synth` command allows testing ipm synthesis, similar to the `#synth` command.

-/

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
  add := fun decl _stx _kind =>
    ipmClassesExt.add decl
}

initialize ipmBacktrackExt :
    SimpleScopedEnvExtension Name (Std.HashSet Name)  ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := ∅
  }

syntax (name := ipm_backtrack) "ipm_backtrack" : attr

/-- This attribute marks instances on which the proof mode synthesis should backtrack. -/
initialize registerBuiltinAttribute {
  name := `ipm_backtrack
  descr := "Enable backtracking for this instance"
  add := fun decl _stx _kind =>
    ipmBacktrackExt.add decl
}


private partial def synthInstanceMainCore (mvar : Expr) : MetaM (Option Unit) := do
  withIncRecDepth do
    let backtrackSet := ipmBacktrackExt.getState (← getEnv)
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
      let (res, match?) ← withTraceNode `Meta.synthInstance
        (λ r => withMCtx mctx do return MessageData.withMCtx mctx m!"{exceptOptionEmoji (r.map (·.1))} apply {inst.val} to {← instantiateMVars (← inferType mvar)}") do
        setMCtx mctx
        let some (mctx', subgoals) ← withAssignableSyntheticOpaque (SynthInstance.tryResolve mvar inst) | return (none, false)
        setMCtx mctx'
        for g in subgoals do
          let some _ ← synthInstanceMainCore g | return (none, true)
        return (some (), true)
      if res.isSome then
        return res
      if (match? && !backtrackSet.contains inst.val.getAppFn.constName) then
        trace[Meta.synthInstance] "no backtracking to other instances"
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
    -- TODO: if it becomes necessary, run whnf under the ∀ quantifiers of type
    -- let type ← preprocess type
    -- TODO: if it becomes necessary, create mvars for outParams
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

syntax (name := ipm_synth) "#ipm_synth " term : command

@[command_elab ipm_synth]
def ipm_synth_elab : Command.CommandElab
  | `(#ipm_synth $term) =>
        withoutModifyingEnv <| Command.runTermElabM fun _ => Term.withDeclName `_ipm_synth do
        let e ← Term.elabTerm term none
        Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
        let e ← Term.levelMVarToParam (← instantiateMVars e)
        match ← ProofMode.trySynthInstance e with
        | .undef => logInfo "Undefined"
        | .none => logInfo "None"
        | .some (e, mvars) => do
            logInfo m!"solution: {← inferType e}, new goals: {← mvars.toList.mapM (λ m => do return m!"{Expr.mvar m}: {← m.getType}")}"
  | _ => throwUnsupportedSyntax
