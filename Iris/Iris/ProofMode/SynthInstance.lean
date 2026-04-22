/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Qq
public import Iris.BI
public import Iris.ProofMode.SynthInstanceAttr

public meta section

/-
This file implements a custom typeclass synthesis algorithm that is used for the proof mode typeclasses.
This custom typeclass synthesis is closer to Rocq typeclass search than Lean typeclass synthesis.
This is necessary since proof mode typeclasses need to be able to instantiate and create new mvars, but the
standard typeclass synthesis does not support this.

Another problem with standard typeclass synthesis in Lean is that an mvar in an input position creates an IsDefEqStuck exception
when matches against an instances with a term in the input position. This IsDefEqStuck exception completely terminates the synthesis
without trying other instances. This creates problems for example for the `Make...` typeclasses that want to treat such cases as a
normal matching failure that should not prevent other instances from matching.

See also https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Issues.20with.20typeclasses.20in.20the.20proof.20mode/with/563410548 for discussion.

In addition to the synthInstance family of functions, we provide the following attributes and annotations:

The `ipm_class` attribute marks that a class should use the IPM synthesis defined in this file. For all other classes,
the IPM synthesis falls back to standard synthesis, enabling one to use standard type classes as parameters for IPM type classes.
Note that IPM synthesis is *not* triggered automatically for holes where the class is marked with `ipm_class`. Instead,
the IPM synthesis needs to be explicitly invoked via the functions in this file.

The `ipm_backtrack` attribute on an instance tells the IPM synthesis to backtrack if instance instance can be applied, but
its preconditions fail to synthesize. This is not enabled by default to avoid accidental exponential blow-ups.

The `ipm_tactic_instance` attribute on a function of type `SynthTactic` declares a tactic that is used to solve synthesis problems for
a given pattern. These tactics can call ipm synthesis recursively. See Tests/Instances.lean for examples.

The `InOut` type in Classes.lean is used to dynamically determine, which parameters are inputs and which are outputs. IPM synthesis
ignores `outParam` and `semiOutParam` annotations, but it is still recommended to add these annotations as documentation.

The `#imp_synth` command allows testing ipm synthesis, similar to the `#synth` command.
-/

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

def MessageData.withMCtx (mctx : MetavarContext) (d : MessageData) : MessageData :=
  .lazy λ ctx => return MessageData.withContext {env := ctx.env, mctx := mctx, lctx := ctx.lctx, opts := ctx.opts} d

partial def synthInstanceMainCore (mvar : Expr) : MetaM (Option Unit) := do
  withIncRecDepth do
    let backtrackSet := ipmBacktrackExt.getState (← getEnv)
    let mvarType  ← inferType mvar
    let mvarType  ← instantiateMVars mvarType
    let some mvarInputs ← checkIPMSynthParams mvarType |
      return ← withTraceNode `Meta.synthInstance (λ _ => return m!"switch to normal synthInstance") do
        let .some e ← trySynthInstance mvarType | return none
        mvar.mvarId!.assign e
        return some ()
    if mvarInputs.size != 0 then
      trace[Meta.synthInstance.mvarInputs] m!"mvar inputs of {mvarType}: {mvarInputs}"

    let mctx0 ← getMCtx
    withTraceNode `Meta.synthInstance (λ _ => return m!"new goal {MessageData.withMCtx mctx0 m!"{mvarType}"} => {mvarType}") do

    -- first tactics and then instances. We cannot interleave them
    -- since we don't know the priorities of the instances.
    let tactics ← forallTelescopeReducing mvarType fun _ type => do
      (synthTacticExt.getState (← getEnv)).getUnify type
    let tactics := tactics.insertionSort fun e₁ e₂ => e₁.prio < e₂.prio
    trace[Meta.synthInstance.tactics] m!"{tactics}"

    let mctx ← getMCtx
    for tac in tactics.reverse do
      let res ← withTraceNode `Meta.synthInstance
        (λ _ => withMCtx mctx do return MessageData.withMCtx mctx m!"apply tactic {tac.name} to {← instantiateMVars (← inferType mvar)}") do
        setMCtx mctx
        forallTelescopeReducing mvarType fun xs mvarTypeBody => do
          let res ← tac.tac.run mvarTypeBody
          match res with
          | .success instVal =>
            trace[Meta.synthInstance] m!"{tac.name} success: {instVal}"
            let mut instType ← inferType instVal
            let .true ← isDefEq mvarTypeBody instType | throwError "{tac.name} produced an ill-typed term: {instVal}"
            let instVal ← mkLambdaFVars xs instVal (etaReduce := true)
            let .true ← isDefEq mvar instVal | throwError "{tac.name} produced an ill-typed term: {instVal}"
            return .success default
          | _ => return res
      match res with
      | .success _ =>
        return some ()
      | .fail => do
        trace[Meta.synthInstance] m!"{tac.name} failed, no backtracking to other instances"
        return none
      | .continue =>
        trace[Meta.synthInstance] m!"{tac.name} did not find an instance, continue to other instances"
        continue

    let instances ← SynthInstance.getInstances mvarType
    let mctx ← getMCtx
    for inst in instances.reverse do
      -- check that all mvar inputs are also mvars in the instance
      if mvarInputs.size != 0 then
        let instType ← inferType inst.val
        let instTypeArgs := instType.getForallBody.getAppArgs
        if mvarInputs.any (λ i => !instTypeArgs[i]!.isBVar) then
          trace[Meta.synthInstance] "skipping {inst.val} since it matches on an input mvar"
          continue

      let (res, match?) ← withTraceNode `Meta.synthInstance
        (λ _ => withMCtx mctx do return MessageData.withMCtx mctx m!"apply {inst.val} to {← instantiateMVars (← inferType mvar)}") do
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

/-- This function should only be directly used by IPM tactic instances
to initiate recursive searches. -/
def synthInstanceRecursive (type : Expr) : MetaM (Option Expr) := do
   let mctx ← getMCtx
   let mvar ← mkFreshExprMVar type
   let res ← try
       synthInstanceMainCore mvar
     catch ex => setMCtx mctx; throw ex
   if res.isSome then
     return mvar
   setMCtx mctx
   return none

/-- This function should only be directly used by IPM tactic instances
to initiate recursive searches. -/
def synthInstanceRecursiveQ (type : Q(Sort u)) : MetaM (Option Q($type)) := synthInstanceRecursive type

def synthInstanceMain (type : Expr) (_maxResultSize : Nat) : MetaM (Option Expr) :=
  withCurrHeartbeats do
     tryCatchRuntimeEx (synthInstanceRecursive type)
       fun ex =>
         if ex.isRuntime then
           throwError "failed to synthesize{indentExpr type}\n{ex.toMessageData}{useDiagnosticMsg}"
         else
           throw ex

def synthInstanceCore? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option Expr) := do
  let opts ← getOptions
  let maxResultSize := maxResultSize?.getD (synthInstance.maxSize.get opts)
  withTraceNode `Meta.synthInstance
    (λ _ => return m!"IPM: {← instantiateMVars type}") do
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

protected def synthInstance? (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Option (Expr × Std.HashSet MVarId)) := do profileitM Exception "typeclass inference IPM" (← getOptions) (decl := type.getAppFn.constName?.getD .anonymous) do
  -- we can be sure that e only depends on the mvars that actually appear in e
  (← synthInstanceCore? type maxResultSize?).mapM λ e => do let e ← instantiateMVars e; return (e, ← e.getMVarDependencies)

protected def trySynthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (LOption (Expr × Std.HashSet MVarId)) := do
  catchInternalId isDefEqStuckExceptionId
    (toLOptionM <| ProofMode.synthInstance? type maxResultSize?)
    (fun _ => pure LOption.undef)

protected def synthInstance (type : Expr) (maxResultSize? : Option Nat := none) : MetaM (Expr × Std.HashSet MVarId) :=
  catchInternalId isDefEqStuckExceptionId
    (do
      let result? ← ProofMode.synthInstance? type maxResultSize?
      match result? with
      | some result => pure result
      | none        => do _ ← throwFailedToSynthesize type; unreachable!)
    (fun _ => do _ ← throwFailedToSynthesize type; unreachable!)

/- It is recommended to use ProofModeM.trySynthInstanceQ and ProofModeM.synthInstanceQ that automatically handle the newly spawed goals. -/

protected def trySynthInstanceQ (α : Q(Sort u)) : MetaM (LOption (Q($α) × Std.HashSet MVarId)) :=
  ProofMode.trySynthInstance α

protected def synthInstanceQ (α : Q(Sort u)) : MetaM (Q($α) × Std.HashSet MVarId) :=
  ProofMode.synthInstance α

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

initialize
  registerTraceClass `Meta.synthInstance.mvarInputs (inherited := true)
  registerTraceClass `Meta.synthInstance.tactics (inherited := true)
