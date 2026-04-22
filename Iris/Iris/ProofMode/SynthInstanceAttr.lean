/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Qq
public import Iris.BI.Notation

public meta section

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq

/-- [InOut] is used to dynamically determine whether a type class
parameter is an input or an output. This is important for classes that
are used with multiple modings, e.g., IntoWand. Instances can match on
the InOut parameter to avoid accidentially instantiating outputs if
matching on an input was intended. -/
inductive InOut where
  | in
  | out

/-- Marker for an unchecked input parameter. -/
@[reducible, expose]
def uncheckedInParam (α : Sort u) : Sort u := α

/-- Return `true` if `e` is of the form `uncheckedInParam _` or `outParam (uncheckedInParam _)`. The second case is necessary for `FromModal`. -/
def isUncheckedInParam (e : Expr) : Bool :=
  e.isAppOfArity ``uncheckedInParam 1 || (e.isOutParam && e.appArg!.isAppOfArity ``uncheckedInParam 1)

/--
The parameters of a class declared with `ipm_class` are categorized into the following categories:

1. in: This is the default for a parameter when not annotated in another way.
2. out: These are parameters marked with `outParam`. These parameters must be mvars when starting typeclass search.
3. semiOut: These are parameters marked with `semiOutParam`. The preceding parameter must be of type `InOut`. The value of the `InOut` parameter decides whether the `semiOut` parameter is treated as an input or an output.
4. uncheckedIn: These are parameters marked with `uncheckedInParam`. These behave like `in` parameters, but allow mvars to match terms (see below).
5. inout: Parameters of type `InOut`, must appear before semiOut parameters (see above).

The following constraints apply to the parameters:
(In the following, semiOut parameters are treated as inputs if the preceding `InOut` is `in` and as outputs if the `InOut` is `out`.)
1. semiOut parameters must have a preceding `InOut` parameter.
2. For each synthesis problem, all output parameters must be mvars.
3. When an input parameter is a mvar, it is not considered to match an instance which does not have an mvar at the top-level. This is to prevent accidentally instantiating mvars. Note that this only applies for mvars the top-level (matching the behavior of Hint Mode : ! in Rocq), since this is the simplest version to implement and catches most (all?) of the cases.
This check 3 is omitted for `uncheckedIn` parameters.
 -/
inductive ParamKind
  | in
  | out
  | semiOut
  | uncheckedIn
  | inout
deriving Inhabited

instance : ToString ParamKind where
  toString
    | .in => "in"
    | .out => "out"
    | .semiOut => "semiOut"
    | .uncheckedIn => "uncheckedIn"
    | .inout => "inout"

section IPMClasses
structure ClassEntry where
  name      : Name
  /--
  Parameter kinds of class.
  For example, for class
  ```
  class FromModal {PROP1 : outParam (Type _)} {PROP2} [outParam (BI PROP1)] [BI PROP2] (φ : outParam $ Prop) (M : outParam $ Modality PROP1 PROP2) (sel : outParam (uncheckedInParam PROP1)) (P : PROP2) (Q : outParam $ PROP1) where
  from_modal : φ → M.M Q ⊢ P
  ```
  `params := #[out, in, out, in, out, out, uncheckedIn, in, out]`
  -/
  params : Array ParamKind

structure ClassState where
  paramMap : SMap Name (Array ParamKind) := SMap.empty
  deriving Inhabited

namespace ClassState

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
  { s with
    paramMap := s.paramMap.insert entry.name entry.params }

/--
Switch the state into persistent mode. We switch to this mode after
we read all imported .olean files.
Recall that we use a `SMap` for implementing the state.
-/
def switch (s : ClassState) : ClassState :=
  { s with
    paramMap := s.paramMap.switch }

end ClassState


initialize ipmClassesExt :
    SimplePersistentEnvExtension ClassEntry ClassState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := ClassState.addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries ClassState.addEntry {} es).switch
  }

private def getIPMParamKinds? (env : Environment) (declName : Name) : Option (Array ParamKind) :=
  (ipmClassesExt.getState env).paramMap.find? declName

private partial def computeParamKinds (params : Array ParamKind) (wasInOut : Bool) (type : Expr) : Except MessageData (Array ParamKind) :=
  match type with
  | .forallE _ d b _ =>
    if wasInOut then
      if d.isSemiOutParam then
        computeParamKinds (params.push .semiOut) false b
      else
        Except.error m!"invalid ipm_class, parameter #{params.size} is a `InOut` that is not followed by a `semiOutParam`"
    else
      -- we need to check this before outParam since `outParam (uncheckedInParam _)` should be an `uncheckedInParam`
      if isUncheckedInParam d then
        computeParamKinds (params.push .uncheckedIn) false b
      else if d.isOutParam then
        computeParamKinds (params.push .out) false b
      else if d.isSemiOutParam then
        Except.error m!"invalid ipm_class, parameter #{params.size+1} is a `semiOutParam` that is not preceded by an `InOut`"
      else if d.isAppOfArity ``InOut 0 then
        computeParamKinds (params.push .inout) true b
      else
        computeParamKinds (params.push .in) false b
  | _ => return params

def checkIPMSynthParams (type : Expr) : MetaM (Option (Array Nat)) := do
  forallTelescopeReducing type fun _ typeBody => do
    let typeBody ← whnf typeBody
    let name := typeBody.getAppFn.constName
    let .some params := getIPMParamKinds? (← getEnv) name | return none
    let args := typeBody.getAppArgs
    if args.size != params.size then
      throwError "mismatched number of arguments"
    let mut inoutIsIn := false
    let mut mvarInputs := #[]
    for i in 0...args.size do
      let param := params[i]!
      let arg := args[i]!
      let param := if param matches .semiOut then
          if inoutIsIn then .in else .out
        else param
      match param with
      | .uncheckedIn => pure ()
      | .in => if arg.getAppFn.isMVar then mvarInputs := mvarInputs.push i
      | .out => if !arg.getAppFn.isMVar then throwError "parameter #{i} {arg} of {type} is an out parameter that is not an mvar"
      | .inout =>
        if arg.isAppOfArity ``InOut.in 0 then
          inoutIsIn := true
        else if arg.isAppOfArity ``InOut.out 0 then
          inoutIsIn := false
        else
          throwError "parameter #{i} {arg} of {type} is an inout parameter that is not .in nor .out"
      | .semiOut => unreachable!
    return some mvarInputs

syntax (name := ipm_class) "ipm_class" : attr

/-- This attribute should be used for classes that use the special IPM synthInstance. -/
initialize registerBuiltinAttribute {
  name := `ipm_class
  descr := "proof mode class"
  add := fun declName stx kind => do
    let env ← getEnv
    let some decl := env.find? declName
      | throwError "unknown declaration '{declName}'"
    unless kind == AttributeKind.global do throwAttrMustBeGlobal `ipm_class kind
    let params ← ofExcept <| computeParamKinds #[] false decl.type
    trace[Meta.synthInstance.ipmParamKinds] m!"IPM params of {declName}: {params}"
    let env := ipmClassesExt.addEntry env {name := declName, params}
    setEnv env
}

end IPMClasses

section IPMBacktrack

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

end IPMBacktrack

section IPMTactic

/-- Result of a tactic registered via the `ipm_tactic_instance` attribute. -/
inductive SynthTacticResult
/-- The tactic produced a term `e` solving the goal. No further tactics or
instances are tried. -/
| success (e : Expr)
/-- The tactic does not apply to this goal. The synthesis continues with the
next tactic, or falls through to regular instance search if no tactics remain. -/
| continue
/-- The tactic determined that the goal is unsolvable. The synthesis aborts
immediately: no further tactics are tried *and* the regular instance search
is skipped. -/
| fail


@[expose]
def SynthTactic : Type := Expr → MetaM SynthTacticResult

def SynthTactic.run (tac : SynthTactic) :
  Expr → MetaM SynthTacticResult := tac


structure SynthTacticEntry where
  tac : SynthTactic
  prio : Nat
  name : Name
instance : BEq SynthTacticEntry where
  beq _ _ := false
instance : Inhabited SynthTacticEntry where
  default := ⟨fun _ _ => return .fail, 0, default⟩
instance : ToMessageData SynthTacticEntry where
  toMessageData e := m!"{e.name}:{e.prio}"

structure SynthTacticEntrySerialized where
  prio : Nat
  name : Name
deriving Repr
instance : BEq SynthTacticEntrySerialized where
  beq _ _ := false
instance : Inhabited SynthTacticEntrySerialized where
  default := ⟨0, default⟩

def SynthTacticEntry.serialize (e : SynthTacticEntry) : SynthTacticEntrySerialized := { prio := e.prio, name := e.name }

unsafe def SynthTacticEntrySerialized.deserialize (e : SynthTacticEntrySerialized) (compile : Bool) : CoreM SynthTacticEntry := do
  let mut name := e.name
  let ty := (← getConstInfo e.name).type
  if ty != .const ``SynthTactic [] then
    throwError "The tactic should have type SynthTactic."
  if compile then
    let d ← getConstInfoDefn e.name
    compileDecl (.defnDecl d)
  let tac ← evalConst SynthTactic name
  return {tac, prio := e.prio, name := e.name}


/-- Environment extension for synth tactics -/
unsafe initialize synthTacticExt :
    ScopedEnvExtension (SynthTacticEntrySerialized × Array DiscrTree.Key) (SynthTacticEntry × Array DiscrTree.Key) (DiscrTree SynthTacticEntry) ←
  registerScopedEnvExtension {
    mkInitial := return {}
    addEntry := fun dt (n, ks) => dt.insertKeyValue ks n
    ofOLeanEntry := fun _ (n, ks) => ImportM.runCoreM do return (← n.deserialize (compile:=false), ks)
    toOLeanEntry := fun (n, ks) => (n.serialize, ks)
  }


private def default_prio : Nat := (eval_prio default)

syntax (name := ipm_tactic_instance) "ipm_tactic_instance" (":" prio)? (ppSpace term),* : attr

unsafe initialize registerBuiltinAttribute {
  name := `ipm_tactic_instance
  descr := "tactic instance used by the proof mode instance synthesis"
  -- we ignore TC failures for BI, they should just create metavariables
  add := fun decl stx kind => MetaM.run' do Elab.Term.TermElabM.run' (ctx := {ignoreTCFailures := true}) do
    let prio := if stx[1][1].isMissing then some default_prio else stx[1][1].isNatLit?
    let .some prio := prio | throwError "unknown priority: {stx[1][1]}"

    let pats ← stx[2].getSepArgs.mapM λ stx => do
      let stx ← `(iprop($(TSyntax.mk stx)))
      Term.elabTerm stx none

    let tac ← (SynthTacticEntrySerialized.mk prio decl).deserialize (compile:=true)
    for pat in pats do
      let key ← DiscrTree.mkPath pat
      synthTacticExt.add (tac, key) kind
}

end IPMTactic

initialize
  registerTraceClass `Meta.synthInstance.ipmParamKinds (inherited := true)
