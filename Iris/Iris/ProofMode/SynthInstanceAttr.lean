/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

public import Qq
public import Iris.BI.Notation

public meta section
open Lean Elab Tactic Meta Qq

section IPMClasses
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
