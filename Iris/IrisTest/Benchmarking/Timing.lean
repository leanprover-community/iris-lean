module

public import Lean
import Iris.Init

namespace IrisTest.Benchmarking
open Lean Elab Term Tactic Meta Command

public meta section

private def msOf (ns : Nat) : Float :=
  Float.ofNat ns / 1000000.0

private def fmt3 (x : Float) : String :=
  let scaled := (x * 1000.0).round.toUInt64.toNat
  let whole  := scaled / 1000
  let frac   := scaled % 1000
  s!"{whole}.{(toString frac)}"

private def median (xs : Array Nat) : Nat :=
  if xs.isEmpty then 0 else
    let s := xs.qsort (· < ·)
    s[s.size / 2]!

def emitBench (label : String) (rep ns kHeartbeats : Nat) : CoreM Unit :=
  logInfo s!"BENCH|{label}|{rep}|{ns}|{kHeartbeats}"

syntax (name := itimeNLabelled) "itimeN " num ppSpace str ppSpace tacticSeq : tactic

syntax (name := itimeLabelled) "itime " str ppSpace tacticSeq : tactic

@[tactic itimeNLabelled] def evalItimeNLabelled : Tactic := fun stx => do
  let `(tactic| itimeN $k:num $lbl:str $tac:tacticSeq) := stx | throwUnsupportedSyntax
  let reps := max 1 k.getNat
  let label := lbl.getString
  let saved ← saveState
  let mut recs : Array (Nat × Nat × Nat) := #[]
  for rep in [0:reps] do
    if rep != 0 then saved.restore (restoreInfo := true)
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    evalTactic tac
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    recs := recs.push (rep, t1 - t0, (h1 - h0) / 1000)
  for (rep, ns, hb) in recs do
    emitBench label rep ns hb

macro_rules
  | `(tactic| itime $lbl:str $tac:tacticSeq) => `(tactic| itimeN 1 $lbl $tac)

syntax (name := ikernelTime) "ikernel_time " num ppSpace str ppSpace tacticSeq : tactic

@[tactic ikernelTime] def evalIKernelTime : Tactic := fun stx => do
  let `(tactic| ikernel_time $k:num $lbl:str $tac:tacticSeq) := stx | throwUnsupportedSyntax
  let goal ← getMainGoal
  evalTactic tac
  let (type, value) ← goal.withContext do
    let fvars := (← getLCtx).decls.foldl (init := #[]) fun acc d? =>
      match d? with
      | some d => if d.isImplementationDetail then acc else acc.push d.toExpr
      | none   => acc
    let type ← mkForallFVars fvars (← instantiateMVars (← goal.getType))
    let value ← mkLambdaFVars fvars (← instantiateMVars (mkMVar goal))
    pure (type, value)
  if value.hasExprMVar || value.hasSorry then
    throwError "ikernel_time: the proof term is not closed"
  let levelParams :=
    (collectLevelParams (collectLevelParams {} type) value).params.toList
  let base := (← getDeclName?).getD `_anon
  let mut recs : Array (Nat × Nat) := #[]
  for rep in [0:max 1 k.getNat] do
    let decl := Declaration.thmDecl
      { name := base ++ Name.mkSimple s!"_kchk{rep}", levelParams, type, value }
    let t0 ← IO.monoNanosNow
    withOptions (·.setBool `debug.skipKernelTC false) <| addDecl decl
    let t1 ← IO.monoNanosNow
    recs := recs.push (rep, t1 - t0)
  for (rep, ns) in recs do
    emitBench lbl.getString rep ns 0

end

end Benchmarking

end IrisTest
