/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Lib

@[expose] public section

open Iris BI OFE

namespace IrisTest.FixpointCore

run_cmd do
  let env ← Lean.getEnv
  for name in [`Iris.nonexpMain, `Iris.contractiveMain, `Iris.Std.nonexpExt] do
    if env.contains name then
      throwError "unexpected automation dependency: {name}"

section
variable [bi : BI PROP] [OFE α]

ifix least (x : α) : PROP := least x

icofix greatest (x : α) : PROP := greatest x

example (x : α) : least (PROP := PROP) x = least.pre x (least x) := least.unfold x
example (x : α) : greatest (PROP := PROP) x = greatest.pre x (greatest x) := greatest.unfold x

-- `.pre` preserves argument order.
icofix swapped (x y : α) : PROP := swapped y x
monotone_by monotone

ifix rotated (setting : Bool) (x y z : α) : PROP := rotated setting y z x
monotone_by monotone

example (Φ : α → α → PROP) (x y : α) : swapped.pre Φ x y = Φ y x := rfl

example (setting : Bool) (Φ : α → α → α → PROP) (x y z : α) :
    rotated.pre setting Φ x y z = Φ y z x := rfl

example (x y : α) :
    swapped (PROP := PROP) x y = swapped.pre swapped x y := swapped.unfold x y

example (setting : Bool) (x y z : α) :
    rotated (PROP := PROP) setting x y z = rotated.pre setting (rotated setting) x y z :=
  rotated.unfold setting x y z
end

iguarded guarded : IProp BundledGFunctors.default := iprop(▷ guarded)
contractive_by
  intros n x y h
  unfold guarded.pre
  exact OFE.Contractive.distLater_dist h

iinductive cycle : Unit → IProp BundledGFunctors.default where
  | left : cycle () -∗ cycle ()
  | right : cycle () -∗ cycle ()
monotone_by monotone

#guard_msgs (drop info) in
iinductive? tracedCycle : Unit → IProp BundledGFunctors.default where
  | left : tracedCycle () -∗ tracedCycle ()
  | right : tracedCycle () -∗ tracedCycle ()
monotone_by monotone

end IrisTest.FixpointCore

-- Root-namespace definitions no longer shadow their generated pre-definitions.
ifix rootShadow (x : Unit) : IProp BundledGFunctors.default := rootShadow x

namespace IrisTest.FixpointCore

-- `monotone` needs no OFE instance on the arguments.
example [BI PROP] : MonoFn (fun Φ : α × α → PROP => Φ) := by monotone

-- Parser failures and runtime panics are checked in a separate Lean process.
private meta def expectLeanOutput (body expected : String) (exitCode : UInt32) :
    Lean.Elab.Command.CommandElabM Unit := do
  let prelude := "module
public import Iris.Instances.IProp
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Lib
@[expose] public section
open Iris BI OFE
namespace IrisTest.AdversarialFixpointPanic
"
  let output ← IO.Process.output {
    cmd := (← IO.appPath).toString
    args := #["--stdin"]
  } (some (prelude ++ body ++ "\nend IrisTest.AdversarialFixpointPanic\n"))
  unless output.exitCode == exitCode && (output.stdout ++ output.stderr).contains expected do
    throwError "expected exit {exitCode} and {expected}; got exit {output.exitCode}\n\
      {output.stdout}{output.stderr}"

-- Zero recursive arguments use Unit instead of indexing an empty argument array.
ifix zero : IProp BundledGFunctors.default := zero

example : zero = zero.pre zero := zero.unfold

-- ERROR: `iguarded` infers arity zero for a recursive call with a type-annotated head.
/-- annotated has type -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
iguarded annotated (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ (annotated : Unit → IProp BundledGFunctors.default) x)
contractive_by
  intros n Φ Ψ h x
  unfold annotated.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- Recursive calls may use named arguments. (Passes under the `iguarded` stub; recheck with the
-- real implementation.)
iguarded named (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ named (x := x))
contractive_by
  intros n Φ Ψ h x
  unfold named.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- Recursive parameter types may depend on each other. (Passes under the `iguarded` stub; recheck
-- with the real implementation.)
iguarded dependent (n : Nat) (i : Fin n) : IProp BundledGFunctors.default :=
  iprop(▷ dependent n i)
contractive_by
  intros n Φ Ψ h i j
  unfold dependent.pre
  exact Contractive.distLater_dist (fun m hm => h m hm i j)

-- Explicit instance binders are retained by the pre-definition.
ifix explicitInstance [BI PROP] (x : Unit) : PROP :=
  iprop(explicitInstance x ∗ explicitInstance x)

-- Explicit section parameters are retained in generated applications.
section
variable (PROP : Type) [bi : BI PROP]

ifix sectionParameter (x : Unit) : PROP := sectionParameter x
end

-- ERROR: `ifix` rejects declaration modifiers such as `private`.
run_cmd (expectLeanOutput "
private ifix hidden (x : Unit) : IProp BundledGFunctors.default := hidden x
" "unexpected token 'ifix'" 1)

-- An empty predicate does not require a recursive occurrence.
iinductive empty : Unit → IProp BundledGFunctors.default where
monotone_by monotone

example (x : Unit) : empty x = iprop(False) := by
  simpa only [empty.pre] using empty.unfold x

-- ERROR: `iinductive` panics when updating the empty selector list for a single constructor.
run_cmd (expectLeanOutput "
iinductive single : Unit → IProp BundledGFunctors.default where
  | step : single () -∗ single ()
" "PANIC at List.getLast!" 0)

-- ERROR: `iinductive` omits Iris proposition parameters from existential binders.
/-- Unknown identifier `P` -/
#guard_msgs (error, drop warning, substring := true) in
iinductive resource : Unit → IProp BundledGFunctors.default where
  | a (P : IProp BundledGFunctors.default) : P -∗ resource () -∗ resource ()
  | b : resource () -∗ resource ()

-- ERROR: `iinductive` misses parenthesized recursive premises and unfolds the wrong occurrence.
/-- ileft: nested () is not a disjunction -/
#guard_msgs (substring := true) in
iinductive nested : Unit → IProp BundledGFunctors.default where
  | a : (nested ()) -∗ nested ()
  | b : nested () -∗ nested ()

-- ERROR: `iinductive` does not introduce ordinary implication premises before unfolding.
/-- True → ⊢ purePremise () -∗ purePremise () -/
#guard_msgs (substring := true) in
iinductive purePremise : Unit → IProp BundledGFunctors.default where
  | a : True → purePremise () -∗ purePremise ()
  | b : purePremise () -∗ purePremise ()

end IrisTest.FixpointCore
