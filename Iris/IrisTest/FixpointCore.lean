/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Lib.FixpointBanach
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
monotone_by imono

ifix rotated (setting : Bool) (x y z : α) : PROP := rotated setting y z x
monotone_by imono

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
monotone_by imono

#guard_msgs (drop info) in
iinductive? tracedCycle : Unit → IProp BundledGFunctors.default where
  | left : tracedCycle () -∗ tracedCycle ()
  | right : tracedCycle () -∗ tracedCycle ()
monotone_by imono

end IrisTest.FixpointCore

-- Root-namespace definitions no longer shadow their generated pre-definitions.
ifix rootShadow (x : Unit) : IProp BundledGFunctors.default := rootShadow x

namespace IrisTest.FixpointCore

-- `imono` needs no OFE instance on the arguments.
example [BI PROP] : BIMono (PROP := PROP) (fun Φ : α × α → PROP => Φ) := by imono

-- Parser failures and runtime panics are checked in a separate Lean process.
private meta def expectLeanOutput (body expected : String) (exitCode : UInt32) :
    Lean.Elab.Command.CommandElabM Unit := do
  let prelude := "module
public import Iris.Instances.IProp
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.Lib.FixpointBanach
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

-- A recursive call may have a type-annotated head.
iguarded annotated (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ (annotated : Unit → IProp BundledGFunctors.default) x)
contractive_by
  intros n Φ Ψ h x
  unfold annotated.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- Recursive calls may use named arguments.
iguarded named (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ named (x := x))
contractive_by
  intros n Φ Ψ h x
  unfold named.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- Recursive parameter types may depend on each other.
iguarded dependent (n : Nat) (i : Fin n) : IProp BundledGFunctors.default :=
  iprop(▷ dependent n i)
contractive_by
  intros n Φ Ψ h i j
  unfold dependent.pre
  exact Contractive.distLater_dist (fun m hm => h m hm i j)

-- A negative occurrence: guarded fixpoints need contractiveness, not monotonicity.
iguarded flip (b : Bool) : IProp BundledGFunctors.default :=
  iprop(▷ flip (!b) -∗ False)
contractive_by
  intros n Φ Ψ h b
  unfold flip.pre
  exact wand_ne.ne (Contractive.distLater_dist (fun m hm => h m hm (!b))) .rfl

example (b : Bool) : flip b = iprop(▷ flip (!b) -∗ False) := flip.unfold b

-- A guarded fixpoint is the Banach fixpoint, so the `FixpointBanach` lemmas apply.
example (b : Bool) : flip b = fixpoint flip.pre b := flip.eq_fixpoint b
example (x : Unit) : Persistent (annotated x) := by
  rw [annotated.eq_fixpoint]
  exact fixpoint_persistent _ (fun _ _ _ => by unfold annotated.pre; infer_instance) x

-- Guarded fixpoints use no `sorry` and no extra axioms.
run_cmd do
  for decl in #[`annotated, `named, `dependent, `flip] do
    for suffix in #[Lean.Name.anonymous, `pre, `pre ++ `contractive, `approx, `unfold] do
      let name := `IrisTest.FixpointCore ++ decl ++ suffix
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

-- Explicit instance binders are retained by the pre-definition.
ifix explicitInstance [BI PROP] (x : Unit) : PROP :=
  iprop(explicitInstance x ∗ explicitInstance x)

-- Explicit section parameters are retained in generated applications.
section
variable (PROP : Type) [bi : BI PROP]

ifix sectionParameter (x : Unit) : PROP := sectionParameter x
end

-- `ifix` accepts declaration modifiers such as `private` and docstrings.
/-- A private fixpoint. -/
private ifix hidden (x : Unit) : IProp BundledGFunctors.default := hidden x

example (x : Unit) : hidden x = hidden.pre x (hidden x) := hidden.unfold x

-- An empty predicate does not require a recursive occurrence.
iinductive empty : Unit → IProp BundledGFunctors.default where

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
