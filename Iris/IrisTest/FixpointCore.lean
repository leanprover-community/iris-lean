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
nonexp_by intros; assumption

icofix greatest (x : α) : PROP := greatest x
nonexp_by intros; assumption

example (x : α) : least (PROP := PROP) x = least.pre least x := least.unfold x
example (x : α) : greatest (PROP := PROP) x = greatest.pre greatest x := greatest.unfold x
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
nonexp_by
  intros Φ hΦ
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl

#guard_msgs (drop info) in
iinductive? tracedCycle : Unit → IProp BundledGFunctors.default where
  | left : tracedCycle () -∗ tracedCycle ()
  | right : tracedCycle () -∗ tracedCycle ()
monotone_by monotone
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl

end IrisTest.FixpointCore

-- 01. The recursive binder shadows the pre-definition at the root namespace.
/-- Invalid field `pre` -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
ifix rootShadow (x : Unit) : IProp BundledGFunctors.default := rootShadow x
nonexp_by intros; assumption

namespace IrisTest.FixpointCore

-- 08. The product OFE instance is left as a goal.
/-- ⊢ OFE (α × α) -/
#guard_msgs (whitespace := lax, substring := true) in
example [BI PROP] [OFE α] :
    MonoInstances.MonotonePred (fun Φ : α × α → PROP => Φ) where
  monotone := by monotone

-- Runtime panics bypass the message log, including #guard_panic.
private meta def expectPanic (body expected : String) (exitCode : UInt32) :
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

-- 09. Zero recursive arguments index empty argument and type arrays.
run_cmd (expectPanic "
ifix zero : IProp BundledGFunctors.default := zero
nonexp_by intros; assumption
" "Error: index out of bounds" 1)

-- 10. An annotated application head is counted at arity zero.
/-- annotated has type -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
iguarded annotated (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ (annotated : Unit → IProp BundledGFunctors.default) x)
contractive_by
  intros n Φ Ψ h x
  unfold annotated.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- 11. The recursive function type discards parameter names.
/-- Invalid argument name `x` -/
#guard_msgs (error, drop warning, substring := true) in
iguarded named (x : Unit) : IProp BundledGFunctors.default :=
  iprop(▷ named (x := x))
contractive_by
  intros n Φ Ψ h x
  unfold named.pre
  exact Contractive.distLater_dist (fun m hm => h m hm x)

-- 12. Dependent recursive parameters become independent arrows.
/-- Application type mismatch: The argument i -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
iguarded dependent (n : Nat) (i : Fin n) : IProp BundledGFunctors.default :=
  iprop(▷ dependent n i)
contractive_by
  intros n Φ Ψ h i j
  unfold dependent.pre
  exact Contractive.distLater_dist (fun m hm => h m hm i j)

-- 13. Instance binders are omitted from the pre-definition.
/-- failed to synthesize instance of type class BIBase PROP -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
ifix explicitInstance [BI PROP] (x : Unit) : PROP :=
  iprop(explicitInstance x ∗ explicitInstance x)
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  exact sep_ne.ne (NonExpansive.ne h) (NonExpansive.ne h)

-- 14. Explicit section parameters are omitted from generated applications.
section
variable (PROP : Type) [bi : BI PROP]

/-- pre sectionParameter -/
#guard_msgs (error, drop warning, whitespace := lax, substring := true) in
ifix sectionParameter (x : Unit) : PROP := sectionParameter x
nonexp_by intros; assumption
end

-- 15. The unfolding theorem cannot resolve a private definition.
/-- Unknown identifier `hidden` -/
#guard_msgs (error, drop warning, substring := true) in
private ifix hidden (x : Unit) : IProp BundledGFunctors.default := hidden x
nonexp_by intros; assumption

-- 16. An empty predicate is rejected for having no recursive occurrence.
/-- monotone fixpoint def: no recursive occurrence of 'empty' found in the body -/
#guard_msgs (substring := true) in
iinductive empty : Unit → IProp BundledGFunctors.default where
nonexp_by
  intros Φ _
  exact ⟨fun {_ _ _} _ => .rfl⟩

-- 17. One constructor reads the last element of an empty selector list.
run_cmd (expectPanic "
iinductive single : Unit → IProp BundledGFunctors.default where
  | step : single () -∗ single ()
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl
" "PANIC at List.getLast!" 0)

-- 18. Proposition-valued constructor parameters are omitted from existential binders.
/-- Unknown identifier `P` -/
#guard_msgs (error, drop warning, substring := true) in
iinductive resource : Unit → IProp BundledGFunctors.default where
  | a (P : IProp BundledGFunctors.default) : P -∗ resource () -∗ resource ()
  | b : resource () -∗ resource ()
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl

-- 19. A parenthesized recursive premise is not counted when selecting the conclusion.
/-- ileft: nested () is not a disjunction -/
#guard_msgs (substring := true) in
iinductive nested : Unit → IProp BundledGFunctors.default where
  | a : (nested ()) -∗ nested ()
  | b : nested () -∗ nested ()
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl

-- 20. An ordinary implication premise is not introduced before rewriting.
/-- True → ⊢ purePremise () -∗ purePremise () -/
#guard_msgs (substring := true) in
iinductive purePremise : Unit → IProp BundledGFunctors.default where
  | a : True → purePremise () -∗ purePremise ()
  | b : purePremise () -∗ purePremise ()
nonexp_by
  intros Φ _
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl

end IrisTest.FixpointCore
