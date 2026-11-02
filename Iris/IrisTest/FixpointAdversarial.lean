/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI.Lib.FixpointBanach
public import Iris.ProofMode.Lib

@[expose] public section

open Iris BI OFE

namespace IrisTest.FixpointAdversarial

/-! ## `monotone_by` runs once -/

section
variable [BI PROP]

elab "logged_imono" : tactic => do
  Lean.logInfo "monotone_by ran"
  Lean.Elab.Tactic.evalTactic (← `(tactic| imono))

/-- info: monotone_by ran -/
#guard_msgs in
ifix once1 (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ once1 (n + 1))
monotone_by logged_imono

/-- info: monotone_by ran -/
#guard_msgs in
icofix once2 (n : Nat) : PROP := iprop(▷ once2 n)
monotone_by logged_imono

-- A non-monotone body: `imono` fails, so a proof is required.
/--
error: ifix: `ifix_monotone_default` did not prove monotonicity. Provide a proof with `monotone_by`, or extend `ifix_monotone_default` with `macro_rules`.
-/
#guard_msgs (error, substring := true) in
ifix bad (n : Nat) : PROP := iprop(bad n -∗ False)

-- An argument named like the definition.
ifix self (self : Nat) : PROP := iprop(⌜self = 0⌝)

example (n : Nat) : self (PROP := PROP) n = iprop(⌜n = 0⌝) := self.unfold n
end

/-! ## `iguarded` -/

section
local notation "PROP" => IProp BundledGFunctors.default

-- The `FixpointBanach` laws, with two arguments, none, and argument names that clash.
iguarded g2 (b : Bool) (n : Nat) : PROP := iprop(▷ g2 (!b) (n + 1))
contractive_by
  intros k Φ Ψ h b n
  unfold g2.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (b : Bool) (n : Nat) : Persistent (g2 b n) := by
  apply g2.persistent
  intro Φ _ b n; unfold g2.pre; infer_instance

iguarded g0 : PROP := iprop(▷ g0)
contractive_by
  intros k x y h; unfold g0.pre; exact Contractive.distLater_dist h

example : Persistent g0 :=
  g0.persistent fun Φ _ => by unfold g0.pre; infer_instance

iguarded gsh (Φ : Nat) (gsh' : Nat) : PROP := iprop(▷ gsh Φ gsh')
contractive_by
  intros k a b h x y; unfold gsh.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (Φ gsh' : Nat) : Persistent (gsh Φ gsh') :=
  gsh.persistent (fun Ψ _ a b => by unfold gsh.pre; infer_instance) Φ gsh'

-- A function type: the laws quantify over its arguments too.
iguarded gf (n : Nat) : Bool → PROP := fun b => iprop(▷ gf (n + 1) b)
contractive_by
  intros k a b h x y; unfold gf.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (b : Bool) : Persistent (gf n b) :=
  gf.persistent (fun Φ _ n b => by unfold gf.pre; infer_instance) n b

/--
error: iguarded: no default tactic proves contractiveness. Provide a proof with `contractive_by`, or extend `iguarded_contractive_default` with `macro_rules`.
-/
#guard_msgs in
iguarded noContr (n : Nat) : PROP := noContr n

-- A default contractiveness tactic, for this section.
section
local macro_rules
  | `(tactic| iguarded_contractive_default) =>
    `(tactic| (intro k Φ Ψ h x; exact Contractive.distLater_dist fun m hm => h m hm _))

iguarded byDefault (n : Nat) : PROP := iprop(▷ byDefault (n + 1))

-- It can be turned off.
set_option iris.fixpoint.contractiveDefault false in
/--
error: iguarded: the default tactic for contractiveness is off. Provide a proof with `contractive_by`, or turn `iris.fixpoint.contractiveDefault` back on.
-/
#guard_msgs in
iguarded turnedOff (n : Nat) : PROP := iprop(▷ turnedOff (n + 1))
end
end

/-! ## Default tactics -/

section
variable [BI PROP]

-- A failing rule falls back to the older ones, here `imono`.
section
local macro_rules | `(tactic| ifix_monotone_default) => `(tactic| fail "not this one")

ifix fallback (n : Nat) : PROP := fallback n
end

-- The default can be turned off; an explicit clause still works.
section
set_option iris.fixpoint.monotoneDefault false

/--
error: icofix: the default tactic for monotonicity is off. Provide a proof with `monotone_by`, or turn `iris.fixpoint.monotoneDefault` back on.
-/
#guard_msgs in
icofix noDefault (n : Nat) : PROP := noDefault n

ifix explicitClause (n : Nat) : PROP := explicitClause n
monotone_by imono
end
end

/-! ## `iguarded` inputs that need care -/

namespace Inputs
local notation "PROP" => IProp BundledGFunctors.default

-- `protected`: the generated statements name it in full.
protected iguarded prot (n : Nat) : PROP := iprop(▷ prot (n + 1))
contractive_by
  intros k a b h x; unfold Inputs.prot.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Inputs.prot n = Inputs.prot.pre Inputs.prot n := Inputs.prot.unfold n

-- `noncomputable`, for a body that uses a noncomputable constant.
noncomputable def ncProp : PROP := Classical.choice ⟨iprop(emp)⟩

noncomputable iguarded nc (n : Nat) : PROP := iprop(▷ (nc (n + 1) ∗ ncProp))
contractive_by
  intros k a b h x; unfold nc.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne (h m hm _) .rfl)

-- An instance argument, and a section instance of the class `eq_fixpoint` also takes.
iguarded withInst [Inhabited Nat] (n : Nat) : PROP := iprop(▷ withInst (n + 1))
contractive_by
  intros k a b h i x; unfold withInst.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example [Inhabited Nat] (n : Nat) : withInst n = fixpoint withInst.pre n := withInst.eq_fixpoint n

section
variable {α : Type} [Inhabited α]

iguarded sectionInh (a : α) : PROP := iprop(▷ (⌜a = default⌝ ∗ sectionInh a))
contractive_by
  intros k Φ Ψ h a; unfold sectionInh.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne .rfl (h m hm _))

example (a : α) : Persistent (sectionInh a) :=
  sectionInh.persistent (fun Φ _ a => by unfold sectionInh.pre; infer_instance) a
end

-- Rejected up front.
/-- error: iguarded: name every argument -/
#guard_msgs in
iguarded hole (_ : Nat) (n : Nat) : PROP := hole 0 n
contractive_by sorry

/-- error: iguarded: arguments cannot have default values -/
#guard_msgs in
iguarded withDefault (n : Nat := 3) : PROP := withDefault n
contractive_by sorry

/-- error: iguarded: the name must be atomic; open a namespace instead -/
#guard_msgs in
iguarded Foo.bar (n : Nat) : PROP := Foo.bar n
contractive_by sorry

section
variable (m : Nat)

/--
error: iguarded: explicit section variables, such as `m`, are not supported; make them implicit, or arguments
-/
#guard_msgs in
iguarded sectionVar (n : Nat) : PROP := sectionVar (n + m)
contractive_by sorry
end

-- A misspelled type is bound automatically, as in a `def`: the error shows it.
/--
error: iguarded: the type of `typo`, `Nat → Prpo`, must be a COFE with a default point, but there is no `IsCOFE` instance
-/
#guard_msgs in
iguarded typo (n : Nat) : Prpo := typo n
contractive_by sorry

-- An explicit section variable used through a projection is caught; one shadowed by an argument
-- is not used.
section
variable (m : Nat)

/--
error: iguarded: explicit section variables, such as `m`, are not supported; make them implicit, or arguments
-/
#guard_msgs in
iguarded viaProj (n : Nat) : PROP := iprop(▷ viaProj m.succ)
contractive_by sorry

iguarded shadowed (m : Nat) : PROP := iprop(▷ shadowed (m + 1))
contractive_by
  intros k a b h x; unfold shadowed.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
end

-- `protected ifix`, and a `local` attribute, which must outlive the command's own section.
protected ifix protFix (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ▷ Inputs.protFix (n + 1))

example (n : Nat) : Inputs.protFix n = Inputs.protFix.pre Inputs.protFix n := Inputs.protFix.unfold n

@[local simp] ifix localSimp (n : Nat) : PROP := iprop(⌜n = 0⌝)

example : localSimp 0 = iprop(⌜0 = 0⌝) := by simp

-- A constant `Inputs.Inputs.clash` must not be taken for the new `Inputs.clash`.
set_option linter.iris.dupNamespace false in
def Inputs.clash : Nat := 0
set_option linter.iris.dupNamespace false in
def Inputs.clashG : Nat := 0

ifix clash (n : Nat) : PROP := iprop(▷ clash (n + 1))

example (n : Nat) : clash n = clash.pre clash n := clash.unfold n

iguarded clashG (n : Nat) : PROP := iprop(▷ clashG (n + 1))
contractive_by
  intros k a b h x; unfold clashG.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Persistent (clashG n) :=
  clashG.persistent (fun Φ _ n => by unfold clashG.pre; infer_instance) n

ifix _root_.rootedFix (n : Nat) : PROP := iprop(▷ rootedFix (n + 1))

example (n : Nat) : rootedFix n = rootedFix.pre rootedFix n := rootedFix.unfold n

-- Attributes that apply only when declaring stay on the definition.
@[semireducible] ifix semireducibleFix (n : Nat) : PROP := iprop(▷ semireducibleFix (n + 1))

end Inputs

/-! ## `imono` failures -/

section
variable [BI PROP]

-- Definitions that are not recursive are unfolded as often as they occur.
def later' (X : PROP) : PROP := iprop(▷ X)
def outer (Φ : Nat → PROP) (n : Nat) : PROP := later' (Φ n)
def both (Φ : Nat → PROP) (n : Nat) : PROP := later' (outer Φ n)

example : BIMono (PROP := PROP) both := by imono

-- A failing rule of the default tactic falls back to the older ones, here `imono`.
section
local macro_rules | `(tactic| ifix_monotone_default) => `(tactic| exact nonsense)

ifix fallsBack (n : Nat) : PROP := fallsBack n
end

-- A recursive helper is unfolded once, not forever.
def bigSep (Φ : List Nat → PROP) : List Nat → PROP
  | [] => iprop(emp)
  | _ :: xs => iprop(Φ xs ∗ bigSep Φ xs)

/-- error: imono: no rule for IrisTest.FixpointAdversarial.bigSep -/
#guard_msgs (error, substring := true) in
example : BIMono (fun (Φ : List Nat → PROP) l => bigSep Φ l) := by imono

-- `if` is split, like `match`.
example : BIMono (fun (Φ : Nat → PROP) n => if n = 0 then iprop(emp) else Φ (n - 1)) := by imono

/-- error: imono: expected a monotonicity goal -/
#guard_msgs (error, substring := true) in
example : True := by imono
end

/-! ## `private` and docstrings, in the public scope -/

public section

/-- A private guarded fixpoint. -/
private iguarded gp (n : Nat) : IProp BundledGFunctors.default := iprop(▷ gp n)
contractive_by
  intros k a b h x; unfold gp.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Persistent (gp n) :=
  gp.persistent (fun Φ _ n => by unfold gp.pre; infer_instance) n

end

end IrisTest.FixpointAdversarial
