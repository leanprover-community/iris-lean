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

-- A non-monotone body is rejected by `imono` with a clear message.
/-- error: imono: not monotone, or not covered by an @[imono] rule -/
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

#check gsh.persistent

-- A function type: Lean cannot see that it is inhabited, so `name` stays noncomputable, and the
-- laws quantify over its arguments too.
iguarded gf (n : Nat) : Bool → PROP := gf n
contractive_by
  intros k a b h x; unfold gf.pre; sorry

example (n : Nat) (b : Bool) : Persistent (gf n b) :=
  gf.persistent (fun Φ _ n b => by unfold gf.pre; infer_instance) n b

/-- error: iguarded: provide a contractive_by proof -/
#guard_msgs in
iguarded noContr (n : Nat) : PROP := noContr n
end

-- Generated theorems take only the section instances they use.
section
variable [BI PROP] [BIFUpdate PROP]

iguarded gi (n : Nat) : PROP := iprop(gi n)
contractive_by sorry
end

section
variable [BI PROP]
example (n : Nat) : gi (PROP := PROP) n = gi.pre gi n := gi.unfold n
example [Inhabited (Nat → PROP)] (n : Nat) : gi (PROP := PROP) n = fixpoint gi.pre n :=
  gi.eq_fixpoint n
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
