/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.BI.Lib.FixpointBanach
public import Iris.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI OFE

namespace IrisTest.FixpointGuarded
local notation "PROP" => IProp BundledGFunctors.default

/--
error: iguarded: no default tactic proves contractiveness. Provide a proof with `contractive_by`, or extend `iguarded_contractive_default` with `macro_rules`.
-/
#guard_msgs in
iguarded noContr (n : Nat) : PROP := noContr n

/--
error: iguarded: the type of `notCOFE`, `Nat → Nat`, must be a COFE with a default point, but there is no `IsCOFE` instance
-/
#guard_msgs in
iguarded notCOFE (n : Nat) : Nat := notCOFE n
contractive_by sorry

-- A negative occurrence: guarded fixpoints need contractiveness, not monotonicity.
iguarded flip (b : Bool) : PROP := iprop(▷ flip (!b) -∗ False)
contractive_by
  intros n Φ Ψ h b
  unfold flip.pre
  exact wand_ne.ne (Contractive.distLater_dist (fun m hm => h m hm (!b))) .rfl

example (b : Bool) : flip b = iprop(▷ flip (!b) -∗ False) := flip.unfold b
example (b : Bool) : flip b = fixpoint flip.pre b := flip.eq_fixpoint b

-- A default tactic, extended for this section, and turned off.
section
local macro_rules
  | `(tactic| iguarded_contractive_default) =>
    `(tactic| (intro k Φ Ψ h x; exact Contractive.distLater_dist fun m hm => h m hm _))

iguarded byDefault (n : Nat) : PROP := iprop(▷ byDefault (n + 1))

set_option iris.fixpoint.contractiveDefault false in
/--
error: iguarded: the default tactic for contractiveness is off. Provide a proof with `contractive_by`, or turn `iris.fixpoint.contractiveDefault` back on.
-/
#guard_msgs in
iguarded turnedOff (n : Nat) : PROP := iprop(▷ turnedOff (n + 1))
end

/-! ## The laws of `FixpointBanach` -/

iguarded g0 : PROP := iprop(▷ g0)
contractive_by intros k x y h; unfold g0.pre; exact Contractive.distLater_dist h

example : Persistent g0 := g0.persistent fun Φ _ => by unfold g0.pre; infer_instance

iguarded g2 (b : Bool) (n : Nat) : PROP := iprop(▷ g2 (!b) (n + 1))
contractive_by
  intros k Φ Ψ h b n; unfold g2.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (b : Bool) (n : Nat) : Persistent (g2 b n) :=
  g2.persistent (fun Φ _ b n => by unfold g2.pre; infer_instance) b n

iguarded dependent (n : Nat) (i : Fin n) : PROP := iprop(▷ dependent n i)
contractive_by
  intros k Φ Ψ h n i; unfold dependent.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

-- A function type: the laws quantify over its parameters too.
iguarded gf (n : Nat) : Bool → PROP := fun b => iprop(▷ gf (n + 1) b)
contractive_by
  intros k Φ Ψ h n b; unfold gf.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (b : Bool) : Persistent (gf n b) :=
  gf.persistent (fun Φ _ n b => by unfold gf.pre; infer_instance) n b

/-! ## Inputs -/

protected iguarded prot (n : Nat) : PROP := iprop(▷ prot (n + 1))
contractive_by
  intros k Φ Ψ h n; unfold FixpointGuarded.prot.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : FixpointGuarded.prot n = FixpointGuarded.prot.pre FixpointGuarded.prot n :=
  FixpointGuarded.prot.unfold n

noncomputable def ncProp : PROP := Classical.choice ⟨iprop(emp)⟩

noncomputable iguarded nc (n : Nat) : PROP := iprop(▷ (nc (n + 1) ∗ ncProp))
contractive_by
  intros k a b h x; unfold nc.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne (h m hm _) .rfl)

-- An instance parameter, auto-bound implicits, and a section instance of the class that
-- `eq_fixpoint` takes.
iguarded withInst [Inhabited Nat] (n : Nat) : PROP := iprop(▷ withInst (n + 1))
contractive_by
  intros k Φ Ψ h i n; unfold withInst.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example [Inhabited Nat] (n : Nat) : withInst n = fixpoint withInst.pre n := withInst.eq_fixpoint n

iguarded autoBound [OFE α] (x : α) : PROP := iprop(▷ autoBound x)
contractive_by
  intros k Φ Ψ h i x; unfold autoBound.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

section
variable {α : Type} [Inhabited α]

iguarded sectionInh (a : α) : PROP := iprop(▷ (⌜a = default⌝ ∗ sectionInh a))
contractive_by
  intros k Φ Ψ h a; unfold sectionInh.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne .rfl (h m hm _))

example (a : α) : Persistent (sectionInh a) :=
  sectionInh.persistent (fun Φ _ a => by unfold sectionInh.pre; infer_instance) a
end

/-- error: iguarded: name every argument -/
#guard_msgs in
iguarded hole (_ : Nat) (n : Nat) : PROP := hole 0 n

/-- error: iguarded: arguments cannot have default values -/
#guard_msgs in
iguarded withDefault (n : Nat := 3) : PROP := withDefault n

/-- error: iguarded: the name must be atomic; open a namespace instead -/
#guard_msgs in
iguarded Foo.bar (n : Nat) : PROP := Foo.bar n

section
variable (m : Nat)

/--
error: iguarded: explicit section variables, such as `m`, are not supported; make them implicit, or arguments
-/
#guard_msgs in
iguarded viaProj (n : Nat) : PROP := iprop(▷ viaProj m.succ)

-- Shadowed by a parameter, it is not used.
iguarded shadowed (m : Nat) : PROP := iprop(▷ shadowed (m + 1))
contractive_by
  intros k Φ Ψ h m; unfold shadowed.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
end

-- No `sorry` or unexpected axioms.
run_cmd do
  for decl in #[`flip, `byDefault, `g0, `g2, `dependent, `gf, `withInst, `autoBound] do
    for suffix in #[Lean.Name.anonymous, `pre, `pre ++ `contractive, `approx, `unfold,
        `eq_fixpoint, `persistent] do
      let name := `IrisTest.FixpointGuarded ++ decl ++ suffix
      unless (← Lean.getEnv).contains name do continue
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

end IrisTest.FixpointGuarded
