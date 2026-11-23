/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.ProofMode.Lib

/-! # Visibility of generated declarations

No `public section`: declarations are private unless marked `public`, and the declarations that the
fixpoint commands generate must follow `name`. -/

open Iris BI OFE

namespace IrisTest.FixpointVisibility

public abbrev P := IProp BundledGFunctors.default

public iguarded pubGuarded (n : Nat) : P := iprop(▷ pubGuarded (n + 1))
contractive_by
  intros k a b h x; unfold pubGuarded.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

public ifix pubFix (n : Nat) : P := iprop(▷ pubFix (n + 1))

-- `expose` applies only when declaring: it stays on the definition.
@[expose] public ifix exposedFix (n : Nat) : P := iprop(▷ exposedFix (n + 1))

iguarded privGuarded (n : Nat) : P := iprop(▷ privGuarded (n + 1))
contractive_by
  intros k a b h x; unfold privGuarded.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

run_cmd Lean.Elab.Command.liftTermElabM do
  let check (isPublic : Bool) (name : Lean.Name) (suffixes : List Lean.Name) := do
    for s in suffixes do
      let n := `IrisTest.FixpointVisibility ++ name ++ s
      let env ← Lean.getEnv
      let n := if isPublic then n else Lean.mkPrivateName env n
      unless env.contains n do
        throwError "{name ++ s} is not {if isPublic then "public" else "private"}"
  check true `pubGuarded [.anonymous, `pre, `approx, `unfold, `eq_fixpoint, `persistent]
  check true `pubFix [.anonymous, `pre, `unfold, `pre_mono, `iter]
  check true `exposedFix [.anonymous, `unfold]
  check false `privGuarded [.anonymous, `pre, `approx, `unfold, `eq_fixpoint, `persistent]

end IrisTest.FixpointVisibility
