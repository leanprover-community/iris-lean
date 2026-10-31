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

iinductive cycle nonexp_by
  intros Φ hΦ
  constructor
  intros n x y h
  cases x
  cases y
  exact .rfl
  : Unit → IProp BundledGFunctors.default where
  | left : cycle () -∗ cycle ()
  | right : cycle () -∗ cycle ()

end IrisTest.FixpointCore
