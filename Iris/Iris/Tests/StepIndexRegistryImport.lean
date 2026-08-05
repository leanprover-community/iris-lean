/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

import Iris.Tests.StepIndexRegistry
public meta import Iris.Tests.StepIndexRegistry

@[expose] public section

namespace Iris.Tests

-- Test that a `local` index does not leak into an importing module

/-- info: [anonymous] -/
#guard_msgs in
#stepindex?

-- Test that an importing module inherits no index, so `infer_stepindex` fails

/-- error: infer_stepindex: no step index in scope; declare one with `local stepindex T` -/
#guard_msgs in
example : Type := by infer_stepindex

section
open ScopedTest

-- Test that a `scoped` index activates across modules when its namespace is opened

/-- info: Unit -/
#guard_msgs in
#stepindex?

def importedBundle : Bundle Nat := ⟨fun _ => 0⟩

-- Test that the auto_param uses the index of the opened scope on an imported structure

/-- info: Iris.Tests.importedBundle : Bundle Nat Unit -/
#guard_msgs in
#check importedBundle

end

-- Test that closing the scope restores the absence of an index

/-- info: [anonymous] -/
#guard_msgs in
#stepindex?

section
local stepindex Nat

def reexportedBundle : Bundle Nat := ⟨fun n => n⟩

-- Test that an importing module can declare its own index

/-- info: Iris.Tests.reexportedBundle : Bundle Nat Nat -/
#guard_msgs in
#check reexportedBundle

-- Test that a polymorphic declaration from the imported module specializes here

/-- info: mkBundle fun x => 0 : Bundle Nat Nat -/
#guard_msgs in
#check mkBundle (fun _ : Nat => (0 : Nat))

end

end Iris.Tests
