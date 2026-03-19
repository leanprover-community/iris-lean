/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Yunsong Yang
-/
module

public import Iris.BI
public meta import Iris.ProofMode.SynthInstance

@[expose] public section

namespace Iris.ProofMode
open Iris.BI

/-- The class [MakeAffinely P Q] is used to compute `Q := <affine> P`. -/
class MakeAffinely [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_affinely : <affine> P ⊣⊢ Q
export MakeAffinely (make_affinely)

/-- The class [MakeIntuitionistically P Q] is used to compute `Q := □ P`. -/
class MakeIntuitionistically [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_intuitionistically : □ P ⊣⊢ Q
export MakeIntuitionistically (make_intuitionistically)

/-- The class [MakeAbsorbingly P Q] is used to compute `Q := <absorb> P`. -/
class MakeAbsorbingly [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_absorbingly : <absorb> P ⊣⊢ Q
export MakeAbsorbingly (make_absorbingly)

/-- The class [MakePersistently P Q] is used to compute `Q := <pers> P`. -/
class MakePersistently [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_persistently : <pers> P ⊣⊢ Q
export MakePersistently (make_persistently)

/-- The class [MakeLaterN n P Q] is used to compute `lP := ▷^n P`. -/
class MakeLaterN [BI PROP] (n : Nat) (P : PROP) (lP : outParam PROP) where
  make_laterN : ▷^[n] P ⊣⊢ lP
export MakeLaterN (make_laterN)
