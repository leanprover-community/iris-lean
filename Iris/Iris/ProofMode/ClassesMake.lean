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

/-- Aliases for [Affine] and [Absorbing], but the instances are severely
restricted. They only inspect the top-level symbol or check if the whole BI
is affine. -/
@[rocq_alias QuickAffine]
class QuickAffine [BI PROP] (P : PROP) where
  quick_affine : Affine P
export QuickAffine (quick_affine)
@[rocq_alias QuickAbsorbing]
class QuickAbsorbing [BI PROP] (P : PROP) where
  quick_absorbing : Absorbing P
export QuickAbsorbing (quick_absorbing)

/-- The class [MakeSep P Q PQ] is used to compute `PQ := P ∗ Q`. -/
@[ipm_class, rocq_alias MakeSep, rocq_alias KnownLMakeSep, rocq_alias KnownRMakeSep]
class MakeSep [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_sep : P ∗ Q ⊣⊢ PQ
export MakeSep (make_sep)

/-- The class [MakeAnd P Q PQ] is used to compute `PQ := P ∧ Q`. -/
@[ipm_class, rocq_alias MakeAnd, rocq_alias KnownLMakeAnd, rocq_alias KnownRMakeAnd]
class MakeAnd [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_and : P ∧ Q ⊣⊢ PQ
export MakeAnd (make_and)

/-- The class [MakeOr P Q PQ] is used to compute `PQ := P ∨ Q`. -/
@[ipm_class, rocq_alias MakeOr, rocq_alias KnownLMakeOr, rocq_alias KnownRMakeOr]
class MakeOr [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_or : P ∨ Q ⊣⊢ PQ
export MakeOr (make_or)

/-- The class [MakeAffinely P Q] is used to compute `Q := <affine> P`. -/
@[ipm_class, rocq_alias MakeAffinely, rocq_alias KnownMakeAffinely]
class MakeAffinely [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_affinely : <affine> P ⊣⊢ Q
export MakeAffinely (make_affinely)

/-- The class [MakeIntuitionistically P Q] is used to compute `Q := □ P`. -/
@[ipm_class, rocq_alias MakeIntuitionistically, rocq_alias KnownMakeIntuitionistically]
class MakeIntuitionistically [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_intuitionistically : □ P ⊣⊢ Q
export MakeIntuitionistically (make_intuitionistically)

/-- The class [MakeAbsorbingly P Q] is used to compute `Q := <absorb> P`. -/
@[ipm_class, rocq_alias MakeAbsorbingly, rocq_alias KnownMakeAbsorbingly]
class MakeAbsorbingly [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_absorbingly : <absorb> P ⊣⊢ Q
export MakeAbsorbingly (make_absorbingly)

/-- The class [MakePersistently P Q] is used to compute `Q := <pers> P`. -/
@[ipm_class, rocq_alias MakePersistently, rocq_alias KnownMakePersistently]
class MakePersistently [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_persistently : <pers> P ⊣⊢ Q
export MakePersistently (make_persistently)

/-- The class [MakeLaterN n P Q] is used to compute `lP := ▷^n P`. -/
@[ipm_class, rocq_alias MakeLaterN, rocq_alias KnownMakeLaterN]
class MakeLaterN [BI PROP] (n : Nat) (P : PROP) (lP : outParam PROP) where
  make_laterN : ▷^[n] P ⊣⊢ lP
export MakeLaterN (make_laterN)

/-- The class [MakeExcept0 P Q] is used to compute `Q := ◇ P`. -/
@[ipm_class, rocq_alias MakeExcept0, rocq_alias KnownMakeExcept0]
class MakeExcept0 [BI PROP] (P : PROP) (Q : outParam PROP) where
  make_except0 : ◇ P ⊣⊢ Q
export MakeExcept0 (make_except0)

/-- The class [MakeBUpd P Q] is used to compute `Q := |==> P`. -/
@[ipm_class]
class MakeBUpd [BI PROP] [BIUpdate PROP] (P : PROP) (Q : outParam PROP) where
  make_bupd : (|==> P) ⊣⊢ Q
export MakeBUpd (make_bupd)

/-- The class [MakeFUpd E1 E2 P Q] is used to compute `Q := |={E1, E2}=> P`. -/
@[ipm_class]
class MakeFUpd [BI PROP] [BIFUpdate PROP] (E1 E2 : CoPset) (P : PROP) (Q : outParam PROP) where
  make_fupd : (|={E1,E2}=> P) ⊣⊢ Q
export MakeFUpd (make_fupd)
