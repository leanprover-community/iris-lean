/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.ProgramLogic.Language

@[expose] public section

namespace Iris.Tests
open Iris ProgramLogic Language Notation

/-! This section provides tests for notation used for the Language interface. -/
section Notation

/--
info: (e, σ) -<obs>-> (e, σ, []) : Prop
-/
#guard_msgs in
variable (e : Expr) (σ : State) (obs : Obs) [PrimStep Expr State Obs] in
#check (PrimStep.primStep (e, σ) obs (e,σ,[]))

/--
info: (t, σ) -<obs>->ₜₚ (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) (obs : List Obs) [Language Expr State Obs Val] in
#check (Language.Step (t, σ) obs (t,σ))

/--
info: (t, σ) -<obs>->ₜₚ^[0] (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) (obs : List Obs) [Language Expr State Obs Val] in
#check (Language.NSteps 0 (t, σ) obs (t,σ))

/--
info: (t, σ) -·->ₜₚ (t, σ) : Prop
-/
#guard_msgs in
variable (t : List Expr) (σ : State) [Language Expr State Obs Val] in
#check (ErasedStep (t, σ) (t,σ))

/--
info: e -ᵖ-> e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (PurePrimStep e e)

/--
info: e -ᵖ->^[0] e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (Relation.Iterate PurePrimStep 0 e e)

/--
info: e -ᵖ->* e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (FromMathlib.Relation.ReflTransGen PurePrimStep e e)

/--
info: e -ᵖ->* e : Prop
-/
#guard_msgs in
variable (e : Expr) [Language Expr State Obs Val] in
#check (FromMathlib.Relation.ReflTransGen PurePrimStep e e)

/--
info: t -ᵖ->ₜₚ* t : Prop
-/
#guard_msgs in
variable (t : List Expr) [Language Expr State Obs Val] in
#check (PureSteps t t)

end Notation
