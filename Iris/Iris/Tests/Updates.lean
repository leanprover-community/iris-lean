/-
Copyright (c) 2026 Fernando Leal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.Updates

open Iris

variable [BI PROP] [BUpd PROP] [FUpd PROP] (P Q : PROP) (E₁ E₂ : CoPset)

/-- info: iprop(P ==∗ Q) : PROP -/
#guard_msgs in
#check iprop(P ==∗ Q)

/-- info: ⊢ P ==∗ Q : Prop -/
#guard_msgs in
#check P ==∗ Q


/-- info: iprop(P ={E₁, E₂}=∗ Q) : PROP -/
#guard_msgs in
#check iprop(P ={E₁,E₂}=∗ Q)

/-- info: iprop(P ={E₁}=∗ Q) : PROP -/
#guard_msgs in
#check iprop(P ={E₁,E₁}=∗ Q)

/-- info: iprop(P ={E₁}=∗ Q) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}=∗ Q)


/-- info: iprop(|={E₁}[E₂]▷=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₂]▷=> P)

/-- info: iprop(|={E₁}▷=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}▷=> P)

/-- info: iprop(|={E₁}▷=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₁]▷=> P)


/-- info: iprop(P ={E₁}[E₂]▷=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₂]▷=∗ P)

/-- info: iprop(P ={E₁}▷=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}▷=∗ P)

/-- info: iprop(P ={E₁}▷=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₁]▷=∗ P)


/-- info: iprop(|={E₁}[E₂]▷^2=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₂]▷^2=> P)

/-- info: iprop(|={E₁}▷^2=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}▷^2=> P)

/-- info: iprop(|={E₁}▷^2=> P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₁]▷^2=> P)
-- -- Delab rules


/-- info: iprop(P ={E₁}[E₂]▷^2=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₂]▷^2=∗ P)

/-- info: iprop(P ={E₁}▷^2=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}▷^2=∗ P)

/-- info: iprop(P ={E₁}▷^2=∗ P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₁]▷^2=∗ P)


/-- info: iprop(|={E₁}[E₂]▷=>^[2] P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₂]▷=>^[2] P)

/-- info: iprop(|={E₁}▷=>^[2] P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}[E₁]▷=>^[2] P)

/-- info: iprop(|={E₁}▷=>^[2] P) : PROP -/
#guard_msgs in
#check iprop(|={E₁}▷=>^[2] P)


/-- info: iprop(P ={E₁}[E₂]▷=∗^[2] P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₂]▷=∗^[2] P)

/-- info: iprop(P ={E₁}▷=∗^[2] P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}▷=∗^[2] P)

/-- info: iprop(P ={E₁}▷=∗^[2] P) : PROP -/
#guard_msgs in
#check iprop(P ={E₁}[E₁]▷=∗^[2] P)
