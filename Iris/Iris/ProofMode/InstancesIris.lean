/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public import Iris.BI
public import Iris.ProofMode.Classes
public import Iris.ProofMode.ModalityInstances
public import Iris.Std.TC
public import Iris.Std.RocqPorting
public import Iris.ProofMode.Tactics
public import Iris.ProofMode.Display

@[expose] public section

namespace Iris.ProofMode
open Iris.BI Iris.Std

@[rocq_alias elim_inv_acc_without_close]
instance elimInv_acc_without_close [BI PROP] {X : Type}
    ϕ1 ϕ2 Pinv Pin (M1 M2 : PROP → PROP) α β mγ Q (Q' : X → PROP)
    [h1 : IntoAcc Pinv ϕ1 Pin M1 M2 α β mγ]
    [h2 : ElimAcc ϕ2 M1 M2 α β mγ Q Q'] :
    ElimInv (ϕ1 ∧ ϕ2) X Pinv Pin α false none Q Q' where
  elim_inv := sorry

@[rocq_alias elim_inv_acc_with_close]
instance elimInv_acc_with_close [BI PROP] {X : Type}
    ϕ1 ϕ2 Pinv Pin (M1 M2 : PROP → PROP) α β mγ Q (Q' : PROP)
    [h1 : IntoAcc Pinv ϕ1 Pin M1 M2 α β mγ]
    [h2 : ∀ R, ElimModal ϕ2 false false (M1 R) R Q Q'] :
    ElimInv (ϕ1 ∧ ϕ2) X Pinv Pin α true
            (some (fun x => iprop(β x -∗ M2 (match mγ x with | none => emp | some m => m))))
            Q (fun _ => Q') where
  elim_inv := sorry
