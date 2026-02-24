/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Iris.ProofMode.Tactics.Basic

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

private theorem mod [BI PROP] {e} {Φ} {p p'} {A A' Q Q' : PROP} [he : ElimModal Φ p p' A A' Q Q']
  (h1 : e ∗ □?p' A' ⊢ Q') (hΦ : Φ) : e ∗ □?p A ⊢ Q :=
    (sep_comm.1.trans (sep_mono_r (wand_intro h1))).trans (he.1 hΦ)

/--
Eliminate a modality from `A` by transforming the goal from `P ∗ □?p A ⊢ Q` to `P ∗ □?p' A' ⊢ Q'`,
where `p'`, `A'`, and `Q'` are determined by `ElimModal`.

Parameters:
- `P`: Context
- `Q`: Goal
- `p`: Persistence flag of `A`
- `k`: Continuation that proves `P ∗ □?p' A' ⊢ Q'`, given the transformed `p'`, `A'`, and `Q'`

Returns a proof of `P ∗ □?p A ⊢ Q`
-/
def iModCore {prop : Q(Type u)} (_bi : Q(BI $prop)) (P Q : Q($prop)) (p : Q(Bool)) (A : Q($prop))
   (k : (p' : Q(Bool)) → (A' Q' : Q($prop)) → ProofModeM Q($P ∗ □?$p' $A' ⊢ $Q'))
   : ProofModeM (Q($P ∗ □?$p $A ⊢ $Q)) := do
    let Φ : Q(Prop) ← mkFreshExprMVarQ q(Prop)
    let p' : Q(Bool) ← mkFreshExprMVarQ q(Bool)
    let A' : Q($prop) ← mkFreshExprMVarQ q($prop)
    let Q' : Q($prop) ← mkFreshExprMVarQ q($prop)
    -- transform `Q` to `Q'` and `A` to `A'`
    let .some _ ← ProofModeM.trySynthInstanceQ q(ElimModal $Φ $p $p' $A $A' $Q $Q')
      | throwError "imod: {A} is not a modality"
    let hΦ : Q($Φ) ← mkFreshExprMVarQ q($Φ)
    iSolveSideconditionAt hΦ.mvarId!
    let p'' : Q(Bool) ← instantiateMVars p'
    let A'' ← instantiateMVarsQ A'
    let Q'' ← instantiateMVarsQ Q'
    -- establish defeq for type refinement
    have : $p'' =Q $p' := ⟨⟩
    have : $A'' =Q $A' := ⟨⟩
    have : $Q'' =Q $Q' := ⟨⟩
    -- show `P ∗ □?p' A' ⊢ Q'`
    let pf ← k p'' A'' Q''
    return q(mod $pf $hΦ)
