/-
Copyright (c) 2026 Yunsong Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunsong Yang
-/
import Iris.ProofMode.ClassesMake
import Iris.ProofMode.InstancesMake

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-
  `IntoIH φ P Q` describes how to turn a pure induction hypothesis `φ` into a proofmode
  hypothesis `Q` under an intuitionistic BI context `□ P`.
-/
@[ipm_class]
class IntoIH [BI PROP] (φ : Prop) (P : PROP) (Q : outParam PROP) where
  into_ih : φ → □ P ⊢ Q

-- TODO: two more instances [into_ih_Forall] and [into_ih_Forall2]
-- have not been implemented
instance intoIH_entails [BI PROP] (P Q : PROP) : IntoIH (P ⊢ Q) P Q where
  into_ih := λ hpq => intuitionistically_elim.trans hpq
instance intoIH_forall [BI PROP] (φ : α → Prop) (P : PROP) (Φ : α → PROP)
    [h : ∀ x, IntoIH (φ x) P (Φ x)] :
    IntoIH (∀ x, φ x) P (BI.forall Φ) where
  into_ih := by
    intro hφ
    apply forall_intro
    intro x
    exact (h x).into_ih (hφ x)
instance intoIH_imp [BI PROP] (φ ψ : Prop) (Δ P Q : PROP)
    [h1 : MakeAffinely iprop(⌜φ⌝) P]
    [h2 : IntoIH ψ Δ Q] :
    IntoIH (φ → ψ) Δ iprop(P -∗ Q) where
  into_ih := by
    intro hImp
    apply wand_intro
    refine (sep_mono_r h1.make_affinely.mpr).trans ?_
    refine persistent_and_affinely_sep_r.2.trans ?_
    exact pure_elim_r (fun hφ => h2.into_ih (hImp hφ))

@[rocq_alias tac_revert_ih]
private theorem ih_revert [BI PROP] {Δ P Q : PROP} {φ : Prop} (hφ : φ)
    [hP : IntoIH φ Δ P]
    (hΔ : Δ ⊢ □ Δ)
    (hPQ : Δ ⊢ iprop(<pers> P → Q)) :
    Δ ⊢ Q := by
  have hP' : □ Δ ⊢ <pers> P :=
    (intuitionistically_intro' (hP.into_ih hφ)).trans persistently_of_intuitionistically
  have hAnd : □ Δ ⊢ iprop(<pers> P ∧ (<pers> P → Q)) :=
    and_intro hP' <| intuitionistically_elim.trans hPQ
  exact hΔ.trans <| hAnd.trans (imp_elim_r (P := iprop(<pers> P)) (Q := Q))
