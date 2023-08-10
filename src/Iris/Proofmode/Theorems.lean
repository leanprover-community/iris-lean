/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments
import Iris.Std

namespace Iris.Proofmode
open Iris.BI Iris.Std
open BI

/-- Introduce one or multiple let-bound variables. -/
scoped macro "intro_let " names:(colGt Lean.binderIdent)* : tactic =>
  `(tactic| (split; rename_i $[$names]*))

-- proof mode
theorem tac_start [BI PROP] (P : PROP) :
    EnvsEntails ⟨.nil, .nil⟩ P → ⊢ P := by
  simp only [EnvsEntails, ofEnvs, bigOp]
  rw' [intuitionistically_true, (left_id : emp ∗ _ ⊣⊢ _)]
  intro h
  exact h

theorem tac_stop [BI PROP] {Γₚ Γₛ : Env PROP} (P : PROP) :
  let Ps := match Γₚ, Γₛ with
    | .nil, .nil => iprop(emp)
    | _   , .nil => iprop(□ [∧] Γₚ)
    | .nil, _    => iprop([∗] Γₛ)
    | _   , _    => iprop(□ [∧] Γₚ ∗ [∗] Γₛ)
  (Ps ⊢ P) →
  EnvsEntails ⟨Γₚ, Γₛ⟩ P
:= by
  cases Γₚ
  <;> cases Γₛ
  all_goals
    simp [EnvsEntails, ofEnvs, bigOp]
    intro Ps
    rw' [Ps]
  case cons.nil =>
    rw' [(right_id : _ ∗ emp ⊣⊢ _)]
  all_goals
    rw' [intuitionistically_true, (left_id : emp ∗ _ ⊣⊢ _)]

theorem tac_clear [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  EnvsEntails (Δ.delete true i) Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  intro inst_affine_absorbing
  cases p
  all_goals
    cases inst_affine_absorbing
    simp only [EnvsEntails]
    intro h_entails
    rw' [envs_lookup_delete_sound true h_lookup, h_entails]
    simp only [intuitionisticallyIf, ite_true, ite_false]
    rw' [sep_elim_r]

-- pure
theorem tac_pure_intro [BI PROP] {Δ : Envs PROP} {a : Bool} {φ : Prop} (Q : PROP) :
  [FromPure a Q φ] →
  [TCIte a (AffineEnv Δ.spatial) TCTrue] →
  φ →
  EnvsEntails Δ Q
:= by
  simp only [EnvsEntails]
  intro _ inst_affine_env hφ
  rw' [← from_pure]
  cases a
  case false =>
    apply pure_intro
    exact hφ
  case true =>
    cases inst_affine_env
    simp only [ofEnvs, affinelyIf]
    rw' [
      affine,
      pure_true hφ,
      affinely_true_emp,
      affinely_emp]

-- implication and wand
theorem tac_imp_intro [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP) :
  [FromImp R P Q] →
  [TCIte Δ.spatial.isEmpty TCTrue (Persistent P)] →
  [FromAffinely P' P] →
  EnvsEntails (Δ.append false P') Q →
  EnvsEntails Δ R
:= by
  simp only [EnvsEntails]
  intro _ inst_pers _ h_entails
  rw' [← from_imp]
  cases h_empty : Δ.spatial.isEmpty
  <;> rw [h_empty] at inst_pers
  <;> cases inst_pers
  case false =>
    apply imp_intro'
    rw' [
      envs_append_sound false P',
      (from_affinely : <affine>?true P ⊢ _),
      persistent_and_affinely_sep_l_1,
      wand_elim_r,
      h_entails]
  case true =>
    rw' [envs_spatial_isEmpty_intuitionistically h_empty]
    apply imp_intro'
    rw' [
      envs_append_sound false P',
      (from_affinely : <affine>?true P ⊢ _)]
    simp only [intuitionistically]
    rw' [
      ← affinely_and_lr,
      persistently_and_intuitionistically_sep_r,
      intuitionistically_elim,
      wand_elim_r,
      h_entails]

theorem tac_imp_intro_intuitionistic [BI PROP] {Δ : Envs PROP} {P P' Q : PROP} (R : PROP) :
  [FromImp R P Q] →
  [IntoPersistently false P P'] →
  EnvsEntails (Δ.append true P') Q →
  EnvsEntails Δ R
:= by
  simp only [EnvsEntails]
  intro _ _ h_entails
  rw' [← from_imp, envs_append_sound true P'] ; simp only
  apply imp_intro'
  rw' [
    persistentlyIf_intro_false P,
    into_persistently,
    persistently_and_intuitionistically_sep_l,
    wand_elim_r,
    h_entails]

theorem tac_imp_intro_drop [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP) :
  [FromImp R P Q] →
  EnvsEntails Δ Q →
  EnvsEntails Δ R
:= by
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [← from_imp]
  apply imp_intro'
  rw' [and_elim_r, h_entails]

theorem tac_wand_intro [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  EnvsEntails (Δ.append false P) Q →
  EnvsEntails Δ R
:= by
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [
    ← from_wand,
    envs_append_sound false P,
    h_entails]

theorem tac_wand_intro_intuitionistic [BI PROP] {Δ : Envs PROP} {P P' Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  [IntoPersistently false P P'] →
  [TCOr (Affine P) (Absorbing Q)] →
  EnvsEntails (Δ.append true P') Q →
  EnvsEntails Δ R
:= by
  simp only [EnvsEntails]
  intro _ _ inst_affine_absorbing h_entails
  rw' [← from_wand, envs_append_sound true P'] ; simp only
  apply wand_intro'
  cases inst_affine_absorbing
  case a.l =>
    rw' [
      ← affine_affinely P,
      persistentlyIf_intro_false P,
      into_persistently,
      wand_elim_r,
      h_entails]
  case a.r =>
    rw' [
      persistentlyIf_intro_false P,
      into_persistently,
      ← absorbingly_intuitionistically,
      absorbingly_sep_l,
      wand_elim_r,
      h_entails,
      absorbing]

-- specialize
theorem tac_specialize [BI PROP] {Δ : Envs PROP} (rpPremise rpWand : Bool) (i j : EnvsIndex.of Δ) (h_ne : i.type = j.type → i.val ≠ j.val) {P2 : PROP} (R : PROP) :
  let (p, P1) := Δ.lookup i
  let Δ' := Δ.delete rpPremise i
  let j' := Δ.updateIndexAfterDelete rpPremise i j h_ne
  let (q, Q) := Δ'.lookup j'
  [IntoWand q p Q P1 P2] →
  EnvsEntails (Δ'.replace rpWand j' (p && q) P2) R →
  EnvsEntails Δ R
:= by
  intro_let p P1 h_lookup_i
  intro Δ' j'
  intro_let q Q h_lookup_j'
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [
    envs_lookup_delete_sound rpPremise h_lookup_i,
    envs_lookup_replace_sound rpWand (p && q) P2 h_lookup_j']
  cases p
  case false =>
    rw' [(IntoWand.into_wand : □?q Q ⊢ □?false P1 -∗ P2)]
    simp only [intuitionisticallyIf, Bool.false_and, ite_false]
    rw' [(assoc : P1 ∗ _ ⊣⊢ _), !wand_elim_r, h_entails]
  case true =>
    simp only [Bool.true_and, ← intuitionisticallyIf_intro_true]
    rw' [
      ← intuitionistically_idem,
      ← intuitionisticallyIf_idem,
      intuitionisticallyIf_of_intuitionistically q,
      (IntoWand.into_wand : □?q Q ⊢ □?true P1 -∗ P2),
      (assoc : □?q □ P1 ∗ _ ⊣⊢ _),
      intuitionisticallyIf_sep_2,
      !wand_elim_r,
      h_entails]

theorem tac_specialize_forall [BI PROP] {Δ : Envs PROP} (rpWand : Bool) (i : EnvsIndex.of Δ) {Φ : α → PROP} (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoForall P Φ] →
  (∃ x, EnvsEntails (Δ.replace rpWand i p (Φ x)) Q) →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ ⟨x, h_entails⟩
  rw' [
    envs_lookup_replace_sound rpWand p (Φ x) h_lookup,
    IntoForall.into_forall,
    forall_elim x,
    wand_elim_r,
    h_entails]

-- forall
theorem tac_forall_intro [BI PROP] {Δ : Envs PROP} {Ψ : α → PROP} (Q : PROP) :
  [FromForall Q Ψ] →
  (∀ a, EnvsEntails Δ iprop(Ψ a)) →
  EnvsEntails Δ Q
:= by
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [← from_forall]
  apply forall_intro
  exact h_entails

-- exists
theorem tac_exists [BI PROP] {Δ : Envs PROP} {Φ : α → PROP} (P : PROP) :
  [FromExists P Φ] →
  (∃ a, EnvsEntails Δ iprop(Φ a)) →
  EnvsEntails Δ P
:= by
  simp only [EnvsEntails]
  intro _ ⟨a, h_entails⟩
  rw' [← from_exists, ← exists_intro a, h_entails]

theorem tac_exists_destruct [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) {Φ : α → PROP} (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoExists P Φ] →
  (∀ a, EnvsEntails (Δ.replace true i p (Φ a)) Q) →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails, Envs.replace]
  intro _ h_entails
  rw' [
    envs_lookup_delete_sound true h_lookup,
    into_exists,
    intuitionisticallyIf_exists,
    sep_exists_r] ; simp only
  apply exists_elim
  intro a
  rw' [
    envs_append_sound p (Φ a),
    wand_elim_r,
    h_entails a]

-- emp
theorem tac_emp_intro [BI PROP] {Γₚ Γₛ : Env PROP} :
  [AffineEnv Γₛ] →
  EnvsEntails ⟨Γₚ, Γₛ⟩ iprop(emp)
:= by
  intro _
  simp only [EnvsEntails, ofEnvs]
  rw' [
    affinely_elim_emp,
    (affine : [∗] Γₛ.toList ⊢ emp),
    (left_id : emp ∗ _ ⊣⊢ _)]

-- assumptions
theorem tac_assumption_lean [BI PROP] {Δ : Envs PROP} {P : PROP} (Q : PROP) :
  (⊢ P) →
  [FromAssumption true P Q] →
  [TCIte Δ.spatial.isEmpty TCTrue (TCOr (Absorbing Q) (AffineEnv Δ.spatial))] →
  EnvsEntails Δ Q
:= by
  simp only [EnvsEntails]
  intro h_P _ inst_absorbing_affine_env
  rw' [
    ← (left_id : emp ∗ ofEnvs Δ ⊣⊢ _),
    ← intuitionistically_emp,
    h_P,
    (from_assumption : □?true P ⊢ Q)]
  cases h_empty : Δ.spatial.isEmpty
  <;> rw [h_empty] at inst_absorbing_affine_env
  <;> cases inst_absorbing_affine_env
  case false.e inst_absorbing_affine_env =>
    cases inst_absorbing_affine_env
    <;> rw' [!sep_elim_l]
  case true.t =>
    rw' [envs_spatial_isEmpty_intuitionistically h_empty, sep_elim_l]

theorem tac_assumption [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [FromAssumption p P Q] →
  let Δ' := Δ.delete true i
  [TCIte Δ'.spatial.isEmpty TCTrue (TCOr (Absorbing Q) (AffineEnv Δ'.spatial))] →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ inst_absorbing_affine_env
  rw' [envs_lookup_delete_sound true h_lookup]
  cases h_empty : (Δ.delete true i).spatial.isEmpty
  <;> rw [h_empty] at inst_absorbing_affine_env
  <;> cases inst_absorbing_affine_env
  case false.e inst_absorbing_affine_env =>
    rw' [(from_assumption : □?p P ⊢ Q)]
    cases inst_absorbing_affine_env
    <;> rw' [!sep_elim_l]
  case true.t =>
    rw' [envs_spatial_isEmpty_intuitionistically h_empty, sep_elim_l]
    exact from_assumption

-- false
theorem tac_exfalso [BI PROP] {Δ : Envs PROP} (Q : PROP) :
  EnvsEntails Δ iprop(False) →
  EnvsEntails Δ Q
:= by
  simp only [EnvsEntails]
  intro h_entails
  rw' [h_entails]
  exact false_elim

theorem tac_false_destruct [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (_, P) := Δ.lookup i
  P = iprop(False) →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro h_false
  rw' [
    envs_lookup_delete_sound true h_lookup,
    intuitionisticallyIf_elim,
    h_false,
    sep_elim_l]
  exact false_elim

-- moving between contexts
theorem tac_pure [BI PROP] {Δ : Envs PROP} {φ : Prop} (i : EnvsIndex.of Δ) (Q : PROP) :
   let (p, P) := Δ.lookup i
  [IntoPure P φ] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  (φ → EnvsEntails (Δ.delete true i) Q) →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ inst_affine_absorbing h_entails
  rw' [envs_lookup_delete_sound true h_lookup]
  cases p
  <;> simp only [intuitionisticallyIf, ite_true, ite_false]
  <;> cases inst_affine_absorbing
  case false.e inst_affine_absorbing =>
    cases inst_affine_absorbing
    case l =>
      rw' [
        ← affine_affinely P,
        into_pure,
        ← persistent_and_affinely_sep_l]
      apply pure_elim φ
      · exact and_elim_l
      · intro h_φ
        rw' [h_entails h_φ, and_elim_r]
    case r =>
      rw' [
        into_pure,
        absorbingly_affinely_intro_of_persistent,
        absorbingly_sep_lr,
        ← persistent_and_affinely_sep_l]
      apply pure_elim_l
      intro h_φ
      rw' [h_entails h_φ, absorbing]
  case true.t =>
    rw' [
      into_pure,
      ← persistently_and_intuitionistically_sep_l,
      persistently_pure]
    apply pure_elim_l
    intro h_φ
    rw' [h_entails h_φ]

theorem tac_intuitionistic [BI PROP] {Δ : Envs PROP} {P' : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoPersistently p P P'] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  EnvsEntails (Δ.replace true i true P') Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ inst_affine_absorbing h_entails
  rw' [envs_lookup_replace_sound true true P' h_lookup]
  cases p
  <;> simp only [intuitionisticallyIf, ite_true, ite_false, intuitionistically]
  <;> cases inst_affine_absorbing
  case false inst_affine_absorbing =>
    cases inst_affine_absorbing
    case l =>
      rw' [
        ← affine_affinely P,
        persistentlyIf_intro_false P,
        into_persistently,
        wand_elim_r,
        h_entails]
    case r =>
      rw' [persistentlyIf_intro_false P, into_persistently]
      conv =>
        lhs
        lhs
        rw [← absorbingly_intuitionistically]
      rw' [
        absorbingly_sep_l,
        wand_elim_r,
        h_entails,
        absorbing]
  case true =>
    rw' [
      persistentlyIf_intro_true P,
      into_persistently,
      wand_elim_r,
      h_entails]

theorem tac_spatial [BI PROP] {Δ : Envs PROP} {P' : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [FromAffinely P' P p] →
  EnvsEntails (Δ.replace true i false P') Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [envs_lookup_replace_sound true false P' h_lookup]
  cases p
  <;> simp only [intuitionisticallyIf, ite_true, ite_false]
  case false =>
    rw' [
      affinelyIf_intro_false P,
      from_affinely,
      wand_elim_r,
      h_entails]
  case true =>
    rw' [
      affinely_of_intuitionistically,
      affinelyIf_intro_true P,
      from_affinely,
      wand_elim_r,
      h_entails]

-- (separating) conjunction splitting
theorem tac_and_split [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) :
  [FromAnd P Q1 Q2] →
  EnvsEntails Δ Q1 →
  EnvsEntails Δ Q2 →
  EnvsEntails Δ P
:= by
  simp only [EnvsEntails]
  intro _ h_entails_1 h_entails_2
  rw' [← from_and]
  apply and_intro
  · exact h_entails_1
  · exact h_entails_2

theorem tac_sep_split [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (mask : List Bool) (h : mask.length = Δ.spatial.length) (P : PROP) :
  let (Δ₁, Δ₂) := Δ.split mask h
  [FromSep P Q1 Q2] →
  EnvsEntails Δ₁ Q1 →
  EnvsEntails Δ₂ Q2 →
  EnvsEntails Δ P
:= by
  intro_let Δ₁ Δ₂ h_split
  simp only [EnvsEntails]
  intro _ h_entails_1 h_entails_2
  rw' [
    envs_split_sound h_split,
    ← from_sep,
    h_entails_1,
    h_entails_2]

-- disjunction selection
theorem tac_disjunction_l [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) :
  [FromOr P Q1 Q2] →
  EnvsEntails Δ Q1 →
  EnvsEntails Δ P
:= by
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [← from_or]
  apply or_intro_l'
  exact h_entails

theorem tac_disjunction_r [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) :
  [FromOr P Q1 Q2] →
  EnvsEntails Δ Q2 →
  EnvsEntails Δ P
:= by
  simp only [EnvsEntails]
  intro _ h_entails
  rw' [← from_or]
  apply or_intro_r'
  exact h_entails

-- destruction
class inductive IntoConjunction [BI PROP] (P : PROP) (P1 P2 : outParam PROP) : Bool → Type
  | and : [IntoAnd true P P1 P2] → IntoConjunction P P1 P2 true
  | sep : [IntoSep P P1 P2] → IntoConjunction P P1 P2 false

attribute [instance] IntoConjunction.and
attribute [instance] IntoConjunction.sep

theorem tac_conjunction_destruct [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoConjunction P P1 P2 p] →
  EnvsEntails (Δ |>.delete true i |>.append p P1 |>.append p P2) Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro inst_conjunction h_entails
  rw' [
    envs_lookup_delete_sound true h_lookup,
    envs_append_sound p P1,
    envs_append_sound p P2] ; simp only
  cases p
  <;> simp only [intuitionisticallyIf, ite_true, ite_false]
  <;> cases inst_conjunction
  case false.sep =>
    rw' [
      into_sep,
      (comm : P1 ∗ P2 ⊣⊢ _),
      ← (assoc : _ ⊣⊢ (P2 ∗ P1) ∗ _),
      wand_elim_r,
      wand_elim_r,
      h_entails]
  case true.and =>
    rw' [intuitionisticallyIf_intro_true P, into_and]
    simp only [intuitionisticallyIf, ite_true]
    rw' [
      intuitionistically_and,
      and_sep_intuitionistically,
      (comm : □ P1 ∗ □ P2 ⊣⊢ _),
      ← (assoc : _ ⊣⊢ (□ P2 ∗ □ P1) ∗ _),
      wand_elim_r,
      wand_elim_r,
      h_entails]

theorem tac_conjunction_destruct_choice [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP} (i : EnvsIndex.of Δ) (d : Bool) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoAnd p P P1 P2] →
  EnvsEntails (if d then Δ.replace true i p P1 else Δ.replace true i p P2) Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ h_entails
  cases d
  case false =>
    rw' [
      envs_lookup_replace_sound true p P2 h_lookup,
      into_and,
      and_elim_r,
      wand_elim_r,
      h_entails]
  case true =>
    rw' [
      envs_lookup_replace_sound true p P1 h_lookup,
      into_and,
      and_elim_l,
      wand_elim_r,
      h_entails]

theorem tac_disjunction_destruct [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [IntoOr P P1 P2] →
  EnvsEntails (Δ.replace true i p P1) Q →
  EnvsEntails (Δ.replace true i p P2) Q →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup
  simp only [EnvsEntails]
  intro _ h_entails_1 h_entails_2
  rw' [envs_lookup_delete_sound true h_lookup] ; simp only
  simp only [Envs.replace] at h_entails_1
  simp only [Envs.replace] at h_entails_2
  rw' [into_or, intuitionisticallyIf_or, sep_or_r]
  apply or_elim
  · rw' [envs_append_sound p P1, wand_elim_r, h_entails_1]
  · rw' [envs_append_sound p P2, wand_elim_r, h_entails_2]

end Iris.Proofmode
