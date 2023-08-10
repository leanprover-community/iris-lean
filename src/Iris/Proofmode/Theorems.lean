/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
import Std.Tactic.RCases
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
theorem tac_start [BI PROP] (P : PROP)  (h : EnvsEntails ⟨.nil, .nil⟩ P) : ⊢ P :=
  (sep_emp.trans intuitionistically_true).2.trans h

theorem tac_stop [BI PROP] {Γₚ Γₛ : Env PROP} (P : PROP) :
    let Ps := match Γₚ, Γₛ with
      | .nil, .nil => iprop(emp)
      | _   , .nil => iprop(□ [∧] Γₚ)
      | .nil, _    => iprop([∗] Γₛ)
      | _   , _    => iprop(□ [∧] Γₚ ∗ [∗] Γₛ)
    (Ps ⊢ P) → EnvsEntails ⟨Γₚ, Γₛ⟩ P := by
  split <;> dsimp [EnvsEntails, ofEnvs] <;> intro h
  · exact (sep_emp.trans intuitionistically_true).1.trans h
  · exact sep_emp.1.trans h
  · exact (sep_congr_l intuitionistically_true |>.trans emp_sep).1.trans h
  · exact h

theorem tac_clear [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
    EnvsEntails (Δ.delete true i) Q →
    EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro inst h
  refine (envs_lookup_delete_sound true h_lookup).1.trans <| (sep_mono_l h).trans ?_
  match inst with
  | TCIte.t => exact sep_elim_l (Q := iprop(□ P))
  | TCIte.e => exact sep_elim_l (Q := P)

-- pure
theorem tac_pure_intro [BI PROP] {Δ : Envs PROP} {a : Bool} {φ : Prop} (Q : PROP)
    [h : FromPure a Q φ] [inst : TCIte a (AffineEnv Δ.spatial) TCTrue] (hφ : φ) :
    EnvsEntails Δ Q :=
  have : ofEnvs Δ ⊢ <affine>?a ⌜φ⌝ :=
    match inst with
    | TCIte.t => affine.trans (eq_true hφ ▸ affinely_true.2)
    | TCIte.e => pure_intro hφ
  this.trans h.1

-- implication and wand
theorem tac_imp_intro [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP)
    [FromImp R P Q] [inst : TCIte Δ.spatial.isEmpty TCTrue (Persistent P)] [FromAffinely P' P]
    (h_entails : EnvsEntails (Δ.append false P') Q) : EnvsEntails Δ R := by
  refine (BI.imp_intro ?_).trans from_imp
  refine Entails.trans ?_ <| (sep_mono_r <| from_affinely (Q := P) (p := true)).trans <|
    (envs_append_sound false P').2.trans h_entails
  exact match h_empty : Δ.spatial.isEmpty, inst with
  | _, TCIte.e => persistent_and_affinely_sep_r_1
  | _, TCIte.t =>
    (and_mono_l (envs_spatial_isEmpty_intuitionistically h_empty).2).trans <|
    affinely_and_lr.1.trans <| persistently_and_intuitionistically_sep_l.1.trans <|
    sep_mono_l intuitionistically_elim

theorem tac_imp_intro_intuitionistic [BI PROP] {Δ : Envs PROP} {P P' Q : PROP} (R : PROP)
    [FromImp R P Q] [IntoPersistently false P P']
    (h_entails : EnvsEntails (Δ.append true P') Q) : EnvsEntails Δ R := by
  refine (BI.imp_intro ?_).trans from_imp
  exact (and_mono_r (into_persistently (p := false) (P := P))).trans <|
    persistently_and_intuitionistically_sep_r.1.trans <|
    (envs_append_sound true P').2.trans h_entails

theorem tac_imp_intro_drop [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP)
    [FromImp R P Q] (h_entails : EnvsEntails Δ Q) : EnvsEntails Δ R :=
  (BI.imp_intro <| and_elim_l' h_entails).trans from_imp

theorem tac_wand_intro [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP)
    [FromWand R P Q] (h_entails : EnvsEntails (Δ.append false P) Q) : EnvsEntails Δ R :=
  (wand_intro <| (envs_append_sound false P).2.trans h_entails).trans from_wand

theorem tac_wand_intro_intuitionistic [BI PROP] {Δ : Envs PROP} {P P' Q : PROP} (R : PROP)
    [FromWand R P Q] [h : IntoPersistently false P P'] [inst : TCOr (Affine P) (Absorbing Q)]
    (h_entails : EnvsEntails (Δ.append true P') Q) : EnvsEntails Δ R := by
  refine (wand_intro ?_).trans from_wand
  have := (envs_append_sound true P').2.trans h_entails
  exact match inst with
  | TCOr.l => (sep_mono_r <| (affine_affinely P).2.trans (affinely_mono h.1)).trans this
  | TCOr.r => (sep_mono_r <| h.1.trans absorbingly_intuitionistically.2).trans <|
      absorbingly_sep_r.1.trans <| (absorbingly_mono this).trans absorbing

-- specialize
theorem tac_specialize [BI PROP] {Δ : Envs PROP} (rpPremise rpWand : Bool) (i j : EnvsIndex.of Δ)
    (h_ne : i.type = j.type → i.val ≠ j.val) {P2 : PROP} (R : PROP) :
    let (p, P1) := Δ.lookup i
    let Δ' := Δ.delete rpPremise i
    let j' := Δ.updateIndexAfterDelete rpPremise i j h_ne
    let (q, Q) := Δ'.lookup j'
    [IntoWand q p Q P1 P2] →
    EnvsEntails (Δ'.replace rpWand j' (p && q) P2) R → EnvsEntails Δ R := by
  intro_let p P1 h_lookup_i; intro Δ' j'; intro_let q Q h_lookup_j'; intro inst h_entails
  refine (envs_lookup_delete_sound rpPremise h_lookup_i).1.trans <|
    (sep_mono_l <| envs_lookup_replace_sound rpWand (p && q) P2 h_lookup_j').trans ?_
  match p, inst with
  | false, inst =>
    exact (sep_mono_l <| sep_mono_r inst.1).trans <|
      sep_assoc.1.trans <| (sep_mono_r wand_elim_l).trans <| wand_elim_l.trans h_entails
  | true, inst =>
    refine (sep_mono_r intuitionistically_idem.2).trans <| sep_assoc.1.trans <|
      (sep_mono_r ?_).trans <| wand_elim_l.trans h_entails
    exact
      (sep_mono intuitionisticallyIf_idem.2 (intuitionisticallyIf_of_intuitionistically q)).trans <|
      intuitionisticallyIf_sep_2.trans <| intuitionisticallyIf_mono <| wand_elim inst.1

theorem tac_specialize_forall [BI PROP] {Δ : Envs PROP}
    (rpWand : Bool) (i : EnvsIndex.of Δ) {Φ : α → PROP} (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoForall P Φ] →
    (∃ x, EnvsEntails (Δ.replace rpWand i p (Φ x)) Q) → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro inst ⟨x, h_entails⟩
  exact (envs_lookup_replace_sound rpWand p (Φ x) h_lookup).trans <|
    (sep_mono_r <| intuitionisticallyIf_mono <| inst.1.trans (forall_elim x)).trans <|
    wand_elim_l.trans h_entails

-- forall
theorem tac_forall_intro [BI PROP] {Δ : Envs PROP} {Ψ : α → PROP} (Q : PROP)
    [inst : FromForall Q Ψ] (h_entails : ∀ a, EnvsEntails Δ (Ψ a)) : EnvsEntails Δ Q :=
  (forall_intro h_entails).trans inst.1

-- exists
theorem tac_exists [BI PROP] {Δ : Envs PROP} {Φ : α → PROP} (P : PROP) [inst : FromExists P Φ] :
    (∃ a, EnvsEntails Δ iprop(Φ a)) → EnvsEntails Δ P
  | ⟨a, h_entails⟩ => h_entails.trans <| (exists_intro a).trans inst.1

theorem tac_exists_destruct [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) {Φ : α → PROP} (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoExists P Φ] →
    (∀ a, EnvsEntails (Δ.replace true i p (Φ a)) Q) → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro inst h_entails
  refine (envs_lookup_delete_sound true h_lookup).1.trans <|
    (sep_mono_r <| (intuitionisticallyIf_mono inst.1).trans intuitionisticallyIf_exists.1).trans <|
    sep_exists_l.1.trans <| exists_elim fun a =>
      (envs_append_sound p (Φ a)).2.trans <| h_entails a

-- emp
theorem tac_emp_intro [BI PROP] {Γₚ Γₛ : Env PROP} [AffineEnv Γₛ] :
    EnvsEntails ⟨Γₚ, Γₛ⟩ emp := affine

-- assumptions
theorem tac_assumption_lean [BI PROP] {Δ : Envs PROP} {P : PROP} (Q : PROP) (h_P : ⊢ P)
    [inst : FromAssumption true P Q]
    [or : TCOr (AffineEnv Δ.spatial) (Absorbing Q)] :
    EnvsEntails Δ Q := by
  have := intuitionistically_emp.2.trans <| (intuitionistically_mono h_P).trans inst.1
  refine emp_sep.2.trans <| (sep_mono_l this).trans ?_
  cases or <;> exact sep_elim_l

theorem tac_assumption [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
  let (p, P) := Δ.lookup i
  [FromAssumption p P Q] →
  let Δ' := Δ.delete true i
  [TCOr (AffineEnv Δ'.spatial) (Absorbing Q)] →
  EnvsEntails Δ Q
:= by
  intro_let p P h_lookup; intro inst _ or
  refine (envs_lookup_delete_sound true h_lookup).1.trans <| (sep_mono_r inst.1).trans ?_
  cases or <;> exact sep_elim_r

-- false
theorem tac_exfalso [BI PROP] {Δ : Envs PROP} (Q : PROP)
    (h_entails : EnvsEntails Δ iprop(False)) : EnvsEntails Δ Q := h_entails.trans false_elim

theorem tac_false_destruct [BI PROP] {Δ : Envs PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
    let (_, P) := Δ.lookup i
    P = iprop(False) → EnvsEntails Δ Q := by
  intro_let p P h_lookup; rintro rfl
  exact (envs_lookup_delete_sound true h_lookup).1.trans <|
    (sep_mono_r intuitionisticallyIf_elim).trans <|
    sep_elim_r.trans false_elim

-- moving between contexts
theorem tac_pure [BI PROP] {Δ : Envs PROP} {φ : Prop} (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoPure P φ] → [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
    (φ → EnvsEntails (Δ.delete true i) Q) → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro hP inst h_entails
  apply (envs_lookup_delete_sound true h_lookup).1.trans
  exact match inst with
  | TCIte.e (u := u) => match u with
    | TCOr.l =>
      (sep_mono_r <| (affine_affinely P).2.trans (affinely_mono hP.1)).trans <|
      persistent_and_affinely_sep_r.2.trans (pure_elim_r h_entails)
    | TCOr.r =>
      (sep_mono_r <| hP.1.trans absorbingly_affinely_intro_of_persistent).trans <|
      absorbingly_sep_lr.2.trans <| persistent_and_affinely_sep_r.2.trans <|
      pure_elim_r fun hφ => (absorbingly_mono <| h_entails hφ).trans absorbing
  | TCIte.t =>
    (sep_mono_r <| intuitionistically_mono hP.1).trans <|
    persistently_and_intuitionistically_sep_r.2.trans <|
    (and_mono_r persistently_pure.1).trans (pure_elim_r h_entails)

theorem tac_intuitionistic [BI PROP] {Δ : Envs PROP} {P' : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoPersistently p P P'] → [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
    EnvsEntails (Δ.replace true i true P') Q → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro hP inst h_entails
  refine (envs_lookup_replace_sound true true P' h_lookup).trans ?_
  exact match inst, hP with
  | TCIte.e (u := u), hP => match u with
    | TCOr.l =>
      (sep_mono_r <| (affine_affinely P).2.trans (affinely_mono hP.1)).trans <|
      wand_elim_l.trans h_entails
    | TCOr.r =>
      (sep_mono_r <| hP.1.trans absorbingly_intuitionistically.2).trans <|
      absorbingly_sep_r.1.trans <| (absorbingly_mono <| wand_elim_l.trans h_entails).trans absorbing
  | TCIte.t, hP => (sep_mono_r <| affinely_mono hP.1).trans <| wand_elim_l.trans h_entails

theorem tac_spatial [BI PROP] {Δ : Envs PROP} {P' : PROP} (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [FromAffinely P' P p] →
    EnvsEntails (Δ.replace true i false P') Q → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro hP h_entails
  exact (envs_lookup_replace_sound true false P' h_lookup).trans <|
    (sep_mono_r <| affinelyIf_of_intuitionisticallyIf.trans hP.1).trans <|
    wand_elim_l.trans h_entails

-- (separating) conjunction splitting
theorem tac_and_split [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) [inst : FromAnd P Q1 Q2]
    (h1 : EnvsEntails Δ Q1) (h2 : EnvsEntails Δ Q2) : EnvsEntails Δ P :=
  (and_intro h1 h2).trans inst.1

theorem tac_sep_split [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (mask : List Bool) (h : mask.length = Δ.spatial.length) (P : PROP) :
    let (Δ₁, Δ₂) := Δ.split mask h
    [FromSep P Q1 Q2] →
    EnvsEntails Δ₁ Q1 → EnvsEntails Δ₂ Q2 → EnvsEntails Δ P := by
  intro_let Δ₁ Δ₂ h_split; intro inst h1 h2
  exact (envs_split_sound h_split).1.trans <| (sep_mono h1 h2).trans inst.1

-- disjunction selection
theorem tac_disjunction_l [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) [inst : FromOr P Q1 Q2]
    (h : EnvsEntails Δ Q1) : EnvsEntails Δ P := (or_intro_l' h).trans inst.1

theorem tac_disjunction_r [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) [inst : FromOr P Q1 Q2]
    (h : EnvsEntails Δ Q2) : EnvsEntails Δ P := (or_intro_r' h).trans inst.1

-- destruction
class inductive IntoConjunction [BI PROP] (P : PROP) (P1 P2 : outParam PROP) : Bool → Type
  | and [h : IntoAnd true P P1 P2] : IntoConjunction P P1 P2 true
  | sep [h : IntoSep P P1 P2] : IntoConjunction P P1 P2 false

attribute [instance] IntoConjunction.and
attribute [instance] IntoConjunction.sep

theorem IntoConjunction.into_sep [BI PROP] {P P1 P2 : PROP} {p} :
    [IntoConjunction P P1 P2 p] → □?p P ⊢ □?p P1 ∗ □?p P2
  | IntoConjunction.and (h := h) => h.1.trans intuitionistically_and_sep.1
  | IntoConjunction.sep (h := h) => h.1

theorem tac_conjunction_destruct [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP}
    (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoConjunction P P1 P2 p] →
    EnvsEntails (Δ.delete true i |>.append p P1 |>.append p P2) Q → EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro inst h
  apply (envs_lookup_delete_sound true h_lookup).1.trans
  apply (sep_mono_r IntoConjunction.into_sep).trans
  refine ((envs_append_sound p P2).trans ?_).2.trans h
  exact (sep_congr_l <| envs_append_sound p P1).trans sep_assoc

theorem tac_conjunction_destruct_choice [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP}
    (i : EnvsIndex.of Δ) (d : Bool) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoAnd p P P1 P2] →
    EnvsEntails (if d then Δ.replace true i p P1 else Δ.replace true i p P2) Q →
    EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro inst h_entails
  split at h_entails <;>
    refine (envs_lookup_replace_sound _ _ _ h_lookup).trans <|
      (sep_mono_r <| inst.1.trans <| intuitionisticallyIf_mono ?_).trans <|
      wand_elim_l.trans h_entails <;>
    [exact and_elim_l; exact and_elim_r]

theorem tac_disjunction_destruct [BI PROP] {Δ : Envs PROP} {P1 P2 : PROP}
    (i : EnvsIndex.of Δ) (Q : PROP) :
    let (p, P) := Δ.lookup i
    [IntoOr P P1 P2] →
    EnvsEntails (Δ.replace true i p P1) Q → EnvsEntails (Δ.replace true i p P2) Q →
    EnvsEntails Δ Q := by
  intro_let p P h_lookup; intro hP h1 h2
  refine (envs_lookup_delete_sound true h_lookup).1.trans <|
    (sep_mono_r <| (intuitionisticallyIf_mono hP.1).trans <|
      (intuitionisticallyIf_or _).1).trans <| sep_or_l.1.trans ?_
  exact or_elim ((envs_append_sound p P1).2.trans h1) ((envs_append_sound p P2).2.trans h2)
