import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments
import Iris.Std.List
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- proof mode
theorem tac_start [BI PROP] (P : PROP) :
  envs_entails ⟨[], []⟩ P →
  ⊢ P
:= sorry

theorem tac_clear [BI PROP] {Γₚ Γₛ : List PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P, Γₚ', Γₛ') := match i with
    | .p i => (true, Γₚ.getR i, Γₚ.eraseIdxR i, Γₛ)
    | .s i => (false, Γₛ.getR i, Γₚ, Γₛ.eraseIdxR i)
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- implication and wand
theorem tac_impl_intro [BI PROP] {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [TCIte Γₛ.isEmptyR TCTrue (Persistent P)] →
  [FromAffinely P' P] →
  envs_entails ⟨Γₚ, Γₛ.concat P'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_impl_intro_intuitionistic [BI PROP] {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [IntoPersistent false P P'] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro [BI PROP] {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  envs_entails ⟨Γₚ, Γₛ.concat P⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro_intuitionistic [BI PROP] {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  [IntoPersistent false P P'] →
  [TCOr (Affine P) (Absorbing Q)] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

-- assumptions
theorem tac_assumption_lean [BI PROP] {Γₚ Γₛ : List PROP} {P : PROP} (Q : PROP) :
  (⊢ P) →
  [FromAssumption true P Q] →
  [TCIte Γₛ.isEmptyR TCTrue (TCOr (Absorbing Q) (AffineEnv Γₛ))] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_assumption [BI PROP] {Γₚ Γₛ : List PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [FromAssumption p P Q] →
  let Γₛ' := if let .s i := i then Γₛ.eraseIdxR i else Γₛ
  [TCIte Γₛ'.isEmptyR TCTrue (TCOr (Absorbing Q) (AffineEnv Γₛ'))] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- false
theorem tac_false_destruct [BI PROP] {Γₚ Γₛ : List PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let P := match i with
    | .p i => Γₚ.getR i
    | .s i => Γₛ.getR i
  P = `[iprop| False] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- moving between contexts
theorem tac_pure [BI PROP] {Γₚ Γₛ : List PROP} {φ : Prop} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
   let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [IntoPure P φ] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
   let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ.eraseIdxR i, Γₛ)
    | .s i => (Γₚ, Γₛ.eraseIdxR i)
  (φ → envs_entails ⟨Γₚ', Γₛ'⟩ Q) →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_intuitionistic [BI PROP] {Γₚ Γₛ : List PROP} {P' : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [IntoPersistent p P P'] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdxR i |>.concat P', Γₛ)
    | .s i => (Γₚ.concat P', Γₛ.eraseIdxR i)
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_spatial [BI PROP] {Γₚ Γₛ : List PROP} {P' : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [FromAffinely P' P p] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ.eraseIdxR i, Γₛ.concat P')
    | .s i => (Γₚ, Γₛ |>.eraseIdxR i |>.concat P')
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- (separating) conjunction splitting
theorem tac_and_split [BI PROP] {Δ : Envs PROP} {Q1 Q2 : PROP} (P : PROP) :
  [FromAnd P Q1 Q2] →
  envs_entails Δ Q1 →
  envs_entails Δ Q2 →
  envs_entails Δ P
:= sorry

theorem tac_sep_split [BI PROP] {Γₚ Γₛ : List PROP} {Q1 Q2 : PROP} (sortedIndices : List Nat) (splitRight : Bool) (P : PROP) :
  [FromSep P Q1 Q2] →
  let (Γₛ₁, Γₛ₂) := Γₛ.partitionIndices (sortedIndices.contains ·)
  let (Γₛ₁, Γₛ₂) := if splitRight then (Γₛ₂, Γₛ₁) else (Γₛ₁, Γₛ₂)
  envs_entails ⟨Γₚ, Γₛ₁⟩ Q1 →
  envs_entails ⟨Γₚ, Γₛ₂⟩ Q2 →
  envs_entails ⟨Γₚ, Γₛ⟩ P
:= sorry

-- destruction
class inductive IntoConjunction [BI PROP] (P : PROP) (P1 P2 : outParam PROP) : Bool → Type
  | and : [IntoAnd true P P1 P2] → IntoConjunction P P1 P2 true
  | sep : [IntoSep P P1 P2] → IntoConjunction P P1 P2 false

attribute [instance] IntoConjunction.and
attribute [instance] IntoConjunction.sep

theorem tac_conjunction_destruct [BI PROP] {Γₚ Γₛ : List PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [IntoConjunction P P1 P2 p] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdxR i |>.concat P1 |>.concat P2, Γₛ)
    | .s i => (Γₚ, Γₛ |>.eraseIdxR i |>.concat P1 |>.concat P2)
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_conjunction_destruct_choice [BI PROP] {Γₚ Γₛ : List PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (d : Bool) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.getR i)
    | .s i => (false, Γₛ.getR i)
  [IntoAnd p P P1 P2] →
  let P' := if d then P1 else P2
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdxR i |>.concat P', Γₛ)
    | .s i => (Γₚ, Γₛ |>.eraseIdxR i |>.concat P')
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_disjunction_destruct [BI PROP] {Γₚ Γₛ : List PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let P := match i with
    | .p i => Γₚ.getR i
    | .s i => Γₛ.getR i
  [IntoOr P P1 P2] →
  let (Γₚₗ, Γₚᵣ, Γₛₗ, Γₛᵣ) := match i with
    | .p i => (
      Γₚ |>.eraseIdxR i |>.concat P1, Γₚ |>.eraseIdxR i |>.concat P2,
      Γₛ, Γₛ)
    | .s i => (
      Γₚ, Γₚ,
      Γₛ |>.eraseIdxR i |>.concat P1, Γₛ |>.eraseIdxR i |>.concat P2)
  envs_entails ⟨Γₚₗ, Γₛₗ⟩ Q →
  envs_entails ⟨Γₚᵣ, Γₛᵣ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

end Iris.Proofmode
