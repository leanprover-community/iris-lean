import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- proof mode
theorem tac_start [BI PROP] (P : PROP) :
  envs_entails ⟨.nil, .nil⟩ P →
  ⊢ P
:= sorry

theorem tac_clear [BI PROP] {Γₚ Γₛ : Env PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P, Γₚ', Γₛ') := match i with
    | .p i => (true, Γₚ.get i, Γₚ.eraseIdx i, Γₛ)
    | .s i => (false, Γₛ.get i, Γₚ, Γₛ.eraseIdx i)
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- implication and wand
theorem tac_impl_intro [BI PROP] {Γₚ Γₛ : Env PROP} {P Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [TCIte Γₛ.isEmpty TCTrue (Persistent P)] →
  [FromAffinely P' P] →
  envs_entails ⟨Γₚ, Γₛ.concat P'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_impl_intro_intuitionistic [BI PROP] {Γₚ Γₛ : Env PROP} {P P' Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [IntoPersistent false P P'] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_impl_intro_drop [BI PROP] {Δ : Envs PROP} {P Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  envs_entails Δ Q →
  envs_entails Δ R
:= sorry

theorem tac_wand_intro [BI PROP] {Γₚ Γₛ : Env PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  envs_entails ⟨Γₚ, Γₛ.concat P⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro_intuitionistic [BI PROP] {Γₚ Γₛ : Env PROP} {P P' Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  [IntoPersistent false P P'] →
  [TCOr (Affine P) (Absorbing Q)] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_forall_intro [BI PROP] {Δ : Envs PROP} {Ψ : α → PROP} (Q : PROP) :
  [FromForall Q Ψ] →
  (∀ a, envs_entails Δ `[iprop| Ψ a]) →
  envs_entails Δ Q
:= sorry

-- assumptions
theorem tac_assumption_lean [BI PROP] {Γₚ Γₛ : Env PROP} {P : PROP} (Q : PROP) :
  (⊢ P) →
  [FromAssumption true P Q] →
  [TCIte Γₛ.isEmpty TCTrue (TCOr (Absorbing Q) (AffineEnv Γₛ))] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_assumption [BI PROP] {Γₚ Γₛ : Env PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [FromAssumption p P Q] →
  let Γₛ' := if let .s i := i then Γₛ.eraseIdx i else Γₛ
  [TCIte Γₛ'.isEmpty TCTrue (TCOr (Absorbing Q) (AffineEnv Γₛ'))] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- false
theorem tac_false_destruct [BI PROP] {Γₚ Γₛ : Env PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let P := match i with
    | .p i => Γₚ.get i
    | .s i => Γₛ.get i
  P = `[iprop| False] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- moving between contexts
theorem tac_pure [BI PROP] {Γₚ Γₛ : Env PROP} {φ : Prop} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
   let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [IntoPure P φ] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
   let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ.eraseIdx i, Γₛ)
    | .s i => (Γₚ, Γₛ.eraseIdx i)
  (φ → envs_entails ⟨Γₚ', Γₛ'⟩ Q) →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_intuitionistic [BI PROP] {Γₚ Γₛ : Env PROP} {P' : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [IntoPersistent p P P'] →
  [TCIte p TCTrue (TCOr (Affine P) (Absorbing Q))] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdx i |>.concat P', Γₛ)
    | .s i => (Γₚ.concat P', Γₛ.eraseIdx i)
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_spatial [BI PROP] {Γₚ Γₛ : Env PROP} {P' : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [FromAffinely P' P p] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ.eraseIdx i, Γₛ.concat P')
    | .s i => (Γₚ, Γₛ |>.eraseIdx i |>.concat P')
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

theorem tac_sep_split [BI PROP] {Γₚ Γₛ : Env PROP} {Q1 Q2 : PROP} (mask : List Bool) (P : PROP) :
  [FromSep P Q1 Q2] →
  let (Γₛ₁, Γₛ₂) := Γₛ.partition mask
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

theorem tac_conjunction_destruct [BI PROP] {Γₚ Γₛ : Env PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [IntoConjunction P P1 P2 p] →
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdx i |>.concat P1 |>.concat P2, Γₛ)
    | .s i => (Γₚ, Γₛ |>.eraseIdx i |>.concat P1 |>.concat P2)
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_conjunction_destruct_choice [BI PROP] {Γₚ Γₛ : Env PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (d : Bool) (Q : PROP) :
  let (p, P) := match i with
    | .p i => (true, Γₚ.get i)
    | .s i => (false, Γₛ.get i)
  [IntoAnd p P P1 P2] →
  let P' := if d then P1 else P2
  let (Γₚ', Γₛ') := match i with
    | .p i => (Γₚ |>.eraseIdx i |>.concat P', Γₛ)
    | .s i => (Γₚ, Γₛ |>.eraseIdx i |>.concat P')
  envs_entails ⟨Γₚ', Γₛ'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

theorem tac_disjunction_destruct [BI PROP] {Γₚ Γₛ : Env PROP} {P1 P2 : PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let P := match i with
    | .p i => Γₚ.get i
    | .s i => Γₛ.get i
  [IntoOr P P1 P2] →
  let (Γₚₗ, Γₚᵣ, Γₛₗ, Γₛᵣ) := match i with
    | .p i => (
      Γₚ |>.eraseIdx i |>.concat P1, Γₚ |>.eraseIdx i |>.concat P2,
      Γₛ, Γₛ)
    | .s i => (
      Γₚ, Γₚ,
      Γₛ |>.eraseIdx i |>.concat P1, Γₛ |>.eraseIdx i |>.concat P2)
  envs_entails ⟨Γₚₗ, Γₛₗ⟩ Q →
  envs_entails ⟨Γₚᵣ, Γₛᵣ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

end Iris.Proofmode
