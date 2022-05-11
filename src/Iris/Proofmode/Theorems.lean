import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments
import Iris.Std.List
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

variable [BI PROP]

-- proof mode
theorem tac_start (P : PROP) :
  envs_entails ⟨[], []⟩ P →
  ⊢ P
:= sorry

-- implication and wand
theorem tac_impl_intro {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [TCIte Γₛ.isEmptyR TCTrue (Persistent P)] →
  [FromAffinely P' P] →
  envs_entails ⟨Γₚ, Γₛ.concat P'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_impl_intro_intuitionistic {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [IntoPersistent false P P'] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  envs_entails ⟨Γₚ, Γₛ.concat P⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro_intuitionistic {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  [IntoPersistent false P P'] →
  [TCOr (Affine P) (Absorbing Q)] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

end Iris.Proofmode
