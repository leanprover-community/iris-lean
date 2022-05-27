import Iris.BI

namespace Iris.Proofmode
open Iris.BI

structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : List PROP
  spatial : List PROP

inductive HypothesisType | intuitionistic | spatial

def of_envs [BI PROP] (Γₚ Γₛ : List PROP) : PROP :=
  match Γₚ, Γₛ with
  | [], [] => `[iprop| emp]
  | _, []  => `[iprop| □ [∧] Γₚ]
  | [], _  => `[iprop| [∗] Γₛ]
  | _, _   => `[iprop| □ [∧] Γₚ ∗ [∗] Γₛ]

def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ.intuitionistic Δ.spatial ⊢ Q


inductive EnvsIndex (lₚ lₛ : Nat)
  | p : Fin lₚ → EnvsIndex lₚ lₛ
  | s : Fin lₛ → EnvsIndex lₚ lₛ


class AffineEnv [BI PROP] (Γ : List PROP) where
  affine_env : ∀ p, p ∈ Γ → Affine p

instance affine_env_nil [BI PROP] :
  AffineEnv (PROP := PROP) []
where
  affine_env := sorry

instance affine_env_cons [BI PROP] (P : PROP) (Γ : List PROP) :
  [Affine P] →
  [AffineEnv Γ] →
  AffineEnv (P :: Γ)
where
  affine_env := sorry

instance (priority := default + 10) affine_env_bi [BIAffine PROP] (Γ : List PROP) :
  AffineEnv Γ
where
  affine_env := sorry

end Iris.Proofmode
