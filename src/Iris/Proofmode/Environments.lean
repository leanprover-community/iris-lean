import Iris.BI

namespace Iris.Proofmode
open Iris.BI
open Lean

structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : List PROP
  spatial : List PROP

def of_envs [BI PROP] (Γₚ Γₛ : List PROP) : PROP :=
  match Γₚ, Γₛ with
  | [], [] => `[iprop| emp]
  | _, []  => `[iprop| □ [∧] Γₚ]
  | [], _  => `[iprop| [∗] Γₛ]
  | _, _   => `[iprop| □ [∧] Γₚ ∗ [∗] Γₛ]

def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ.intuitionistic Δ.spatial ⊢ Q


inductive HypothesisType | intuitionistic | spatial

structure HypothesisIndex where
  type : HypothesisType
  index : Nat
  length : Nat

inductive EnvsIndex (lₚ lₛ : Nat)
  | p : Fin lₚ → EnvsIndex lₚ lₛ
  | s : Fin lₛ → EnvsIndex lₚ lₛ

def HypothesisIndex.quoteAsEnvsIndex : HypothesisIndex → MetaM Syntax
  | ⟨.intuitionistic, index, length⟩ =>
    `(EnvsIndex.p ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)
  | ⟨.spatial, index, length⟩ =>
    `(EnvsIndex.s ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)


class AffineEnv [BI PROP] (Γ : List PROP) where
  affineEnv : ∀ p, p ∈ Γ → Affine p

instance affineEnvNil [BI PROP] :
  AffineEnv (PROP := PROP) []
where
  affineEnv := sorry

instance affineEnvCons [BI PROP] (P : PROP) (Γ : List PROP) :
  [Affine P] →
  [AffineEnv Γ] →
  AffineEnv (P :: Γ)
where
  affineEnv := sorry

instance (priority := default + 10) affineEnvBi [BIAffine PROP] (Γ : List PROP) :
  AffineEnv Γ
where
  affineEnv := sorry

end Iris.Proofmode
