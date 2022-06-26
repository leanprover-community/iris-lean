import Iris.BI

namespace Iris.Proofmode
open Iris.BI
open Lean

-- Env
inductive Env (α : Type)
  | nil  : Env α
  | cons : α → Env α → Env α

namespace Env

@[reducible]
def concat : Env α → α → Env α
  | .nil, b       => .cons b .nil
  | .cons a as, b => .cons a <| as.concat b

@[reducible]
def isEmpty : Env α → Bool
  | .nil      => true
  | .cons _ _ => false

@[reducible]
def length : Env α → Nat
  | .nil       => 0
  | .cons _ as => as.length + 1

@[reducible]
def eraseIdx : (e : Env α) → Fin (e.length) → Env α
  | .cons _ as, ⟨0    , _⟩ => as
  | .cons a as, ⟨i + 1, h⟩ => .cons a <| as.eraseIdx ⟨i, Nat.le_of_succ_le_succ h⟩

@[reducible]
def get : (e : Env α) → Fin (e.length) → α
  | .cons a _ , ⟨0    , _⟩ => a
  | .cons _ as, ⟨i + 1, h⟩ => as.get ⟨i, Nat.le_of_succ_le_succ h⟩

@[reducible]
def partition (as : Env α) (mask : List Bool) : Env α × Env α :=
  go as mask
where
  @[reducible]
  go : Env α → List Bool → Env α × Env α
  | .cons a as, b :: bs =>
    let (ls, rs) := go as bs
    if b then
      (.cons a ls, rs)
    else
      (ls, .cons a rs)
  | _, _ =>
    (.nil, nil)

@[reducible]
def toList : Env α → List α
  | .nil       => []
  | .cons a as => a :: toList as

inductive Mem : α → Env α → Prop
  | head (a : α) (as : Env α)         : Mem a (.cons a as)
  | tail (a : α) (as : Env α) {b : α} : Mem b as → Mem b (.cons a as)

instance : Membership α (Env α) where
  mem := Mem

instance : Coe (Env α) (List α) where
  coe := toList

instance [ToString α] : ToString <| Env α where
  toString e := e.toList.toString

end Env


-- Envs
structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : Env PROP
  spatial        : Env PROP

def of_envs [BI PROP] (Γₚ Γₛ : Env PROP) : PROP :=
  match Γₚ, Γₛ with
  | .nil, .nil => `[iprop| emp]
  | _   , .nil => `[iprop| □ [∧] Γₚ]
  | .nil, _    => `[iprop| [∗] Γₛ]
  | _   , _    => `[iprop| □ [∧] Γₚ ∗ [∗] Γₛ]

def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ.intuitionistic Δ.spatial ⊢ Q


-- HypothesisIndex
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


-- AffineEnv
class AffineEnv [BI PROP] (Γ : Env PROP) where
  affineEnv : ∀ P, P ∈ Γ → Affine P

instance affineEnvNil [BI PROP] :
  AffineEnv (PROP := PROP) .nil
where
  affineEnv := sorry

instance affineEnvConcat [BI PROP] (P : PROP) (Γ : Env PROP) :
  [Affine P] →
  [AffineEnv Γ] →
  AffineEnv (.cons P Γ)
where
  affineEnv := sorry

instance (priority := default + 10) affineEnvBi [BIAffine PROP] (Γ : Env PROP) :
  AffineEnv Γ
where
  affineEnv := sorry

end Iris.Proofmode
