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

theorem length_cons_list_cons {a : α} {as : List α} {b : β} {bs : Env β} :
  (a :: as).length = (Env.cons b bs).length →
  as.length = bs.length
:= by
  intro h
  simp only [length, List.length] at h
  rw [Nat.add_right_cancel h]

@[reducible]
def eraseIdx : (Γ : Env α) → Fin (Γ.length) → Env α
  | .cons _ as, ⟨0    , _⟩ => as
  | .cons a as, ⟨i + 1, h⟩ => .cons a <| as.eraseIdx ⟨i, Nat.le_of_succ_le_succ h⟩

@[reducible]
def get : (Γ : Env α) → Fin (Γ.length) → α
  | .cons a _ , ⟨0    , _⟩ => a
  | .cons _ as, ⟨i + 1, h⟩ => as.get ⟨i, Nat.le_of_succ_le_succ h⟩

@[reducible]
def split (Γ : Env α) (mask : List Bool) (h : mask.length = Γ.length) : Env α × Env α :=
  go Γ mask h
where
  @[reducible]
  go : (Γ : Env α) → (mask : List Bool) → (mask.length = Γ.length) → Env α × Env α
  | .nil, .nil, _ => (.nil, nil)
  | .cons a as, true :: bs, h =>
    let (ls, rs) := go as bs (length_cons_list_cons h)
    (.cons a ls, rs)
  | .cons a as, false :: bs, h =>
    let (ls, rs) := go as bs (length_cons_list_cons h)
    (ls, .cons a rs)

@[reducible]
def toList : Env α → List α
  | .nil       => []
  | .cons a as => a :: toList as

inductive Mem : α → Env α → Prop
  | head (a : α) (as : Env α)         : Mem a (.cons a as)
  | tail (a : α) {b : α} (as : Env α) : Mem b as → Mem b (.cons a as)

instance : Membership α (Env α) where
  mem := Mem

instance : Coe (Env α) (List α) where
  coe := toList

instance [ToString α] : ToString <| Env α where
  toString e := e.toList.toString

end Env

-- Env Theorems
theorem env_mem_cons_1 [BI PROP] {P : PROP} {Ps : Env PROP} : P ∈ Env.cons P Ps := by
  simp [Membership.mem, Env.Mem.head]

theorem env_mem_cons_2 [BI PROP] {P Q : PROP} {Ps : Env PROP} : P ∈ Ps → P ∈ Env.cons Q Ps := by
  intro h_Ps
  apply Env.Mem.tail
  exact h_Ps

-- Envs
structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : Env PROP
  spatial        : Env PROP

def of_envs [BI PROP] : Envs PROP → PROP
  | ⟨Γₚ, Γₛ⟩ => `[iprop| □ [∧] Γₚ ∗ [∗] Γₛ]

def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ ⊢ Q

-- HypothesisIndex
inductive HypothesisType | intuitionistic | spatial

structure HypothesisIndex where
  type : HypothesisType
  index : Nat
  length : Nat

inductive EnvsIndex (lₚ lₛ : Nat)
  | p : Fin lₚ → EnvsIndex lₚ lₛ
  | s : Fin lₛ → EnvsIndex lₚ lₛ

abbrev EnvsIndex.of [BI PROP] (Δ : Envs PROP) := EnvsIndex Δ.intuitionistic.length Δ.spatial.length

def HypothesisIndex.quoteAsEnvsIndex : HypothesisIndex → MetaM (TSyntax `term)
  | ⟨.intuitionistic, index, length⟩ =>
    ``(EnvsIndex.p ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)
  | ⟨.spatial, index, length⟩ =>
    ``(EnvsIndex.s ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)

namespace Envs

@[reducible]
def concat [BI PROP] : Bool → PROP → Envs PROP → Envs PROP
  | true,  P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ.concat P, Γₛ⟩
  | false, P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ, Γₛ.concat P⟩

@[reducible]
def delete [BI PROP] : Bool → (Δ : Envs PROP) → EnvsIndex.of Δ → Envs PROP
  | true , ⟨Γₚ, Γₛ⟩, .p i => ⟨Γₚ.eraseIdx i, Γₛ⟩
  | false, ⟨Γₚ, Γₛ⟩, .p _ => ⟨Γₚ, Γₛ⟩
  | _    , ⟨Γₚ, Γₛ⟩, .s i => ⟨Γₚ, Γₛ.eraseIdx i⟩

@[reducible]
def lookup [BI PROP] : (Δ : Envs PROP) → EnvsIndex.of Δ → Bool × PROP
  | ⟨Γₚ, _⟩, .p i => (true, Γₚ.get i)
  | ⟨_, Γₛ⟩, .s i => (false, Γₛ.get i)

@[reducible]
def replace [BI PROP] (Δ : Envs PROP) (i : EnvsIndex.of Δ) (p : Bool) (P : PROP) :=
  Δ.delete true i |>.concat p P

@[reducible]
def split [BI PROP] : (Δ : Envs PROP) → (mask : List Bool) → (mask.length = Δ.spatial.length) → Envs PROP × Envs PROP
  | ⟨Γₚ, Γₛ⟩, mask, h =>
    let ⟨Γₛ₁, Γₛ₂⟩ := Γₛ.split mask h
    (⟨Γₚ, Γₛ₁⟩, ⟨Γₚ, Γₛ₂⟩)

end Envs

-- Envs Theorems
theorem envs_concat_sound [BI PROP] {Δ : Envs PROP} (p : Bool) (Q : PROP) :
  of_envs Δ ⊢ □?p Q -∗ of_envs (Δ.concat p Q)
:= sorry

theorem envs_lookup_delete_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} {p : Bool} {P : PROP} :
  Δ.lookup i = (p, P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (Δ.delete true i)
:= sorry

theorem envs_lookup_replace_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} {p : Bool} {P : PROP} (q : Bool) (Q : PROP) :
  Δ.lookup i = (p, P) →
  of_envs Δ ⊢ □?p P ∗ (□?q Q -∗ of_envs (Δ.replace i q Q))
:= sorry

theorem envs_replace_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} (p : Bool) (Q : PROP) :
  of_envs (Δ.delete true i) ⊢ □?p Q -∗ of_envs (Δ.replace i p Q)
:= sorry

theorem envs_split_sound [BI PROP] {Δ Δ₁ Δ₂ : Envs PROP} {mask : List Bool} {h : mask.length = Δ.spatial.length} :
  Δ.split mask h = (Δ₁, Δ₂) →
  of_envs Δ ⊢ of_envs Δ₁ ∗ of_envs Δ₂
:= sorry

theorem envs_spatial_is_empty_intuitionistically [BI PROP] {Δ : Envs PROP} :
  Δ.spatial.isEmpty = true → of_envs Δ ⊢ □ of_envs Δ
:= sorry

-- AffineEnv
class AffineEnv [BI PROP] (Γ : Env PROP) where
  affineEnv : ∀ P, P ∈ Γ → Affine P
export AffineEnv (affineEnv)

instance affineEnvNil [BI PROP] :
  AffineEnv (PROP := PROP) .nil
where
  affineEnv := by
    intro _ h
    cases h

instance affineEnvConcat [BI PROP] (P : PROP) (Γ : Env PROP) :
  [Affine P] →
  [AffineEnv Γ] →
  AffineEnv (.cons P Γ)
where
  affineEnv := by
    intro P h
    cases h
    case head =>
      exact ⟨affine⟩
    case tail h =>
      exact affineEnv P h

instance (priority := default + 10) affineEnvBi (Γ : Env PROP) :
  [BIAffine PROP] →
  AffineEnv Γ
where
  affineEnv := by
    intro P _
    exact BIAffine.affine P

scoped instance affineEnvSpatial [BI PROP] (Γ : Env PROP)
  [inst : AffineEnv Γ] :
  Affine (`[iprop| [∗] Γ] : PROP)
where
  affine := by
    induction Γ generalizing inst
    case nil =>
      rw' [big_sepL_nil]
    case cons P Ps h_ind =>
      have : AffineEnv Ps := ⟨by
        intro P h_Ps
        exact inst.affineEnv P (env_mem_cons_2 h_Ps)⟩
      have : Affine P := inst.affineEnv P env_mem_cons_1
      rw' [big_sepL_cons, h_ind, affine]

end Iris.Proofmode
