import Iris.BI
import Iris.Std

namespace Iris.Proofmode
open Iris.BI Iris.Std
open Lean

-- Env
inductive Env (α : Type)
  | nil  : Env α
  | cons : α → Env α → Env α

namespace Env

@[reducible]
def append : Env α → α → Env α
  | .nil, b       => .cons b .nil
  | .cons a as, b => .cons a <| as.append b

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
  rw' [Nat.add_right_cancel h]

@[reducible]
def eraseIdx : (Γ : Env α) → Fin (Γ.length) → Env α
  | .cons _ as, ⟨0    , _⟩ => as
  | .cons a as, ⟨i + 1, h⟩ => .cons a <| as.eraseIdx ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[reducible]
def get : (Γ : Env α) → Fin (Γ.length) → α
  | .cons a _ , ⟨0    , _⟩ => a
  | .cons _ as, ⟨i + 1, h⟩ => as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[reducible]
def split : (Γ : Env α) → (mask : List Bool) → (mask.length = Γ.length) → Env α × Env α
  | .nil, .nil, _ => (.nil, nil)
  | .cons a as, true :: bs, h =>
    let (ls, rs) := split as bs (length_cons_list_cons h)
    (.cons a ls, rs)
  | .cons a as, false :: bs, h =>
    let (ls, rs) := split as bs (length_cons_list_cons h)
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

delab_rule toList
  | `($_ $env) => `($env)

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

theorem env_erase_idx_cons [BI PROP] {P : PROP} {Ps : Env PROP} {i : Nat} {h : i + 1 < (Env.cons P Ps).length} :
  (Env.cons P Ps).eraseIdx ⟨i + 1, h⟩ = (Env.cons P <| Ps.eraseIdx ⟨i, Nat.lt_of_succ_lt_succ h⟩)
:= by
  rw' [Env.eraseIdx]
  · exact P
  · exact Nat.zero_lt_succ _

theorem env_get_cons [BI PROP] {P : PROP} {Ps : Env PROP} {i : Nat} {h : i + 1 < (Env.cons P Ps).length} :
  (Env.cons P Ps).get ⟨i + 1, h⟩ = Ps.get ⟨i, Nat.lt_of_succ_lt_succ h⟩
:= by
  rw' [Env.get]
  · exact Ps
  · exact Nat.zero_lt_succ _

theorem env_big_op_sep_append [BI PROP] {Γ : Env PROP} {P : PROP} : [∗] (Γ.append P) ⊣⊢ [∗] Γ ∗ P := by
  induction Γ
  <;> simp only [Env.append, Env.toList]
  case nil =>
    simp only [big_op]
    rw' [(left_id : emp ∗ _ ⊣⊢ _)]
  case cons P' _ h_ind =>
    rw' [
      !big_op_sep_cons,
      h_ind,
      ← (assoc : _ ⊣⊢ (P' ∗ _) ∗ P)]

theorem env_big_op_and_append [BI PROP] {Γ : Env PROP} {P : PROP} : □ [∧] (Γ.append P) ⊣⊢ □ [∧] Γ ∗ □ P := by
  induction Γ
  <;> simp only [Env.append, Env.toList]
  case nil =>
    simp only [big_op]
    rw' [
      intuitionistically_True_emp,
      (left_id : emp ∗ _ ⊣⊢ _)]
  case cons P' _ h_ind =>
    rw' [
      !big_op_and_cons,
      !intuitionistically_and,
      !and_sep_intuitionistically,
      h_ind,
      ← (assoc : _ ⊣⊢ (□ P' ∗ _) ∗ □ P)]

theorem env_big_op_sep_erase_idx_get [BI PROP] {Γ : Env PROP} (i : Fin Γ.length) :
  [∗] Γ ⊣⊢ [∗] (Γ.eraseIdx i) ∗ (Γ.get i)
:= by
  let ⟨val, is_lt⟩ := i
  induction val generalizing Γ
  case zero =>
    cases Γ
    case nil =>
      contradiction
    case cons P' _ =>
      rw' [Env.eraseIdx, Env.get]
      simp only [Env.toList]
      rw' [
        big_op_sep_cons,
        (comm : P' ∗ _ ⊣⊢ _)]
  case succ val h_ind =>
    cases Γ
    case nil =>
      contradiction
    case cons P' _ =>
      let is_lt := Nat.lt_of_succ_lt_succ is_lt
      let h_ind := h_ind ⟨val, is_lt⟩ is_lt
      rw' [env_erase_idx_cons, env_get_cons]
      simp only [Env.toList]
      rw' [
        !big_op_sep_cons,
        ← (assoc : _ ⊣⊢ (P' ∗ _) ∗ _),
        ← h_ind]

theorem env_big_op_and_erase_idx_get [BI PROP] {Γ : Env PROP} (i : Fin Γ.length) :
  □ [∧] Γ ⊣⊢ □ [∧] (Γ.eraseIdx i) ∗ □ (Γ.get i)
:= by
  let ⟨val, is_lt⟩ := i
  induction val generalizing Γ
  case zero =>
    cases Γ
    case nil =>
      contradiction
    case cons P' _ =>
      rw' [Env.eraseIdx, Env.get]
      simp only [Env.toList]
      rw' [
        big_op_and_cons,
        intuitionistically_and,
        and_sep_intuitionistically,
        (comm : □ P' ∗ _ ⊣⊢ _)]
  case succ val h_ind =>
    cases Γ
    case nil =>
      contradiction
    case cons P' _ =>
      let is_lt := Nat.lt_of_succ_lt_succ is_lt
      let h_ind := h_ind ⟨val, is_lt⟩ is_lt
      rw' [env_erase_idx_cons, env_get_cons]
      simp only [Env.toList]
      rw' [
        !big_op_and_cons,
        !intuitionistically_and,
        !and_sep_intuitionistically,
        ← (assoc : _ ⊣⊢ (□ P' ∗ _) ∗ _),
        ← h_ind]

theorem env_split_cons_false [BI PROP] {P : PROP} {Ps : Env PROP} {bs : List Bool} {Γ₁ Γ₂ : Env PROP} {h : (false :: bs).length = (Env.cons P Ps).length} :
  (Γ₁, Γ₂) = (Env.cons P Ps).split (false :: bs) h →
  ∃ (Γ₂' : Env PROP), Γ₂ = Env.cons P Γ₂' ∧
  ∃ (h' : bs.length = Ps.length), (Γ₁, Γ₂') = Ps.split bs h'
:= by
  intro h_split
  simp only [Env.split] at h_split
  cases h_split
  apply Exists.intro _
  apply And.intro rfl ?_
  apply Exists.intro (Env.length_cons_list_cons h)
  simp

theorem env_split_cons_true [BI PROP] {P : PROP} {Ps : Env PROP} {bs : List Bool} {Γ₁ Γ₂ : Env PROP} {h : (true :: bs).length = (Env.cons P Ps).length} :
  (Γ₁, Γ₂) = (Env.cons P Ps).split (true :: bs) h →
  ∃ (Γ₁' : Env PROP), Γ₁ = Env.cons P Γ₁' ∧
  ∃ (h' : bs.length = Ps.length), (Γ₁', Γ₂) = Ps.split bs h'
:= by
  intro h_split
  simp only [Env.split] at h_split
  cases h_split
  apply Exists.intro _
  apply And.intro rfl ?_
  apply Exists.intro (Env.length_cons_list_cons h)
  simp

theorem env_big_op_sep_split [BI PROP] {Γ Γ₁ Γ₂ : Env PROP} {mask : List Bool} {h : mask.length = Γ.length} :
  (Γ₁, Γ₂) = Γ.split mask h →
  ([∗] Γ : PROP) ⊢ [∗] Γ₁ ∗ [∗] Γ₂
:= by
  intro h_split
  induction Γ generalizing mask Γ₁ Γ₂
  case nil =>
    cases mask
    case nil =>
      simp only [Env.split] at h_split
      cases h_split
      simp only [big_op]
      rw' [(left_id : emp ∗ _ ⊣⊢ _)]
    case cons =>
      simp only [List.length, Env.length] at h
      contradiction
  case cons P Ps h_ind =>
    cases mask
    case nil =>
      simp only [List.length, Env.length] at h
      contradiction
    case cons b bs =>
      cases b
      case false =>
        let ⟨_, h_split_P, _, h_split_Ps⟩ := env_split_cons_false h_split
        rw' [h_split_P]
        simp only [Env.toList]
        rw' [
          !big_op_sep_cons,
          (assoc : _ ∗ (P ∗ _) ⊣⊢ _),
          (comm : _ ∗ P ⊣⊢ _),
          ← (assoc : _ ⊣⊢ (P ∗ _) ∗ _),
          h_ind h_split_Ps]
      case true =>
        let ⟨_, h_split_P, _, h_split_Ps⟩ := env_split_cons_true h_split
        rw' [h_split_P]
        simp only [Env.toList]
        rw' [
          !big_op_sep_cons,
          ← (assoc : _ ⊣⊢ (P ∗ _) ∗ _),
          h_ind h_split_Ps]

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
def append [BI PROP] : Bool → PROP → Envs PROP → Envs PROP
  | true,  P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ.append P, Γₛ⟩
  | false, P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ, Γₛ.append P⟩

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
def replace [BI PROP] (Δ : Envs PROP) (i : EnvsIndex.of Δ) (p : Bool) (P : PROP) : Envs PROP :=
  Δ.delete true i |>.append p P

@[reducible]
def split [BI PROP] : (Δ : Envs PROP) → (mask : List Bool) → (mask.length = Δ.spatial.length) → Envs PROP × Envs PROP
  | ⟨Γₚ, Γₛ⟩, mask, h =>
    let ⟨Γₛ₁, Γₛ₂⟩ := Γₛ.split mask h
    (⟨Γₚ, Γₛ₁⟩, ⟨Γₚ, Γₛ₂⟩)

end Envs

-- Envs Theorems
theorem envs_append_sound [BI PROP] {Δ : Envs PROP} (p : Bool) (Q : PROP) :
  of_envs Δ ⊢ □?p Q -∗ of_envs (Δ.append p Q)
:= by
  apply wand_intro_l ?_
  cases p
  <;> simp only [bi_intuitionistically_if, ite_true, ite_false, of_envs]
  case false =>
    rw' [
      env_big_op_sep_append,
      (assoc : _ ∗ (_ ∗ Q) ⊣⊢ _),
      (comm : _ ∗ Q ⊣⊢ _)]
  case true =>
    rw' [
      env_big_op_and_append,
      (comm : _ ∗ □ Q ⊣⊢ _),
      ← (assoc : _ ⊣⊢ (□ Q ∗ _) ∗ _)]

theorem envs_lookup_delete_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} {p : Bool} {P : PROP} (rp : Bool) :
  Δ.lookup i = (p, P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (Δ.delete rp i)
:= by
  cases i
  all_goals
    simp only [Envs.lookup]
    intro h_lookup
    cases h_lookup
    simp only [Envs.delete, of_envs, bi_intuitionistically_if, ite_true, ite_false]
  case s i =>
    rw' [
      (comm : Δ.spatial.get i ∗ _ ⊣⊢ _),
      ← (assoc : _ ⊣⊢ _ ∗ _),
      ← env_big_op_sep_erase_idx_get]
  case p i =>
    cases rp
    <;> simp only
    case true =>
      rw' [
        (assoc : _ ∗ _ ⊣⊢ _),
        (comm : □ Δ.intuitionistic.get i ∗ _ ⊣⊢ _),
        ← env_big_op_and_erase_idx_get i]
    case false =>
      rw' [
        (assoc : _ ∗ _ ⊣⊢ _),
        (comm : □ Δ.intuitionistic.get i ∗ _ ⊣⊢ _),
        env_big_op_and_erase_idx_get i,
        ← (assoc : _ ⊣⊢ (_ ∗ _) ∗ □ Δ.intuitionistic.get i),
        ← intuitionistically_sep_dup]

theorem envs_lookup_replace_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} {p : Bool} {P : PROP} (q : Bool) (Q : PROP) :
  Δ.lookup i = (p, P) →
  of_envs Δ ⊢ □?p P ∗ (□?q Q -∗ of_envs (Δ.replace i q Q))
:= by
  intro h_lookup
  simp only [Envs.replace]
  rw' [
    ← envs_append_sound q Q,
    ← envs_lookup_delete_sound true h_lookup]

theorem envs_split_env_spatial_split [BI PROP] {Δ Δ₁ Δ₂ : Envs PROP} {mask : List Bool} {h : mask.length = Δ.spatial.length} :
  Envs.split Δ mask h = (Δ₁, Δ₂) →
  Δ₁.intuitionistic = Δ.intuitionistic ∧
  Δ₂.intuitionistic = Δ.intuitionistic ∧
  (Δ₁.spatial, Δ₂.spatial) = Env.split Δ.spatial mask h
:= by
  simp only [Envs.split]
  intro h_split
  cases h_split
  <;> simp

theorem envs_split_sound [BI PROP] {Δ Δ₁ Δ₂ : Envs PROP} {mask : List Bool} {h : mask.length = Δ.spatial.length} :
  Δ.split mask h = (Δ₁, Δ₂) →
  of_envs Δ ⊢ of_envs Δ₁ ∗ of_envs Δ₂
:= by
  intro h_split_Δ
  let ⟨h_split_Γₚ₁, h_split_Γₚ₂, h_split_Γₛ⟩ := envs_split_env_spatial_split h_split_Δ
  simp only [of_envs]
  rw' [
    h_split_Γₚ₁,
    h_split_Γₚ₂,
    env_big_op_sep_split h_split_Γₛ,
    (assoc : _ ∗ (□ _ ∗ _) ⊣⊢ _),
    (comm : _ ∗ □ _ ⊣⊢ _),
    (assoc : □ _ ∗ (□ _ ∗ _) ⊣⊢ _),
    ← intuitionistically_sep_dup,
    ← (assoc : _ ⊣⊢ (_ ∗ _) ∗ _)]

theorem envs_spatial_is_empty_intuitionistically [BI PROP] {Δ : Envs PROP} :
  Δ.spatial.isEmpty = true →
  of_envs Δ ⊢ □ of_envs Δ
:= by
  simp only [Env.isEmpty, of_envs]
  cases Δ.spatial
  <;> simp [big_op]
  rw' [
    (right_id : _ ∗ emp ⊣⊢ _),
    intuitionistically_idemp]

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
      rw' [big_op_sep_nil]
    case cons P Ps h_ind =>
      have : AffineEnv Ps := ⟨by
        intro P h_Ps
        exact inst.affineEnv P (env_mem_cons_2 h_Ps)⟩
      have : Affine P := inst.affineEnv P env_mem_cons_1
      rw' [big_op_sep_cons, h_ind, affine]

end Iris.Proofmode
