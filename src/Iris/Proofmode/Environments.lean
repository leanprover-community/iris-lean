/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI
import Iris.Std

namespace Iris.Proofmode
open Iris.BI Iris.Std
open Lean

/-- Single separation logic context, implemented as a list of hypotheses. A custom datatype is used
instead of the standard `List` to ensure that all operations are `reducible`. -/
inductive Env (α : Type)
  | nil  : Env α
  | cons : α → Env α → Env α

-- Env Operations
namespace Env

/-- Append a hypothesis to the end of the environment. -/
@[reducible]
def append : Env α → α → Env α
  | .nil, b       => .cons b .nil
  | .cons a as, b => .cons a <| as.append b

/-- Return whether the environment is empty, i.e. it contains no hypotheses. -/
@[reducible]
def isEmpty : Env α → Bool
  | .nil      => true
  | .cons _ _ => false

/-- Return the length of the environment, i.e. the number of contained hypotheses. -/
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

/-- Delete the hypothesis at the given index. -/
@[reducible]
def delete : (Γ : Env α) → Fin (Γ.length) → Env α
  | .cons _ as, ⟨0    , _⟩ => as
  | .cons a as, ⟨i + 1, h⟩ => .cons a <| as.delete ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Return the hypothesis at a given index without removing it. -/
@[reducible]
def get : (Γ : Env α) → Fin (Γ.length) → α
  | .cons a _ , ⟨0    , _⟩ => a
  | .cons _ as, ⟨i + 1, h⟩ => as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Split the environment into two disjoint environments. The given boolean mask must have the same
length as the environment. If the boolean mask contains the value `true` at a given index, the
hypothesis at the same index in the original environment is contained in the left environment in
the result. If the value is `false`, the hypothesis is contained in the right environment. -/
@[reducible]
def split : (Γ : Env α) → (mask : List Bool) → (mask.length = Γ.length) → Env α × Env α
  | .nil, .nil, _ => (.nil, .nil)
  | .cons a as, b :: bs, h =>
    let (ls, rs) := split as bs (length_cons_list_cons h)
    match b with | true => (.cons a ls, rs) | false => (ls, .cons a rs)

/-- Return a list with exactly the hypotheses from the environment in the same order as in
the environment. -/
@[reducible]
def toList : Env α → List α
  | .nil       => []
  | .cons a as => a :: toList as

/-- Proposition of membership for an hypothesis in an environment. -/
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

theorem env_delete_cons [BI PROP] {P : PROP} {Ps : Env PROP} {i : Nat} {h : i + 1 < (Env.cons P Ps).length} :
  (Env.cons P Ps).delete ⟨i + 1, h⟩ = (Env.cons P <| Ps.delete ⟨i, Nat.lt_of_succ_lt_succ h⟩)
:= by
  rw' [Env.delete]
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

theorem env_idx_rec [BI PROP] (P : (Γ : Env PROP) → Fin Γ.length → Prop)
  (zero : ∀ {P'} {Γ'} {is_lt}, P (.cons P' Γ') ⟨0, is_lt⟩)
  (succ : ∀ {P'} {Γ'} {val} {is_lt} {is_lt'}, P Γ' ⟨val, is_lt⟩ → P (.cons P' Γ') ⟨Nat.succ val, is_lt'⟩) :
  ∀ Γ i, P Γ i
:= by
  intro Γ i
  let ⟨val, is_lt⟩ := i
  induction val generalizing Γ
  case zero =>
    cases Γ with
    | nil =>
      contradiction
    | cons P' Γ' =>
      exact zero
  case succ val h_ind =>
    cases Γ with
    | nil =>
      contradiction
    | cons P' Γ' =>
      let is_lt := Nat.lt_of_succ_lt_succ is_lt
      specialize h_ind Γ' ⟨val, is_lt⟩ is_lt
      exact succ h_ind

theorem env_big_op_sep_delete_get [BI PROP] {Γ : Env PROP} (i : Fin Γ.length) :
  [∗] Γ ⊣⊢ [∗] (Γ.delete i) ∗ (Γ.get i)
:= by
  induction Γ, i using env_idx_rec
  case zero P' _ _ =>
    rw' [
      Env.delete,
      Env.get,
      big_op_sep_cons,
      (comm : P' ∗ _ ⊣⊢ _)]
  case succ P' _ _ _ _ h_ind =>
    rw' [
      env_delete_cons,
      env_get_cons,
      !big_op_sep_cons,
      ← (assoc : _ ⊣⊢ (P' ∗ _) ∗ _),
      ← h_ind]

theorem env_big_op_and_delete_get [BI PROP] {Γ : Env PROP} (i : Fin Γ.length) :
  □ [∧] Γ ⊣⊢ □ [∧] (Γ.delete i) ∗ □ (Γ.get i)
:= by
  induction Γ, i using env_idx_rec
  case zero P' _ _ =>
    rw' [
      Env.delete,
      Env.get,
      big_op_and_cons,
      intuitionistically_and,
      and_sep_intuitionistically,
      (comm : □ P' ∗ _ ⊣⊢ _)]
  case succ P' _ _ _ _ h_ind =>
    rw' [
      env_delete_cons,
      env_get_cons,
      !big_op_and_cons,
      !intuitionistically_and,
      !and_sep_intuitionistically,
      ← (assoc : _ ⊣⊢ (□ P' ∗ _) ∗ _),
      ← h_ind]

theorem env_delete_length [BI PROP] {Γ : Env PROP} {i : Fin Γ.length} : (Γ.delete i).length = Γ.length - 1 := by
  induction Γ, i using env_idx_rec
  case zero =>
    rw [Env.delete, Env.length, Nat.add_sub_cancel]
  case succ _ _ is_lt _ h_ind =>
    rw [
      env_delete_cons,
      Env.length,
      h_ind,
      Env.length,
      Nat.add_sub_cancel,
      Nat.sub_add_cancel ?_]
    · apply Nat.succ_le_of_lt
      exact Nat.zero_lt_of_lt is_lt

theorem env_delete_idx_length [BI PROP] {Γ : Env PROP} {i : Fin Γ.length} : i ≤ (Γ.delete i).length := by
  let ⟨val, is_lt⟩ := i
  rw [env_delete_length]
  apply Nat.le_of_lt_succ
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel ?_]
  exact is_lt
  · apply Nat.succ_le_of_lt
    exact Nat.zero_lt_of_lt is_lt

theorem env_delete_idx_length_of_lt [BI PROP] {Γ : Env PROP} {i : Fin Γ.length} {j : Nat} : j < i → j < (Γ.delete i).length := by
  intro h
  apply Nat.lt_of_lt_of_le h ?_
  exact env_delete_idx_length

theorem env_delete_idx_pred_length [BI PROP] {Γ : Env PROP} (i : Fin Γ.length) (h : 0 < i.val) : ∀ {j}, (i - 1) < (Γ.delete j).length := by
  intro j
  let ⟨val, is_lt⟩ := i
  rw [env_delete_length]
  apply Nat.lt_sub_of_add_lt
  rw [Nat.sub_add_cancel]
  exact is_lt
  · apply Nat.succ_le_of_lt
    exact h

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


/-- Combined separation logic context with two `Env` objects for the intuitionistic and
spatial context. -/
structure Envs (PROP : Type) [BI PROP] where
  intuitionistic : Env PROP
  spatial        : Env PROP

/-- Embedding of a separation logic context in form of an `Envs` object in a separation
logic proposition. -/
def of_envs [BI PROP] : Envs PROP → PROP
  | ⟨Γₚ, Γₛ⟩ => iprop(□ [∧] Γₚ ∗ [∗] Γₛ)

/-- Embedding of a separation logic context in form of an `Envs` object together with a separation
logic proposition in one separation logic proposition. This embedding is used in the Iris Proof
Mode where the embedded proposition is the goal of the proof. -/
def envs_entails [BI PROP] (Δ : Envs PROP) (Q : PROP) : Prop :=
  of_envs Δ ⊢ Q

/-- Types of hypotheses. -/
inductive HypothesisType
  | intuitionistic | spatial
  deriving BEq

/-- Unbounded index of a hypothesis in a combined separation logic context.

This datatype is used for convenience on the meta level only - environment operations and theorems
use the bounded dataype `EnvsIndex` instead. -/
structure HypothesisIndex where
  type : HypothesisType
  index : Nat
  length : Nat
  deriving BEq

/-- Bounded index of a hypothesis in a combined separation logic context.

The lengths of the individual contexts are used as type arguments instead of an `Envs` object to
allow for an easier syntax generation on the meta level. -/
inductive EnvsIndex (lₚ lₛ : Nat)
  | p : Fin lₚ → EnvsIndex lₚ lₛ
  | s : Fin lₛ → EnvsIndex lₚ lₛ

/-- Return the hypothesis type of the hypothesis referenced by the given index. -/
@[reducible]
def EnvsIndex.type : EnvsIndex lₚ lₛ → HypothesisType
  | .p _ => .intuitionistic
  | .s _ => .spatial

/-- Return the unbounded index value of the given index. -/
@[reducible]
def EnvsIndex.val : EnvsIndex lₚ lₛ → Nat
  | .p ⟨val, _⟩ => val
  | .s ⟨val, _⟩ => val

/-- `EnvsIndex` type for the given `Envs` object. -/
abbrev EnvsIndex.of [BI PROP] (Δ : Envs PROP) := EnvsIndex Δ.intuitionistic.length Δ.spatial.length

/-- Generate the syntax of a (bounded) `EnvsIndex` object based on an unbounded `HypothesisIndex`.
The proofs of the index bounds are generated using the tactic `decide`. -/
def HypothesisIndex.quoteAsEnvsIndex : HypothesisIndex → MetaM (TSyntax `term)
  | ⟨.intuitionistic, index, length⟩ =>
    ``(EnvsIndex.p ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)
  | ⟨.spatial, index, length⟩ =>
    ``(EnvsIndex.s ⟨$(quote index), by show $(quote index) < $(quote length) ; decide⟩)

-- Envs Operations
namespace Envs

/-- Append a hypothesis to the end of one of the separation logic contexts. The boolean flag
indicates whether the hypothesis should be appended to the intuitionistic (`true`) or spatial
(`false`) context. -/
@[reducible]
def append [BI PROP] : Bool → PROP → Envs PROP → Envs PROP
  | true,  P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ.append P, Γₛ⟩
  | false, P, ⟨Γₚ, Γₛ⟩ => ⟨Γₚ, Γₛ.append P⟩

/-- Delete the hypothesis at the given (combined) index. The boolean flag indicates whether the
hypothesis should be deleted even if it is part of the intuitionistic context. -/
@[reducible]
def delete [BI PROP] : Bool → (Δ : Envs PROP) → EnvsIndex.of Δ → Envs PROP
  | true , ⟨Γₚ, Γₛ⟩, .p i => ⟨Γₚ.delete i, Γₛ⟩
  | false, ⟨Γₚ, Γₛ⟩, .p _ => ⟨Γₚ, Γₛ⟩
  | _    , ⟨Γₚ, Γₛ⟩, .s i => ⟨Γₚ, Γₛ.delete i⟩

/-- Return the hypothesis at the given index. -/
@[reducible]
def lookup [BI PROP] : (Δ : Envs PROP) → EnvsIndex.of Δ → Bool × PROP
  | ⟨Γₚ, _⟩, .p i => (true, Γₚ.get i)
  | ⟨_, Γₛ⟩, .s i => (false, Γₛ.get i)

/-- Replace the hypothesis at index `i` with the hypothesis `P`. The boolean flag `p` indicates
whether the new hypothesis should be placed in the intuitionistic (`true`) or spatial (`false`)
context. If the boolean flag `rp` is set, the original hypothesis is removed even if it is part of
the intuitionistic context. If it is not set, the original hypothesis is kept. The new hypothesis
is added in both cases. -/
@[reducible]
def replace [BI PROP] (Δ : Envs PROP) (rp : Bool) (i : EnvsIndex.of Δ) (p : Bool) (P : PROP) : Envs PROP :=
  Δ.delete rp i |>.append p P

/-- Split the spatial context into two disjoint parts. See `Env.split` for details. -/
@[reducible]
def split [BI PROP] : (Δ : Envs PROP) → (mask : List Bool) → (mask.length = Δ.spatial.length) → Envs PROP × Envs PROP
  | ⟨Γₚ, Γₛ⟩, mask, h =>
    let ⟨Γₛ₁, Γₛ₂⟩ := Γₛ.split mask h
    (⟨Γₚ, Γₛ₁⟩, ⟨Γₚ, Γₛ₂⟩)

@[reducible]
def natPred : Nat → Nat
  | .zero => .zero
  | .succ n => n

@[reducible]
def natCmp : Nat → Nat → Ordering
  | .zero, .zero => .eq
  | .succ _, .zero => .gt
  | .zero, .succ _ => .lt
  | .succ m, .succ n => natCmp m n

theorem natCmp_lt : ∀ {m n}, natCmp m n = .lt ↔ m < n
  | 0, 0 | 0, .succ _ => by simp [Nat.succ_pos]
  | .succ _, 0 => by rw [natCmp]; simp [Nat.not_lt_zero]
  | .succ _, .succ _ => by rw [natCmp, natCmp_lt]; exact ⟨Nat.succ_lt_succ, Nat.lt_of_succ_lt_succ⟩

theorem natCmp_gt : ∀ {m n}, natCmp m n = .gt ↔ n < m
  | 0, 0 | .succ _, 0 => by simp [Nat.succ_pos]
  | 0, .succ _ => by rw [natCmp]; simp [Nat.not_lt_zero]
  | .succ _, .succ _ => by rw [natCmp, natCmp_gt]; exact ⟨Nat.succ_lt_succ, Nat.lt_of_succ_lt_succ⟩

theorem natCmp_eq {m n} : natCmp m n = .eq ↔ n = m :=
  match h : natCmp m n with
  | .lt => by simp [(Nat.ne_of_lt (natCmp_lt.1 h)).symm]
  | .gt => by simp [Nat.ne_of_lt (natCmp_gt.1 h)]
  | .eq => by
    simp; apply Nat.eq_of_not_lt_not_lt
    · simp [← natCmp_gt, h]
    · simp [← natCmp_lt, h]

/-- Update an index `j` of `Δ` to reference the same hypothesis in `Δ.delete rp i`, i.e. after the
hypothesis at index `i` has been deleted. The indices `i` and `j` must reference
different hypotheses. -/
@[reducible]
def updateIndexAfterDelete [BI PROP] (Δ : Envs PROP) : (rp : Bool) → (i : EnvsIndex.of Δ) → (j : EnvsIndex.of Δ) → (i.type = j.type → i.val ≠ j.val) → EnvsIndex.of (Δ.delete rp i)
  | rp, .p i, .s ⟨val, is_lt⟩, _ =>
    .s ⟨val, by cases rp <;> simp [is_lt]⟩
  | _, .s i, .p ⟨val, is_lt⟩, _ =>
    .p ⟨val, by simp [delete, is_lt]⟩
  | false, .p _, .p ⟨val, is_lt⟩, _ =>
    .p ⟨val, by simp [delete, is_lt]⟩
  | true, .p ⟨val_d, is_lt_d⟩, .p ⟨val, is_lt⟩, h_ne =>
    match h_cmp : natCmp val val_d with
    | .lt => EnvsIndex.p ⟨val, env_delete_idx_length_of_lt (natCmp_lt.1 h_cmp)⟩
    | .gt => EnvsIndex.p ⟨natPred val, env_delete_idx_pred_length ⟨val, is_lt⟩ (Nat.zero_lt_of_lt (natCmp_gt.1 h_cmp))⟩
    | .eq => False.elim <| h_ne (by simp) (natCmp_eq.1 h_cmp)
  | rp, .s ⟨val_d, is_lt_d⟩, .s ⟨val, is_lt⟩, h_ne =>
    match h_cmp : natCmp val val_d with
    | .lt => EnvsIndex.s ⟨val, by simp only [delete]; exact env_delete_idx_length_of_lt (natCmp_lt.1 h_cmp)⟩
    | .gt => EnvsIndex.s ⟨natPred val, by simp only [delete]; exact env_delete_idx_pred_length ⟨val, is_lt⟩ (Nat.zero_lt_of_lt (natCmp_gt.1 h_cmp))⟩
    | .eq => False.elim <| h_ne (by simp) (natCmp_eq.1 h_cmp)

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
      ← env_big_op_sep_delete_get]
  case p i =>
    cases rp
    <;> simp only
    case true =>
      rw' [
        (assoc : _ ∗ _ ⊣⊢ _),
        (comm : □ Δ.intuitionistic.get i ∗ _ ⊣⊢ _),
        ← env_big_op_and_delete_get i]
    case false =>
      rw' [
        (assoc : _ ∗ _ ⊣⊢ _),
        (comm : □ Δ.intuitionistic.get i ∗ _ ⊣⊢ _),
        env_big_op_and_delete_get i,
        ← (assoc : _ ⊣⊢ (_ ∗ _) ∗ □ Δ.intuitionistic.get i),
        ← intuitionistically_sep_dup]

theorem envs_lookup_replace_sound [BI PROP] {Δ : Envs PROP} {i : EnvsIndex.of Δ} {p : Bool} {P : PROP} (rp : Bool) (q : Bool) (Q : PROP) :
  Δ.lookup i = (p, P) →
  of_envs Δ ⊢ □?p P ∗ (□?q Q -∗ of_envs (Δ.replace rp i q Q))
:= by
  intro h_lookup
  simp only [Envs.replace]
  rw' [
    ← envs_append_sound q Q,
    ← envs_lookup_delete_sound rp h_lookup]

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
  Affine (iprop([∗] Γ) : PROP)
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
