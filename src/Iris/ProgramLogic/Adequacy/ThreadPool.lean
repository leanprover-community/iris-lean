/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Lifting
import Iris.Instances.UPred.Instance

/-! # Adequacy: Thread Pool Definitions

Reference: `iris/program_logic/adequacy.v`

This file sets up the thread-pool weakest precondition, the core list
helpers, and the local abbreviations shared by the adequacy proof.
-/

namespace Iris.ProgramLogic

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic

variable {GF : BundledGFunctors} {M : Type _ → Type _} {F : Type _}
variable [UFraction F]
variable [FiniteMap Positive M] [DecidableEq Positive]
variable [FiniteMapLaws Positive M] [HeapFiniteMap Positive M]
variable [ElemG GF (InvF GF M F)]
variable [ElemG GF (COFE.constOF CoPsetDisj)]
variable [ElemG GF (COFE.constOF GSetDisj)]

variable {Λ : Language}
variable [inst : IrisGS Λ GF]
variable {W : WsatGS GF}
/-! ## Local Abbreviations -/

noncomputable abbrev fupd' {W : WsatGS GF}
    (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  -- specialize the fancy update to the Iris world satisfaction
  uPred_fupd (M := M) (F := F) W E1 E2 P

abbrev maskEmpty : Iris.Set Positive := fun _ => False
  -- the empty mask is the constantly-false predicate

abbrev state_interp (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- state interpretation from the IrisGS instance
  IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt

abbrev fork_post : Λ.val → IProp GF :=
  -- fork postcondition from the IrisGS instance
  IrisGS.fork_post (Λ := Λ) (GF := GF)

abbrev stuckness_pred (s : Stuckness) (e : Λ.expr) (σ : Λ.state) : Prop :=
  -- matches the predicate used in `wp_pre`
  match s with
  | .notStuck => reducible e σ
  | .maybeStuck => True

noncomputable abbrev wp_univ {W : WsatGS GF} (s : Stuckness) (e : Λ.expr)
    (Φ : Λ.val → IProp GF) : IProp GF :=
  -- shorthand for `WP` with the full mask
  wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ

noncomputable abbrev wptp_fork {W : WsatGS GF} (s : Stuckness)
    (efs : List Λ.expr) : IProp GF :=
  -- shorthand for forked-thread WPs
  big_sepL (fun _ ef =>
    wp_univ (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s ef fork_post) efs

/-! ## Thread Pool WP

A thread pool weakest precondition `wptp s es Φs` asserts that
each thread `es[i]` satisfies `WP es[i] @ s; ⊤ {{ Φs[i] }}`.
We define it as the big separating conjunction over paired lists. -/

/-- Body of the thread pool WP with an index offset.
Coq: `big_sepL` list indexing in `adequacy.v`. -/
noncomputable def wptp_body_at_fn {W : WsatGS GF} (s : Stuckness)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) : Nat → Λ.expr → IProp GF :=
  -- index into `Φs` with the given offset
  fun i e =>
    match Φs[i + k]? with
    | some Φ => wp (W := W) (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
    | none => BIBase.emp

/-- Body of the thread pool WP with an index offset.
Coq: `big_sepL` list indexing in `adequacy.v`. -/
noncomputable def wptp_body_at {W : WsatGS GF}
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) : IProp GF :=
  -- index into `Φs` with the given offset
  big_sepL (PROP := IProp GF) (wptp_body_at_fn (Λ := Λ) (GF := GF)
    (M := M) (F := F) (W := W) s Φs k) es

omit [DecidableEq Positive] [FiniteMapLaws Positive M] in
/-- Unfold `wptp_body_at` to the underlying big_sepL. -/
@[simp] theorem wptp_body_at_unfold {W : WsatGS GF}
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs k =
      big_sepL (PROP := IProp GF)
        (wptp_body_at_fn (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s Φs k) es := by
  -- unfold the definition
  rfl

/-- Thread pool weakest precondition: the big separating conjunction of
per-thread WPs over the thread pool.
Coq: `wptp` notation in `adequacy.v`. -/
noncomputable def wptp {W : WsatGS GF}
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- track list-length equality explicitly (as in `big_sepL2`)
  BIBase.sep (BIBase.pure (es.length = Φs.length))
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es Φs 0)

noncomputable abbrev wptp_post {W : WsatGS GF}
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- package the post-state interpretation with a fork-extended `wptp`
  BIBase.«exists» fun nt' =>
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ ns κs (nt + nt'))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) (W := W) s es
        (Φs ++ List.replicate nt' fork_post))

/-! ## List Helpers -/

omit [DecidableEq Positive] in
theorem get?_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat)
    (h : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := by
  -- reduce by list recursion and index cases
  induction l₁ generalizing i with
  | nil =>
      cases h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have h' : i < xs.length := by
            simpa [List.length] using Nat.lt_of_succ_lt_succ h
          simpa using ih (i := i) h'

omit [DecidableEq Positive] in
theorem get?_append_right {α : Type _} (l₁ l₂ : List α) (i : Nat)
    (h : l₁.length ≤ i) :
    (l₁ ++ l₂)[i]? = l₂[i - l₁.length]? := by
  -- reduce by list recursion and index arithmetic
  induction l₁ generalizing i with
  | nil =>
      simp
  | cons x xs ih =>
      cases i with
      | zero =>
          cases h
      | succ i =>
          have h' : xs.length ≤ i := by
            simpa [List.length] using Nat.le_of_succ_le_succ h
          simpa [List.length, Nat.succ_sub_succ] using ih (i := i) h'

omit [DecidableEq Positive] in
theorem get?_replicate {α : Type _} (n : Nat) (a : α) (i : Nat)
    (h : i < n) :
    (List.replicate n a)[i]? = some a := by
  -- unfold `replicate` along the index
  induction n generalizing i with
  | zero =>
      cases h
  | succ n ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have h' : i < n := by
            simpa using Nat.lt_of_succ_lt_succ h
          simpa using ih (i := i) h'

omit [DecidableEq Positive] in
theorem get?_lt_of_eq_some {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  -- show any successful lookup is in range
  induction l generalizing i with
  | nil =>
      cases i <;> simp at h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at h
          subst h
          simp
      | succ i =>
          have h' : xs[i]? = some a := by
            simpa using h
          have hi := ih (i := i) h'
          simpa [List.length] using Nat.succ_lt_succ hi

omit [DecidableEq Positive] in
theorem get?_eq_some_of_lt {α : Type _} (l : List α) {i : Nat}
    (h : i < l.length) :
    l[i]? = some (l.get ⟨i, h⟩) := by
  -- compute the lookup by recursion on the list
  induction l generalizing i with
  | nil =>
      cases h
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi : i < xs.length := by
            simpa [List.length] using Nat.lt_of_succ_lt_succ h
          simp

omit [DecidableEq Positive] in
theorem append_replicate {α : Type _} (Φs : List α) (n m : Nat) (a : α) :
    Φs ++ List.replicate n a ++ List.replicate m a =
      Φs ++ List.replicate (n + m) a := by
  -- fold the two replicate blocks into one
  calc
    Φs ++ List.replicate n a ++ List.replicate m a =
        Φs ++ (List.replicate n a ++ List.replicate m a) := by
          simp [List.append_assoc]
    _ = Φs ++ List.replicate (n + m) a := by
          simp

omit [DecidableEq Positive] in
theorem length_take_eq {α : Type _} (es t2 : List α) (n : Nat)
    (hlen : t2.length = es.length + n) :
    (t2.take es.length).length = es.length := by
  -- bound the take length by the given equation
  have hle : es.length ≤ t2.length := by
    simp [hlen]
  simpa using (List.length_take_of_le (l := t2) (i := es.length) hle)

omit [DecidableEq Positive] in
theorem length_drop_eq {α : Type _} (es t2 : List α) (n : Nat)
    (hlen : t2.length = es.length + n) :
    (t2.drop es.length).length = n := by
  -- turn the drop length into subtraction
  calc
    (t2.drop es.length).length = t2.length - es.length := by simp
    _ = (es.length + n) - es.length := by simp [hlen]
    _ = n := by simp

omit [DecidableEq Positive] in
theorem list_length_eq_one {α : Type _} (l : List α) (h : l.length = 1) :
    ∃ a, l = [a] := by
  -- split on the shape of the list
  cases l with
  | nil =>
      cases h
  | cons a l =>
      cases l with
      | nil =>
          exact ⟨a, rfl⟩
      | cons b l =>
          cases h

omit [DecidableEq Positive] in
theorem get?_append_replicate {α : Type _} (Φs : List α) (n : Nat) (a : α)
    (i k : Nat) (hlen : Φs.length = k) (hi : i < n) :
    (Φs ++ List.replicate n a)[i + k]? = some a := by
  -- reduce to the replicate suffix and apply `get?_replicate`
  have hle : Φs.length ≤ i + k := by
    simp [hlen]
  have hget := get?_append_right (l₁ := Φs) (l₂ := List.replicate n a) (i := i + k) hle
  have hsub : i + k - Φs.length = i := by
    simp [hlen]
  have hget' :
      (Φs ++ List.replicate n a)[i + k]? = (List.replicate n a)[i]? := by
    -- rewrite the shifted index into the replicate suffix
    simpa [hsub] using hget
  exact hget'.trans (get?_replicate (n := n) (a := a) (i := i) hi)

omit [DecidableEq Positive] in
theorem mem_split {α : Type _} {a : α} {l : List α} (h : a ∈ l) :
    ∃ t1 t2, l = t1 ++ a :: t2 := by
  -- split the list at the first occurrence of `a`
  induction l with
  | nil =>
      cases h
  | cons x xs ih =>
      -- split membership into head/tail cases
      simp [List.mem_cons] at h
      cases h with
      | inl hx =>
          subst hx
          exact ⟨[], xs, by simp⟩
      | inr hmem =>
          rcases ih hmem with ⟨t1, t2, ht⟩
          exact ⟨x :: t1, t2, by simp [ht]⟩


end Iris.ProgramLogic
