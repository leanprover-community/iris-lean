/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Lifting
import Iris.Instances.UPred.Instance

/-! # Adequacy

Reference: `iris/program_logic/adequacy.v`

The adequacy theorem connects the Iris program logic to the operational
semantics at the meta-level. It states that if we can prove a weakest
precondition in Iris, then the program is safe (not stuck) and, when it
terminates, the postcondition holds at the meta-level.

## Simplifications

This port omits later credit support. The `£` parameter from the Coq version
is dropped, while `step_fupdN` is kept in a simplified form without credits.
The `num_laters_per_step` is fixed to 0 (one later per step), so `steps_sum`
is trivially `n`.

## Main Results

- `wptp_step'` — single step preserves thread pool WP
- `wptp_preservation` — n-step preservation
- `wp_not_stuck'` — WP implies not stuck
- `wp_strong_adequacy` — the main strong adequacy theorem
- `Adequate` — adequacy record (result + not stuck)
- `adequate_alt` — alternative characterization
- `adequate_tp_safe` — thread pool type safety
- `wp_adequacy` — simplified adequacy for single expressions
- `wp_invariance` — state invariance theorem
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

private noncomputable abbrev fupd' (E1 E2 : Iris.Set Positive) (P : IProp GF) : IProp GF :=
  -- specialize the fancy update to the Iris world satisfaction
  uPred_fupd (M := M) (F := F) W E1 E2 P

private abbrev maskEmpty : Iris.Set Positive := fun _ => False
  -- the empty mask is the constantly-false predicate

private abbrev state_interp (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- state interpretation from the IrisGS instance
  IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt

private abbrev fork_post : Λ.val → IProp GF :=
  -- fork postcondition from the IrisGS instance
  IrisGS.fork_post (Λ := Λ) (GF := GF)

private abbrev stuckness_pred (s : Stuckness) (e : Λ.expr) (σ : Λ.state) : Prop :=
  -- matches the predicate used in `wp_pre`
  match s with
  | .notStuck => reducible e σ
  | .maybeStuck => True

private noncomputable abbrev wp_univ (s : Stuckness) (e : Λ.expr)
    (Φ : Λ.val → IProp GF) : IProp GF :=
  -- shorthand for `WP` with the full mask
  wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ

private noncomputable abbrev wptp_fork (s : Stuckness) (efs : List Λ.expr) : IProp GF :=
  -- shorthand for forked-thread WPs
  big_sepL (fun _ ef => wp_univ (Λ := Λ) (GF := GF) (M := M) (F := F) s ef fork_post) efs

/-! ## Thread Pool WP

A thread pool weakest precondition `wptp s es Φs` asserts that
each thread `es[i]` satisfies `WP es[i] @ s; ⊤ {{ Φs[i] }}`.
We define it as the big separating conjunction over paired lists. -/

/-- Body of the thread pool WP with an index offset.
Coq: `big_sepL` list indexing in `adequacy.v`. -/
private noncomputable def wptp_body_at
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) : IProp GF :=
  -- index into `Φs` with the given offset
  big_sepL (fun i e =>
    match Φs[i + k]? with
    | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
    | none => BIBase.emp) es

/-- Thread pool weakest precondition: the big separating conjunction of
per-thread WPs over the thread pool.
Coq: `wptp` notation in `adequacy.v`. -/
noncomputable def wptp
    (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- track list-length equality explicitly (as in `big_sepL2`)
  BIBase.sep (BIBase.pure (es.length = Φs.length))
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)

private noncomputable abbrev wptp_post
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- package the post-state interpretation with a fork-extended `wptp`
  BIBase.«exists» fun nt' =>
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ ns κs (nt + nt'))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es
        (Φs ++ List.replicate nt' fork_post))

/-! ## List Helpers -/

private theorem get?_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat)
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

private theorem get?_append_right {α : Type _} (l₁ l₂ : List α) (i : Nat)
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

private theorem get?_replicate {α : Type _} (n : Nat) (a : α) (i : Nat)
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

private theorem get?_lt_of_eq_some {α : Type _} {l : List α} {i : Nat} {a : α}
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

private theorem get?_eq_some_of_lt {α : Type _} (l : List α) {i : Nat}
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
          simpa using ih (i := i) hi

private theorem append_replicate {α : Type _} (Φs : List α) (n m : Nat) (a : α) :
    Φs ++ List.replicate n a ++ List.replicate m a =
      Φs ++ List.replicate (n + m) a := by
  -- fold the two replicate blocks into one
  calc
    Φs ++ List.replicate n a ++ List.replicate m a =
        Φs ++ (List.replicate n a ++ List.replicate m a) := by
          simp [List.append_assoc]
    _ = Φs ++ List.replicate (n + m) a := by
          simp

private theorem length_take_eq {α : Type _} (es t2 : List α) (n : Nat)
    (hlen : t2.length = es.length + n) :
    (t2.take es.length).length = es.length := by
  -- bound the take length by the given equation
  have hle : es.length ≤ t2.length := by
    simpa [hlen] using (Nat.le_add_right es.length n)
  simpa using (List.length_take_of_le (l := t2) (n := es.length) hle)

private theorem length_drop_eq {α : Type _} (es t2 : List α) (n : Nat)
    (hlen : t2.length = es.length + n) :
    (t2.drop es.length).length = n := by
  -- turn the drop length into subtraction
  calc
    (t2.drop es.length).length = t2.length - es.length := by simp
    _ = (es.length + n) - es.length := by simpa [hlen]
    _ = n := by simp

private theorem list_length_eq_one {α : Type _} (l : List α) (h : l.length = 1) :
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

private theorem get?_append_replicate {α : Type _} (Φs : List α) (n : Nat) (a : α)
    (i k : Nat) (hlen : Φs.length = k) (hi : i < n) :
    (Φs ++ List.replicate n a)[i + k]? = some a := by
  -- reduce to the replicate suffix and apply `get?_replicate`
  have hle : Φs.length ≤ i + k := by
    simpa [hlen] using Nat.le_add_left k i
  have hget := get?_append_right (l₁ := Φs) (l₂ := List.replicate n a) (i := i + k) hle
  have hsub : i + k - Φs.length = i := by
    simpa [hlen] using Nat.add_sub_cancel_right i k
  have hget' :
      (Φs ++ List.replicate n a)[i + k]? = (List.replicate n a)[i]? := by
    -- rewrite the shifted index into the replicate suffix
    simpa [hsub] using hget
  exact hget'.trans (get?_replicate (n := n) (a := a) (i := i) hi)

private theorem mem_split {α : Type _} {a : α} {l : List α} (h : a ∈ l) :
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

/-! ## Wptp Helpers -/

private theorem wptp_length (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs ⊢
      BIBase.pure (es.length = Φs.length) := by
  -- drop the body of the conjunction
  exact sep_elim_l (P := BIBase.pure (es.length = Φs.length))
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)

private theorem wptp_body_of_wptp (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs ⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 := by
  -- drop the pure length equality
  exact sep_elim_r (P := BIBase.pure (es.length = Φs.length))
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)

private theorem sep_pure_intro {φ : Prop} (P : IProp GF) (h : φ) :
    P ⊢ BIBase.sep (BIBase.pure φ) P := by
  -- insert `True` then replace it with the desired pure fact
  exact (true_sep_2 (PROP := IProp GF) (P := P)).trans
    (sep_mono (pure_intro h) .rfl)

private theorem wptp_of_body (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (hlen : es.length = Φs.length) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 ⊢
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs := by
  -- reinsert the pure length equality to form `wptp`
  simpa [wptp] using (sep_pure_intro (P := wptp_body_at (Λ := Λ) (GF := GF)
    (M := M) (F := F) s es Φs 0) hlen)

private theorem wptp_singleton_intro (s : Stuckness) (e : Λ.expr)
    (Φ : Λ.val → IProp GF) :
    wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ ⊢
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ] := by
  -- build the singleton pool WP from its body
  have hbody :
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ ⊢
        wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ] 0 := by
    simpa [wptp_body_at, big_sepL_cons]
  have hlen : ([e] : List Λ.expr).length = ([Φ] : List (Λ.val → IProp GF)).length := by
    simp
  exact hbody.trans <|
    wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (Φs := [Φ]) hlen

private theorem wptp_singleton_elim (s : Stuckness) (e : Λ.expr)
    (Φ : Λ.val → IProp GF) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ] ⊢
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ := by
  -- strip the singleton body and simplify
  have hbody :=
    wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (Φs := [Φ])
  simpa [wptp_body_at, big_sepL_cons] using hbody

private theorem wptp_body_at_split_middle
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t1 ++ e1 :: t2) Φs k ⊣⊢
      BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs k)
        (BIBase.sep
          (match Φs[k + t1.length]? with
          | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ
          | none => BIBase.emp)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs (k + t1.length + 1))) := by
  -- split the big separating conjunction over `t1` and `e1 :: t2`
  have happ :=
    big_sepL_app (PROP := IProp GF)
      (Φ := fun i e =>
        match Φs[i + k]? with
        | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
        | none => BIBase.emp) t1 (e1 :: t2)
  -- simplify the tail using the cons rule
  simpa [wptp_body_at, big_sepL_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happ

private theorem wptp_body_at_middle
    (s : Stuckness) (t1 t2 : List Λ.expr) (e : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (k : Nat) (Φ : Λ.val → IProp GF)
    (hget : Φs[k + t1.length]? = some Φ) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t1 ++ e :: t2) Φs k ⊣⊢
      BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs k)
        (BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (k + t1.length + 1))) := by
  -- specialize the split lemma and rewrite the middle lookup
  simpa [hget] using (wptp_body_at_split_middle (Λ := Λ) (GF := GF)
    (M := M) (F := F) (s := s) (t1 := t1) (t2 := t2) (e1 := e)
    (Φs := Φs) (k := k))

private theorem wptp_body_at_append_left
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k n : Nat) (hle : k + es.length ≤ Φs.length) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es (Φs ++ List.replicate n fork_post) k ⊣⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs k := by
  -- the append does not affect indices below `Φs.length`
  refine ⟨?_, ?_⟩
  · refine big_sepL_mono ?_
    intro i e hget
    have hi := get?_lt_of_eq_some hget
    have hlt : i + k < Φs.length := by
      have hlt' : i + k < es.length + k := Nat.add_lt_add_right hi k
      have hlt'' : i + k < k + es.length := by
        simpa [Nat.add_comm] using hlt'
      exact Nat.lt_of_lt_of_le hlt'' (by simpa [Nat.add_comm] using hle)
    have hget' := get?_append_left (l₁ := Φs) (l₂ := List.replicate n fork_post)
      (i := i + k) hlt
    simpa [wptp_body_at, hget'] 
  · refine big_sepL_mono ?_
    intro i e hget
    have hi := get?_lt_of_eq_some hget
    have hlt : i + k < Φs.length := by
      have hlt' : i + k < es.length + k := Nat.add_lt_add_right hi k
      have hlt'' : i + k < k + es.length := by
        simpa [Nat.add_comm] using hlt'
      exact Nat.lt_of_lt_of_le hlt'' (by simpa [Nat.add_comm] using hle)
    have hget' := get?_append_left (l₁ := Φs) (l₂ := List.replicate n fork_post)
      (i := i + k) hlt
    simpa [wptp_body_at, hget']

private theorem wptp_body_at_replicate
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) (hlen : Φs.length = k) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es
        (Φs ++ List.replicate es.length fork_post) k ⊣⊢
      big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) es := by
  -- the entire tail list comes from the replicate suffix
  refine ⟨?_, ?_⟩
  · refine big_sepL_mono ?_
    intro i ef hget
    have hi := get?_lt_of_eq_some hget
    have hsome := get?_append_replicate (Φs := Φs) (n := es.length) (a := fork_post)
      (i := i) (k := k) (hlen := hlen) hi
    simpa [wptp_body_at, hsome]
  · refine big_sepL_mono ?_
    intro i ef hget
    have hi := get?_lt_of_eq_some hget
    have hsome := get?_append_replicate (Φs := Φs) (n := es.length) (a := fork_post)
      (i := i) (k := k) (hlen := hlen) hi
    simpa [wptp_body_at, hsome]

private theorem wptp_body_at_append_fork
    (s : Stuckness) (t2 efs : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) (hlen : Φs.length = k + t2.length) :
    BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
      (big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) ⊣⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) k := by
  -- split on append and rewrite each side appropriately
  have happ :=
    big_sepL_app (PROP := IProp GF)
      (Φ := fun i e =>
        match (Φs ++ List.replicate efs.length fork_post)[i + k]? with
        | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
        | none => BIBase.emp) t2 efs
  have happ' :
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
          (Φs ++ List.replicate efs.length fork_post) k ⊣⊢
        BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 (Φs ++ List.replicate efs.length fork_post) k)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length)) := by
    simpa [wptp_body_at, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happ
  have hle : k + t2.length ≤ Φs.length := by
    simpa [hlen] using Nat.le_refl (k + t2.length)
  have hleft := wptp_body_at_append_left (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t2) (Φs := Φs) (k := k) (n := efs.length) hle
  have hright := wptp_body_at_replicate (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := efs) (Φs := Φs) (k := k + t2.length) (hlen := hlen)
  refine ⟨?_, ?_⟩
  · have hsep :
        BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) ⊢
          BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s t2 (Φs ++ List.replicate efs.length fork_post) k)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length)) :=
        sep_mono (PROP := IProp GF)
          (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
          (P' := big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)
          (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 (Φs ++ List.replicate efs.length fork_post) k)
          (Q' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length))
          hleft.2 hright.2
    exact hsep.trans (happ'.symm.1)
  · have hsep :
        BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s t2 (Φs ++ List.replicate efs.length fork_post) k)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length)) ⊢
          BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) :=
        sep_mono (PROP := IProp GF)
          (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 (Φs ++ List.replicate efs.length fork_post) k)
          (P' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length))
          (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
          (Q' := big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)
          hleft.1 hright.1
    exact (happ'.1).trans hsep

private theorem wptp_tail_fork
    (s : Stuckness) (t1 t2 efs : List Λ.expr)
    (Φs : List (Λ.val → IProp GF))
    (hlen : Φs.length = t1.length + t2.length + 1) :
    BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 Φs (t1.length + 1))
      (big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) ⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s
        (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) (t1.length + 1) := by
  -- specialize the append-fork lemma with the computed offset
  have hlen' : Φs.length = (t1.length + 1) + t2.length := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen
  exact (wptp_body_at_append_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t2 := t2) (efs := efs) (Φs := Φs)
    (k := t1.length + 1) (hlen := hlen')).1

private theorem wptp_append_lookup
    (t1 t2 efs : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    (Φs ++ List.replicate efs.length fork_post)[t1.length]? = some Φ := by
  -- show the lookup stays in the left prefix
  have hlt : t1.length < Φs.length := by
    have hlt' : t1.length < t1.length + 1 + t2.length := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    simpa [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt'
  simpa [hget] using
    (get?_append_left (l₁ := Φs) (l₂ := List.replicate efs.length fork_post)
      (i := t1.length) hlt)

private theorem wptp_lookup_middle
    (t1 t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (hlen : Φs.length = t1.length + t2.length + 1) :
    ∃ Φ, Φs[t1.length]? = some Φ := by
  -- use the list length equality to show the middle index is in range
  have hlt : t1.length < Φs.length := by
    have hlt' : t1.length < t1.length + 1 + t2.length := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
    simpa [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt'
  refine ⟨Φs.get ⟨t1.length, hlt⟩, ?_⟩
  exact get?_eq_some_of_lt (l := Φs) hlt

private theorem wptp_middle_append
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t1 (Φs ++ List.replicate efs.length fork_post) 0)
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post)
          (t1.length + 1))) ⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s
        (t1 ++ e2 :: t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) 0 := by
  -- rebuild the middle using the updated lookup
  have hget' := wptp_append_lookup (t1 := t1) (t2 := t2) (efs := efs)
    (Φs := Φs) (Φ := Φ) hlen hget
  have hget0 :
      (Φs ++ List.replicate efs.length fork_post)[0 + t1.length]? = some Φ := by
    -- align the index with the expected `0 + t1.length`
    simpa [Nat.zero_add] using hget'
  have hmid :=
    (wptp_body_at_middle (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t1 := t1) (t2 := t2 ++ efs) (e := e2)
      (Φs := Φs ++ List.replicate efs.length fork_post) (k := 0) (Φ := Φ) hget0).2
  simpa [Nat.zero_add, Nat.add_assoc, List.append_assoc] using hmid

private theorem wptp_rebuild_len
    (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF))
    (hlen : Φs.length = t1.length + t2.length + 1) :
    (t1 ++ e2 :: t2 ++ efs).length =
      (Φs ++ List.replicate efs.length fork_post).length := by
  -- compute the list lengths explicitly
  simp [List.length_append, List.length_cons, List.length_replicate, hlen,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem wptp_rebuild
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (t1.length + 1))
          (big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))
    ⊢ wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
        (t1 ++ e2 :: t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) := by
  -- replace the tail, rebuild the middle, then add the length proof
  have hle : 0 + t1.length ≤ Φs.length := by
    -- `t1.length` is within the left prefix of `Φs`
    have hle' : t1.length ≤ t1.length + t2.length + 1 := by
      exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    simpa [Nat.zero_add, hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle'
  have hleft := wptp_body_at_append_left (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t1) (Φs := Φs) (k := 0) (n := efs.length) hle
  have htail := wptp_tail_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (Φs := Φs) hlen
  have htail' :
      BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s t2 Φs (t1.length + 1))
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)) ⊢
        BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) (t1.length + 1)) :=
    sep_mono (PROP := IProp GF)
      (P := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
      (P' := BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
      (Q := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
      (Q' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) (t1.length + 1))
      BIBase.Entails.rfl htail
  have hprep :
      BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
          (BIBase.sep
            (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
            (BIBase.sep
              (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
                s t2 Φs (t1.length + 1))
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))) ⊢
        BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t1 (Φs ++ List.replicate efs.length fork_post) 0)
          (BIBase.sep
            (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post)
              (t1.length + 1))) :=
    sep_mono (PROP := IProp GF)
      (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
      (P' := BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (t1.length + 1))
          (big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))
      (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t1 (Φs ++ List.replicate efs.length fork_post) 0)
      (Q' := BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post)
          (t1.length + 1)))
      hleft.2 htail'
  have hmid := wptp_middle_append (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) hlen hget
  have hlen2 := wptp_rebuild_len (Λ := Λ) (GF := GF)
    (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2) (Φs := Φs) hlen
  exact hprep.trans (hmid.trans <|
    wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := t1 ++ e2 :: t2 ++ efs)
      (Φs := Φs ++ List.replicate efs.length fork_post) hlen2)

private theorem sep_reorder_for_rebuild
    (P A B C D : IProp GF) :
    BIBase.sep (BIBase.sep P (BIBase.sep B D)) (BIBase.sep A C) ⊣⊢
      BIBase.sep P (BIBase.sep A (BIBase.sep B (BIBase.sep C D))) := by
  -- swap the middle components and reassociate the tail
  have hswap :
      BIBase.sep (BIBase.sep P (BIBase.sep B D)) (BIBase.sep A C) ⊣⊢
        BIBase.sep (BIBase.sep P A) (BIBase.sep (BIBase.sep B D) C) :=
    sep_sep_sep_comm (P := P) (Q := BIBase.sep B D) (R := A) (S := C)
  have htail :
      BIBase.sep (BIBase.sep B D) C ⊣⊢ BIBase.sep B (BIBase.sep C D) := by
    exact (sep_right_comm (P := B) (Q := D) (R := C)).trans
      (sep_assoc (P := B) (Q := C) (R := D))
  have hmid :
      BIBase.sep (BIBase.sep P A) (BIBase.sep (BIBase.sep B D) C) ⊣⊢
        BIBase.sep (BIBase.sep P A) (BIBase.sep B (BIBase.sep C D)) := by
    refine ⟨?_, ?_⟩
    · exact sep_mono (PROP := IProp GF)
        (P := BIBase.sep P A) (P' := BIBase.sep (BIBase.sep B D) C)
        (Q := BIBase.sep P A) (Q' := BIBase.sep B (BIBase.sep C D))
        BIBase.Entails.rfl htail.1
    · exact sep_mono (PROP := IProp GF)
        (P := BIBase.sep P A) (P' := BIBase.sep B (BIBase.sep C D))
        (Q := BIBase.sep P A) (Q' := BIBase.sep (BIBase.sep B D) C)
        BIBase.Entails.rfl htail.2
  exact hswap.trans (hmid.trans (sep_assoc (P := P) (Q := A) (R := BIBase.sep B (BIBase.sep C D))))

private theorem wptp_step_post_push (X A C : IProp GF) :
    BIBase.sep (BIBase.later X) (BIBase.sep A C) ⊢
      BIBase.later (BIBase.sep X (BIBase.sep A C)) := by
  -- add the `later` frame to the right and combine with `later_sep`
  have hlat : BIBase.sep A C ⊢ BIBase.later (BIBase.sep A C) := later_intro
  exact (sep_mono (PROP := IProp GF) .rfl hlat).trans
    (later_sep (P := X) (Q := BIBase.sep A C)).2

private theorem wptp_step_post_inner
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
        (BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
          (big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))
      (BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))) ⊢
      BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (t1 ++ e2 :: t2 ++ efs)
          (Φs ++ List.replicate efs.length fork_post)) := by
  -- reorder the pieces and rebuild the thread pool
  have hreorder := (sep_reorder_for_rebuild
    (P := state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
    (A := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
    (B := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
    (C := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs (t1.length + 1))
    (D := big_sepL (fun _ ef =>
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)).1
  exact hreorder.trans <|
    sep_mono (PROP := IProp GF) .rfl
      (wptp_rebuild (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) hlen hget)

private theorem wptp_step_post
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (BIBase.later
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
          (BIBase.sep
            (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
      (BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))) ⊢
      BIBase.later
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
            (t1 ++ e2 :: t2 ++ efs)
            (Φs ++ List.replicate efs.length fork_post))) := by
  -- push under `▷` then apply the rebuild lemma inside
  let X :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  let A := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0
  let C := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs (t1.length + 1)
  have hpush := wptp_step_post_push (X := X) (A := A) (C := C)
  have hinner := wptp_step_post_inner (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt)
    hlen hget
  exact hpush.trans (later_mono (PROP := IProp GF) hinner)

private theorem wptp_post_merge
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt nt' : Nat) :
    wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
        s es (Φs ++ List.replicate nt' fork_post) σ ns κs (nt + nt')
      ⊢ wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
        s es Φs σ ns κs nt := by
  -- repackage the existential by merging the replicate suffixes
  refine exists_elim ?_
  intro nt''
  refine exists_intro' (a := nt' + nt'') ?_
  simpa [append_replicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (.rfl : _ ⊢ _)

private theorem wptp_split_fork
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (hlen : es.length = Φs.length) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s (es ++ t2)
        (Φs ++ List.replicate t2.length fork_post) ⊣⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2) := by
  -- split the thread pool into initial and forked components
  have hbody := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es ++ t2) (Φs := Φs ++ List.replicate t2.length fork_post)
  have hsplit := (wptp_body_at_append_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t2 := es) (efs := t2) (Φs := Φs) (k := 0)
    (hlen := by simpa [Nat.zero_add, hlen, List.length_append, List.length_replicate])) .1
  have hleft :
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 ⊢
        wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs :=
    wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (Φs := Φs) hlen
  refine ⟨?_, ?_⟩
  · have hsep :
        wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s (es ++ t2)
            (Φs ++ List.replicate t2.length fork_post) ⊢
          BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2) :=
        hbody.trans hsplit
    exact hsep.trans (sep_mono (PROP := IProp GF) hleft .rfl)
  · have hbody' :
        wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs ⊢
          wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 :=
        wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := es) (Φs := Φs)
    have hcomb :
        BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2) ⊢
          wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (es ++ t2)
            (Φs ++ List.replicate t2.length fork_post) 0 :=
        (wptp_body_at_append_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t2 := es) (efs := t2) (Φs := Φs) (k := 0)
          (hlen := by simpa [Nat.zero_add, hlen, List.length_append, List.length_replicate])).2
    have hlen' :
        (es ++ t2).length =
          (Φs ++ List.replicate t2.length fork_post).length := by
      simp [hlen, List.length_append, List.length_replicate, Nat.add_assoc, Nat.add_left_comm]
    have hwrap :
        wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (es ++ t2)
            (Φs ++ List.replicate t2.length fork_post) 0 ⊢
          wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s (es ++ t2)
            (Φs ++ List.replicate t2.length fork_post) :=
      wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es ++ t2) (Φs := Φs ++ List.replicate t2.length fork_post) hlen'
    exact (sep_mono (PROP := IProp GF) hbody' .rfl).trans (hcomb.trans hwrap)

private theorem wptp_split_take_drop
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (nt' : Nat) (hlen_init : es.length = Φs.length)
    (hlen_t2 : t2.length = Φs.length + nt') :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
        (Φs ++ List.replicate nt' fork_post) ⊣⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2.take es.length) Φs)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post)
          (t2.drop es.length)) := by
  let es' := t2.take es.length -- split the pool at the original length
  let t2' := t2.drop es.length
  have ht2 : t2.length = es.length + nt' := by -- normalize the length equation
    simpa [hlen_init] using hlen_t2
  have hsplit : t2 = es' ++ t2' := by
    simpa [es', t2'] using (List.take_append_drop es.length t2).symm
  have hlen_es : es'.length = es.length := by
    simpa [es'] using length_take_eq (es := es) (t2 := t2) (n := nt') ht2
  have hlen_esΦ : es'.length = Φs.length := by
    simpa [hlen_es, hlen_init]
  have hlen_drop : t2'.length = nt' := by
    simpa [t2'] using length_drop_eq (es := es) (t2 := t2) (n := nt') ht2
  have hsplit_wptp :=
    wptp_split_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es') (t2 := t2') (Φs := Φs) hlen_esΦ
  simpa [hsplit, hlen_drop, es', t2'] using hsplit_wptp

private theorem wptp_post_split_resources
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat)
    (hlen_init : es.length = Φs.length)
    (hlen_t2 : t2.length = Φs.length + nt') :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
          (Φs ++ List.replicate nt' fork_post)) ⊢
      BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.drop es.length).length)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2.take es.length) Φs)
          (big_sepL (fun _ ef =>
            wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post)
            (t2.drop es.length))) := by
  have ht2 : t2.length = es.length + nt' := by
    simpa [hlen_init] using hlen_t2
  have hlen_drop : (t2.drop es.length).length = nt' := by
    simpa using length_drop_eq (es := es) (t2 := t2) (n := nt') ht2
  have hstate :
      state_interp (Λ := Λ) (GF := GF) σ2 n [] nt' ⊢
        state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.drop es.length).length := by
    simpa [hlen_drop]
  have hsplit :=
    wptp_split_take_drop (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs) (nt' := nt') hlen_init hlen_t2
  exact sep_mono (PROP := IProp GF) hstate hsplit.1

private theorem wptp_post_len
    (s : Stuckness) (t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
          (Φs ++ List.replicate nt' fork_post)) ⊢
      BIBase.pure (t2.length = Φs.length + nt') := by
  have hlen := -- extract the length equality from `wptp`
    (sep_elim_r
      (P := state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
        (Φs ++ List.replicate nt' fork_post))).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := t2) (Φs := Φs ++ List.replicate nt' fork_post))
  refine hlen.trans ?_
  refine pure_mono ?_
  intro h
  simpa [List.length_append, List.length_replicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

private noncomputable abbrev adequacy_cont
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- continuation that consumes the final resources to establish `φ`
  BIBase.forall fun es' =>
    BIBase.forall fun t2' =>
      BIBase.wand (BIBase.pure (t2 = es' ++ t2')) <|
      BIBase.wand (BIBase.pure (es'.length = es.length)) <|
      BIBase.wand
        (BIBase.pure (∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2)) <|
      BIBase.wand (state_interp (Λ := Λ) (GF := GF) σ2 n [] t2'.length) <|
      BIBase.wand
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es' Φs) <|
      BIBase.wand
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2') <|
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)

private noncomputable abbrev adequacy_pre
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- precondition: initial state interpretation, pool WP, and continuation
  BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (BIBase.sep
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
      (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2)
        (n := n) (Φs := Φs) (φ := φ)))

private noncomputable abbrev adequacy_inv
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop) : IProp GF :=
  -- existentially package the postconditions for the thread pool
  BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)

private noncomputable abbrev adequacy_post
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop) : IProp GF :=
  -- postcondition: final state interpretation, post WPs, and continuation
  BIBase.sep
    (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
      s t2 Φs σ2 n [] 0)
    (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))

private theorem adequacy_cont_drop
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ1 : Λ.state) (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (φ : Prop) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
          (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))) ⊢
      BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs) := by
  -- discard the continuation from the precondition
  exact sep_mono (PROP := IProp GF) .rfl
    (sep_elim_l
      (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
      (Q := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)))

private theorem wptp_len_from_pre
    (s : Stuckness) (es : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ1 : Λ.state) (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state)
    (n : Nat) (φ : Prop) :
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (BIBase.sep
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
          (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))) ⊢
      BIBase.pure (es.length = Φs.length) := by
  -- extract the length equality hidden in `wptp`
  exact (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (Q := BIBase.sep
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
      (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)))).trans
    ((sep_elim_l (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)
      (Q := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (Φs := Φs)))

private theorem wptp_preservation_core
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (Φs : List (Λ.val → IProp GF))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs σ2 n [] 0) := by
  -- specialize preservation to an empty fork suffix
  simpa [List.append_nil] using
    wptp_preservation (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (n := n) (es1 := es) (es2 := t2) (κs := κs) (κs' := [])
      (σ1 := σ1) (ns := 0) (σ2 := σ2) (nt := 0) (Φs := Φs) hsteps

private theorem wptp_preservation_frame
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) (φ : Prop)
  (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (adequacy_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)) := by
  let cont := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F) -- frame continuation
    (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  let post := wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs σ2 n [] 0
  have hmono :
      BIBase.sep
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs)) cont ⊢
        BIBase.sep
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n post) cont :=
    sep_mono (PROP := IProp GF)
      (wptp_preservation_core (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (κs := κs) (t2 := t2) (σ2 := σ2)
        (n := n) (Φs := Φs) hsteps) .rfl
  exact (sep_assoc (P := state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
    (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs) (R := cont)).2.trans
    (hmono.trans
      (step_fupdN_frame_r (Λ := Λ) (GF := GF) (M := M) (F := F) (n := n)
        (P := post) (Q := cont)))

private theorem apply_cont
    (s : Stuckness) (es t2 es' t2' : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (hcont : adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    (hsplit : t2 = es' ++ t2')
    (hlen_es : es'.length = es.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :
    BIBase.sep hcont
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 n [] t2'.length)
          (BIBase.sep
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es' Φs)
            (big_sepL (fun _ ef =>
              wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) t2')))
      ⊢ uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  iintro ⟨Hcont, Hσ, Hwp, Hfork⟩ -- apply the stored continuation
  ispecialize Hcont $$ es'
  ispecialize Hcont $$ t2'
  ispecialize Hcont $$ []
  · ipure_intro; exact hsplit
  ispecialize Hcont $$ []
  · ipure_intro; exact hlen_es
  ispecialize Hcont $$ []
  · ipure_intro; exact hns
  ispecialize Hcont $$ Hσ
  ispecialize Hcont $$ Hwp
  ispecialize Hcont $$ Hfork
  iexact Hcont

private theorem wptp_post_apply_core
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n nt' : Nat) (φ : Prop)
    (hcont : adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    (hlen_init : es.length = Φs.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2)
    (hlen_t2 : t2.length = Φs.length + nt') :
    BIBase.sep hcont
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ2 n [] nt')
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
            (Φs ++ List.replicate nt' fork_post))) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  let es' := t2.take es.length -- isolate the original threads
  let t2' := t2.drop es.length
  have hsplit : t2 = es' ++ t2' := by
    simpa [es', t2'] using (List.take_append_drop es.length t2).symm
  have hlen_es : es'.length = es.length := by
    have ht2 : t2.length = es.length + nt' := by simpa [hlen_init] using hlen_t2
    simpa [es'] using length_take_eq (es := es) (t2 := t2) (n := nt') ht2
  have hres :=
    wptp_post_split_resources (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs)
      (σ2 := σ2) (n := n) (nt' := nt') hlen_init hlen_t2
  have happly :=
    apply_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (es' := es') (t2' := t2') (Φs := Φs)
      (σ2 := σ2) (n := n) (φ := φ) hcont hsplit hlen_es hns
  exact (sep_mono (PROP := IProp GF) .rfl hres).trans happly

private theorem wptp_post_apply
    (s : Stuckness) (es t2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (hcont : adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    (hlen_init : es.length = Φs.length)
    (hns : ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :
    BIBase.sep hcont
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs σ2 n [] 0) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  refine (sep_exists_l (P := hcont) (Ψ := fun nt' => -- open the post-state existential
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ2 n [] (0 + nt'))
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s t2
        (Φs ++ List.replicate nt' fork_post)))).1.trans ?_
  refine exists_elim ?_
  intro nt'
  have hlenP :=
    wptp_post_len (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t2 := t2) (Φs := Φs) (σ2 := σ2) (n := n) (nt' := nt')
  refine pure_elim (PROP := IProp GF)
    (φ := t2.length = Φs.length + nt') hlenP ?_
  intro hlen_t2
  exact wptp_post_apply_core (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (t2 := t2) (Φs := Φs)
    (σ2 := σ2) (n := n) (nt' := nt') (φ := φ) hcont hlen_init hns hlen_t2

private theorem wp_progress_drop_cont
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := .notStuck) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ))) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
            BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)) := by
  intro W -- drop the continuation to obtain the plain pool WP
  refine (Hwp W).trans ?_
  refine fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ))
    (Q := BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
      BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)) ?_
  refine exists_elim ?_; intro Φs
  exact adequacy_cont_drop (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := .notStuck) (es := es) (Φs := Φs) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)

private theorem wp_progress_from_strong
    (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    ∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2 := by
  intro e2 hs hemem -- reduce to the non-stuck case and reuse `wp_progress`
  cases s with
  | notStuck =>
      have hwp' :=
        wp_progress_drop_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (es := es) (σ1 := σ1) (κs := κs) (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp
      exact wp_progress (Λ := Λ) (GF := GF) (M := M) (F := F)
        (n := n) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (e2 := e2) hwp' hsteps hemem
  | maybeStuck =>
      cases hs

/-! ## FUpd Helpers -/

private theorem fupd_intro (E : Iris.Set Positive) (P : IProp GF) :
    P ⊢ fupd' (Λ := Λ) (M := M) (F := F) E E P := by
  -- introduce a nested update and then collapse it
  have hsubset : Subset E E := by
    intro _ h; exact h
  have hintro :=
    fupd_intro_mask (W := W)
      (M := M) (F := F) (E1 := E) (E2 := E) hsubset (P := P)
  exact hintro.trans <|
    fupd_trans (W := W)
      (M := M) (F := F) (E1 := E) (E2 := E) (E3 := E) (P := P)

private theorem fupd_intro_univ_empty (P : IProp GF) :
    P ⊢ fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty P := by
  -- open to the empty mask, shrink, then compose
  have hsubset : Subset maskEmpty Iris.Set.univ := by
    intro _ h; exact False.elim h
  have hopen :=
    fupd_intro_mask (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty) hsubset (P := P)
  have hshrink :
      fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ P ⊢
        fupd' (Λ := Λ) (M := M) (F := F) maskEmpty maskEmpty P :=
    fupd_plain_mask (W := W)
      (M := M) (F := F) (E1 := maskEmpty) (E2 := Iris.Set.univ) hsubset (P := P)
  have hmono :
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty
          (fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ P) ⊢
        fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty
          (fupd' (Λ := Λ) (M := M) (F := F) maskEmpty maskEmpty P) :=
    fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (P := fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ P)
      (Q := fupd' (Λ := Λ) (M := M) (F := F) maskEmpty maskEmpty P) hshrink
  exact hopen.trans (hmono.trans <|
    fupd_trans (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
      (E3 := maskEmpty) (P := P))

private noncomputable def step_fupdN (n : Nat) (P : IProp GF) : IProp GF :=
  -- iterate a single `fupd`/`▷` layer `n` times
  match n with
  | 0 => P
  | n + 1 =>
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ <|
        BIBase.later (step_fupdN n P)

private theorem step_fupdN_mono (n : Nat) {P Q : IProp GF} (h : P ⊢ Q) :
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n Q := by
  -- recurse on `n`, pushing entailment under fupd/later
  induction n with
  | zero =>
      simpa [step_fupdN] using h
  | succ n ih =>
      have hl :
          BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) ⊢
            BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n Q) :=
        later_mono (PROP := IProp GF) ih
      simpa [step_fupdN] using
        (fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P))
          (Q := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n Q)) hl)

private theorem step_fupdN_frame_r_later (n : Nat) (P Q : IProp GF)
    (ih :
      BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) Q ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n (BIBase.sep P Q)) :
    BIBase.sep
        (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P)) Q ⊢
      BIBase.later
        (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n (BIBase.sep P Q)) := by
  have hsep : -- move `later` across `sep` before applying the induction hypothesis
      BIBase.sep
          (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P)) Q ⊢
        BIBase.later
          (BIBase.sep
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) Q) :=
    (sep_mono (PROP := IProp GF) .rfl later_intro).trans
      (later_sep (PROP := IProp GF)).2
  exact hsep.trans (later_mono (PROP := IProp GF) ih)

private theorem step_fupdN_frame_r (n : Nat) (P Q : IProp GF) :
    BIBase.sep (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) Q ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n (BIBase.sep P Q) := by
  induction n with -- push framing under each `step_fupdN` layer
  | zero =>
      simpa [step_fupdN]
  | succ n ih =>
      have hinside :=
        step_fupdN_frame_r_later (Λ := Λ) (GF := GF) (M := M) (F := F)
          (n := n) (P := P) (Q := Q) ih
      have hframe :=
        fupd_frame_r (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P))
          (Q := Q)
      have hmono :=
        fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.sep
            (BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P)) Q)
          (Q := BIBase.later
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n (BIBase.sep P Q)))
          hinside
      simpa [step_fupdN] using hframe.trans hmono

private theorem step_fupdN_soundness (P : IProp GF) (n : Nat)
    (h : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) :
    (BIBase.emp : IProp GF) ⊢ P := by
  -- peel off `fupd`/`▷` layers, then apply the induction hypothesis
  induction n with
  | zero =>
      simpa [step_fupdN] using (h W)
  | succ n ih =>
      have hlate :
          (BIBase.emp : IProp GF) ⊢
            BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) := by
        have h' :
            ∀ W' : WsatGS GF,
              (BIBase.emp : IProp GF) ⊢
                uPred_fupd (M := M) (F := F) W' Iris.Set.univ Iris.Set.univ
                  (BIBase.later
                    (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P)) := by
          intro W'
          simpa [step_fupdN] using (h W')
        exact fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
          (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later
            (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P)) h'
      have htrue :
          (True : IProp GF) ⊢
            BIBase.later (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P) :=
        (true_emp (PROP := IProp GF)).1.trans hlate
      have hpred :
          (True : IProp GF) ⊢
            step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P :=
        UPred.later_soundness htrue
      have hpred' :
          (BIBase.emp : IProp GF) ⊢
            step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n P :=
        (true_emp (PROP := IProp GF)).2.trans hpred
      exact ih (h := fun _ => hpred')

/-! ## WP Step Helpers -/

private noncomputable abbrev wp_step_cont (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (κ : List Λ.observation) (Φ : Λ.val → IProp GF)
    (ns : Nat) (κs : List Λ.observation) (nt : Nat) : IProp GF :=
  -- the recursive continuation of the step case in `wp_pre`
  BIBase.forall fun e2 : Λ.expr =>
    BIBase.forall fun σ2 : Λ.state =>
      BIBase.forall fun efs : List Λ.expr =>
        BIBase.wand (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs)) <|
          fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ <|
            BIBase.later <|
              BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
                (BIBase.sep
                  (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                  (big_sepL (fun _ ef =>
                    wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))

private theorem adq_wp_step_pre (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) (hv : Λ.to_val e1 = none) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    ⊢ fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty
        (BIBase.sep (BIBase.pure (stuckness_pred s e1 σ1))
          (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
            (ns := ns) (κs := κs) (nt := nt))) := by
  -- unfold the WP and specialize the step case
  have hwp :
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ ⊢
        wp_pre (Λ := Λ) (GF := GF) (M := M) (F := F) s
          (wp (M := M) (F := F) (Λ := Λ) s) Iris.Set.univ e1 Φ :=
    (wp_unfold (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (E := Iris.Set.univ) (e := e1) (Φ := Φ)).1
  refine (sep_mono_r hwp).trans ?_
  -- specialize the quantified state parameters, then apply the wand
  simp [wp_pre, hv, wp_pre_step, wp_step_cont]
  refine (sep_mono_r ?_).trans (wand_elim_r (PROP := IProp GF))
  refine (forall_elim (PROP := IProp GF) (Ψ := fun σ => _) σ1).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun ns => _) ns).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun κ => _) κ).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun κs => _) κs).trans ?_
  exact (forall_elim (PROP := IProp GF) (Ψ := fun nt => _) nt)

private theorem wp_step_cont_wand (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF) :
    wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt) ⊢
      BIBase.wand (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs))
        (fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ
          (BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep
                (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                (big_sepL (fun _ ef =>
                  wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))) := by
  -- specialize the nested `∀` binders
  refine (forall_elim (PROP := IProp GF) (Ψ := fun e2 => _) e2).trans ?_
  refine (forall_elim (PROP := IProp GF) (Ψ := fun σ2 => _) σ2).trans ?_
  exact (forall_elim (PROP := IProp GF) (Ψ := fun efs => _) efs)

private theorem wp_step_cont_pure (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt) ⊢
      BIBase.sep (BIBase.pure (Λ.prim_step e1 σ1 κ e2 σ2 efs))
        (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
          (ns := ns) (κs := κs) (nt := nt)) := by
  -- insert the pure step using `True ∗ P`
  exact (true_sep_2 (PROP := IProp GF)
    (P := wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
      (ns := ns) (κs := κs) (nt := nt))).trans
    (sep_mono (pure_intro hstep) .rfl)

private theorem adq_wp_step_cont (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep (BIBase.pure (stuckness_pred s e1 σ1))
      (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
        (ns := ns) (κs := κs) (nt := nt))
    ⊢ fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ
        (BIBase.later
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))) := by
  -- drop the stuckness predicate and apply the step continuation
  refine (sep_elim_r (P := BIBase.pure _) (Q := wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
    (ns := ns) (κs := κs) (nt := nt))).trans ?_
  have hwand := wp_step_cont_wand (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ)
  have hpure := wp_step_cont_pure (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
  exact hpure.trans (sep_mono .rfl hwand) |>.trans (wand_elim_r (PROP := IProp GF))

/-! ## Single Step -/

/-- A single primitive step preserves the weakest precondition.
Given a step `e1 → e2` producing new threads `efs`, the state
interpretation and WP transfer to the post-state.
Coq: `wp_step` in `adequacy.v`. -/
theorem adq_wp_step (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state) (ns : Nat)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (e2 : Λ.expr) (σ2 : Λ.state) (efs : List Λ.expr) (nt : Nat)
    (Φ : Λ.val → IProp GF)
    (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.sep
            (IrisGS.state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef
                  (IrisGS.fork_post (Λ := Λ) (GF := GF))) efs)))) :=
  by
    -- unfold the WP step case and apply the concrete primitive step
    have hv : Λ.to_val e1 = none :=
      val_stuck (Λ := Λ) (e := e1) (σ := σ1) (κ := κ) (e' := e2) (σ' := σ2) (efs := efs) hstep
    have hpre := adq_wp_step_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt)
      (Φ := Φ) hv
    have hcont := adq_wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
      (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
    -- lift the continuation through the outer update, then compose
    have hmono :
        fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty
            (BIBase.sep
              (BIBase.pure (stuckness_pred s e1 σ1))
              (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
                (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
                (ns := ns) (κs := κs) (nt := nt)) ) ⊢
          fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ maskEmpty
            (fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ
              (BIBase.later
                (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
                  (BIBase.sep
                    (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                    (big_sepL (fun _ ef =>
                      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))) :=
      fupd_mono (W := W)
        (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
        (P := BIBase.sep
          (BIBase.pure (stuckness_pred s e1 σ1))
          (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (e1 := e1) (σ1 := σ1) (κ := κ) (Φ := Φ)
            (ns := ns) (κs := κs) (nt := nt)))
        (Q := fupd' (Λ := Λ) (M := M) (F := F) maskEmpty Iris.Set.univ
          (BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep
                (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                (big_sepL (fun _ ef =>
                  wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))) hcont
    have htrans :=
      fupd_trans (W := W)
        (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
        (E3 := Iris.Set.univ) (P := BIBase.later
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
    exact hpre.trans (hmono.trans htrans)

/-! ## Wptp Step Helpers -/

private theorem wptp_step_split
    (s : Stuckness) (t1 t2 : List Λ.expr) (e1 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation) (nt : Nat)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t1 ++ e1 :: t2) Φs 0) ⊢
      BIBase.sep
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ))
        (BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (t1.length + 1))) := by
  -- split the middle element and swap to isolate the stepped thread
  let A := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0
  let B := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ
  let C := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs (t1.length + 1)
  have hget0 : Φs[0 + t1.length]? = some Φ := by
    -- align the index with the explicit `0 + t1.length`
    simpa [Nat.zero_add] using hget
  have hsplit := (wptp_body_at_middle (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (e := e1) (Φs := Φs) (k := 0)
    (Φ := Φ) hget0).1
  have hbody :
      BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s (t1 ++ e1 :: t2) Φs 0) ⊢
        BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
              (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
                s t2 Φs (0 + t1.length + 1)))) :=
    sep_mono (PROP := IProp GF)
      (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (P' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t1 ++ e1 :: t2) Φs 0)
      (Q := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (Q' := BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (BIBase.sep
          (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (0 + t1.length + 1))))
      BIBase.Entails.rfl hsplit
  have hbody' :
      BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s (t1 ++ e1 :: t2) Φs 0) ⊢
        BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
          (BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ)
              (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
                s t2 Φs (t1.length + 1)))) := by
    -- normalize the offset arithmetic in the tail
    simpa [Nat.zero_add] using hbody
  have hassoc := (sep_assoc (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := A) (R := BIBase.sep B C)).2
  have hswap := (sep_sep_sep_comm (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
    (Q := A) (R := B) (S := C)).1
  exact hbody'.trans (hassoc.trans hswap)

private theorem wptp_step_apply
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs) :
    BIBase.sep
      (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1 Φ))
      (BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.sep
          (BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (BIBase.sep
                (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
                (big_sepL (fun _ ef =>
                  wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
          (BIBase.sep
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              s t2 Φs (t1.length + 1)))) := by
  -- step the focused thread and frame the remaining pool
  let X :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
      (BIBase.sep
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  have hwp := adq_wp_step (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e1 := e1) (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs)
    (e2 := e2) (σ2 := σ2) (efs := efs) (nt := nt) (Φ := Φ) hstep
  exact (sep_mono (PROP := IProp GF) hwp .rfl).trans
    (fupd_frame_r (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.later X)
      (Q := BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))))

private theorem wptp_step_frame
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e1 e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (σ1 σ2 : Λ.state) (ns : Nat) (κ : List Λ.observation) (κs : List Λ.observation)
    (nt : Nat) (hstep : Λ.prim_step e1 σ1 κ e2 σ2 efs)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t1 ++ e1 :: t2) Φs 0) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (t1 ++ e2 :: t2 ++ efs)
              (Φs ++ List.replicate efs.length fork_post)))) := by
  -- split the middle thread, step it, then rebuild the pool
  have hsplit := wptp_step_split (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (e1 := e1) (Φs := Φs) (Φ := Φ)
    (σ1 := σ1) (ns := ns) (κ := κ) (κs := κs) (nt := nt) hget
  have happly := wptp_step_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
    (κ := κ) (κs := κs) (nt := nt) hstep
  have hpost := wptp_step_post (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) (σ2 := σ2) (ns := ns) (κs := κs) (nt := nt) hlen hget
  have hmono :=
    fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (BIBase.later
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (BIBase.sep
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
              (big_sepL (fun _ ef =>
                wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))))
        (BIBase.sep
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
          (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            s t2 Φs (t1.length + 1))))
      (Q := BIBase.later
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
            (t1 ++ e2 :: t2 ++ efs)
            (Φs ++ List.replicate efs.length fork_post)))) hpost
  exact hsplit.trans (happly.trans hmono)

/-! ## Thread Pool Step -/

/-- A step of the thread pool preserves the thread pool WP.
Coq: `wptp_step` in `adequacy.v`. -/
private theorem wptp_step_len_false (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hlen : es1.length ≠ Φs.length) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- discharge the inconsistent-length case via pure elimination
  let Q :=
    BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs)
  have hlenP : Q ⊢ BIBase.pure (es1.length = Φs.length) :=
    (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs)).trans
      (wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F) (s := s) (es := es1) (Φs := Φs))
  have hkill : es1.length = Φs.length → Q ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es2 Φs σ2 (ns + 1) κs nt)) := by
    intro h; exact (False.elim (hlen h))
  exact pure_elim (φ := es1.length = Φs.length) hlenP hkill

private theorem wptp_step_len_true (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (Λ := Λ) (es1, σ1) κ (es2, σ2))
    (hlen : es1.length = Φs.length) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es1 Φs) ⊢
      fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- focus the stepping thread, then rebuild the pool and add the existential
  classical
  cases hstep with
  | step_atomic e1 σ1' e2 σ2' efs t1 t2 _ hprim =>
      have hlen' : Φs.length = t1.length + t2.length + 1 := by
        simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen.symm
      rcases wptp_lookup_middle (t1 := t1) (t2 := t2) (Φs := Φs) hlen' with ⟨Φ, hget⟩
      have hbody := wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := t1 ++ e1 :: t2) (Φs := Φs)
      have hframe := wptp_step_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e1 := e1) (e2 := e2)
        (Φs := Φs) (Φ := Φ) (σ1 := σ1) (σ2 := σ2) (ns := ns)
        (κ := κ) (κs := κs) (nt := nt) hprim hlen' hget
      have hmain := (sep_mono (PROP := IProp GF) .rfl hbody).trans hframe
      have hmain' :
          BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
                (t1 ++ [e1] ++ t2) Φs) ⊢
            fupd' (Λ := Λ) (M := M) (F := F) Iris.Set.univ Iris.Set.univ
              (BIBase.later
                (BIBase.sep
                  (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
                  (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
                    (t1 ++ [e2] ++ t2 ++ efs)
                    (Φs ++ List.replicate efs.length fork_post)))) := by
        simpa [List.singleton_append, List.append_assoc] using hmain
      have hex : BIBase.later
          (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
              (t1 ++ e2 :: t2 ++ efs)
              (Φs ++ List.replicate efs.length fork_post))) ⊢
          BIBase.later (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s (t1 ++ e2 :: t2 ++ efs) Φs σ2 (ns + 1) κs nt) := by
        refine later_mono ?_
        refine exists_intro' (a := efs.length) ?_
        simpa [Nat.add_comm] using (.rfl : _ ⊢ _)
      have hex' :
          BIBase.later
              (BIBase.sep
                (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
                (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
                  (t1 ++ [e2] ++ t2 ++ efs)
                  (Φs ++ List.replicate efs.length fork_post))) ⊢
            BIBase.later
              (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
                s (t1 ++ [e2] ++ t2 ++ efs) Φs σ2 (ns + 1) κs nt) := by
        simpa [List.singleton_append, List.append_assoc] using hex
      exact hmain'.trans <|
        fupd_mono (W := W)
          (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
          (P := BIBase.later
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ2 (ns + 1) κs (efs.length + nt))
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s
                (t1 ++ [e2] ++ t2 ++ efs)
                (Φs ++ List.replicate efs.length fork_post))))
          (Q := BIBase.later
            (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
              s (t1 ++ [e2] ++ t2 ++ efs) Φs σ2 (ns + 1) κs nt)) hex'

theorem wptp_step' (s : Stuckness) (es1 es2 : List Λ.expr)
    (κ : List Λ.observation) (κs : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hstep : step (es1, σ1) κ (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κ ++ κs) nt)
      (wptp (M := M) (F := F) (Λ := Λ) s es1 Φs)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ Iris.Set.univ
        (BIBase.later
          (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
            s es2 Φs σ2 (ns + 1) κs nt)) := by
  -- split on length consistency, then dispatch to the appropriate lemma
  classical
  by_cases hlen : es1.length = Φs.length
  · simpa [state_interp] using
      wptp_step_len_true (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hstep hlen
  · simpa [state_interp] using
      wptp_step_len_false (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es1 := es1) (es2 := es2) (κ := κ) (κs := κs)
        (σ1 := σ1) (ns := ns) (σ2 := σ2) (nt := nt)
        (Φs := Φs) hlen

/-! ## Multi-Step Preservation -/

/-- Multi-step preservation: after `n` steps, the thread pool WP
and state interpretation are preserved (modulo fupd and later).
Coq: `wptp_preservation` in `adequacy.v`. -/
theorem wptp_preservation (s : Stuckness) (n : Nat)
    (es1 es2 : List Λ.expr) (κs κs' : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF))
    (hsteps : nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2)) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ1 ns (κs ++ κs') nt)
      (wptp (M := M) (F := F) (Λ := Λ) s es1 Φs)
    ⊢ step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          s es2 Φs σ2 (n + ns) κs' nt) := by
  -- induct on the execution trace, generalizing `ns`/`nt`/`Φs`
  induction n generalizing es1 es2 κs σ1 σ2 Φs ns nt with
  | zero =>
      cases hsteps with
      | nsteps_refl ρ =>
          refine exists_intro' (a := 0) ?_
          simp [step_fupdN, wptp_post, List.append_nil, Nat.add_comm, Nat.add_assoc]
  | succ n ih =>
      cases hsteps with
      | nsteps_l n' ρ1 ρ2 ρ3 κ κs_tail hstep hrest =>
          rcases ρ2 with ⟨es_mid, σ_mid⟩
          have hstep' :=
            (by
              simpa [List.append_assoc] using
                wptp_step' (Λ := Λ) (GF := GF) (M := M) (F := F)
                  (s := s) (es1 := es1) (es2 := es_mid) (κ := κ)
                  (κs := κs_tail ++ κs') (σ1 := σ1) (ns := ns)
                  (σ2 := σ_mid) (nt := nt) (Φs := Φs) hstep)
          have hmono :
              BIBase.later
                (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
                  s es_mid Φs σ_mid (ns + 1) (κs_tail ++ κs') nt) ⊢
                BIBase.later
                  (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
                    (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
                      s es2 Φs σ2 (n + (ns + 1)) κs' nt)) := by
            refine later_mono ?_
            refine exists_elim ?_
            intro nt'
            have ih' :=
              ih (es1 := es_mid) (es2 := es2) (κs := κs_tail)
                (σ1 := σ_mid) (σ2 := σ2)
                (Φs := Φs ++ List.replicate nt' fork_post)
                (hsteps := hrest) (ns := ns + 1) (nt := nt + nt')
            have hmerge :=
              wptp_post_merge (Λ := Λ) (GF := GF) (M := M) (F := F)
                (s := s) (es := es2) (Φs := Φs) (σ := σ2)
                (ns := n + (ns + 1)) (κs := κs') (nt := nt) (nt' := nt')
            exact (by
              simpa [List.append_assoc, Nat.add_assoc] using
                ih'.trans (step_fupdN_mono (Λ := Λ) (GF := GF) (M := M) (F := F) n hmerge))
          have hmono' :=
            fupd_mono (W := W)
              (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
              (P := BIBase.later
                (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
                  s es_mid Φs σ_mid (ns + 1) (κs_tail ++ κs') nt))
              (Q := BIBase.later
                (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
                  (wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
                    s es2 Φs σ2 (n + (ns + 1)) κs' nt))) hmono
          simpa [fupd', step_fupdN, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using hstep'.trans hmono'

/-! ## Wptp Progress -/

private theorem wptp_post_not_stuck
    (es2 : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (σ2 : Λ.state) (ns : Nat) (κs : List Λ.observation) (nt : Nat)
    (e2 : Λ.expr) (hemem : e2 ∈ es2) :
    wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
        .notStuck es2 Φs σ2 ns κs nt ⊢
      uPred_fupd (M := M) (F := F) W
        Iris.Set.univ maskEmpty (BIBase.pure (not_stuck e2 σ2)) := by
  -- open the existential and extract the WP for `e2`
  classical
  refine exists_elim ?_
  intro nt'
  have hlen :
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post) ⊢
        BIBase.pure (es2.length = (Φs ++ List.replicate nt' fork_post).length) :=
    wptp_length (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (es := es2) (Φs := Φs ++ List.replicate nt' fork_post)
  have hbody :
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
          (Φs ++ List.replicate nt' fork_post) ⊢
        wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          .notStuck es2 (Φs ++ List.replicate nt' fork_post) 0 :=
    wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (es := es2) (Φs := Φs ++ List.replicate nt' fork_post)
  refine (pure_elim (PROP := IProp GF)
    (φ := es2.length = (Φs ++ List.replicate nt' fork_post).length) ?_ ?_)
  · exact (sep_elim_r (P := state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
      (Q := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
        (Φs ++ List.replicate nt' fork_post))).trans hlen
  · intro hlen'
    rcases mem_split hemem with ⟨t1, t2, ht⟩
    have hlen_es : es2.length = t1.length + 1 + t2.length := by
      simpa [ht, List.length_append, List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hlt_es : t1.length < es2.length := by
      have hlt : t1.length < t1.length + 1 := Nat.lt_succ_self _
      have hle : t1.length + 1 ≤ t1.length + 1 + t2.length := Nat.le_add_right _ _
      exact Nat.lt_of_lt_of_le hlt (by simpa [hlen_es] using hle)
    have hlt : t1.length < (Φs ++ List.replicate nt' fork_post).length := by
      simpa [hlen'] using hlt_es
    let Φ := (Φs ++ List.replicate nt' fork_post).get ⟨t1.length, hlt⟩
    have hget :
        (Φs ++ List.replicate nt' fork_post)[t1.length]? = some Φ :=
      get?_eq_some_of_lt (l := Φs ++ List.replicate nt' fork_post) (i := t1.length) hlt
    have hmid :=
      (wptp_body_at_middle (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := .notStuck) (t1 := t1) (t2 := t2) (e := e2)
        (Φs := Φs ++ List.replicate nt' fork_post) (k := 0) (Φ := Φ)
        (by simpa [ht] using hget)).1
    have hwp :
        wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
            (Φs ++ List.replicate nt' fork_post) ⊢
          wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ := by
      have hsep := hbody.trans (by simpa [ht] using hmid)
      exact hsep.trans
        (sep_elim_r (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          .notStuck t1 (Φs ++ List.replicate nt' fork_post) 0)
          (Q := BIBase.sep
            (wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ)
            (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
              .notStuck t2 (Φs ++ List.replicate nt' fork_post) (t1.length + 1)))).trans
        (sep_elim_l (P := wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ)
          (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
            .notStuck t2 (Φs ++ List.replicate nt' fork_post) (t1.length + 1)))
    have hframe :
        BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
            (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es2
              (Φs ++ List.replicate nt' fork_post)) ⊢
          BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ2 ns κs (nt + nt'))
            (wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e2 Φ) :=
      sep_mono (PROP := IProp GF) .rfl hwp
    exact hframe.trans
      (wp_not_stuck' (Λ := Λ) (GF := GF) (M := M) (F := F)
        (e := e2) (σ := σ2) (ns := ns) (κs := κs) (nt := nt + nt') (Φ := Φ))

private theorem wptp_progress (n : Nat)
    (es1 es2 : List Λ.expr) (κs κs' : List Λ.observation)
    (σ1 : Λ.state) (ns : Nat) (σ2 : Λ.state) (nt : Nat)
    (Φs : List (Λ.val → IProp GF)) (e2 : Λ.expr)
    (hsteps : nsteps (Λ := Λ) n (es1, σ1) κs (es2, σ2)) (hemem : e2 ∈ es2) :
    BIBase.sep
      (state_interp (Λ := Λ) (GF := GF) σ1 ns (κs ++ κs') nt)
      (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es1 Φs) ⊢
    step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
        (BIBase.pure (not_stuck e2 σ2))) := by
  -- preserve the thread pool, then extract not-stuck for the chosen thread
  have hpres :=
    wptp_preservation (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := .notStuck) (n := n) (es1 := es1) (es2 := es2)
      (κs := κs) (κs' := κs') (σ1 := σ1) (ns := ns)
      (σ2 := σ2) (nt := nt) (Φs := Φs) hsteps
  have hmono :
      wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F)
          .notStuck es2 Φs σ2 (n + ns) κs' nt ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2)) :=
    wptp_post_not_stuck (Λ := Λ) (GF := GF) (M := M) (F := F)
      (es2 := es2) (Φs := Φs) (σ2 := σ2) (ns := n + ns)
      (κs := κs') (nt := nt) (e2 := e2) hemem
  exact hpres.trans (step_fupdN_mono (Λ := Λ) (GF := GF) (M := M) (F := F) n hmono)

private theorem wp_progress (n : Nat)
    (es : List Λ.expr) (σ1 : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (e2 : Λ.expr)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
            BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
              (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hemem : e2 ∈ t2) :
    not_stuck e2 σ2 := by
  -- run preservation and soundness to extract not-stuck at the meta-level
  have hmono :
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
            (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
              (BIBase.pure (not_stuck e2 σ2)))) := by
    refine (Hwp W).trans ?_
    refine fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.«exists» fun (Φs : List (Λ.val → IProp GF)) =>
        BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
          (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) .notStuck es Φs))
      (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2)))) ?_
    refine exists_elim ?_
    intro Φs
    exact wptp_progress (Λ := Λ) (GF := GF) (M := M) (F := F)
      (n := n) (es1 := es) (es2 := t2) (κs := κs) (κs' := [])
      (σ1 := σ1) (ns := 0) (σ2 := σ2) (nt := 0)
      (Φs := Φs) (e2 := e2) hsteps hemem
  have hstep :
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
            (BIBase.pure (not_stuck e2 σ2))) :=
    fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
      (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2)))) (h := fun _ => hmono)
  have hplain :
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
          (BIBase.pure (not_stuck e2 σ2)) :=
    step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
        (BIBase.pure (not_stuck e2 σ2))) (n := n) (h := fun _ => hstep)
  have htrue :
      (True : IProp GF) ⊢ BIBase.pure (not_stuck e2 σ2) :=
    (true_emp (PROP := IProp GF)).1.trans <|
      fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
        (E1 := Iris.Set.univ) (E2 := maskEmpty) (P := BIBase.pure (not_stuck e2 σ2))
        (h := fun _ => hplain)
  exact UPred.pure_soundness (P := not_stuck e2 σ2) htrue

/-! ## Not Stuck -/

/-- WP at `NotStuck` stuckness implies the expression is not stuck.
Coq: `wp_not_stuck` in `adequacy.v`. -/
theorem wp_not_stuck' (e : Λ.expr) (σ : Λ.state) (ns : Nat)
    (κs : List Λ.observation) (nt : Nat)
    (Φ : Λ.val → IProp GF) :
    BIBase.sep
      (IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
      (wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)
    ⊢ uPred_fupd (M := M) (F := F) W
        Iris.Set.univ (fun _ => False) (BIBase.pure (not_stuck e σ)) :=
  by
    -- split on the value case and use `adq_wp_step_pre` otherwise
    classical
    cases hto : Λ.to_val e with
    | some v =>
        have hns : not_stuck e σ := Or.inl ⟨v, hto⟩
        have hpure :
            wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ ⊢
              BIBase.pure (not_stuck e σ) := pure_intro hns
        exact (sep_elim_r
          (P := IrisGS.state_interp (Λ := Λ) (GF := GF) σ ns κs nt)
          (Q := wp (M := M) (F := F) (Λ := Λ) .notStuck Iris.Set.univ e Φ)).trans <|
          hpure.trans (fupd_intro_univ_empty (Λ := Λ) (GF := GF) (M := M) (F := F)
            (P := BIBase.pure (not_stuck e σ)))
    | none =>
        have hpre := adq_wp_step_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := .notStuck) (e1 := e) (σ1 := σ) (ns := ns)
          (κ := []) (κs := κs) (nt := nt) (Φ := Φ) hto
        have hmono :
            BIBase.sep (BIBase.pure (reducible e σ))
                (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
                  (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
                  (Φ := Φ) (ns := ns) (κs := κs) (nt := nt)) ⊢
              BIBase.pure (not_stuck e σ) := by
          -- drop the continuation and lift reducibility to not-stuck
          exact (sep_elim_l (P := BIBase.pure (reducible e σ))
            (Q := wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
              (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
              (Φ := Φ) (ns := ns) (κs := κs) (nt := nt))).trans
            (pure_mono fun h => Or.inr h)
        exact hpre.trans <|
          fupd_mono (W := W)
            (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := maskEmpty)
            (P := BIBase.sep (BIBase.pure (reducible e σ))
              (wp_step_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
                (s := .notStuck) (e1 := e) (σ1 := σ) (κ := [])
                (Φ := Φ) (ns := ns) (κs := κs) (nt := nt)))
            (Q := BIBase.pure (not_stuck e σ)) hmono

/-! ## Adequate -/

/-- The adequacy record: a program `e1` starting in state `σ1` is adequate
if (1) whenever it reduces to a value, the postcondition holds, and
(2) it is never stuck (when `s = NotStuck`).
Coq: `adequate` record in `adequacy.v`. -/
structure Adequate (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (φ : Λ.val → Λ.state → Prop) : Prop where
  /-- If the main thread terminates with value `v2` in state `σ2`, then `φ v2 σ2`. -/
  adequate_result : ∀ t2 σ2 v2,
    rtc (erased_step (Λ := Λ)) ([e1], σ1) (Λ.of_val v2 :: t2, σ2) →
    φ v2 σ2
  /-- If `s = NotStuck`, every reachable expression is not stuck. -/
  adequate_not_stuck : ∀ t2 σ2 e2,
    s = .notStuck →
    rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2) →
    e2 ∈ t2 → not_stuck e2 σ2

/-- Alternative characterization of adequacy.
Coq: `adequate_alt` in `adequacy.v`. -/
theorem adequate_alt (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (φ : Λ.val → Λ.state → Prop) :
    Adequate s e1 σ1 φ ↔
    ∀ t2 σ2,
      rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2) →
        (∀ v2 t2', t2 = Λ.of_val v2 :: t2' → φ v2 σ2) ∧
        (∀ e2, s = .notStuck → e2 ∈ t2 → not_stuck e2 σ2) :=
  by
    -- unfold the record and rearrange the quantifiers
    constructor
    · intro had t2 σ2 hrtc
      refine ⟨?_, ?_⟩
      · intro v2 t2' ht2
        exact had.adequate_result t2' σ2 v2 (by simpa [ht2] using hrtc)
      · intro e2 hs hemem
        exact had.adequate_not_stuck t2 σ2 e2 hs hrtc hemem
    · intro h
      refine ⟨?_, ?_⟩
      · intro t2 σ2 v2 hrtc
        have h' := h (Λ.of_val v2 :: t2) σ2 hrtc
        exact (h'.1 v2 t2 rfl)
      · intro t2 σ2 e2 hs hrtc hemem
        exact (h t2 σ2 hrtc).2 e2 hs hemem

/-- Thread pool type safety: an adequate program either all threads
have terminated or the pool can take another step.
Coq: `adequate_tp_safe` in `adequacy.v`. -/
theorem adequate_tp_safe (e1 : Λ.expr) (t2 : List Λ.expr) (σ1 σ2 : Λ.state)
    (φ : Λ.val → Λ.state → Prop)
    (had : Adequate (Λ := Λ) .notStuck e1 σ1 φ)
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    (∀ e, e ∈ t2 → ∃ v, Λ.to_val e = some v) ∨
    ∃ t3 σ3, erased_step (Λ := Λ) (t2, σ2) (t3, σ3) :=
  by
    -- either all threads are values, or pick a non-value and step it
    classical
    by_cases hval : ∀ e, e ∈ t2 → ∃ v, Λ.to_val e = some v
    · exact Or.inl hval
    · have hnot : ∃ e, e ∈ t2 ∧ ∀ v, Λ.to_val e ≠ some v := by
        -- extract a counterexample to the value predicate
        simpa [Classical.not_forall, not_exists, Decidable.not_imp_iff_and_not] using hval
      rcases hnot with ⟨e2, hemem, hnv⟩
      have hns := had.adequate_not_stuck t2 σ2 e2 rfl hsteps hemem
      rcases hns with ⟨v, hv⟩ | hred
      · exact False.elim (hnv v hv)
      · rcases hred with ⟨κ, e3, σ3, efs, hprim⟩
        rcases mem_split hemem with ⟨t1, t2', ht2⟩
        refine Or.inr ⟨t1 ++ e3 :: t2' ++ efs, σ3, ?_⟩
        refine ⟨κ, ?_⟩
        simpa [ht2, List.append_assoc] using
          (step.step_atomic (Λ := Λ) (e1 := e2) (σ1 := σ2)
            (e2 := e3) (σ2 := σ3) (efs := efs) (t1 := t1) (t2 := t2')
            (κ := κ) hprim)

/-! ## Strong Adequacy -/

section StrongAdequacy

variable (s : Stuckness) (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)

private noncomputable abbrev adq_inv : IProp GF :=
  -- packaged adequacy invariant for the current run
  adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)

private theorem adequacy_post_apply
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_post (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) := by
  -- discharge the continuation using the progress lemma
  let cont := adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ)
  let post := wptp_post (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs σ2 n [] 0
  have hns :=
    wp_progress_from_strong (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps
  have happly :=
    wptp_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (Φs := Φs)
      (σ2 := σ2) (n := n) (φ := φ) (hcont := cont) hlen_init hns
  exact (sep_comm (PROP := IProp GF) (P := post) (Q := cont)).1.trans happly

private theorem adequacy_pre_to_step_fupd
    (Φs : List (Λ.val → IProp GF))
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2))
    (hlen_init : es.length = Φs.length) :
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) ⊢
      step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
        (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  -- preserve the pool and apply the continuation under `step_fupdN`
  have happly :=
    adequacy_post_apply (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs)
      (φ := φ) Hwp hsteps hlen_init
  have hmono := step_fupdN_mono (Λ := Λ) (GF := GF) (M := M) (F := F) n happly
  exact (wptp_preservation_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ) hsteps).trans hmono

private theorem wp_strong_adequacy_step
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ adq_inv)
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
          (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) := by
  intro W -- push the adequacy invariant through preservation
  refine (Hwp W).trans ?_
  refine fupd_mono (W := W)
    (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
    (P := adq_inv)
    (Q := step_fupdN (Λ := Λ) (GF := GF) (M := M) (F := F) n
      (uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))) ?_
  refine exists_elim ?_; intro Φs
  have hlen :=
    wptp_len_from_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := es) (Φs := Φs) (σ1 := σ1) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)
  refine pure_elim (PROP := IProp GF)
    (φ := es.length = Φs.length) hlen ?_
  intro hlen_init
  exact adequacy_pre_to_step_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := es) (σ1 := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs)
    (φ := φ) Hwp hsteps hlen_init

end StrongAdequacy

/-- The main strong adequacy theorem of Iris.
Given an Iris proof of the weakest precondition for a thread pool,
any property `φ` that follows from the postconditions holds at the
meta-level after `n` steps of execution.
Coq: `wp_strong_adequacy` in `adequacy.v`. -/
theorem wp_strong_adequacy (s : Stuckness)
    (es : List Λ.expr) (σ1 : Λ.state) (n : Nat)
    (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
            (s := s) (es := es) (σ1 := σ1) (κs := κs)
            (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))
    (hsteps : nsteps (Λ := Λ) n (es, σ1) κs (t2, σ2)) :
    φ :=
  by
    -- strip the step-indexed update and conclude
    have hstep :=
      wp_strong_adequacy_step (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (σ1 := σ1) (n := n) (κs := κs)
        (t2 := t2) (σ2 := σ2) (φ := φ) Hwp hsteps
    have hplain :
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ) :=
      step_fupdN_soundness (Λ := Λ) (GF := GF) (M := M) (F := F)
        (P := uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
        (n := n) (h := hstep)
    have htrue :
        (True : IProp GF) ⊢ (BIBase.pure φ) :=
      (true_emp (PROP := IProp GF)).1.trans <|
        fupd_soundness_no_lc (M := M) (F := F) (GF := GF)
          (E1 := Iris.Set.univ) (E2 := maskEmpty) (P := BIBase.pure φ)
          (h := fun _ => hplain)
    exact UPred.pure_soundness (P := φ) htrue

/-! ## Simplified Adequacy -/

private theorem head_eq_of_splits (e2 : Λ.expr) (t2 t2' t2'' : List Λ.expr) (v2 : Λ.val)
    (hsplit' : t2 = e2 :: t2'') (ht2 : t2 = Λ.of_val v2 :: t2') :
    e2 = Λ.of_val v2 := by
  -- compare heads of the two decompositions of `t2`
  have hcons : e2 :: t2'' = Λ.of_val v2 :: t2' := by
    calc
      e2 :: t2'' = t2 := by simpa [hsplit']
      _ = Λ.of_val v2 :: t2' := by simpa [ht2]
  cases hcons
  rfl

private theorem wp_value_fupd_mask (s : Stuckness) (v2 : Λ.val) (φ : Λ.val → Prop) :
    wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ (Λ.of_val v2)
        (fun v => BIBase.pure (φ v)) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) := by
  -- use the value case and then shrink the mask
  have hval :
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ (Λ.of_val v2)
          (fun v => BIBase.pure (φ v)) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.pure (φ v2)) := by
    simpa using
      (wp_value_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (E := Iris.Set.univ) (Φ := fun v => BIBase.pure (φ v)) (v := v2)).1
  have hmask :
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ (BIBase.pure (φ v2)) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) :=
    fupd_elim (W := W)
      (E1 := Iris.Set.univ) (E2 := Iris.Set.univ) (E3 := maskEmpty)
      (Q := BIBase.pure (φ v2)) (P := BIBase.pure (φ v2))
      (h := fupd_intro_univ_empty (Λ := Λ) (GF := GF) (M := M) (F := F)
        (P := BIBase.pure (φ v2)))
  exact hval.trans hmask

private theorem wptp_singleton_fupd
    (s : Stuckness) (e2 : Λ.expr) (v2 : Λ.val) (φ : Λ.val → Prop)
    (hhead : e2 = Λ.of_val v2) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e2]
        [fun v => BIBase.pure (φ v)] ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure (φ v2)) := by
  -- reduce to the singleton WP and use the value case
  have hwp :=
    wptp_singleton_elim (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e2) (Φ := fun v => BIBase.pure (φ v))
  have hval :=
    wp_value_fupd_mask (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (v2 := v2) (φ := φ)
  exact hwp.trans (by simpa [hhead] using hval)

private theorem adequacy_cont_value
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (v2 : Λ.val) (t2' : List Λ.expr) (φ : Λ.val → Prop)
    (ht2 : t2 = Λ.of_val v2 :: t2') :
    (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [fun v => BIBase.pure (φ v)]) (φ := φ v2) := by
  -- discharge the continuation using the head value
  iintro %es' %t2'' ⌜hsplit⌝ ⌜hlen⌝ _ _ Hwp _
  rcases list_length_eq_one (l := es') (by simpa using hlen) with ⟨e2, hes⟩
  subst hes
  have hsplit' : t2 = e2 :: t2'' := by simpa using hsplit
  have hhead := head_eq_of_splits (Λ := Λ) (e2 := e2) (t2 := t2)
    (t2' := t2') (t2'' := t2'') (v2 := v2) hsplit' ht2
  iapply (wptp_singleton_fupd (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e2 := e2) (v2 := v2) (φ := φ) hhead)
  iexact Hwp

private theorem adequacy_cont_true
    (s : Stuckness) (es t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φs : List (Λ.val → IProp GF)) :
    (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := es) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := Φs) (φ := True) := by
  -- ignore the resources and return `True` under a fancy update
  iintro %es' %t2' _ _ _ _ _ _
  exact (pure_intro True.intro).trans <|
    fupd_intro_univ_empty (Λ := Λ) (GF := GF) (M := M) (F := F)
      (P := BIBase.pure True)

private theorem adequacy_cont_invariance
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (φ : Prop) :
    BIBase.wand
        (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
        (BIBase.«exists» fun (_ : Iris.Set Positive) =>
          uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [fun _ => BIBase.pure True]) (φ := φ) := by
  -- use the provided wand to discharge the final state interpretation
  iintro Hφ
  iintro %es' %t2' ⌜hsplit⌝ ⌜hlen⌝ _ _ Hσ _ _
  rcases list_length_eq_one (l := es') (by simpa using hlen) with ⟨e2, hes⟩
  subst hes
  have hsplit' : t2 = e2 :: t2' := by simpa using hsplit
  have hlen' : t2.length - 1 = t2'.length := by
    simpa [hsplit'] using (Nat.succ_sub_one t2'.length)
  simp [hlen'] at Hφ
  ispecialize Hφ $$ Hσ
  iapply (exists_elim
    (Φ := fun (_ : Iris.Set Positive) =>
      uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
    (Q := uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ)) ?_)
  · intro _; exact .rfl
  · iexact Hφ

private theorem wptp_frame_cont
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop)
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ] ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- append the continuation using `emp` framing
  exact (sep_emp (P := wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ])).2.trans
    (sep_mono (PROP := IProp GF) .rfl hcont)

private theorem wp_to_wptp_cont_frame
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop) (R : IProp GF)
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- lift the singleton WP and swap in the continuation resource
  have hwp :=
    wptp_singleton_intro (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (Φ := Φ)
  have hframe :
      BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R ⊢
        BIBase.sep (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ]) R :=
    sep_mono (PROP := IProp GF) hwp .rfl
  exact hframe.trans (sep_mono (PROP := IProp GF) .rfl hcont)

private theorem wp_to_wptp_cont
    (s : Stuckness) (e : Λ.expr) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
    (Φ : Λ.val → IProp GF) (φ : Prop)
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ ⊢
      BIBase.sep
        (wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ])
        (adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
          (Φs := [Φ]) (φ := φ)) := by
  -- add `emp` and use the framed continuation lemma
  have hframe :=
    wp_to_wptp_cont_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
      (Φ := Φ) (φ := φ) (R := (BIBase.emp : IProp GF)) hcont
  exact (sep_emp (P := wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ)).2.trans hframe

section AdequacyInv

variable (s : Stuckness) (e : Λ.expr) (σ : Λ.state)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
variable (Φ : Λ.val → IProp GF) (φ : Prop)

private theorem wp_adequacy_inv_core
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) ⊢
      adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) := by
  -- package the singleton continuation into the adequacy invariant
  have hwp_cont :=
    wp_to_wptp_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) hcont
  exact (exists_intro' (Ψ := fun Φs =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (σ1 := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    [Φ] (sep_mono (PROP := IProp GF) .rfl hwp_cont))

private theorem wp_adequacy_inv_frame_core
    (R : IProp GF)
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R) ⊢
      adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) := by
  -- package the framed continuation into the adequacy invariant
  have hwp_cont :=
    wp_to_wptp_cont_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
      (Φ := Φ) (φ := φ) (R := R) hcont
  exact (exists_intro' (Ψ := fun Φs =>
    adequacy_pre (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (σ1 := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φs := Φs) (φ := φ))
    [Φ] (sep_mono (PROP := IProp GF) .rfl hwp_cont))

private theorem wp_adequacy_inv
    (Hwp : ∀ W : WsatGS GF, ∀ κs : List Λ.observation,
      (BIBase.emp : IProp GF) ⊢
        uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
          (BIBase.sep
            (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
            (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ)))
    (hcont : (BIBase.emp : IProp GF) ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e]) (σ1 := σ) (κs := κs)
          (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) := by
  -- repackage the single-thread WP into the adequacy invariant
  intro W
  have hcore := wp_adequacy_inv_core (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e := e) (σ := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) hcont
  exact (Hwp W κs).trans <|
    fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ))
      (Q := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) hcore

private theorem wp_adequacy_inv_frame
    (W : WsatGS GF) (R : IProp GF)
    (Hwp : (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.sep
          (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
          (BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R)))
    (hcont : R ⊢
      adequacy_cont (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
        (Φs := [Φ]) (φ := φ)) :
    (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e]) (σ1 := σ) (κs := κs)
          (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) := by
  -- frame the extra resource into the continuation
  have hcore := wp_adequacy_inv_frame_core (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (e := e) (σ := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := Φ) (φ := φ) (R := R) hcont
  exact Hwp.trans <|
    fupd_mono (W := W)
      (M := M) (F := F) (E1 := Iris.Set.univ) (E2 := Iris.Set.univ)
      (P := BIBase.sep
        (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
        (BIBase.sep (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ) R))
      (Q := adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (es := [e]) (σ1 := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)) hcore

end AdequacyInv

private theorem wp_adequacy_value
    (s : Stuckness) (e : Λ.expr) (σ : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v)))))
    (hsteps : nsteps (Λ := Λ) n ([e], σ) κs (t2, σ2))
    (v2 : Λ.val) (t2' : List Λ.expr) (ht2 : t2 = Λ.of_val v2 :: t2') :
    φ v2 := by
  -- apply strong adequacy with the value continuation
  have hcont :=
    adequacy_cont_value (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (t2 := t2) (σ2 := σ2) (n := n)
      (v2 := v2) (t2' := t2') (φ := φ) ht2
  have Hinv :=
    wp_adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (σ := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun v => BIBase.pure (φ v))
      (φ := φ v2) Hwp hcont
  exact wp_strong_adequacy (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := [e]) (σ1 := σ) (n := n) (κs := κs)
    (t2 := t2) (σ2 := σ2) (φ := φ v2) Hinv hsteps

private theorem wp_adequacy_not_stuck
    (s : Stuckness) (e : Λ.expr) (σ : Λ.state) (κs : List Λ.observation)
    (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat) (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v)))))
    (hsteps : nsteps (Λ := Λ) n ([e], σ) κs (t2, σ2))
    (e2 : Λ.expr) (hs : s = .notStuck) (hemem : e2 ∈ t2) :
    not_stuck (Λ := Λ) e2 σ2 := by
  -- reuse strong adequacy to extract the progress property
  have hcont :=
    adequacy_cont_true (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (t2 := t2) (σ2 := σ2) (n := n)
      (Φs := [fun v => BIBase.pure (φ v)])
  have Hinv :=
    wp_adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (e := e) (σ := σ) (κs := κs)
      (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun v => BIBase.pure (φ v))
      (φ := True) Hwp hcont
  exact wp_progress_from_strong (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := [e]) (σ1 := σ) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (φ := True) Hinv hsteps e2 hs hemem

section InvarianceInv

variable (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
variable (κs : List Λ.observation) (t2 : List Λ.expr) (σ2 : Λ.state) (n : Nat)
variable (φ : Prop)

private theorem wp_invariance_inv
    (Hwp : ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
          (BIBase.sep
            (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1
              (fun _ => BIBase.pure True))
            (BIBase.wand
              (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
              (BIBase.«exists» fun (_ : Iris.Set Positive) =>
                uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
                  (BIBase.pure φ)))))) :
    ∀ W : WsatGS GF, (BIBase.emp : IProp GF) ⊢
      uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
        (adequacy_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (es := [e1]) (σ1 := σ1) (κs := κs) (t2 := t2)
          (σ2 := σ2) (n := n) (φ := φ)) := by
  -- wrap the invariance wand into the adequacy invariant
  intro W
  let R : IProp GF :=
    BIBase.wand (state_interp (Λ := Λ) (GF := GF) σ2 n [] (t2.length - 1))
      (BIBase.«exists» fun (_ : Iris.Set Positive) =>
        uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty (BIBase.pure φ))
  exact wp_adequacy_inv_frame (Λ := Λ) (GF := GF) (M := M) (F := F)
    (W := W) (s := s) (e := e1) (σ := σ1) (κs := κs)
    (t2 := t2) (σ2 := σ2) (n := n) (Φ := fun _ => BIBase.pure True)
    (φ := φ) (R := R) (by simpa [R] using (Hwp W)) (by
      simpa [R] using
        (adequacy_cont_invariance (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (e := e1) (t2 := t2) (σ2 := σ2) (n := n) (φ := φ)))

end InvarianceInv


/-- Simplified adequacy for a single expression. This requires the
`IrisGS` instance to use `num_laters_per_step = 0` and a simple
state interpretation that ignores step count and fork count.
Coq: `wp_adequacy` in `adequacy.v`. -/
theorem wp_adequacy (s : Stuckness) (e : Λ.expr) (σ : Λ.state)
    (φ : Λ.val → Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep
              (state_interp (Λ := Λ) (GF := GF) σ 0 κs 0)
              (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e
                (fun v => BIBase.pure (φ v))))) :
    Adequate (Λ := Λ) s e σ (fun v _ => φ v) :=
  by
    -- unpack `rtc` into `nsteps` and use strong adequacy for value/progress
    refine (adequate_alt (Λ := Λ) (s := s) (e1 := e) (σ1 := σ)
      (φ := fun v _ => φ v)).2 ?_
    intro t2 σ2 hrtc
    rcases (erased_steps_nsteps (Λ := Λ) ([e], σ) (t2, σ2)).1 hrtc with
      ⟨n, κs, hsteps⟩
    refine ⟨?_, ?_⟩
    · intro v2 t2' ht2
      exact wp_adequacy_value (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e := e) (σ := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps v2 t2' ht2
    · intro e2 hs hemem
      exact wp_adequacy_not_stuck (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e := e) (σ := σ) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) Hwp hsteps e2 hs hemem

/-! ## Invariance -/

/-- State invariance: if we can prove a WP and extract a property `φ`
from the final state interpretation, then `φ` holds at the meta-level.
Coq: `wp_invariance` in `adequacy.v`. -/
theorem wp_invariance (s : Stuckness) (e1 : Λ.expr) (σ1 : Λ.state)
    (t2 : List Λ.expr) (σ2 : Λ.state) (φ : Prop)
    (Hwp : ∀ W : WsatGS GF,
      ∀ κs : List Λ.observation,
      ∀ ns : Nat,
        (BIBase.emp : IProp GF) ⊢
          uPred_fupd (M := M) (F := F) W Iris.Set.univ Iris.Set.univ
            (BIBase.sep (state_interp (Λ := Λ) (GF := GF) σ1 0 κs 0)
              (BIBase.sep
                (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e1
                  (fun _ => BIBase.pure True))
                (BIBase.wand
                  (state_interp (Λ := Λ) (GF := GF) σ2 ns [] (t2.length - 1))
                  (BIBase.«exists» fun (_ : Iris.Set Positive) =>
                    uPred_fupd (M := M) (F := F) W Iris.Set.univ maskEmpty
                      (BIBase.pure φ))))))
    (hsteps : rtc (erased_step (Λ := Λ)) ([e1], σ1) (t2, σ2)) :
    φ :=
  by
    -- reduce to `nsteps` and apply strong adequacy with invariance continuation
    rcases (erased_steps_nsteps (Λ := Λ) ([e1], σ1) (t2, σ2)).1 hsteps with
      ⟨n, κs, hsteps⟩
    have Hinv :=
      wp_invariance_inv (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (e1 := e1) (σ1 := σ1) (κs := κs)
        (t2 := t2) (σ2 := σ2) (n := n) (φ := φ) (Hwp := fun W => Hwp W κs n)
    exact wp_strong_adequacy (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e1]) (σ1 := σ1) (n := n) (κs := κs)
      (t2 := t2) (σ2 := σ2) (φ := φ) Hinv hsteps

end Iris.ProgramLogic
