/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.ThreadPool

/-! # Adequacy: Thread Pool Helpers (A)

Reference: `iris/program_logic/adequacy.v`

This file collects the first chunk of helper lemmas about the thread-pool
weakest precondition (`wptp`) and its list indexing structure.
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
/-! ## Wptp Helpers -/

theorem wptp_length (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs ⊢
      BIBase.pure (es.length = Φs.length) := by
  -- drop the body of the conjunction
  exact sep_elim_l (P := BIBase.pure (es.length = Φs.length))
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)

theorem wptp_body_of_wptp (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs ⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 := by
  -- drop the pure length equality
  exact sep_elim_r (P := BIBase.pure (es.length = Φs.length))
    (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0)

theorem sep_pure_intro {φ : Prop} (P : IProp GF) (h : φ) :
    P ⊢ BIBase.sep (BIBase.pure φ) P := by
  -- insert `True` then replace it with the desired pure fact
  exact (true_sep_2 (PROP := IProp GF) (P := P)).trans
    (sep_mono (pure_intro h) .rfl)

theorem wptp_of_body (s : Stuckness) (es : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (hlen : es.length = Φs.length) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs 0 ⊢
      wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s es Φs := by
  -- reinsert the pure length equality to form `wptp`
  simpa [wptp] using (sep_pure_intro (P := wptp_body_at (Λ := Λ) (GF := GF)
    (M := M) (F := F) s es Φs 0) hlen)

theorem wptp_singleton_intro (s : Stuckness) (e : Λ.expr)
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

theorem wptp_singleton_elim (s : Stuckness) (e : Λ.expr)
    (Φ : Λ.val → IProp GF) :
    wptp (Λ := Λ) (GF := GF) (M := M) (F := F) s [e] [Φ] ⊢
      wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ := by
  -- strip the singleton body and simplify
  have hbody :=
    wptp_body_of_wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := [e]) (Φs := [Φ])
  simpa [wptp_body_at, big_sepL_cons] using hbody

theorem wptp_body_at_split_middle
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

theorem wptp_body_at_middle
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

theorem wptp_body_at_append_left
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

theorem wptp_body_at_replicate
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

theorem wptp_body_at_append_split
    (s : Stuckness) (t2 efs : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) k ⊣⊢
      BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 (Φs ++ List.replicate efs.length fork_post) k)
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length)) := by
  -- split the `big_sepL` over the append
  have happ :=
    big_sepL_app (PROP := IProp GF)
      (Φ := fun i e =>
        match (Φs ++ List.replicate efs.length fork_post)[i + k]? with
        | some Φ => wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e Φ
        | none => BIBase.emp) t2 efs
  simpa [wptp_body_at, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happ

theorem wptp_body_at_append_fork_left
    (s : Stuckness) (t2 efs : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) (hlen : Φs.length = k + t2.length) :
    BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) ⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) k := by
  -- rewrite the left and right components, then rejoin the split
  have hle : k + t2.length ≤ Φs.length := by
    simpa [hlen] using Nat.le_refl (k + t2.length)
  have hleft := wptp_body_at_append_left (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t2) (Φs := Φs) (k := k) (n := efs.length) hle
  have hright := wptp_body_at_replicate (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := efs) (Φs := Φs) (k := k + t2.length) (hlen := hlen)
  have hsep :=
    sep_mono (PROP := IProp GF)
      (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
      (P' := big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)
      (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 (Φs ++ List.replicate efs.length fork_post) k)
      (Q' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length))
      hleft.2 hright.2
  exact hsep.trans (wptp_body_at_append_split (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t2 := t2) (efs := efs) (Φs := Φs) (k := k)).symm.1

theorem wptp_body_at_append_fork_right
    (s : Stuckness) (t2 efs : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) (hlen : Φs.length = k + t2.length) :
    wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) k ⊢
      BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) := by
  -- split, then rewrite the two sides back to the original shape
  have hle : k + t2.length ≤ Φs.length := by
    simpa [hlen] using Nat.le_refl (k + t2.length)
  have hleft := wptp_body_at_append_left (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t2) (Φs := Φs) (k := k) (n := efs.length) hle
  have hright := wptp_body_at_replicate (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := efs) (Φs := Φs) (k := k + t2.length) (hlen := hlen)
  have hsep :=
    sep_mono (PROP := IProp GF)
      (P := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 (Φs ++ List.replicate efs.length fork_post) k)
      (P' := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s efs (Φs ++ List.replicate efs.length fork_post) (k + t2.length))
      (Q := wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
      (Q' := big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)
      hleft.1 hright.1
  exact (wptp_body_at_append_split (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t2 := t2) (efs := efs) (Φs := Φs) (k := k)).1.trans hsep

theorem wptp_body_at_append_fork
    (s : Stuckness) (t2 efs : List Λ.expr) (Φs : List (Λ.val → IProp GF))
    (k : Nat) (hlen : Φs.length = k + t2.length) :
    BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t2 Φs k)
      (big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs) ⊣⊢
      wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s (t2 ++ efs)
        (Φs ++ List.replicate efs.length fork_post) k := by
  -- package the two directional entailments
  exact ⟨
    wptp_body_at_append_fork_left (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t2 := t2) (efs := efs) (Φs := Φs) (k := k) hlen,
    wptp_body_at_append_fork_right (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (t2 := t2) (efs := efs) (Φs := Φs) (k := k) hlen⟩

theorem wptp_tail_fork
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

theorem wptp_append_lookup
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

theorem wptp_lookup_middle
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

theorem wptp_middle_append
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

theorem wptp_rebuild_len
    (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF))
    (hlen : Φs.length = t1.length + t2.length + 1) :
    (t1 ++ e2 :: t2 ++ efs).length =
      (Φs ++ List.replicate efs.length fork_post).length := by
  -- compute the list lengths explicitly
  simp [List.length_append, List.length_cons, List.length_replicate, hlen,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem wptp_rebuild_tail
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1) :
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
          s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) (t1.length + 1)) := by
  -- replace the tail segment using `wptp_tail_fork`
  have htail := wptp_tail_fork (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (Φs := Φs) hlen
  exact sep_mono (PROP := IProp GF)
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

noncomputable abbrev wptp_rebuild_left
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF) : IProp GF :=
  -- full `wptp` body before rebuilding the middle
  BIBase.sep
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0)
    (BIBase.sep
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
      (BIBase.sep
        (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
          s t2 Φs (t1.length + 1))
        (big_sepL (fun _ ef =>
          wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs)))

noncomputable abbrev wptp_rebuild_right
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF) : IProp GF :=
  -- `wptp` body after replacing the forked tail
  BIBase.sep
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
      s t1 (Φs ++ List.replicate efs.length fork_post) 0)
    (BIBase.sep
      (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post)
        (t1.length + 1)))

noncomputable abbrev wptp_rebuild_head
    (s : Stuckness) (t1 : List Λ.expr) (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- shared head of the `wptp` body
  wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F) s t1 Φs 0

noncomputable abbrev wptp_rebuild_head_ext
    (s : Stuckness) (t1 : List Λ.expr) (efs : List Λ.expr)
    (Φs : List (Λ.val → IProp GF)) : IProp GF :=
  -- head after adding the forked suffix to `Φs`
  wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
    s t1 (Φs ++ List.replicate efs.length fork_post) 0

theorem wptp_rebuild_prep
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hleft :
      wptp_rebuild_head (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t1 := t1) (Φs := Φs) ⊢
        wptp_rebuild_head_ext (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t1 := t1) (efs := efs) (Φs := Φs)) :
    wptp_rebuild_left (Λ := Λ) (GF := GF) (M := M) (F := F)
          (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
          (Φs := Φs) (Φ := Φ) ⊢
      wptp_rebuild_right (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) := by
  -- rewrite the head with `hleft` and the tail with `wptp_rebuild_tail`
  have htail := wptp_rebuild_tail (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) hlen
  let P := wptp_rebuild_head (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (Φs := Φs)
  let Q := BIBase.sep
    (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
    (BIBase.sep
      (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
        s t2 Φs (t1.length + 1))
      (big_sepL (fun _ ef =>
        wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ ef fork_post) efs))
  let P' := wptp_rebuild_head_ext (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (efs := efs) (Φs := Φs)
  let Q' := BIBase.sep
    (wp (M := M) (F := F) (Λ := Λ) s Iris.Set.univ e2 Φ)
    (wptp_body_at (Λ := Λ) (GF := GF) (M := M) (F := F)
      s (t2 ++ efs) (Φs ++ List.replicate efs.length fork_post)
      (t1.length + 1))
  have hsep : BIBase.sep P Q ⊢ BIBase.sep P' Q' :=
    sep_mono (PROP := IProp GF) hleft htail
  simpa [wptp_rebuild_left, wptp_rebuild_right, P, Q, P', Q'] using hsep

theorem wptp_rebuild
    (s : Stuckness) (t1 t2 efs : List Λ.expr) (e2 : Λ.expr)
    (Φs : List (Λ.val → IProp GF)) (Φ : Λ.val → IProp GF)
    (hlen : Φs.length = t1.length + t2.length + 1)
    (hget : Φs[t1.length]? = some Φ) :
    wptp_rebuild_left (Λ := Λ) (GF := GF) (M := M) (F := F)
        (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
        (Φs := Φs) (Φ := Φ) ⊢ wptp (Λ := Λ) (GF := GF) (M := M) (F := F)
          s (t1 ++ e2 :: t2 ++ efs) (Φs ++ List.replicate efs.length fork_post) := by
  -- replace the tail, rebuild the middle, then add the length proof
  have hle : t1.length ≤ Φs.length := by
    -- `t1.length` is within the left prefix of `Φs`
    have hle' : t1.length ≤ t1.length + t2.length + 1 :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    simpa [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle'
  have hleft := wptp_body_at_append_left (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (es := t1) (Φs := Φs) (k := 0) (n := efs.length) (by simpa using hle)
  have hprep := wptp_rebuild_prep (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) hlen hleft.2
  have hmid := wptp_middle_append (Λ := Λ) (GF := GF) (M := M) (F := F)
    (s := s) (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2)
    (Φs := Φs) (Φ := Φ) hlen hget
  have hlen2 := wptp_rebuild_len (Λ := Λ) (GF := GF)
    (t1 := t1) (t2 := t2) (efs := efs) (e2 := e2) (Φs := Φs) hlen
  exact hprep.trans (hmid.trans <|
    wptp_of_body (Λ := Λ) (GF := GF) (M := M) (F := F)
      (s := s) (es := t1 ++ e2 :: t2 ++ efs)
      (Φs := Φs ++ List.replicate efs.length fork_post) hlen2)

theorem sep_reorder_for_rebuild
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


end Iris.ProgramLogic
