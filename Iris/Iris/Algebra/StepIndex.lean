/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang
-/
module

public meta import Iris.Std.RocqPorting
public import Iris.Std.Classes

@[expose] public section

namespace Iris

@[rocq_alias sidx, rocq_alias SIdxMixin]
class SIdx (I : Type u) extends LT I, LE I, Zero I where
  succ : I → I
  lt_trans : ∀ {n m p : I}, n < m → m < p → n < p
  lt_wf : WellFounded ((· < ·) : I → I → Prop)
  lt_trichotomyT : ∀ n m : I, n < m ⊕' n = m ⊕' m < n
  le_lteq : ∀ {m n : I}, n ≤ m ↔ n < m ∨ n = m
  not_lt_zero : ∀ n : I, ¬n < 0
  lt_succ_self : ∀ n : I, n < succ n
  succ_le_of_lt : ∀ {n m : I}, n < m → succ n ≤ m
  weak_case : ∀ n : I, (Σ' m : I, n = succ m) ⊕' ∀ m : I, m < n → succ m < n

/-- The step-indexing successor operator. -/
scoped prefix:max "succᵢ" => SIdx.succ

class SIdxFinite (I : Type u) [SIdx I] where
  finite_index : ∀ n : I, n = 0 ∨ ∃ m, n = succᵢ m

#rocq_ignore SIdx.lt_trans "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.lt_wf "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.lt_trichotomy "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.le_lteq "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.nlt_0_r "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.lt_succ_diag_r "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.le_succ_l_2 "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.weak_case "Lifting of mixin properties not required as they are part of the type class SIdx"

namespace SIdx

open Iris Std

variable {I : Type u} [inst : SIdx I] {m n p : I}

@[rocq_alias SIdx.lt_succ_diag_r']
theorem lt_succ_diag_r' (h : n = succᵢ m) : m < n := by
  subst h
  exact inst.lt_succ_self m

@[rocq_alias SIdx.inhabited]
instance inhabited : Inhabited I where
  default := 0

theorem lt_irrefl (n : I) : ¬n < n := by
  intro h
  induction n using inst.lt_wf.induction with
  | h n ih => apply ih n <;> exact h

instance : Std.Irrefl ((· < ·) : I → I → Prop) where
  irrefl := lt_irrefl

theorem lt_asymm (h : n < m) : ¬m < n := by
  intro h1
  apply lt_irrefl n
  exact inst.lt_trans h h1

instance : Std.Asymm ((· < ·) : I → I → Prop) where
  asymm _ _ := lt_asymm

instance : Trans (· < ·) (· < ·) ((· < ·) : I → I → Prop) where
  trans := lt_trans

@[rocq_alias SIdx.lt_strict]
instance : IsStrictOrder ((· < ·) : I → I → Prop) where

@[rocq_alias SIdx.lt_le_incl]
theorem lt_le_incl (h : n < m) : n ≤ m := by
  apply le_lteq.mpr; left; assumption

/-- For the `rfl` tactic. -/
@[refl, simp]
theorem le_refl : n ≤ n := by apply inst.le_lteq.mpr; right; rfl

instance : Std.Refl ((· ≤ ·) : I → I → Prop) where
  refl _ := le_refl

theorem le_trans (h1 : n ≤ m) (h2 : m ≤ p) : n ≤ p := by
  rcases le_lteq.mp h1 with (h1 | rfl)
  · rcases le_lteq.mp h2 with (h2 | rfl)
    · exact lt_le_incl <| inst.lt_trans h1 h2
    · exact lt_le_incl h1
  · assumption

instance : Trans (· ≤ ·) (· ≤ ·) ((· ≤ ·) : I → I → Prop) where
  trans := le_trans

theorem le_antisymm (h1 : m ≤ n) (h2 : n ≤ m) : m = n := by
  rcases le_lteq.mp h2 with (h2 | h2)
  · rcases le_lteq.mp h1 with (h1 | h1)
    · exact absurd (inst.lt_trans h2 h1) (lt_irrefl n)
    · exact h1
  · subst h2; rfl

@[rocq_alias SIdx.le_po]
instance le_po : Std.IsPartialOrder I where
  le_refl _ := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

@[rocq_alias SIdx.lt_ge_cases]
theorem lt_ge_cases (m n : I) : n < m ∨ m ≤ n := by
  rcases inst.lt_trichotomyT n m with (h | h | h)
  · left; exact h
  · right; apply le_lteq.mpr; right; symm; assumption
  · right; exact lt_le_incl h

@[rocq_alias SIdx.le_gt_cases]
theorem le_gt_cases (m n : I) : n ≤ m ∨ m < n := lt_ge_cases n m |>.symm

@[rocq_alias SIdx.le_total]
theorem le_total : n ≤ m ∨ m ≤ n := by
  rcases lt_ge_cases m n with (h | h)
  · left; exact lt_le_incl h
  · right; assumption

instance : Std.Total ((· ≤ ·) : I → I → Prop) where
  total _ _ := le_total

@[rocq_alias SIdx.lt_le_trans]
theorem lt_le_trans (h1 : n < m) (h2 : m ≤ p) : n < p := by
  rcases inst.le_lteq.mp h2 with (h2 | h2)
  · exact inst.lt_trans h1 h2
  · subst h2; assumption

instance : Trans (· < ·) (· ≤ ·) ((· < ·) : I → I → Prop) where
  trans := lt_le_trans

@[rocq_alias SIdx.le_lt_trans]
theorem le_lt_trans (h1 : n ≤ m) (h2 : m < p) : n < p := by
  rcases inst.le_lteq.mp h1 with (h1 | h1)
  · exact inst.lt_trans h1 h2
  · subst h1; assumption

instance : Trans (· ≤ ·) (· < ·) ((· < ·) : I → I → Prop) where
  trans := le_lt_trans

@[rocq_alias SIdx.le_succ_diag_r]
theorem le_succ_diag_r : n ≤ succᵢ n := by
  apply lt_le_incl
  apply inst.lt_succ_self

@[rocq_alias SIdx.le_ngt]
theorem le_ngt : n ≤ m ↔ ¬ m < n := by
  constructor <;> intro h0
  · intro h1
    exact lt_irrefl m (lt_le_trans h1 h0)
  · rcases lt_ge_cases n m <;> trivial

@[rocq_alias SIdx.lt_nge]
theorem lt_nge : n < m ↔ ¬ m ≤ n := by
  constructor <;> intro h0
  · intro h1
    exact lt_irrefl n <| lt_le_trans h0 h1
  · rcases lt_ge_cases m n <;> trivial

@[rocq_alias SIdx.le_neq]
theorem le_neq : n < m ↔ n ≤ m ∧ n ≠ m := by
  constructor <;> intro h
  · refine ⟨lt_le_incl h, ?_⟩
    rintro rfl
    exact lt_irrefl n h
  · rcases h with ⟨h1, h2⟩
    apply lt_nge.mpr
    intro h3
    apply h2
    exact le_antisymm h1 h3

@[rocq_alias SIdx.le_succ_l]
theorem le_succ_l : succᵢ n ≤ m ↔ n < m := by
  constructor <;> intro h
  · exact lt_le_trans (lt_succ_self n) h
  · exact succ_le_of_lt h

@[rocq_alias SIdx.lt_succ_r]
theorem lt_succ_r : n < succᵢ m ↔ n ≤ m := by
  constructor <;> intro h
  · refine le_ngt.mpr ?_
    intro h1
    apply lt_irrefl n
    apply lt_le_trans h
    exact succ_le_of_lt h1
  · exact le_lt_trans h <| inst.lt_succ_self m

@[rocq_alias SIdx.succ_le_mono]
theorem succ_le_mono : n ≤ m ↔ succᵢ n ≤ succᵢ m := by
  rewrite [le_succ_l, lt_succ_r]; rfl

@[rocq_alias SIdx.succ_lt_mono]
theorem succ_lt_mono : n < m ↔ succᵢ n < succᵢ m := by
  rewrite [lt_succ_r, le_succ_l]; rfl

@[rocq_alias SIdx.succ_inj]
theorem succ_inj (h : succᵢ n = succᵢ m) : n = m := by
  apply le_antisymm <;> apply succ_le_mono.mpr <;> rw [h]

@[rocq_alias SIdx.nlt_succ_r]
theorem nlt_succ_r : ¬ m < succᵢ n ↔ n < m := by
  rw [lt_succ_r, lt_nge]

@[rocq_alias SIdx.le_0_l]
theorem le_0_l : 0 ≤ n := le_ngt.mpr <| inst.not_lt_zero n

@[rocq_alias SIdx.le_0_r]
theorem le_0_r : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply le_antisymm
    · assumption
    · exact le_0_l
  · subst h; rfl

@[rocq_alias SIdx.neq_0_lt_0]
theorem neq_0_lt_0 : n ≠ 0 ↔ 0 < n := by
  constructor
  · intro h
    rcases lt_ge_cases n 0 with (h1 | h1)
    · assumption
    · exact absurd (le_0_r.mp h1) h
  · rintro h rfl
    exact inst.not_lt_zero 0 h

@[rocq_alias SIdx.neq_succ_0]
theorem neq_succ_0 : succᵢ n ≠ 0 := neq_0_lt_0.mpr <| lt_succ_r.mpr le_0_l

@[rocq_alias SIdx.succ_neq]
theorem succ_neq : n ≠ succᵢ n := by
  intro h
  have hlt := inst.lt_succ_self n
  rw [← h] at hlt
  exact lt_irrefl n hlt

@[rocq_alias SIdx.eq_dec]
instance (priority := low) eqDec : DecidableEq I := fun n m =>
  match inst.lt_trichotomyT n m with
  | .inl h => by
    apply isFalse
    rintro rfl
    exact lt_irrefl n h
  | .inr (.inl h) => isTrue h
  | .inr (.inr h) => by
    apply isFalse
    rintro rfl
    exact lt_irrefl n h

@[rocq_alias SIdx.lt_dec]
instance (priority := low) (n m : I) : Decidable (n < m) :=
  match inst.lt_trichotomyT n m with
  | .inl h => isTrue h
  | .inr (.inl h) => by
    apply isFalse
    rintro h'
    subst h
    exact lt_irrefl n h'
  | .inr (.inr h) => by
    apply isFalse
    intro h'
    exact lt_irrefl m <| inst.lt_trans h h'

@[rocq_alias SIdx.le_dec]
instance (priority := low) (n m : I) : Decidable (n ≤ m) :=
  match inst.lt_trichotomyT n m with
  | .inl h => by
    apply isTrue
    exact lt_le_incl h
  | .inr (.inl h) => by
    apply isTrue
    exact le_lteq.mpr <| .inr h
  | .inr (.inr h) => by
    apply isFalse
    intro h'
    exact lt_irrefl m <| lt_le_trans h h'

@[rocq_alias SIdx.limit]
structure Limit (n : I) [SIdx I] where
  succ_lt : ∀ m, m < n → succᵢ m < n
  ne_zero : n ≠ 0

@[simp, rocq_alias SIdx.limit_0]
theorem limit_0 : ¬Limit (0 : I) := by
  intro h
  exact h.ne_zero rfl

@[rocq_alias SIdx.limit_lt_0]
theorem Limit.limit_lt_0 (h : Limit n) : 0 < n := neq_0_lt_0.mp h.ne_zero

@[simp, rocq_alias SIdx.limit_S]
theorem limit_S (n : I) : ¬Limit (succᵢ n) := by
  intro h
  apply lt_irrefl (succᵢ n)
  apply h.succ_lt n
  exact lt_succ_self n

@[rocq_alias SIdx.limit_finite]
theorem limit_finite [inst : SIdxFinite I] (n : I) : ¬Limit n := by
  intro h
  rcases SIdxFinite.finite_index n with (h0 | h0)
  · exact h.ne_zero h0
  · rcases h0 with ⟨m, hm⟩
    apply limit_S m
    subst hm
    assumption

@[rocq_alias SIdx.case]
def case (n : I) : (n = 0) ⊕' (Σ' m, n = succᵢ m) ⊕' Limit n :=
  if h : n = 0 then .inl h
  else
    match inst.weak_case n with
    | .inl ⟨m, hm⟩ => .inr <| .inl ⟨m, hm⟩
    | .inr hlim => .inr <| .inr ⟨hlim, h⟩

@[rocq_alias SIdx.rec]
def rec' {P : I → Sort v}
    (s : P 0)
    (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) :
    ∀ n, P n :=
  WellFounded.fix inst.lt_wf fun n IH =>
    match SIdx.case n with
    | .inl EQ => EQ ▸ s
    | .inr <| .inl ⟨m, EQ⟩ => EQ ▸ f m (IH m (lt_succ_diag_r' EQ))
    | .inr <| .inr Hlim => lim n Hlim IH

@[rocq_alias SIdx.rec_unfold]
theorem rec_unfold {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) (n : I) :
    rec' s f lim n =
      match SIdx.case n with
      | .inl EQ => EQ ▸ s
      | .inr (.inl ⟨m, EQ⟩) => EQ ▸ f m (rec' s f lim m)
      | .inr (.inr Hlim) => lim n Hlim (fun m _ => rec' s f lim m) :=
  inst.lt_wf.fix_eq _ n

@[rocq_alias SIdx.rec_zero]
theorem rec_zero {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) :
    rec' s f lim 0 = s := by
  rw [rec_unfold s f lim 0]
  cases SIdx.case (0 : I) with
  | inl EQ => rfl
  | inr h =>
    cases h with
    | inl h =>
      let ⟨m, EQ⟩ := h
      exact absurd EQ.symm neq_succ_0
    | inr Hlim => exact absurd Hlim limit_0

@[rocq_alias SIdx.rec_succ]
theorem rec_succ {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) (n : I) :
    rec' s f lim (succᵢ n) = f n (rec' s f lim n) := by
  rw [rec_unfold s f lim (succᵢ n)]
  cases SIdx.case (succᵢ n) with
  | inl EQ => exact absurd EQ neq_succ_0
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨m, EQ⟩ := h
      obtain rfl := succ_inj EQ
      rfl
    | inr Hlim => exact absurd Hlim (limit_S n)

@[rocq_alias SIdx.rec_lim]
theorem rec_lim {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) (n : I) (Hn : Limit n) :
    rec' s f lim n = lim n Hn (fun m _ => rec' s f lim m) := by
  rw [rec_unfold s f lim n]
  cases SIdx.case n with
  | inl EQ => exact absurd EQ Hn.ne_zero
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨m, EQ⟩ := h
      exact absurd (EQ ▸ Hn) (limit_S m)
    | inr Hlim => rfl

#rocq_ignore SIdx.rec_lim_ext
  "Proof irrelevance already handled automatically by Lean for the theorems \
  rec_zero, rec_succ and rec_elim"

end SIdx
