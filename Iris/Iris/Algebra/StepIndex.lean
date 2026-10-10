/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler, Alvin Tang, Markus de Medeiros
-/
module

public import Iris.Std.Classes
public meta import Iris.Algebra.StepIndexRegistry
public meta import Lean.PrettyPrinter.Delaborator.Builtins

@[expose] public section

namespace Iris

/-- `SI : stepindex (Type _)` marks `SI` as a step index binder, like `outParam` marks an output:
`@[indexed]` declarations take theirs from the `local stepindex` section (see `elabStepindex`).
It is the identity, and prints as its argument. -/
@[reducible] def stepindex (α : Sort u) : Sort u := α

open Lean in
@[app_unexpander stepindex] meta def unexpandStepindex : PrettyPrinter.Unexpander
  | `($_ $a) => `($a)
  | _ => throw ()

/-- `sn` is the successor of `n`: the least element above `n`. -/
@[rocq_alias is_succ]
structure IsSucc {I : Type u} [LT I] (n sn : I) : Prop where
  lt : n < sn
  least : ¬∃ p, n < p ∧ p < sn

@[rocq_alias sidx, rocq_alias SIdxMixin]
class SIdx (I : Type u) extends LT I, LE I, Zero I where
  lt_trans : ∀ {n m p : I}, n < m → m < p → n < p
  lt_wf : WellFounded ((· < ·) : I → I → Prop)
  lt_trichotomyT : ∀ n m : I, n < m ⊕' n = m ⊕' m < n
  le_lteq : ∀ {m n : I}, n ≤ m ↔ n < m ∨ n = m
  not_lt_zero : ∀ n : I, ¬n < 0
  weak_case : ∀ n : I, (Σ' m : I, IsSucc m n) ⊕' ∀ m sm : I, m < n → IsSucc m sm → sm < n

/- `SIdx` carries `<`, `≤` and `0`, but index types usually have them already (`Nat`). Low priority on the
parent projections, so the type's own instances win (otherwise `Zero Nat` resolves to `natSIdx.toZero`,
which `omega`/`simp` do not recognise). -/
attribute [instance 50] SIdx.toLT SIdx.toLE SIdx.toZero

/-- There is no step-indexing: `0` is the only index. -/
@[rocq_alias SIdxZero]
class SIdxZero (I : Type u) [SIdx I] : Prop where
  all_0 : ∀ n : I, n = 0

/-- Finite step-indexing: no limit indices. Still allows no step-indexing (`SIdxZero`). -/
@[rocq_alias SIdxFinite]
class SIdxFinite (I : Type u) [SIdx I] : Prop where
  finite_index : ∀ n : I, n = 0 ∨ ∃ m, IsSucc m n

/-- A successor operation, so step-indexing is non-trivial. -/
@[rocq_alias SIdxSucc]
class SIdxSucc (I : Type u) [SIdx I] where
  succ : I → I
  succ_isSucc : ∀ n : I, IsSucc n (succ n)

/-- The step-indexing successor operator. -/
@[reducible] def SIdx.succ {I : Type u} [SIdx I] [SIdxSucc I] : I → I := SIdxSucc.succ

scoped prefix:max "succᵢ" => SIdx.succ

@[rocq_alias SIdx.zero_finite]
instance (priority := low) SIdxZero.toFinite {I : Type u} [SIdx I] [SIdxZero I] : SIdxFinite I where
  finite_index n := .inl (SIdxZero.all_0 n)

#rocq_ignore SIdx.lt_trans "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.lt_wf "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.lt_trichotomy "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.le_lteq "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.nlt_0_r "Lifting of mixin properties not required as they are part of the type class SIdx"
#rocq_ignore SIdx.weak_case "Lifting of mixin properties not required as they are part of the type class SIdx"

namespace SIdx

open Iris Iris.Std

variable {I : Type u} [inst : SIdx I] {m n p : I}


@[rocq_alias SIdx.inhabited]
instance (priority := low) inhabited : Inhabited I where
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

/-! ## Successors -/

@[rocq_alias SIdx.is_succ_lt]
theorem is_succ_lt {n sn : I} (h : IsSucc n sn) : n < sn := h.1

@[rocq_alias SIdx.is_succ_0]
theorem is_succ_0 {n : I} : ¬IsSucc n (0 : I) := fun h => inst.not_lt_zero n h.1

@[rocq_alias SIdx.is_succ_gt_l]
theorem is_succ_gt_l {n sn m : I} (h : IsSucc n sn) (hm : n < m) : sn ≤ m :=
  le_ngt.mpr fun h' => h.2 ⟨m, hm, h'⟩

@[rocq_alias SIdx.is_succ_lt_r]
theorem is_succ_lt_r {n sn m : I} (h : IsSucc n sn) (hm : m < sn) : m ≤ n :=
  le_ngt.mpr fun h' => h.2 ⟨m, h', hm⟩

theorem _root_.Iris.IsSucc.le_of_lt {n sn m : I} (h : IsSucc n sn) (hm : m < sn) : m ≤ n := is_succ_lt_r h hm

@[rocq_alias SIdx.is_succ_unique_l]
theorem is_succ_unique_l {n sn₁ sn₂ : I} (h₁ : IsSucc n sn₁) (h₂ : IsSucc n sn₂) : sn₁ = sn₂ :=
  le_antisymm (is_succ_gt_l h₁ h₂.1) (is_succ_gt_l h₂ h₁.1)

@[rocq_alias SIdx.is_succ_unique_r]
theorem is_succ_unique_r {n₁ n₂ sn : I} (h₁ : IsSucc n₁ sn) (h₂ : IsSucc n₂ sn) : n₁ = n₂ :=
  le_antisymm (is_succ_lt_r h₂ h₁.1) (is_succ_lt_r h₁ h₂.1)

/-- Every index below some other index has a successor (the least index above it). -/
theorem exists_isSucc_of_lt {m n : I} (h : m < n) : ∃ sm, IsSucc m sm := by
  induction n using inst.lt_wf.induction with
  | h k ih =>
    by_cases hp : ∃ p, m < p ∧ p < k
    · obtain ⟨p, hmp, hpk⟩ := hp
      exact ih p hpk hmp
    · exact ⟨k, h, hp⟩

/-! ## Limit indices -/

@[rocq_alias SIdx.limit]
structure Limit (n : I) [SIdx I] : Prop where
  gt_succ : ∀ m sm, m < n → IsSucc m sm → sm < n
  ne_zero : n ≠ 0

@[simp, rocq_alias SIdx.limit_0]
theorem limit_0 : ¬Limit (0 : I) := by
  intro h
  exact h.ne_zero rfl

@[rocq_alias SIdx.limit_lt_0]
theorem Limit.limit_lt_0 (h : Limit n) : 0 < n := neq_0_lt_0.mp h.ne_zero

/-- Below a limit index, every index has a successor that is still below the limit. -/
theorem Limit.exists_succ_lt (h : Limit n) (hm : m < n) : ∃ sm, IsSucc m sm ∧ sm < n :=
  let ⟨sm, hs⟩ := exists_isSucc_of_lt hm
  ⟨sm, hs, h.gt_succ m sm hm hs⟩

@[rocq_alias SIdx.limit_is_succ]
theorem limit_is_succ {n sn : I} (hs : IsSucc n sn) : ¬Limit sn :=
  fun h => lt_irrefl sn (h.gt_succ n sn hs.1 hs)

@[rocq_alias SIdx.limit_finite]
theorem limit_finite [SIdxFinite I] (n : I) : ¬Limit n := by
  intro h
  rcases SIdxFinite.finite_index n with h0 | ⟨m, hm⟩
  · exact h.ne_zero h0
  · exact limit_is_succ hm h

@[rocq_alias SIdx.case]
def case (n : I) : (n = 0) ⊕' (Σ' m, IsSucc m n) ⊕' Limit n :=
  if h : n = 0 then .inl h
  else
    match inst.weak_case n with
    | .inl ⟨m, hm⟩ => .inr <| .inl ⟨m, hm⟩
    | .inr hlim => .inr <| .inr ⟨hlim, h⟩

/-! ## Step indices with a successor operation -/

section succ
variable [SIdxSucc I]

@[rocq_alias SIdx.lt_succ_diag_r]
theorem lt_succ_self (n : I) : n < succᵢ n := (SIdxSucc.succ_isSucc n).1

@[rocq_alias SIdx.le_succ_l_2]
theorem succ_le_of_lt {n m : I} (h : n < m) : succᵢ n ≤ m := is_succ_gt_l (SIdxSucc.succ_isSucc n) h

@[rocq_alias SIdx.is_succ_S]
theorem is_succ_S {n sn : I} : IsSucc n sn ↔ sn = succᵢ n :=
  ⟨fun h => is_succ_unique_l h (SIdxSucc.succ_isSucc n), fun h => h ▸ SIdxSucc.succ_isSucc n⟩

@[rocq_alias SIdx.lt_succ_diag_r']
theorem lt_succ_diag_r' (h : n = succᵢ m) : m < n := by
  subst h
  exact lt_succ_self m
@[rocq_alias SIdx.le_succ_diag_r]
theorem le_succ_diag_r : n ≤ succᵢ n := by
  apply lt_le_incl
  apply lt_succ_self
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
  · exact le_lt_trans h <| lt_succ_self m

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

@[rocq_alias SIdx.neq_succ_0]
theorem neq_succ_0 : succᵢ n ≠ 0 := neq_0_lt_0.mpr <| lt_succ_r.mpr le_0_l
@[rocq_alias SIdx.succ_neq]
theorem succ_neq : n ≠ succᵢ n := by
  intro h
  have hlt := lt_succ_self n
  rw [← h] at hlt
  exact lt_irrefl n hlt


@[rocq_alias SIdx.limit_alt]
theorem limit_alt : Limit n ↔ (∀ m, m < n → succᵢ m < n) ∧ n ≠ 0 :=
  ⟨fun h => ⟨fun m hm => h.gt_succ m _ hm (SIdxSucc.succ_isSucc m), h.ne_zero⟩,
   fun ⟨h, h0⟩ => ⟨fun m _ hm hs => is_succ_S.mp hs ▸ h m hm, h0⟩⟩

theorem Limit.succ_lt (h : Limit n) : ∀ m, m < n → succᵢ m < n :=
  (limit_alt.mp h).1

@[simp, rocq_alias SIdx.limit_succ]
theorem limit_S (n : I) : ¬Limit (succᵢ n) := limit_is_succ (SIdxSucc.succ_isSucc n)

@[rocq_alias SIdx.case_succ]
def case_succ (n : I) : (n = 0) ⊕' (Σ' m, n = succᵢ m) ⊕' Limit n :=
  match case n with
  | .inl h => .inl h
  | .inr (.inl ⟨m, hm⟩) => .inr (.inl ⟨m, is_succ_S.mp hm⟩)
  | .inr (.inr h) => .inr (.inr h)
@[rocq_alias SIdx.rec]
def rec' {P : I → Sort v}
    (s : P 0)
    (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) :
    ∀ n, P n :=
  WellFounded.fix inst.lt_wf fun n IH =>
    match SIdx.case_succ n with
    | .inl EQ => EQ ▸ s
    | .inr <| .inl ⟨m, EQ⟩ => EQ ▸ f m (IH m (lt_succ_diag_r' EQ))
    | .inr <| .inr Hlim => lim n Hlim IH

@[rocq_alias SIdx.rec_unfold]
theorem rec_unfold {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) (n : I) :
    rec' s f lim n =
      match SIdx.case_succ n with
      | .inl EQ => EQ ▸ s
      | .inr (.inl ⟨m, EQ⟩) => EQ ▸ f m (rec' s f lim m)
      | .inr (.inr Hlim) => lim n Hlim (fun m _ => rec' s f lim m) :=
  inst.lt_wf.fix_eq _ n

@[rocq_alias SIdx.rec_zero]
theorem rec_zero {P : I → Sort v} (s : P 0) (f : ∀ n, P n → P (succᵢ n))
    (lim : ∀ n, Limit n → (∀ m, m < n → P m) → P n) :
    rec' s f lim 0 = s := by
  rw [rec_unfold s f lim 0]
  cases SIdx.case_succ (0 : I) with
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
  cases SIdx.case_succ (succᵢ n) with
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
  cases SIdx.case_succ n with
  | inl EQ => exact absurd EQ Hn.ne_zero
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨m, EQ⟩ := h
      exact absurd (EQ ▸ Hn) (limit_S m)
    | inr Hlim => rfl


end succ

#rocq_ignore SIdx.rec_lim_ext
  "Proof irrelevance already handled automatically by Lean for the theorems \
  rec_zero, rec_succ and rec_lim"

end SIdx

end Iris

/-! ## `local stepindex T`

Code that works at one fixed step index type (e.g. HeapLang at `Nat`) writes `local stepindex Nat`
once, and then uses the step-index-free API: `CMRA α`, `Auth α`, `✓ x`, `α -n> β`, … . The command
records `T` as the step index of the current section (read by `stepindex%`) and opens the scope
`Iris.StepIndexSugar`, in which every `@[indexed]` declaration gets its step index (the binder of
type `stepindex (Type _)`) filled in with `stepindex%` when it is not given, and prints back
without it. Both last until the end of the current section.

The step-index-free notations (`✓ x`, `x ≼ₒ y`, `α -n> β`, `x ~~> y`, `iprop(a ≡ b)`, …) are
available everywhere, next to their `[SI]` forms: they expand to `stepindex%`, which is the step
index of the section, or a hole (to be found by unification) outside a `local stepindex` section.

Rules of thumb:
* every definition, structure or constructor that takes a step index and is used without it is
  `@[indexed]`; lemmas only when nothing else determines their step index (`have h := lemma`);
* in a sugared section a positional step index counts as given only in a full application, or when
  it is the section's own step index variable (`bi_least_fixpoint SI F`);
* the sugar does not reach `simp [lemma]` lists, dot calls on locals (`h.lemma`) or `@C`: write the
  step index there. -/

namespace Iris.StepIndexSugar

open Lean Elab Term

/-- The constants that `f` names (unless `f` is a local variable), with their `@[indexed]` data. -/
meta def indexedHeads (f : Ident) : TermElabM (List (Name × Option IndexedInfo)) := do
  let table := indexedExt.getState (← getEnv)
  -- fast path: no `@[indexed]` declaration has this last name component
  let .str _ last := f.getId.eraseMacroScopes | return []
  unless table.lasts.contains (.mkSimple last) do return []
  if (← isLocalIdent? f).isSome then return []
  return (← resolveGlobalName f.getId).filterMap fun (n, fields) =>
    if fields.isEmpty then some (n, table.decls.find? n) else none

/-- `f args` with the step index of the section filled in, or `none` when it is given (positionally
or by name) or not reached by a partial application. -/
meta def fillSI (i : IndexedInfo) (f : Syntax) (args : Array Syntax) : TermElabM (Option Syntax) := do
  let isNamed (a : Syntax) := a.isOfKind ``Parser.Term.namedArgument
  if args.any fun a => isNamed a && a[1].getId == i.name then return none
  -- filled in already (this is an alternative of an overloaded `C args` coming back)
  if args.any fun a => a.getAtomVal == "stepindex%" || a[0].getAtomVal == "stepindex%" then
    return none
  let si ← `(stepindex%)
  match i.explicitPos with
  | none =>
    let named ← `(Parser.Term.namedArgument| ($(mkIdent i.name) := $si))
    return some (Syntax.mkApp ⟨f⟩ (args.push named |>.map (⟨·⟩)))
  | some p =>
    let posIdx := (List.range args.size).filter fun j =>
      !(isNamed args[j]! || args[j]!.isOfKind ``Parser.Term.ellipsis)
    -- fewer positional arguments than reach the step index: a partial application before it;
    -- as many as all explicit arguments: the step index is given
    unless p ≤ posIdx.length && posIdx.length < i.arity do return none
    -- in a generic section, its step index variable written in place (`C SI F` partially applied):
    -- given. (Not for a constant like `Nat`, which may well be an ordinary argument.)
    let secSI := siExt.getState (← getEnv)
    if h : p < posIdx.length ∧ ((← getLCtx).findFromUserName? secSI).isSome then
      let a := args[posIdx[p]]!
      if a.isIdent && a.getId == secSI then return none
    let k := if h : p < posIdx.length then posIdx[p] else args.size
    return some (Syntax.mkApp ⟨f⟩ ((args.insertIdx! k si.raw).map (⟨·⟩)))

/-- The identifier of a head `C` or `C.{u, …}`. -/
meta def headIdent? (f : Syntax) : Option Ident :=
  if f.isIdent then some ⟨f⟩
  else if f.isOfKind ``Parser.Term.explicitUniv && f[0].isIdent then some ⟨f[0]⟩
  else none

/-- `stx` (`C args`, `C` or `C.{u, …}`) with the step index of the section filled in, when `C` is
`@[indexed]`. When `C` is overloaded, each reading becomes an alternative (with the step index filled
in for the `@[indexed]` ones), and overload resolution picks among them as usual. -/
meta def elabIndexed (stx : Syntax) (head : Syntax) (args : Array Syntax)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let some f := headIdent? head | throwUnsupportedSyntax
  let heads ← indexedHeads f
  unless heads.any (·.2.isSome) do throwUnsupportedSyntax
  -- the head, naming the constant `n` unambiguously
  let headFor (n : Name) : Syntax :=
    let c := mkCIdentFrom f n
    if head.isIdent then c else head.setArg 0 c
  let mut alts : Array Syntax := #[]
  for (n, i?) in heads do
    let h := if heads.length == 1 then head else headFor n
    match i? with
    | some i =>
      let some s ← fillSI i h args | throwUnsupportedSyntax
      alts := alts.push s
    | none => alts := alts.push (if args.isEmpty then h else Syntax.mkApp ⟨h⟩ (args.map (⟨·⟩)))
  let stx' := if h : alts.size = 1 then alts[0] else mkNode choiceKind alts
  -- the default elaborators, not `elabTerm` on `C args`: the result is again `C args`, and must not
  -- come back here (a partial application would get a second step index)
  withMacroExpansion stx stx' <|
    if stx'.isOfKind choiceKind then elabTerm stx' expectedType? else Lean.Elab.Term.elabApp stx' expectedType?

/-- In a `local stepindex` section, `C args` for an `@[indexed]` `C` elaborates with the step index
filled in (see `Iris.Algebra.StepIndex`). -/
@[scoped term_elab app] meta def elabIndexedApp : TermElab := fun stx expectedType? =>
  elabIndexed stx stx[0] stx[1].getArgs expectedType?

/-- A bare `C` (or `C.{u, …}`) for an `@[indexed]` `C`: `C stepindex%` (or `C (SI := stepindex%)`). -/
@[scoped term_elab ident] meta def elabIndexedIdent : TermElab := fun stx expectedType? =>
  elabIndexed stx stx #[] expectedType?

@[scoped term_elab explicitUniv, inherit_doc elabIndexedIdent]
meta def elabIndexedExplicitUniv : TermElab := fun stx expectedType? =>
  elabIndexed stx stx #[] expectedType?

/-- Whether `si` is the step index of the section (set by `local stepindex`). -/
meta def isSectionSI (si : Term) : CoreM Bool := do
  let n := siExt.getState (← getEnv)
  return !n.isAnonymous && si.raw.isIdent && si.raw.getId == n

open PrettyPrinter Delaborator SubExpr in
/-- In a `local stepindex` section, `C SI args` for an `@[indexed]` `C` with an explicit step index
prints as `C args` when `SI` is the step index of the section. -/
@[scoped delab app] meta def delabIndexedApp : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let some i := (indexedExt.getState (← getEnv)).decls.find? c | failure
  let some p := i.explicitPos | failure
  guard (e.getAppNumArgs > i.argIdx)
  unless ← isSectionSI (← withNaryArg i.argIdx delab) do failure
  let stx : Term ← Lean.PrettyPrinter.Delaborator.delabApp
  let `($f $args*) := stx | return stx
  unless p < args.size do return stx
  if args.size == 1 then return f
  return ⟨Syntax.mkApp f (args.eraseIdx! p)⟩

end Iris.StepIndexSugar

namespace Iris

open Lean Parser in
/-- `local stepindex T` makes `T` the step index of the current section: the `@[indexed]`
declarations take it when their step index is not given, and print without it (see the module docs
of `Iris.Algebra.StepIndex`).

```
local stepindex Nat
variable [CMRA α]          -- CMRA Nat α
example (x : α) : ✓ x → ✓ x := id
```
-/
syntax (name := stepindexCmd) Term.attrKind &"stepindex " term : command

open Lean Elab Command in
@[command_elab stepindexCmd]
meta def elabStepindex : CommandElab := fun stx => do
  let `(command| $k:attrKind stepindex $T:term) := stx | throwUnsupportedSyntax
  unless (← liftMacroM <| toAttributeKind k) == .local do
    throwError "`stepindex` must be `local`: it sets the step index of the current section"
  unless T.raw.isIdent do
    throwError "`stepindex` expects an identifier, but got{indentD T}\n\n\
      Introduce an abbreviation first, e.g. `abbrev MySI := ...` then `local stepindex MySI`."
  runTermElabM fun _ => do
    let Te ← Term.elabType T
    unless (← Meta.trySynthInstance (← Meta.mkAppM ``SIdx #[Te])) matches .some _ do
      throwError "`stepindex` requires a `SIdx` instance for{indentExpr Te}"
  siExt.add T.raw.getId .local
  elabCommand (← `(command| open scoped Iris.StepIndexSugar))

end Iris
