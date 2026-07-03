/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.Std.GenMultiSets
public import Batteries.Data.List.Perm
public import Batteries.Data.List.Count

@[expose] public section

namespace Iris.Std

/-- Lists up to permutation. -/
def listPermSetoid (α : Type _) : Setoid (List α) where
  r := List.Perm
  iseqv := ⟨.refl, (·.symm), (·.trans)⟩

/-- A finite multiset, represented as a list quotiented by permutation. -/
def Multiset (α : Type _) : Type _ := Quotient (listPermSetoid α)

namespace Multiset

variable {α : Type _}

/-- The multiset of a list. -/
def ofList (l : List α) : Multiset α := Quotient.mk _ l

instance : EmptyCollection (Multiset α) := ⟨ofList []⟩
instance : Singleton α (Multiset α) := ⟨fun a => ofList [a]⟩

/-- Multiset sum (`⊎`): list append. -/
def disjUnion (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁ ++ l₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.append h₂))

/-- A chosen representative (noncomputable; uses choice). -/
noncomputable def out (s : Multiset α) : List α := Classical.choose s.exists_rep

theorem ofList_out (s : Multiset α) : ofList (out s) = s := Classical.choose_spec s.exists_rep

theorem out_ofList_perm (l : List α) : List.Perm (out (ofList l)) l :=
  Quotient.exact (ofList_out (ofList l))

section Dec
variable [DecidableEq α]

/-- Multiplicity: number of occurrences in any representative. -/
def multiplicity (a : α) (s : Multiset α) : Nat :=
  Quotient.liftOn s (fun l => l.count a) (fun _ _ h => h.count_eq a)

/-- Difference (`∖`): per-element truncated subtraction. -/
instance : SDiff (Multiset α) :=
  ⟨fun s t => Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁.diff l₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.diff h₂))⟩

/-- Union (`∪`): per-element maximum. -/
instance : Union (Multiset α) :=
  ⟨fun s t => Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁ ++ l₂.diff l₁))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.append (h₂.diff h₁)))⟩

/-- Intersection (`∩`): per-element minimum. -/
instance : Inter (Multiset α) :=
  ⟨fun s t => Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁.diff (l₁.diff l₂)))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.diff (h₁.diff h₂)))⟩

/-- `count` of a list difference (not available under this name in Batteries). -/
private theorem count_diff (a : α) (l₁ l₂ : List α) :
    (l₁.diff l₂).count a = l₁.count a - l₂.count a := by
  induction l₂ generalizing l₁ with
  | nil => simp
  | cons b bs ih =>
    rw [List.diff_cons, ih, List.count_erase, List.count_cons]
    by_cases hab : b = a
    · subst hab; simp; omega
    · simp [hab]

instance : MultiSet (Multiset α) α where
  multiplicity := multiplicity
  disjUnion := disjUnion

instance : LawfulMultiSet (Multiset α) α where
  ext := by
    intro X Y h
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    exact Quotient.sound (List.perm_iff_count.mpr h)
  multiplicity_empty := by intro x; show ([] : List α).count x = 0; simp
  multiplicity_singleton_eq := by intro x; show ([x] : List α).count x = 1; simp
  multiplicity_singleton_ne := by
    intro x y hxy; show ([y] : List α).count x = 0
    rw [List.count_eq_zero]; simp [hxy]
  multiplicity_disjUnion := by
    intro X Y x
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    show (l₁ ++ l₂).count x = l₁.count x + l₂.count x
    exact List.count_append ..
  multiplicity_difference := by
    intro X Y x
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    show (l₁.diff l₂).count x = l₁.count x - l₂.count x
    exact count_diff ..
  multiplicity_union := by
    intro X Y x
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    show (l₁ ++ l₂.diff l₁).count x = max (l₁.count x) (l₂.count x)
    rw [List.count_append, count_diff]; omega
  multiplicity_intersection := by
    intro X Y x
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    show (l₁.diff (l₁.diff l₂)).count x = min (l₁.count x) (l₂.count x)
    rw [count_diff, count_diff]; omega

theorem multiplicity_out (a : α) (s : Multiset α) : multiplicity a s = (out s).count a := by
  induction s using Quotient.inductionOn with | _ l =>
  show l.count a = (out (ofList l)).count a
  exact ((out_ofList_perm l).count_eq a).symm

noncomputable instance : FiniteMultiSet (Multiset α) α where
  toList s := out s

noncomputable instance : LawfulFiniteMultiSet (Multiset α) α where
  mem_toList {a s} := by
    show a ∈ out s ↔ 0 < multiplicity a s
    rw [multiplicity_out, List.count_pos_iff]
  toList_empty := by
    show out (∅ : Multiset α) = []
    exact List.perm_nil.mp (out_ofList_perm [])
  toList_singleton {a} := by
    show out ({a} : Multiset α) = [a]
    exact List.perm_singleton.mp (out_ofList_perm [a])
  toList_disjUnion {X Y} := by
    show List.Perm (out (X ⊎ Y)) (out X ++ out Y)
    induction X using Quotient.inductionOn with | _ l₁ =>
    induction Y using Quotient.inductionOn with | _ l₂ =>
    refine (out_ofList_perm (l₁ ++ l₂)).trans ?_
    exact (out_ofList_perm l₁).symm.append (out_ofList_perm l₂).symm

end Dec

end Multiset

end Iris.Std
