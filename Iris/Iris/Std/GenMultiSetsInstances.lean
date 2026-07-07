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

/-- Induction on `Multiset`: it suffices to consider `ofList l`. -/
@[elab_as_elim] protected theorem ind {motive : Multiset α → Prop}
    (mk : ∀ l, motive (ofList l)) (s : Multiset α) : motive s := Quotient.ind mk s

/-- Induction on two `Multiset`s simultaneously. -/
@[elab_as_elim] protected theorem ind₂ {motive : Multiset α → Multiset α → Prop}
    (mk : ∀ l₁ l₂, motive (ofList l₁) (ofList l₂)) (s t : Multiset α) : motive s t :=
  Quotient.ind₂ mk s t

instance : EmptyCollection (Multiset α) := ⟨ofList []⟩
instance : Singleton α (Multiset α) := ⟨fun a => ofList [a]⟩

theorem empty_eq : (∅ : Multiset α) = ofList [] := rfl
theorem singleton_eq (a : α) : ({a} : Multiset α) = ofList [a] := rfl

/-- Multiset sum (`⊎`): list append. -/
def disjUnion (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁ ++ l₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.append h₂))

/-- An arbitrary list representative. -/
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

/-- Union (`∪`): per-element maximum, via `l₁ ++ (l₂ ∖ l₁)`. -/
instance : Union (Multiset α) :=
  ⟨fun s t => Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁ ++ l₂.diff l₁))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.append (h₂.diff h₁)))⟩

/-- Intersection (`∩`): per-element minimum, via `l₁ ∖ (l₁ ∖ l₂)`. -/
instance : Inter (Multiset α) :=
  ⟨fun s t => Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁.diff (l₁.diff l₂)))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (h₁.diff (h₁.diff h₂)))⟩

instance : MultiSet (Multiset α) α where
  multiplicity := multiplicity
  disjUnion := disjUnion

/-- Count of a `List.diff`. -/
private theorem count_diff (a : α) (l₁ l₂ : List α) :
    (l₁.diff l₂).count a = l₁.count a - l₂.count a := by
  induction l₂ generalizing l₁ with
  | nil => simp
  | cons b bs ih => rw [List.diff_cons, ih, List.count_erase, List.count_cons]; omega

theorem multiplicity_ofList (a : α) (l : List α) :
    MultiSet.multiplicity a (ofList l) = l.count a := rfl
theorem disjUnion_ofList (l₁ l₂ : List α) :
    (ofList l₁ ⊎ ofList l₂ : Multiset α) = ofList (l₁ ++ l₂) := rfl
theorem sdiff_ofList (l₁ l₂ : List α) :
    (ofList l₁ \ ofList l₂ : Multiset α) = ofList (l₁.diff l₂) := rfl
theorem union_ofList (l₁ l₂ : List α) :
    (ofList l₁ ∪ ofList l₂ : Multiset α) = ofList (l₁ ++ l₂.diff l₁) := rfl
theorem inter_ofList (l₁ l₂ : List α) :
    (ofList l₁ ∩ ofList l₂ : Multiset α) = ofList (l₁.diff (l₁.diff l₂)) := rfl

instance : LawfulMultiSet (Multiset α) α where
  ext := by
    intro X Y
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    exact fun h => Quotient.sound (List.perm_iff_count.mpr h)
  multiplicity_empty := by simp [empty_eq, multiplicity_ofList]
  multiplicity_singleton_eq := by simp [singleton_eq, multiplicity_ofList]
  multiplicity_singleton_ne := by
    intro x y h
    simp only [singleton_eq, multiplicity_ofList, List.count_eq_zero, List.mem_singleton]
    exact h
  multiplicity_disjUnion := by
    intro X Y x
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    simp [disjUnion_ofList, multiplicity_ofList, List.count_append]
  multiplicity_difference := by
    intro X Y x
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    simp [sdiff_ofList, multiplicity_ofList, count_diff]
  multiplicity_union := by
    intro X Y x
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    simp only [union_ofList, multiplicity_ofList, List.count_append, count_diff]; omega
  multiplicity_intersection := by
    intro X Y x
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    simp only [inter_ofList, multiplicity_ofList, count_diff]; omega

theorem multiplicity_out (a : α) (s : Multiset α) :
    MultiSet.multiplicity a s = (out s).count a := by
  induction s using Multiset.ind with | mk l =>
  rw [multiplicity_ofList]; exact ((out_ofList_perm l).count_eq a).symm

noncomputable instance : FiniteMultiSet (Multiset α) α where
  toList s := out s

noncomputable instance : LawfulFiniteMultiSet (Multiset α) α where
  mem_toList {a s} := by
    show a ∈ out s ↔ 0 < MultiSet.multiplicity a s
    rw [multiplicity_out, List.count_pos_iff]
  toList_empty := List.perm_nil.mp (out_ofList_perm [])
  toList_singleton {a} := List.perm_singleton.mp (out_ofList_perm [a])
  toList_disjUnion {X Y} := by
    show List.Perm (out (X ⊎ Y)) (out X ++ out Y)
    induction X, Y using Multiset.ind₂ with | mk l₁ l₂ =>
    exact (out_ofList_perm (l₁ ++ l₂)).trans
      ((out_ofList_perm l₁).symm.append (out_ofList_perm l₂).symm)

end Dec

end Multiset

end Iris.Std
