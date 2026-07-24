module

public import IrisDoNightly.Semantics
public import Std.Data.ExtTreeMap
public import Std.Data.ExtTreeSet

@[expose] public section
namespace Iris.HeapLang

open _root_.Std Iris.Std

/-! ## The separation algebra operations -/

def State.disjoint (σ₁ σ₂ : State) : Prop :=
  ∀ l, σ₁.get? l = none ∨ σ₂.get? l = none

def State.union (σ₁ σ₂ : State) : State where
  heap := σ₁.heap ∪ σ₂.heap
  usedProphId := σ₁.usedProphId ∪ σ₂.usedProphId

def State.emp : State := ⟨∅, ∅⟩

def State.single (l : Loc) (v : Option Val) : State :=
  ⟨(∅ : ExtTreeMap Loc (Option Val) compare).insert l v, ∅⟩

scoped infixl:70 " #ₕ " => State.disjoint
scoped infixl:65 " ⊎ₕ " => State.union

theorem State.ext' {σ₁ σ₂ : State}
    (hh : σ₁.heap = σ₂.heap) (hu : σ₁.usedProphId = σ₂.usedProphId) : σ₁ = σ₂ := by
  cases σ₁; cases σ₂; subst hh; subst hu; rfl

theorem State.get?_eq (σ : State) (l : Loc) : σ.get? l = σ.heap[l]? := rfl

@[simp] theorem State.get?_union (σ₁ σ₂ : State) (l : Loc) :
    (σ₁ ⊎ₕ σ₂).get? l = (σ₂.get? l).or (σ₁.get? l) := by
  simp only [State.get?_eq, State.union]
  exact ExtTreeMap.getElem?_union

@[simp] theorem State.get?_emp (l : Loc) : State.emp.get? l = none := by
  simp only [State.get?_eq, State.emp]
  exact ExtTreeMap.getElem?_empty

theorem State.get?_single (l l' : Loc) (v : Option Val) :
    (State.single l v).get? l' = if l' = l then some v else none := by
  simp only [State.get?_eq, State.single]
  rw [ExtTreeMap.getElem?_insert, ExtTreeMap.getElem?_empty]
  by_cases h : l = l'
  · subst h; simp [compare_self]
  · rw [if_neg (by simpa [compare_eq_iff_eq] using h), if_neg (fun hc => h hc.symm)]

theorem State.union_none_iff (σ₁ σ₂ : State) (l : Loc) :
    (σ₁ ⊎ₕ σ₂).get? l = none ↔ σ₁.get? l = none ∧ σ₂.get? l = none := by
  simp only [State.get?_union, Option.or_eq_none_iff]
  exact And.comm

theorem State.disjoint_comm {σ₁ σ₂ : State} (h : σ₁ #ₕ σ₂) : σ₂ #ₕ σ₁ :=
  fun l => (h l).symm

theorem State.union_comm {σ₁ σ₂ : State} (h : σ₁ #ₕ σ₂) : σ₁ ⊎ₕ σ₂ = σ₂ ⊎ₕ σ₁ := by
  apply State.ext'
  · ext l
    simp only [State.union, ExtTreeMap.getElem?_union]
    rcases h l with hl | hl <;> simp only [State.get?_eq] at hl <;> simp [hl]
  · show σ₁.usedProphId ∪ σ₂.usedProphId = σ₂.usedProphId ∪ σ₁.usedProphId
    ext k; simp only [ExtTreeSet.mem_union_iff]; exact Or.comm

theorem State.union_assoc (σ₁ σ₂ σ₃ : State) :
    (σ₁ ⊎ₕ σ₂) ⊎ₕ σ₃ = σ₁ ⊎ₕ (σ₂ ⊎ₕ σ₃) := by
  apply State.ext'
  · ext l; simp only [State.union, ExtTreeMap.getElem?_union, Option.or_assoc]
  · show (σ₁.usedProphId ∪ σ₂.usedProphId) ∪ σ₃.usedProphId
        = σ₁.usedProphId ∪ (σ₂.usedProphId ∪ σ₃.usedProphId)
    ext k; simp only [ExtTreeSet.mem_union_iff]; exact or_assoc

theorem State.disjoint_union_left {σ₁ σ₂ σ₃ : State} :
    (σ₁ ⊎ₕ σ₂) #ₕ σ₃ ↔ σ₁ #ₕ σ₃ ∧ σ₂ #ₕ σ₃ := by
  simp only [State.disjoint, State.union_none_iff]
  grind

theorem State.disjoint_union_right {σ₁ σ₂ σ₃ : State} :
    σ₁ #ₕ (σ₂ ⊎ₕ σ₃) ↔ σ₁ #ₕ σ₂ ∧ σ₁ #ₕ σ₃ := by
  simp only [State.disjoint, State.union_none_iff]
  grind

theorem State.emp_disjoint (σ : State) : State.emp #ₕ σ :=
  fun l => Or.inl (State.get?_emp l)

theorem State.emp_union (σ : State) : State.emp ⊎ₕ σ = σ := by
  apply State.ext'
  · ext l
    simp only [State.union, State.emp, ExtTreeMap.getElem?_union, ExtTreeMap.getElem?_empty,
      Option.or_none]
  · show State.emp.usedProphId ∪ σ.usedProphId = σ.usedProphId
    ext k; simp only [State.emp, ExtTreeSet.mem_union_iff, ExtTreeSet.not_mem_empty, false_or]

end Iris.HeapLang
