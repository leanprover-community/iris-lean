/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.Semantics
public import Iris.Std.GenSetsInstances
meta import Iris.Std.RocqPorting

/-! # Metatheory of HeapLang

This file contains some metatheory about the HeapLang language, which is not needed for
verifying programs: syntactic closedness of expressions and values, and parallel substitution.
-/

@[expose] public section
namespace Iris.HeapLang

open Iris.Std

/-- Sets of variable names, `stringset` in Rocq. -/
abbrev StringSet := Std.ExtTreeSet String compare

/-- Finite maps from variable names to values, `gmap string val` in Rocq. Substitution maps are
generic over the map implementation; this is the default one. -/
abbrev VarMapF := fun V => Std.ExtTreeMap String V compare

/-- Adding a binder to a set of identifiers. -/
@[rocq_alias heap_lang.set_binder_insert]
def Binder.setInsert : Binder → StringSet → StringSet
  | .anon, X => X
  | .named f, X => {f} ∪ X

mutual

/-- Check if expression `e` is closed w.r.t. the set `X` of variable names, and that all
the values in `e` are closed. -/
@[rocq_alias heap_lang.is_closed_expr]
def Exp.isClosed (X : StringSet) : Exp → Bool
  | .val v => v.isClosed
  | .var x => decide (x ∈ X)
  | .rec_ f x e => e.isClosed (f.setInsert (x.setInsert X))
  | .unop _ e | .fst e | .snd e | .injL e | .injR e | .fork e | .free e | .load e => e.isClosed X
  | .app e₁ e₂ | .binop _ e₁ e₂ | .pair e₁ e₂ | .allocN e₁ e₂ | .store e₁ e₂ | .xchg e₁ e₂
  | .faa e₁ e₂ => e₁.isClosed X && e₂.isClosed X
  | .if e₀ e₁ e₂ | .case e₀ e₁ e₂ | .cmpXchg e₀ e₁ e₂ | .resolve e₀ e₁ e₂ =>
      e₀.isClosed X && e₁.isClosed X && e₂.isClosed X
  | .newProph => true

/-- Check that all the values in `v` are closed. -/
@[rocq_alias heap_lang.is_closed_val]
def Val.isClosed : Val → Bool
  | .lit _ => true
  | .rec_ f x e => e.isClosed (f.setInsert (x.setInsert ∅))
  | .pair v₁ v₂ => v₁.isClosed && v₂.isClosed
  | .injL v | .injR v => v.isClosed

end

/-- Insert a binder into a map of values, `binder_insert` in stdpp. -/
def Binder.insertMap [PartialMap M String] (b : Binder) (v : V) (vs : M V) : M V :=
  match b with
  | .anon => vs
  | .named x => PartialMap.insert vs x v

/-- Delete a binder from a map of values, `binder_delete` in stdpp. -/
def Binder.deleteMap [PartialMap M String] (b : Binder) (vs : M V) : M V :=
  match b with
  | .anon => vs
  | .named x => PartialMap.delete vs x

/-- Parallel substitution. -/
@[rocq_alias heap_lang.subst_map]
def Exp.substMap [PartialMap M String] (vs : M Val) : Exp → Exp
  | .val v => .val v
  | .var y => match PartialMap.get? vs y with
    | some v => .val v
    | none => .var y
  | .rec_ f y e => .rec_ f y (e.substMap (y.deleteMap (f.deleteMap vs)))
  | .app e₁ e₂ => .app (e₁.substMap vs) (e₂.substMap vs)
  | .unop op e => .unop op (e.substMap vs)
  | .binop op e₁ e₂ => .binop op (e₁.substMap vs) (e₂.substMap vs)
  | .if e₀ e₁ e₂ => .if (e₀.substMap vs) (e₁.substMap vs) (e₂.substMap vs)
  | .pair e₁ e₂ => .pair (e₁.substMap vs) (e₂.substMap vs)
  | .fst e => .fst (e.substMap vs)
  | .snd e => .snd (e.substMap vs)
  | .injL e => .injL (e.substMap vs)
  | .injR e => .injR (e.substMap vs)
  | .case e₀ e₁ e₂ => .case (e₀.substMap vs) (e₁.substMap vs) (e₂.substMap vs)
  | .allocN e₁ e₂ => .allocN (e₁.substMap vs) (e₂.substMap vs)
  | .free e => .free (e.substMap vs)
  | .load e => .load (e.substMap vs)
  | .store e₁ e₂ => .store (e₁.substMap vs) (e₂.substMap vs)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (e₀.substMap vs) (e₁.substMap vs) (e₂.substMap vs)
  | .xchg e₁ e₂ => .xchg (e₁.substMap vs) (e₂.substMap vs)
  | .faa e₁ e₂ => .faa (e₁.substMap vs) (e₂.substMap vs)
  | .fork e => .fork (e.substMap vs)
  | .newProph => .newProph
  | .resolve e₀ e₁ e₂ => .resolve (e₀.substMap vs) (e₁.substMap vs) (e₂.substMap vs)

open LawfulSet in
theorem Binder.setInsert_mono {b : Binder} {X Y : StringSet} (h : X ⊆ Y) :
    b.setInsert X ⊆ b.setInsert Y := by
  cases b
  · exact h
  · intro x hx
    simp only [Binder.setInsert, mem_union] at hx ⊢
    exact hx.imp id (h x)

@[simp]
theorem Exp.isClosed_ofVal {X : StringSet} {v : Val} : Exp.isClosed X (Exp.ofVal v) = v.isClosed :=
  rfl

@[simp]
theorem Exp.substStr_ofVal {x : String} {v w : Val} :
    Exp.substStr x v (Exp.ofVal w) = Exp.ofVal w := rfl

@[simp]
theorem Exp.substStr_var {x y : String} {v : Val} :
    Exp.substStr x v (.var y) = if x = y then Exp.ofVal v else .var y := by
  simp [Exp.substStr]

@[simp]
theorem Exp.substStr_rec {x : String} {v : Val} {f y : Binder} {e : Exp} :
    Exp.substStr x v (.rec_ f y e)
      = .rec_ f y (if Binder.named x ≠ f ∧ Binder.named x ≠ y then e.substStr x v else e) := by
  simp [Exp.substStr]

@[simp, rocq_alias heap_lang.set_unfold_elem_of_insert_binder]
theorem Binder.mem_setInsert {b : Binder} {X : StringSet} {y : String} :
    y ∈ b.setInsert X ↔ y ∈ X ∨ Binder.named y = b := by
  cases b <;> simp [Binder.setInsert] <;> grind

@[rocq_alias heap_lang.is_closed_weaken]
theorem Exp.isClosed_weaken {X Y : StringSet} {e : Exp} (h : e.isClosed X) (hXY : X ⊆ Y) :
    e.isClosed Y := by
  induction X, e using Exp.isClosed.induct (motive_2 := fun _ => True) generalizing Y <;>
    simp_all [Exp.isClosed]
  · exact hXY _ h
  · rename_i ih
    exact ih (Binder.setInsert_mono (Binder.setInsert_mono hXY))

@[rocq_alias heap_lang.is_closed_weaken_empty]
theorem Exp.isClosed_weaken_empty {X : StringSet} {e : Exp} (h : e.isClosed ∅) : e.isClosed X :=
  Exp.isClosed_weaken h LawfulSet.empty_subset

@[rocq_alias heap_lang.is_closed_subst]
theorem Exp.isClosed_substStr {X : StringSet} {x : String} {v : Val} {e : Exp}
    (hv : v.isClosed) (he : e.isClosed ({x} ∪ X)) : (e.substStr x v).isClosed X := by
  induction e using Exp.substStr.induct (x := x) generalizing X <;>
    (try simp_all [Exp.substStr, Exp.isClosed]) <;> (try grind [Exp.substStr, Exp.isClosed])
  rename_i ih
  split
  · exact ih (Exp.isClosed_weaken he fun y hy => by simp_all <;> grind)
  · exact Exp.isClosed_weaken he fun y hy => by simp_all <;> grind

@[rocq_alias heap_lang.subst_is_closed]
theorem Exp.substStr_isClosed {X : StringSet} {x : String} {v : Val} {e : Exp}
    (he : e.isClosed X) (hx : x ∉ X) : e.substStr x v = e := by
  induction e using Exp.substStr.induct (x := x) generalizing X <;>
    (try simp_all [Exp.substStr, Exp.isClosed]) <;> (try grind [Exp.substStr, Exp.isClosed])
  rename_i ih
  intro hf hx'
  exact ih he (by simp_all)

@[rocq_alias heap_lang.is_closed_subst']
theorem Exp.isClosed_subst {X : StringSet} {b : Binder} {v : Val} {e : Exp}
    (hv : v.isClosed) (he : e.isClosed (b.setInsert X)) : (e.subst b v).isClosed X := by
  cases b
  · exact he
  · exact Exp.isClosed_substStr hv he

@[rocq_alias heap_lang.subst_is_closed_empty]
theorem Exp.substStr_isClosed_empty {x : String} {v : Val} {e : Exp} (he : e.isClosed ∅) :
    e.substStr x v = e :=
  Exp.substStr_isClosed he LawfulSet.mem_empty

@[rocq_alias heap_lang.subst_subst]
theorem Exp.substStr_substStr {x : String} {v v' : Val} {e : Exp} :
    (e.substStr x v').substStr x v = e.substStr x v' := by
  induction e using Exp.substStr.induct (x := x) <;>
    (try simp_all [Exp.substStr]) <;> (try grind [Exp.substStr])

@[rocq_alias heap_lang.subst_subst']
theorem Exp.subst_subst {b : Binder} {v v' : Val} {e : Exp} :
    (e.subst b v').subst b v = e.subst b v' := by
  cases b <;> simp [Exp.subst, Exp.substStr_substStr]

@[rocq_alias heap_lang.subst_subst_ne]
theorem Exp.substStr_substStr_ne {x y : String} {v v' : Val} {e : Exp} (h : x ≠ y) :
    (e.substStr y v').substStr x v = (e.substStr x v).substStr y v' := by
  induction e using Exp.substStr.induct (x := x) <;>
    (try simp_all [Exp.substStr]) <;> (try grind [Exp.substStr])
  all_goals split <;> simp_all

@[rocq_alias heap_lang.subst_subst_ne']
theorem Exp.subst_subst_ne {b₁ b₂ : Binder} {v v' : Val} {e : Exp} (h : b₁ ≠ b₂) :
    (e.subst b₂ v').subst b₁ v = (e.subst b₁ v).subst b₂ v' := by
  cases b₁ <;> cases b₂ <;> simp_all [Exp.subst]
  exact Exp.substStr_substStr_ne h

@[rocq_alias heap_lang.subst_rec']
theorem Exp.subst_rec {f y b : Binder} {v : Val} {e : Exp} (h : b = f ∨ b = y ∨ b = .anon) :
    (Exp.rec_ f y e).subst b v = .rec_ f y e := by
  cases b <;> simp_all [Exp.subst, Exp.substStr] <;> grind

@[rocq_alias heap_lang.subst_rec_ne']
theorem Exp.subst_rec_ne {f y b : Binder} {v : Val} {e : Exp}
    (hf : b ≠ f ∨ f = .anon) (hy : b ≠ y ∨ y = .anon) :
    (Exp.rec_ f y e).subst b v = .rec_ f y (e.subst b v) := by
  cases b <;> simp_all [Exp.subst, Exp.substStr] <;> grind

/-- The Rocq proof of `base_step_is_closed` inlines this case analysis. -/
theorem UnOp.eval_isClosed {op : UnOp} {v v' : Val} (h : op.eval v = some v') : v'.isClosed := by
  unfold UnOp.eval at h
  split at h <;> cases h <;> rfl

@[rocq_alias heap_lang.bin_op_eval_closed]
theorem BinOp.eval_isClosed {op : BinOp} {v₁ v₂ v : Val} (h : op.eval v₁ v₂ = some v) :
    v.isClosed := by
  unfold BinOp.eval at h
  split at h <;> (try split at h) <;> cases h <;> rfl

/-- All values stored in the heap of `σ` are closed. -/
def State.isClosed (σ : State) : Prop := ∀ l v, σ.get? l = some (some v) → v.isClosed

/-- Allocating closed values preserves closedness of the heap. Unlike the Rocq version, this
does not need the allocated locations to be fresh. -/
@[rocq_alias heap_lang.heap_closed_alloc]
theorem State.isClosed_initHeap {σ : State} {l : Loc} {n : Int} {ov : Option Val}
    (hσ : σ.isClosed) (hv : ∀ w, ov = some w → w.isClosed) : (σ.initHeap l n ov).isClosed := by
  intro k w hk
  simp only [State.get?, get?_foldl_insert] at hk
  split at hk
  · exact hv w (by grind)
  · exact hσ k w hk

@[rocq_alias heap_lang.base_step_is_closed]
theorem BaseStep.isClosed {e₁ : Exp} {σ₁ : State} {κ : List Observation} {e₂ : Exp} {σ₂ : State}
    {es : List Exp} (h : BaseStep e₁ σ₁ κ e₂ σ₂ es) (he : e₁.isClosed ∅) (hσ : σ₁.isClosed) :
    e₂.isClosed ∅ ∧ (∀ e ∈ es, e.isClosed ∅) ∧ σ₂.isClosed := by
  induction h <;> simp_all [Exp.isClosed, Val.isClosed]
  case betaS => exact Exp.isClosed_subst he.2 (Exp.isClosed_subst he.1 he.1)
  case unOpS => exact UnOp.eval_isClosed (by assumption)
  case binOpS => exact BinOp.eval_isClosed (by assumption)
  case allocNS => exact State.isClosed_initHeap hσ (by simp_all)
  case freeS => exact State.isClosed_initHeap hσ (by simp)
  case loadS => exact hσ _ _ (by assumption)
  case storeS => exact State.isClosed_initHeap hσ (by simp_all)
  case xchgS => exact ⟨hσ _ _ (by assumption), State.isClosed_initHeap hσ (by simp_all)⟩
  case cmpXchgS =>
    refine ⟨hσ _ _ (by assumption), ?_⟩
    split
    · exact State.isClosed_initHeap hσ (by simp_all)
    · exact hσ
  case faaS => exact State.isClosed_initHeap hσ (by simp [Val.isClosed])
  case newProphS => exact hσ

section SubstMap

variable {M : Type _ → Type _} {V : Type _} [LawfulPartialMap M String]

/-! The following five lemmas correspond to the `binder_insert`/`binder_delete` lemmas of stdpp. -/

@[simp]
theorem Binder.get?_insertMap {b : Binder} {v : V} {vs : M V} {y : String} :
    PartialMap.get? (b.insertMap v vs) y =
      if Binder.named y = b then some v else PartialMap.get? vs y := by
  cases b <;> simp [Binder.insertMap, LawfulPartialMap.get?_insert] <;> grind

@[simp]
theorem Binder.get?_deleteMap {b : Binder} {vs : M V} {y : String} :
    PartialMap.get? (b.deleteMap vs) y =
      if Binder.named y = b then none else PartialMap.get? vs y := by
  cases b <;> simp [Binder.deleteMap, LawfulPartialMap.get?_delete] <;> grind

theorem Binder.deleteMap_empty {b : Binder} : b.deleteMap (∅ : M V) = ∅ :=
  equiv_iff_eq.mp fun _ => by simp [get?_empty]

theorem Binder.deleteMap_delete_comm {b : Binder} {vs : M V} {x : String} :
    b.deleteMap (PartialMap.delete vs x) = PartialMap.delete (b.deleteMap vs) x :=
  equiv_iff_eq.mp fun _ => by simp [LawfulPartialMap.get?_delete] <;> grind

theorem Binder.deleteMap_insert_of_ne {b : Binder} {vs : M V} {x : String} {v : V}
    (h : Binder.named x ≠ b) :
    b.deleteMap (PartialMap.insert vs x v) = PartialMap.insert (b.deleteMap vs) x v :=
  equiv_iff_eq.mp fun _ => by simp [LawfulPartialMap.get?_insert] <;> grind

/-- A map that binds no variable acts as the identity substitution. The Rocq proof of
`subst_map_empty` inlines this argument. -/
theorem Exp.substMap_of_get?_eq_none {vs : M Val} {e : Exp}
    (h : ∀ y, PartialMap.get? vs y = none) : e.substMap vs = e := by
  revert h
  induction vs, e using Exp.substMap.induct <;> intro h <;> simp_all [Exp.substMap]

@[rocq_alias heap_lang.subst_map_empty]
theorem Exp.substMap_empty {e : Exp} : e.substMap (∅ : M Val) = e :=
  Exp.substMap_of_get?_eq_none fun _ => get?_empty _

/-- The variable case of `subst_map_insert`. -/
theorem Exp.substMap_insert_var {x y : String} {v : Val} {vs : M Val} :
    Exp.substMap (PartialMap.insert vs x v) (.var y)
      = (Exp.substMap (PartialMap.delete vs x) (.var y)).substStr x v := by
  by_cases h : x = y
  · simp [Exp.substMap, LawfulPartialMap.get?_insert, LawfulPartialMap.get?_delete, h]
  · cases hg : PartialMap.get? vs y <;>
      simp [Exp.substMap, LawfulPartialMap.get?_insert, LawfulPartialMap.get?_delete, hg, h]

@[rocq_alias heap_lang.subst_map_insert]
theorem Exp.substMap_insert {x : String} {v : Val} {vs : M Val} {e : Exp} :
    e.substMap (PartialMap.insert vs x v) = (e.substMap (PartialMap.delete vs x)).substStr x v := by
  induction vs, e using Exp.substMap.induct <;>
    (try exact Exp.substMap_insert_var) <;> simp_all [Exp.substMap, Exp.substStr]
  rename_i f y e ih
  split
  · next h =>
    rw [Binder.deleteMap_insert_of_ne (by grind), Binder.deleteMap_insert_of_ne (by grind), ih,
      Binder.deleteMap_delete_comm, Binder.deleteMap_delete_comm]
  · next h =>
    refine congrArg (Exp.substMap · e) (equiv_iff_eq.mp fun k => ?_)
    simp [LawfulPartialMap.get?_insert, LawfulPartialMap.get?_delete]
    grind

@[rocq_alias heap_lang.subst_map_singleton]
theorem Exp.substMap_singleton {x : String} {v : Val} {e : Exp} :
    e.substMap (PartialMap.singleton x v : M Val) = e.substStr x v := by
  rw [PartialMap.singleton, Exp.substMap_insert, LawfulPartialMap.delete_empty, Exp.substMap_empty]

@[rocq_alias heap_lang.subst_map_binder_insert]
theorem Exp.substMap_insertMap {b : Binder} {v : Val} {vs : M Val} {e : Exp} :
    e.substMap (b.insertMap v vs) = (e.substMap (b.deleteMap vs)).subst b v := by
  cases b
  · rfl
  · exact Exp.substMap_insert

@[rocq_alias heap_lang.subst_map_binder_insert_empty]
theorem Exp.substMap_insertMap_empty {b : Binder} {v : Val} {e : Exp} :
    e.substMap (b.insertMap v (∅ : M Val)) = e.subst b v := by
  rw [Exp.substMap_insertMap, Binder.deleteMap_empty, Exp.substMap_empty]

@[rocq_alias heap_lang.subst_map_binder_insert_2]
theorem Exp.substMap_insertMap_2 {b₁ b₂ : Binder} {v₁ v₂ : Val} {vs : M Val} {e : Exp} :
    e.substMap (b₁.insertMap v₁ (b₂.insertMap v₂ vs))
      = ((e.substMap (b₂.deleteMap (b₁.deleteMap vs))).subst b₁ v₁).subst b₂ v₂ := by
  cases b₁ <;> cases b₂ <;>
    simp_all [Binder.insertMap, Binder.deleteMap, Exp.subst, Exp.substMap_insert]
  rename_i s₁ s₂
  by_cases h : s₁ = s₂
  · subst h
    rw [LawfulPartialMap.delete_insert, LawfulPartialMap.delete_delete, Exp.substStr_substStr]
  · rw [LawfulPartialMap.delete_insert_of_ne (Ne.symm h), Exp.substMap_insert,
      LawfulPartialMap.delete_delete_comm, Exp.substStr_substStr_ne h]

@[rocq_alias heap_lang.subst_map_binder_insert_2_empty]
theorem Exp.substMap_insertMap_2_empty {b₁ b₂ : Binder} {v₁ v₂ : Val} {e : Exp} :
    e.substMap (b₁.insertMap v₁ (b₂.insertMap v₂ (∅ : M Val)))
      = (e.subst b₁ v₁).subst b₂ v₂ := by
  rw [Exp.substMap_insertMap_2, Binder.deleteMap_empty, Binder.deleteMap_empty, Exp.substMap_empty]

@[rocq_alias heap_lang.subst_map_is_closed]
theorem Exp.substMap_isClosed {X : StringSet} {vs : M Val} {e : Exp} (he : e.isClosed X)
    (h : ∀ x ∈ X, PartialMap.get? vs x = none) : e.substMap vs = e := by
  revert X
  induction vs, e using Exp.substMap.induct <;> intros <;>
    simp_all [Exp.substMap, Exp.isClosed] <;> (try grind)
  rename_i ih he h
  exact ih he fun x hx _ _ => h x (by simp_all)

@[rocq_alias heap_lang.subst_map_is_closed_empty]
theorem Exp.substMap_isClosed_empty {vs : M Val} {e : Exp} (he : e.isClosed ∅) :
    e.substMap vs = e :=
  Exp.substMap_isClosed he fun _ hx => absurd hx LawfulSet.mem_empty

end SubstMap

end Iris.HeapLang
