/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import Iris.Algebra.Heap
import Iris.Algebra.Lib.ClassicalHeaps

/-- Heaps with intrinsically finite domain, represented as an association list.
Keys taken to be Nat for the sake of example. -/

inductive FiniteDomFunction (V : Type _)
| empty : FiniteDomFunction V
| set : Nat → V → FiniteDomFunction V → FiniteDomFunction V
| remove : Nat → FiniteDomFunction V → FiniteDomFunction V

open FiniteDomFunction

@[simp] def FiniteDomFunction.lookup (f : FiniteDomFunction V) (k : Nat) : Option V :=
  match f with
  | .empty => none
  | .set n v' rest => if n = k then some v' else rest.lookup k
  | .remove n rest => if n = k then none else rest.lookup k

@[simp] def FiniteDomFunction.update (f : FiniteDomFunction V) (k : Nat) (v : Option V) : FiniteDomFunction V :=
  match v with
  | some v' => f.set k v'
  | none => f.remove k

@[simp] def FiniteDomFunction.map (F : Nat → V → Option V') (f : FiniteDomFunction V)  : FiniteDomFunction V' :=
  match f with
  | .empty => .empty
  | .set n v rest =>
      match (F n v) with
      | .some r => .set n r (rest.map F)
      | .none => .remove n (rest.map F)
  | .remove n rest => .remove n (rest.map F)

@[simp] def FiniteDomFunction.fresh (f : FiniteDomFunction V) : Nat :=
  match f with
  | .empty => 0
  | .set n _ rest => max (n + 1) rest.fresh
  | .remove n rest => max (n + 1) rest.fresh

@[simp] def FiniteDomFunction.construct (f : Nat → Option V) (N : Nat) : FiniteDomFunction V :=
  match N with
  | .zero => .empty
  | .succ N' =>
      match (f N') with
      | some v => .set N' v (FiniteDomFunction.construct f N')
      | none => (FiniteDomFunction.construct f N')

@[simp] def FiniteDomFunction.construct_spec (f : Nat → Option V) (N : Nat) : Nat → (Option V) :=
  fun n => if n < N then f n else none

theorem FiniteDomFunction.lookup_update (f : FiniteDomFunction V):
    (f.update k v).lookup = fset (f.lookup) k v := by
  refine funext (fun k' => ?_)
  cases f <;> cases v <;> simp [fset]

theorem FiniteDomFunction.fresh_lookup_ge (f : FiniteDomFunction V) n :
    f.fresh ≤ n → f.lookup n = none := by
  induction f
  · simp
  · rename_i n' v' rest IH
    intro H
    simp at H
    simp
    split <;> rename_i h
    · omega
    · apply IH
      omega
  · rename_i n' rest IH
    intro H
    simp at H
    simp
    intro H'
    apply IH
    omega

theorem FiniteDomFunction.construct_get (f : Nat → Option V) (N : Nat) :
    lookup (construct f N) = construct_spec f N := by
  refine funext (fun k => ?_)
  rcases Nat.lt_or_ge k N with (HL|HG)
  · induction N <;> simp
    rename_i N' IH
    split <;> rename_i h
    · simp [h]
      split
      · simp_all
      · rw [IH (by omega)]
        simp
        omega
    · rw [if_pos HL]
      if h : k < N'
        then
          simp [IH h]
          intro H1
          omega
        else
          have Hx : k = N' := by omega
          simp_all
          clear Hx
          clear h
          suffices (∀ N'', N' ≤ N'' → (construct f N').lookup N'' = none) by apply this _ N'.le_refl
          induction N'
          · simp
          · rename_i n' IH
            intro N'' H
            simp
            cases h : f n' <;> simp
            · apply IH
              omega
            · split
              · simp
                exfalso
                omega
              · apply IH
                omega
  · simp
    rw [if_neg (by omega)]
    induction N <;> simp
    rename_i N' IH
    split
    · simp only [lookup]
      split; omega
      apply IH
      omega
    · apply IH
      omega
instance FiniteDomFunction.instFiniteDomStore : Store (FiniteDomFunction V) Nat (Option V) where
  get := lookup
  set := update
  get_set_eq He := by simp only [lookup_update, fset, if_pos He]
  get_set_ne He := by simp only [lookup_update, fset, if_neg He]

abbrev op_lift (op : V → V → V) (v1 v2 : Option V) : Option V :=
  match v1, v2 with
  | some v1, some v2 => some (op v1 v2)
  | some v1, none => some v1
  | none, some v2 => some v2
  | none, none => none

instance FiniteDomFunction.instFiniteDomHeap : Heap (fun V => FiniteDomFunction V) Nat where
  hmap h f := f.map h
  hmap_alloc := by
    intros V t k v V' f H
    induction t
    · simp_all [empty, Store.get, map]
    · rename_i n' v' t' IH
      simp_all [Store.get]
      cases h1 : f n' v' <;> simp <;> split <;> rename_i h2 <;> simp_all
    · rename_i n' t' IH
      simp_all [Store.get]
  hmap_unalloc := by
    intros V t k V' f H
    induction t
    · simp_all [empty, Store.get, map]
    · rename_i n' v' t' IH
      simp_all [Store.get]
      cases h1 : f n' v' <;> simp only [lookup] <;> split <;> simp_all
    · rename_i n' t' IH
      simp_all [Store.get]
  empty _ := .empty
  get_empty := by intros; simp [Store.get]
  merge op t1 t2 := construct (fun n => op_lift op (t1.lookup n) (t2.lookup n)) (max t1.fresh t2.fresh)
  get_merge := by
    intro V op t1 t2 k
    simp only [Store.get]
    simp [FiniteDomFunction.construct_get]
    split <;> rename_i h
    · rfl
    · have Ht1 : t1.fresh ≤ k := by omega
      have Ht2 : t2.fresh ≤ k := by omega
      rw [FiniteDomFunction.fresh_lookup_ge _ _ Ht1]
      rw [FiniteDomFunction.fresh_lookup_ge _ _ Ht2]

instance instFinitDomAllocHeap : AllocHeap (fun V => FiniteDomFunction V) Nat  where
  notFull _ := True
  fresh {_ f} _ := f.fresh
  get_fresh {_ f _} := fresh_lookup_ge f f.fresh (f.fresh.le_refl)

instance : UnboundedHeap (fun V => FiniteDomFunction V) Nat where
  notFull_empty := by simp [notFull]
  notFull_set_fresh {V t v H} := by simp [notFull]
