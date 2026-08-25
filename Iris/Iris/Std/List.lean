/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/
module

public import Iris.Std.FromMathlib
public import Iris.Std.Classes
public import Iris.Std.Option
import Batteries.Data.List.Basic
import Batteries.Data.List.Perm

/-! # List Lemmas -/

@[expose] public section

namespace List

/-- List equivalence relation parameterized by an element equivalence relation. -/
inductive Equiv {α : Type _} (R : α → α → Prop) : List α → List α → Prop where
  | nil : Equiv R [] []
  | cons {x y : α} {l k : List α} : R x y → Equiv R l k → Equiv R (x :: l) (y :: k)

def zipIdxInt {α : Type _} (l : List α) (n : Int) : List (α × Int) :=
  l.mapIdx (fun i v => (v, (i : Int) + n))

/-- `inserts i k l` overwrites `l` at the consecutive positions `i, i+1, …` with the
elements of `k`. Indices past the end of `l` are no-ops (as for `List.set`), so `l`'s
length is unchanged. This is the Lean counterpart of stdpp's `list_inserts`. -/
def inserts {α : Type _} (i : Nat) : List α → List α → List α
  | [],     l => l
  | x :: k, l => (inserts (i + 1) k l).set i x

theorem mem_le_foldr_max (x : Int) (L : List Int) (h : x ∈ L) :
    x ≤ L.foldr max 0 := by induction L <;> grind

theorem nodup_map_of_injective {B : Type _} {f : A → B} {l : List A}
    (hinj : f.Injective) (hnodup : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp [List.Nodup]
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [List.nodup_cons] at hnodup ⊢
    simp only [List.mem_map]
    refine ⟨?_, ih hnodup.2⟩
    intro ⟨y, hy, heq⟩
    cases hinj heq.symm
    exact hnodup.1 hy

theorem Forall₂.append {l₁ l₁' l₂ l₂'} : List.Forall₂ R l₁ l₂ → List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | .nil, h => h
  | .cons step rest, h => .cons step (append rest h)

@[grind →]
theorem exists_of_forall₂_cons {l₁ l₂} {x} : List.Forall₂ R (x :: l₁) l₂ →
    ∃ y l₂', l₂ = y :: l₂' ∧ R x y ∧ List.Forall₂ R l₁ l₂'
  | .cons y l₂' => by grind

@[grind →]
theorem exists_of_forall₂_append {l₁ l₁' l} (h : List.Forall₂ R (l₁ ++ l₁') l) :
     ∃ l₂ l₂', l = l₂ ++ l₂' ∧ List.Forall₂ R l₁ l₂ ∧ List.Forall₂ R l₁' l₂' ∧ l₁.length = l₂.length := by
  induction l₁ generalizing l with
  | nil =>
    exists [], l
    simpa using h
  | cons x l₁ IH =>
    grind only [= List.cons_append, → exists_of_forall₂_cons, =_ List.cons_append,
      = List.length_cons, List.Forall₂.cons]

@[grind =]
theorem getElem?_some_iff_append
{a : α} {i : Nat} {l : List α} : l[i]? = some a ↔ ∃ s t : List α, l = s ++ a :: t ∧ s.length = i := by
  refine ⟨fun h => ?_, ?_⟩
  · induction i generalizing l with
    | zero =>
      rcases l with _ | ⟨hd, tl⟩
      · simp at h
      · simpa using h
    | succ i IH =>
      rcases l with _ | ⟨hd, tl⟩
      · simp at h
      simp at h
      grind only [=_ List.cons_append, = List.length_cons]
  · rintro ⟨ps, ss, rfl, h2⟩
    grind only [= List.getElem?_append, = List.getElem?_cons]

theorem Forall₂.length_eq {R : α → β → Prop} {l : List α} {k : List β} :
    List.Forall₂ R l k → l.length = k.length
  | .nil => rfl
  | .cons _ h => congrArg (· + 1) (h.length_eq)

theorem Forall₂.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) {l : List α} {k : List β}
    (h : Forall₂ R l k) : Forall₂ S l k := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (H hab) ih



theorem Forall₂.refl {R : α → α → Prop} (H : ∀ a, R a a) : (l : List α) → Forall₂ R l l
  | [] => .nil
  | _ :: l => .cons (H _) (Forall₂.refl H l)

theorem Forall₂.rfl {R : α → α → Prop} (H : ∀ a, R a a) {l : List α} : Forall₂ R l l :=
  Forall₂.refl H l

theorem Forall₂.symm {R : α → α → Prop} (H : ∀ {a b}, R a b → R b a) {l k : List α}
    (h : Forall₂ R l k) : Forall₂ R k l := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (H hab) ih

theorem Forall₂.trans {R : α → α → Prop} (H : ∀ {a b c}, R a b → R b c → R a c) :
    ∀ {l k m : List α}, Forall₂ R l k → Forall₂ R k m → Forall₂ R l m
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (H h1 h2) (Forall₂.trans (R := R) H t1 t2)

theorem Forall₂.equivalence {R : α → α → Prop} (H : Equivalence R) : Equivalence (Forall₂ R) where
  refl := Forall₂.refl H.1
  symm := Forall₂.symm H.2
  trans := Forall₂.trans (R := R) H.3

theorem Forall₂.map {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (H : ∀ {a b}, R a b → S (f a) (g b)) {l : List α} {k : List β}
    (h : Forall₂ R l k) : Forall₂ S (l.map f) (k.map g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (H hab) ih

theorem Forall₂.getElem? {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) (i : Nat) : Option.Forall₂ R l[i]? k[i]? := by
  induction h generalizing i with
  | nil => exact trivial
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i

theorem Forall₂.getD {R : α → β → Prop} {a : α} {b : β} (hab : R a b) {l : List α} {k : List β}
    (h : Forall₂ R l k) (i : Nat) : R (l.getD i a) (k.getD i b) :=
  (h.getElem? i).getD hab

theorem Forall₂.of_getElem? {R : α → β → Prop} {l : List α} {k : List β}
    (h : ∀ (i : Nat), Option.Forall₂ R l[i]? k[i]?) : Forall₂ R l k := by
  induction l generalizing k with
  | nil =>
    cases k with
    | nil => exact .nil
    | cons b k' => exact (h 0).elim
  | cons a l' ih =>
    cases k with
    | nil => exact (h 0).elim
    | cons b k' => exact .cons (h 0) (ih fun i => h (i + 1))

theorem Forall₂.take {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : (m : Nat) → Forall₂ R (l.take m) (k.take m)
  | 0 => .nil
  | m + 1 => by
    cases h with
    | nil => exact .nil
    | cons hd t => exact .cons hd (t.take m)

theorem Forall₂.drop {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : (m : Nat) → Forall₂ R (l.drop m) (k.drop m)
  | 0 => h
  | m + 1 => by
    cases h with
    | nil => exact .nil
    | cons _ t => exact t.drop m

theorem Forall₂.reverse {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : Forall₂ R l.reverse k.reverse := by
  induction h with
  | nil => exact .nil
  | cons hd t ih => rw [List.reverse_cons, List.reverse_cons]; exact ih.append (.cons hd .nil)

theorem Forall₂.replicate {R : α → β → Prop} {a : α} {b : β} (H : R a b) :
    (m : Nat) → Forall₂ R (List.replicate m a) (List.replicate m b)
  | 0 => .nil
  | m + 1 => by rw [List.replicate_succ, List.replicate_succ]; exact .cons H (Forall₂.replicate H m)

theorem Forall₂.getLast? {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : Option.Forall₂ R l.getLast? k.getLast? := by
  induction h with
  | nil => exact trivial
  | @cons a b l' k' hab t ih =>
    cases t with
    | nil => rw [List.getLast?_singleton, List.getLast?_singleton]; exact hab
    | cons hd t2 => rw [List.getLast?_cons_cons, List.getLast?_cons_cons]; exact ih

theorem Forall₂.set {R : α → β → Prop} {a : α} {b : β} (hab : R a b) {l : List α} {k : List β}
    (h : Forall₂ R l k) : (i : Nat) → Forall₂ R (l.set i a) (k.set i b)
  | 0 => by cases h with | nil => exact .nil | cons _ t => exact .cons hab t
  | i + 1 => by cases h with | nil => exact .nil | cons hd t => exact .cons hd (t.set hab i)

theorem Forall₂.inserts {R : α → β → Prop} {k₁ : List α} {k₂ : List β} (hk : Forall₂ R k₁ k₂)
    {l₁ : List α} {l₂ : List β} (hl : Forall₂ R l₁ l₂) :
    ∀ i : Nat, Forall₂ R (List.inserts i k₁ l₁) (List.inserts i k₂ l₂) := by
  induction hk with
  | nil => exact fun _ => hl
  | cons hab _ ih => exact fun i => (ih (i + 1)).set hab i

theorem Forall₂.eraseIdx {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : (i : Nat) → Forall₂ R (l.eraseIdx i) (k.eraseIdx i)
  | 0 => by cases h with | nil => exact .nil | cons _ t => exact t
  | i + 1 => by cases h with | nil => exact .nil | cons hd t => exact .cons hd (t.eraseIdx i)

theorem Forall₂.modify {R : α → β → Prop} {f : α → α} {g : β → β}
    (hfg : ∀ {a b}, R a b → R (f a) (g b)) {l : List α} {k : List β}
    (h : Forall₂ R l k) : (i : Nat) → Forall₂ R (l.modify i f) (k.modify i g)
  | 0 => by cases h with | nil => exact .nil | cons hd t => exact .cons (hfg hd) t
  | i + 1 => by cases h with | nil => exact .nil | cons hd t => exact .cons hd (t.modify hfg i)

theorem Forall₂.filter {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ {a b}, R a b → p a = q b) {l : List α} {k : List β}
    (h : Forall₂ R l k) : Forall₂ R (l.filter p) (k.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    cases hq : q b
    · rw [List.filter_cons_of_neg (by simp [hpq hab, hq]), List.filter_cons_of_neg (by simp [hq])]
      exact ih
    · rw [List.filter_cons_of_pos ((hpq hab).trans hq), List.filter_cons_of_pos hq]
      exact .cons hab ih

theorem Forall₂.takeD {R : α → β → Prop} {a : α} {b : β} (hab : R a b) {l : List α} {k : List β}
    (h : Forall₂ R l k) : (n : Nat) → Forall₂ R (List.takeD n l a) (List.takeD n k b)
  | 0 => .nil
  | n + 1 => by
    cases h with
    | nil => rw [List.takeD_nil, List.takeD_nil]; exact .replicate hab _
    | cons hd t => rw [List.takeD_succ, List.takeD_succ]; exact .cons hd (t.takeD hab n)

end List
