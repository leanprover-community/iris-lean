/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros
-/
import Iris.Algebra.Monoid
import Iris.Std.List
import Iris.Std.PartialMap

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.
-/

open OFE Iris.Std

def bigOpL {M : Type u} {A : Type v} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit]
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op (fun n => Φ (n + 1)) xs)

def bigOpM {M : Type u} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit] {K : Type _}
    {V : Type _} (Φ : K → V → M) {M' : Type _ → Type _} [LawfulFiniteMap M' K] (m : M' V) : M :=
  bigOpL op (fun _ kv => Φ kv.1 kv.2) (toList (K := K) m)

/-- Big op over list with index: `[^ op list] k ↦ x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ↦ " ident " ∈ " term ", " term : term
/-- Big op over list without index: `[^ op list] x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ∈ " term ", " term : term

/-- Big op over map with key: `[^ op map] k ↦ x ∈ m, P` -/
scoped syntax atomic("[^") term " map]" ident " ↦ " ident " ∈ " term ", " term : term
/-- Big op over map without key: `[^ op map] x ∈ m, P` -/
scoped syntax atomic("[^") term " map]" ident " ∈ " term ", " term : term

scoped macro_rules
  | `([^ $o list] $k ↦ $x ∈ $l, $P) => `(bigOpL $o (fun $k $x => $P) $l)
  | `([^ $o list] $x ∈ $l, $P) => `(bigOpL $o (fun _ $x => $P) $l)
  | `([^ $o map] $k ↦ $x ∈ $m, $P) => `(bigOpM $o (fun $k $x => $P) $m)
  | `([^ $o map] $x ∈ $m, $P) => `(bigOpM $o (fun _ $x => $P) $m)

namespace BigOpL

variable {M : Type _} {A : Type _} [OFE M] {op : M → M → M} {unit : M} [MonoidOps op unit]

open MonoidOps

@[simp] theorem bigOpL_nil (Φ : Nat → A → M) : ([^ op list] k ↦ x ∈ ([] : List A), Φ k x) = unit := rfl

@[simp] theorem bigOpL_cons (Φ : Nat → A → M) (a : A) (as : List A) :
    ([^ op list] k ↦ x ∈ a :: as, Φ k x) = op (Φ 0 a) ([^ op list] k ↦ x ∈ as, Φ (k + 1) x) := rfl

theorem bigOpL_singleton_equiv (Φ : Nat → A → M) (a : A) :
    ([^ op list] k ↦ x ∈ [a], Φ k x) ≡ Φ 0 a := by simp

theorem bigOpL_equiv {Φ Ψ : Nat → A → M} {l : List A} (h : ∀ {i x}, l[i]? = some x → Φ i x ≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  match l with | .nil => .rfl | .cons _ _ => op_proper (h rfl) (bigOpL_equiv (h ·))

theorem bigOpL_dist {Φ Ψ : Nat → A → M} {l : List A} {n : Nat}
    (h : ∀ {i x}, l[i]? = some x → Φ i x ≡{n}≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡{n}≡ ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  match l with | .nil => .rfl | .cons _ _ => op_dist (h rfl) (bigOpL_dist (h ·))

/-- Congruence when the functions are equivalent on all indices. -/
theorem bigOpL_equiv_of_forall_equiv {Φ Ψ : Nat → A → M} {l : List A} (h : ∀ {i x}, Φ i x ≡ Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  bigOpL_equiv (fun _ => h)

theorem bigOpL_append_equiv (Φ : Nat → A → M) (l₁ l₂ : List A) :
    ([^ op list] k ↦ x ∈ l₁ ++ l₂, Φ k x) ≡
    op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Φ (k + l₁.length) x) :=
  match l₁ with
  | .nil => op_left_id.symm
  | .cons _ _ => op_congr_right (bigOpL_append_equiv ..) |>.trans op_assoc.symm

theorem bigOpL_snoc_equiv (Φ : Nat → A → M) (l : List A) (a : A) :
    ([^ op list] k ↦ x ∈ l ++ [a], Φ k x) ≡ op ([^ op list] k ↦ x ∈ l, Φ k x) (Φ l.length a) := by
  refine .trans (bigOpL_append_equiv Φ l [a]) ?_
  refine .trans ?_ (op_congr_right (op_right_id (op := op)))
  simp

theorem bigOpL_const_unit_equiv {l : List A} : ([^ op list] _x ∈ l, unit) ≡ unit :=
  match l with | .nil => .rfl | .cons _ _ => op_left_id.trans bigOpL_const_unit_equiv

theorem bigOpL_op_equiv (Φ Ψ : Nat → A → M) (l : List A) :
    ([^ op list] k ↦ x ∈ l, op (Φ k x) (Ψ k x)) ≡
    op ([^ op list] k ↦ x ∈ l, Φ k x) ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  match l with
  | .nil => op_left_id.symm
  | .cons _ _ => op_congr_right (bigOpL_op_equiv ..) |>.trans op_op_op_comm

theorem bigOpL_map_equiv {B : Type _} (h : A → B) (Φ : Nat → B → M) (l : List A) :
    ([^ op list] k ↦ x ∈ l.map h, Φ k x) ≡ ([^ op list] k ↦ x ∈ l, Φ k (h x)) :=
  match l with | [] => .rfl | _ :: l => op_proper .rfl (bigOpL_map_equiv h (Φ <| · + 1) l)

/-- Applying bigOpL with an operation closed under P will remain in P. -/
theorem bigOpL_closed {P : M → Prop} {Φ : Nat → A → M} {l : List A} (hunit : P unit)
    (hop : ∀ {x y}, P x → P y → P (op x y)) (hf : ∀ {i x}, l[i]? = some x → P (Φ i x)) :
    P ([^ op list] k ↦ x ∈ l, Φ k x) :=
  match l with | .nil => hunit | .cons _ _ => hop (hf rfl) (bigOpL_closed hunit hop (hf ·))

theorem bigOpL_equiv_of_perm (Φ : A → M) {l₁ l₂ : List A} (hp : l₁.Perm l₂) :
    ([^ op list] x ∈ l₁, Φ x) ≡ ([^ op list] x ∈ l₂, Φ x) :=
  match hp with
  | .nil => .rfl
  | .cons _ h => op_congr_right (bigOpL_equiv_of_perm _ h)
  | .swap _ _ _ => op_left_comm
  | .trans h1 h2 => bigOpL_equiv_of_perm Φ h1 |>.trans (bigOpL_equiv_of_perm Φ h2)

theorem bigOpL_take_drop_equiv (Φ : Nat → A → M) (l : List A) (n : Nat) :
    ([^ op list] k ↦ x ∈ l, Φ k x) ≡
    op ([^ op list] k ↦ x ∈ l.take n, Φ k x) ([^ op list] k ↦ x ∈ l.drop n, Φ (n + k) x) := by
  by_cases hn : n ≤ l.length
  · simpa [hn, Nat.add_comm] using bigOpL_append_equiv _ (l.take n) (l.drop n)
  · have hn : l.length ≤ n := Nat.le_of_not_ge hn
    simpa [List.drop_eq_nil_of_le hn, List.take_of_length_le hn] using op_right_id.symm

theorem bigOpL_filterMap_equiv {B : Type v} (h : A → Option B) (Φ : B → M) (l : List A) :
    ([^ op list] x ∈ l.filterMap h, Φ x) ≡ ([^ op list] x ∈ l, (h x).elim unit Φ) := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    cases hx : h x
    · simpa [hx] using ih.trans op_left_id.symm
    · simpa [hx] using op_congr_right ih

theorem bigOpL_flatMap_equiv {B : Type v} (h : A → List B) (Φ : B → M) (l : List A) :
    ([^ op list] x ∈ l.flatMap h, Φ x) ≡ ([^ op list] x ∈ l, [^ op list] y ∈ h x, Φ y) :=
  match l with
  | .nil => .rfl
  | .cons _ _ => (bigOpL_append_equiv ..).trans (op_congr_right <| bigOpL_flatMap_equiv ..)

theorem bigOpL_gen_proper_2 {B : Type v} (R : M → M → Prop) {Φ : Nat → A → M}
    {Ψ : Nat → B → M} {l₁ : List A} {l₂ : List B} (hunit : R unit unit)
    (hop : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b')) (hlen : l₁.length = l₂.length)
    (hf : ∀ {i x y}, l₁[i]? = some x → l₂[i]? = some y → R (Φ i x) (Ψ i y)) :
    R ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil => cases l₂ with | nil => exact hunit | cons _ _ => simp at hlen
  | cons _ _ ih => cases l₂ with
    | nil => simp at hlen
    | cons y ys => exact hop (hf rfl rfl) (ih (Nat.add_right_cancel hlen) (hf · ·))

theorem bigOpL_gen_proper (R : M → M → Prop) {Φ Ψ : Nat → A → M} {l : List A}
    (hR_refl : ∀ {x}, R x x) (hR_op : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ {k y}, l[k]? = some y → R (Φ k y) (Ψ k y)) :
    R ([^ op list] k ↦ x ∈ l, Φ k x) ([^ op list] k ↦ x ∈ l, Ψ k x) := by
  refine bigOpL_gen_proper_2 R hR_refl hR_op rfl (fun hx hy => ?_)
  obtain ⟨rfl⟩ := hx ▸ hy
  exact hf hx

theorem bigOpL_ext {Φ Ψ : Nat → A → M} {l : List A} (h : ∀ {i x}, l[i]? = some x → Φ i x = Ψ i x) :
    ([^ op list] k ↦ x ∈ l, Φ k x) = ([^ op list] k ↦ x ∈ l, Ψ k x) :=
  bigOpL_gen_proper (· = ·) rfl (· ▸ · ▸ rfl) h

theorem bigOpL_proper_2 [OFE A] {Φ Ψ : Nat → A → M} {l₁ l₂ : List A} (hlen : l₁.length = l₂.length)
    (hf : ∀ {k y₁ y₂}, l₁[k]? = some y₁ → l₂[k]? = some y₂ → Φ k y₁ ≡ Ψ k y₂) :
    ([^ op list] k ↦ x ∈ l₁, Φ k x) ≡ ([^ op list] k ↦ x ∈ l₂, Ψ k x) :=
  bigOpL_gen_proper_2 (· ≡ ·) .rfl op_proper hlen hf

theorem bigOpL_zipIdx_equiv (Φ : A × Nat → M) (n : Nat) (l : List A) :
    ([^ op list] x ∈ l.zipIdx n, Φ x) ≡ ([^ op list] k ↦ x ∈ l, Φ (x, n + k)) :=
  match l with
  | .nil => .rfl
  | .cons _ _ => op_proper .rfl <| (bigOpL_zipIdx_equiv _ (n + 1) _).trans (.of_eq <| by grind)

theorem bigOpL_zipIdxInt_equiv (Φ : A × Int → M) (n : Int) (l : List A) :
    ([^ op list] x ∈ List.zipIdxInt l n, Φ x) ≡ ([^ op list] k ↦ x ∈ l, Φ (x, n + (k : Int))) := by
  change bigOpL op (fun _ => Φ) (l.mapIdx (fun i v => (v, (i : Int) + n)))
       ≡ bigOpL op (fun i x => Φ (x, n + (i : Int))) l
  induction l generalizing n with
  | nil => exact .rfl
  | cons x xs ih =>
    rw [List.mapIdx_cons]
    refine op_proper (by simp) ?_
    rw [show (fun (i : Nat) v => (v, ↑(i + 1) + n)) = fun (i : Nat) v => (v, ↑i + (n + 1)) by grind]
    exact ih _ |>.trans (bigOpL_equiv_of_forall_equiv <| .of_eq (by grind))

-- markusde 2 : Here

theorem bigOpL_zipWith_op_equiv {B C : Type _} {f : A → B → C} {g1 : C → A} {g2 : C → B}
    {l₁ : List A} {l₂ : List B} (Φ : Nat → A → M) (Ψ : Nat → B → M)
    (hg1 : ∀ x y, g1 (f x y) = x) (hg2 : ∀ x y, g2 (f x y) = y) (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ c ∈ List.zipWith f l₁ l₂, op (Φ k (g1 c)) (Ψ k (g2 c))) ≡
    op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil =>
    cases l₂ with
    | nil => simpa [List.zipWith_nil_left, bigOpL_nil] using op_left_id.symm
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      refine .trans ?_ op_op_op_comm
      simp only [List.zipWith_cons_cons, bigOpL_cons, hg1, hg2]
      exact op_congr_right <| ih _ _ <| Nat.add_right_cancel hlen

/-- Big op over zipped list with separated functions. -/
theorem bigOpL_zip_op_equiv {B : Type v} {l₁ : List A} {l₂ : List B} (Φ : Nat → A → M)
    (Ψ : Nat → B → M) (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ xy ∈ l₁.zip l₂, op (Φ k xy.1) (Ψ k xy.2)) ≡
      op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  simpa only [List.zip] using bigOpL_zipWith_op_equiv _ _ (fun _ _ => rfl) (fun _ _ => rfl) hlen

section Hom

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]
variable {B : Type w} {R : M₂ → M₂ → Prop} {f : M₁ → M₂}

/-- Monoid homomorphisms distribute over big ops. -/
theorem bigOpL_hom (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f) (Φ : Nat → B → M₁) (l : List B) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) := by
  induction l generalizing Φ with
  | nil => simpa only [bigOpL_nil] using hom.map_unit
  | cons x xs ih =>
    simp only [bigOpL_cons]
    refine hom.rel_trans (hom.map_op _ _) ?_
    exact hom.op_proper (hom.rel_refl _) (ih _)

/-- Weak monoid homomorphisms distribute over non-empty big ops. -/
theorem bigOpL_hom_weak (hom : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : Nat → B → M₁) (l : List B) (hne : l ≠ []) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) := by
  induction l generalizing Φ with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [bigOpL_cons, bigOpL_nil]
      haveI : NonExpansive f := hom.map_ne
      exact (hom.rel_proper (NonExpansive.eqv op_right_id) op_right_id).mpr (hom.rel_refl _)
    | cons y ys =>
      apply hom.rel_trans (hom.map_op _ _)
      exact hom.op_proper (hom.rel_refl _) (ih _ (List.cons_ne_nil y ys))

end Hom
end BigOpL

namespace BigOpM

open scoped PartialMap

variable {M : Type u} [OFE M] {op : M → M → M} {unit : M} [MonoidOps op unit]
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}
variable [LawfulFiniteMap M' K]

open BigOpL MonoidOps LawfulPartialMap 

theorem bigOpM_equiv (Φ : K → V → M) (m₁ m₂ : M' V) (h : m₁ ≡ₘ m₂) :
    ([^ op map] k ↦ x ∈ m₁, Φ k x) ≡ ([^ op map] k ↦ x ∈ m₂, Φ k x) := by
  simpa only [bigOpM] using bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_perm_of_get?_eq h)

@[simp] theorem bigOpM_empty (Φ : K → V → M) :
    ([^ op map] k ↦ x ∈ (∅ : M' V), Φ k x) = unit := by
  show bigOpL op _ (toList (∅ : M' V)) = unit
  simp [toList, toList_empty]

theorem bigOpM_insert_equiv (Φ : K → V → M) (m : M' V) (i : K) (x : V) (hi : get? m i = none) :
    ([^ op map] k ↦ v ∈ PartialMap.insert m i x, Φ k v) ≡
      op (Φ i x) ([^ op map] k ↦ v ∈ m, Φ k v) := by
  simpa only [bigOpM] using bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_insert (v := x) hi)

theorem bigOpM_delete_equiv (Φ : K → V → M) (m : M' V) (i : K) (x : V) (hi : get? m i = some x) :
    ([^ op map] k ↦ v ∈ m, Φ k v) ≡ op (Φ i x) ([^ op map] k ↦ v ∈ PartialMap.delete m i, Φ k v) := by
  refine (bigOpM_equiv Φ m _ (insert_delete_cancel hi · |>.symm)).trans ?_
  exact bigOpM_insert_equiv Φ (PartialMap.delete m i) _ _ (get?_delete_eq rfl)

-- markusde: TODO (refactor me)
theorem bigOpM_gen_proper_2 [DecidableEq K] {A : Type _} {B : Type _} (R : M → M → Prop)
    (Φ : K → A → M) (Ψ : K → B → M) (m1 : M' A) (m2 : M' B)
    (hR_sub : ∀ x y, x ≡ y → R x y)
    (hR_equiv : Equivalence R)
    (hR_op : ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b'))
    (hfg : ∀ k,
      match get? m1 k, get? m2 k with
      | some y1, some y2 => R (Φ k y1) (Ψ k y2)
      | none, none => True
      | _, _ => False) :
    R ([^ op map] k ↦ x ∈ m1, Φ k x) ([^ op map] k ↦ x ∈ m2, Ψ k x) := by
  let P1 : M' A → Prop := fun m1' => ∀ (m2' : M' B) (Φ' : K → A → M) (Ψ' : K → B → M),
      (∀ k, match get? m1' k, get? m2' k with
        | some y1, some y2 => R (Φ' k y1) (Ψ' k y2)
        | none, none => True
        | _, _ => False) →
      R ([^ op map] k ↦ x ∈ m1', Φ' k x) ([^ op map] k ↦ x ∈ m2', Ψ' k x)
  suffices h : P1 m1 from h m2 Φ Ψ hfg
  apply LawfulFiniteMap.induction_on (K := K) (P := P1)
  · intro m₁ m₂ heq hP m2' Φ' Ψ' hfg'
    apply hR_equiv.trans (hR_sub _ _ (bigOpM_equiv Φ' m₁ m₂ heq).symm)
    exact hP m2' Φ' Ψ' (fun k => by rw [heq k]; exact hfg' k)
  · show P1 (∅ : M' A)
    intro m2' Φ' Ψ' hfg'
    let P2 : M' B → Prop := fun m2'' => ∀ (Φ'' : K → A → M) (Ψ'' : K → B → M),
        (∀ k, match get? (∅ : M' A) k, get? m2'' k with
          | some y1, some y2 => R (Φ'' k y1) (Ψ'' k y2)
          | none, none => True
          | _, _ => False) →
        R ([^ op map] k ↦ x ∈ (∅ : M' A), Φ'' k x) ([^ op map] k ↦ x ∈ m2'', Ψ'' k x)
    suffices h2 : P2 m2' from h2 Φ' Ψ' hfg'
    apply LawfulFiniteMap.induction_on (K := K) (P := P2)
    · intro m₁ m₂ heq hP Φ'' Ψ'' hfg''
      apply hR_equiv.trans (hP Φ'' Ψ'' (fun k => by rw [heq k]; exact hfg'' k))
      exact hR_sub _ _ (bigOpM_equiv Ψ'' m₁ m₂ heq)
    · show P2 (∅ : M' B)
      intro _ _ _
      show R ([^ op map] k ↦ x ∈ (∅ : M' A), _) ([^ op map] k ↦ x ∈ (∅ : M' B), _)
      rw [bigOpM_empty, bigOpM_empty]; exact hR_sub unit unit Equiv.rfl
    · intro k _ _ _ _ Φ'' Ψ'' hfg''
      have := hfg'' k
      rw [show get? (∅ : M' A) k = none from get?_empty k, get?_insert_eq rfl] at this
      exact this.elim
  · intro k x1 m1' hm1'k IH m2' Φ' Ψ' hfg'
    have hfg_k := hfg' k
    rw [get?_insert_eq rfl] at hfg_k
    cases hm2k : get? m2' k with
    | none => rw [hm2k] at hfg_k; cases hfg_k
    | some x2 =>
      rw [hm2k] at hfg_k
      refine hR_equiv.trans (hR_sub _ _ (bigOpM_insert_equiv Φ' m1' k x1 hm1'k)) ?_
      apply hR_equiv.trans _ (hR_sub _ _ (Equiv.symm (bigOpM_delete_equiv Ψ' m2' k x2 hm2k)))
      apply hR_op _ _ _ _ hfg_k
      apply IH
      intro k'
      by_cases hkk' : k = k'
      · subst hkk'; rw [get?_delete_eq rfl, hm1'k]; trivial
      · have := hfg' k'; rw [get?_insert_ne hkk'] at this; rwa [get?_delete_ne hkk']

theorem bigOpM_gen_proper {M : Type u} [OFE M] {op : M → M → M} {unit : M} [MonoidOps op unit]
    {R : M → M → Prop} {Φ Ψ : K → V → M} {m : M' V}
    (hR_refl : ∀ x, R x x) (hR_op : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ k x, get? m k = some x → R (Φ k x) (Ψ k x)) :
    R ([^ op map] k ↦ x ∈ m, Φ k x) ([^ op map] k ↦ x ∈ m, Ψ k x) := by
  refine bigOpL_gen_proper_2 R (hR_refl unit) hR_op rfl ?_
  intro i x y hx hy
  obtain ⟨rfl⟩ := hx ▸ hy
  exact hf x.1 x.2 (toList_get.mp <| List.mem_iff_getElem?.mpr ⟨i, hx⟩)

theorem bigOpM_ext {M : Type u} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit]
    (Φ Ψ : K → V → M) (m : M' V) (hf : ∀ k x, get? m k = some x → Φ k x = Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) = ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper (R := (· = ·)) (fun _ => rfl) (fun ha hb => ha ▸ hb ▸ rfl) hf

-- markusde: Here
theorem bigOpM_dist (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡{n}≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper (R := (· ≡{n}≡ ·)) (fun _ => Dist.rfl) op_dist hf

theorem bigOpM_proper (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, get? m k = some x → Φ k x ≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper (R := (· ≡ ·)) (fun _ => Equiv.rfl) op_proper hf

theorem bigOpM_proper_2 [DecidableEq K] [OFE A] (Φ : K → A → M) (Ψ : K → A → M) (m1 m2 : M' A)
    (hm : ∀ k, get? m1 k = get? m2 k)
    (hf : ∀ k y1 y2,
      get? m1 k = some y1 →
      get? m2 k = some y2 →
      y1 ≡ y2 →
      Φ k y1 ≡ Ψ k y2) :
    ([^ op map] k ↦ x ∈ m1, Φ k x) ≡ ([^ op map] k ↦ x ∈ m2, Ψ k x) := by
  apply bigOpM_gen_proper_2 (R := (· ≡ ·)) _ _ _ _ (fun _ _ h => h) equiv_eqv (fun _ _ _ _ => op_proper)
  intro k
  have hlk := hm k
  cases hm1k : get? m1 k with
  | none => rw [hm1k] at hlk; rw [← hlk]; trivial
  | some y1 =>
    rw [hm1k] at hlk
    cases hm2k : get? m2 k with
    | none => rw [hm2k] at hlk; cases hlk
    | some y2 => rw [hm2k] at hlk; cases hlk; exact hf k y1 y1 hm1k hm2k Equiv.rfl

theorem bigOpM_dist_pointwise (Φ Ψ : K → V → M) (m : M' V) (n : Nat)
    (hf : ∀ k x, Φ k x ≡{n}≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡{n}≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
    bigOpM_dist _ _ _ _ fun k x _ => hf k x

theorem bigOpM_proper_pointwise (Φ Ψ : K → V → M) (m : M' V)
    (hf : ∀ k x, Φ k x ≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
    bigOpM_proper _ _ _ fun k x _ => hf k x

theorem bigOpM_toList_equiv (Φ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡
    ([^ op list] kx ∈ LawfulFiniteMap.toList (K := K) m, Φ kx.1 kx.2) := by rfl

theorem bigOpM_ofList_equiv [DecidableEq K] (Φ : K → V → M) (l : List (K × V))
    (hnodup : NoDupKeys l) :
    ([^ op map] k ↦ x ∈ (PartialMap.ofList l : M' V), Φ k x) ≡
      ([^ op list] kx ∈ l, Φ kx.1 kx.2) := by
  simp only [bigOpM]
  exact bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_ofList hnodup)

theorem bigOpM_singleton_equiv (Φ : K → V → M) (i : K) (x : V) :
    ([^ op map] k ↦ v ∈ ({[i := x]} : M' V), Φ k v) ≡ Φ i x := by
  rw [show ({[i := x]} : M' V) = PartialMap.insert (∅ : M' V) i x from rfl]
  apply (bigOpM_insert_equiv Φ (∅ : M' V) i x (get?_empty i)).trans
  rw [bigOpM_empty]; exact op_right_id

theorem bigOpM_const_unit_equiv [DecidableEq K] (m : M' V) :
    bigOpM op (fun (_ : K) _ => unit) m ≡ unit := by
  let P : M' V → Prop := fun m' => bigOpM op (fun (_ : K) (_ : V) => unit) m' ≡ unit
  show P m; apply LawfulFiniteMap.induction_on (K := K) (P := P)
  · intro m₁ m₂ heq h
    refine (bigOpM_equiv _ _ _ heq).symm.trans ?_
    exact h
  · show P (∅ : M' V); show _ ≡ _; rw [bigOpM_empty]
  · intro i x m' hm' IH
    refine (bigOpM_insert_equiv _ _ _ _ hm').trans ?_
    refine (op_proper Equiv.rfl IH).trans ?_
    exact op_left_id

theorem bigOpM_map_equiv (h : V → B) (Φ : K → B → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ PartialMap.map h m, Φ k x) ≡
      ([^ op map] k ↦ v ∈ m, Φ k (h v)) := by
  simp only [bigOpM]
  refine (bigOpL_equiv_of_perm _ LawfulFiniteMap.toList_map).trans ?_
  exact bigOpL_map_equiv (op := op) _ _ (LawfulFiniteMap.toList (K := K) m)

theorem bigOpM_filterMap_equiv (h : V → Option V) (Φ : K → V → M) (m : M' V)
    (hinj : Function.Injective h) :
    ([^ op map] k ↦ x ∈ PartialMap.filterMap h m, Φ k x) ≡
      ([^ op map] k ↦ v ∈ m, (h v).elim unit (Φ k)) := by
  simp only [bigOpM]
  refine (bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_filterMap hinj)).trans ?_
  refine (bigOpL_filterMap_equiv (op := op) _ _ _).trans ?_
  exact bigOpL_equiv_of_forall_equiv @fun _ kv => by cases hkv : h kv.2 <;> simp [Option.elim, Option.map]

theorem bigOpM_insert_delete_equiv (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    ([^ op map] k ↦ v ∈ PartialMap.insert m i x, Φ k v) ≡
      op (Φ i x) ([^ op map] k ↦ v ∈ PartialMap.delete m i, Φ k v) := by
  refine (bigOpM_equiv _ _ _ fun k => (insert_delete k).symm).trans ?_
  exact bigOpM_insert_equiv _ _ _ _ (get?_delete_eq rfl)

theorem bigOpM_insert_override_equiv (Φ : K → A → M) (m : M' A) (i : K) (x x' : A) :
    get? m i = some x → Φ i x ≡ Φ i x' →
    ([^ op map] k ↦ v ∈ PartialMap.insert m i x', Φ k v) ≡
      ([^ op map] k ↦ v ∈ m, Φ k v) := by
  intro hi hΦ
  refine (bigOpM_insert_delete_equiv Φ m i x').trans ?_
  refine (op_proper hΦ.symm Equiv.rfl).trans ?_
  exact (bigOpM_delete_equiv Φ m i x hi).symm

theorem bigOpM_fn_insert_equiv [DecidableEq K] {B : Type w} (g : K → V → B → M) (f : K → B) (m : M' V)
    (i : K) (x : V) (b : B) (hi : get? m i = none) :
    ([^ op map] k ↦ y ∈ PartialMap.insert m i x, g k y (if k = i then b else f k)) ≡
    op (g i x b) ([^ op map] k ↦ y ∈ m, g k y (f k)) := by
  refine (bigOpM_insert_equiv _ m i x hi).trans
    (op_proper (by simp) (bigOpM_proper _ _ _ fun k y hk => ?_))
  simp [show k ≠ i from fun heq => by subst heq; rw [hi] at hk; cases hk]

theorem bigOpM_fn_insert_equiv' [DecidableEq K] (f : K → M) (m : M' V) (i : K) (x : V) (P : M)
    (hi : get? m i = none) :
    ([^ op map] k ↦ _v ∈ PartialMap.insert m i x, if k = i then P else f k) ≡
    op P ([^ op map] k ↦ _v ∈ m, f k) := by
  refine (bigOpM_insert_equiv _ m i x hi).trans
    (op_proper (by simp) (bigOpM_proper _ _ _ fun k _ hk => ?_))
  simp [show k ≠ i from fun heq => by subst heq; rw [hi] at hk; cases hk]

theorem bigOpM_filter_equiv (φ : K → V → Bool) (Φ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ PartialMap.filter φ m, Φ k x) ≡ ([^ op map] k ↦ x ∈ m, if φ k x then Φ k x else unit) := by
  unfold bigOpM
  refine (bigOpL_equiv_of_perm _ LawfulFiniteMap.toList_filter).trans ?_
  suffices ∀ l : List (K × V),
      bigOpL op (fun _ kv => Φ kv.1 kv.2) (l.filter (fun kv => φ kv.1 kv.2)) ≡
      bigOpL op (fun _ kv => if φ kv.1 kv.2 then Φ kv.1 kv.2 else unit) l from this _
  intro l
  induction l with
  | nil => exact Equiv.rfl
  | cons kv kvs ih =>
    simp only [List.filter]
    cases hp : φ kv.1 kv.2 with
    | false =>
      simp only [bigOpL_cons, hp]
      exact Equiv.trans ih op_left_id.symm
    | true =>
      simp only [bigOpL_cons, hp, ite_true]
      exact op_congr_right ih

theorem bigOpM_union_equiv [DecidableEq K] (Φ : K → V → M) (m1 m2 : M' V) (hdisj : m1 ##ₘ m2) :
    ([^ op map] k ↦ x ∈ m1 ∪ m2, Φ k x) ≡ op ([^ op map] k ↦ x ∈ m1, Φ k x) ([^ op map] k ↦ x ∈ m2, Φ k x) := by
  let P : M' V → Prop := fun m1 =>
    PartialMap.disjoint m1 m2 →
    ([^ op map] k ↦ x ∈ PartialMap.union m1 m2, Φ k x) ≡
    op ([^ op map] k ↦ x ∈ m1, Φ k x) ([^ op map] k ↦ x ∈ m2, Φ k x)
  suffices h : P m1 from h hdisj
  apply LawfulFiniteMap.induction_on (K := K) (P := P)
  · intro m₁ m₂' heq hP hdisj'
    have hdisj'' : PartialMap.disjoint m₁ m2 :=
      fun k hk => hdisj' k ⟨(heq k).symm ▸ hk.1, hk.2⟩
    have hunion_eq := bigOpM_equiv (op := op) (unit := unit)
      Φ (PartialMap.union m₁ m2) (PartialMap.union m₂' m2)
      (fun k => by rw [get?_union, get?_union, heq k])
    refine hunion_eq.symm.trans ?_
    refine (hP hdisj'').trans ?_
    exact op_proper (bigOpM_equiv Φ m₁ m₂' heq) Equiv.rfl
  · show P (∅ : M' V)
    intro _; rw [bigOpM_empty]
    refine Equiv.trans ?_ op_left_id.symm
    apply bigOpM_equiv Φ _ _
    intro k; show get? (PartialMap.union (∅ : M' V) m2) k = get? m2 k
    rw [get?_union, show get? (∅ : M' V) k = none from get?_empty k]; simp
  · intro i x m hi_none IH hdisj'
    have hi_union : get? (PartialMap.union m m2) i = none := by
      rw [get?_union_none]
      refine ⟨hi_none, ?_⟩
      cases (PartialMap.disjoint_iff _ m2).mp hdisj' i with
      | inl h => rw [get?_insert_eq rfl] at h; cases h
      | inr h => exact h
    have hdisj_inner : PartialMap.disjoint m m2 := fun k ⟨hk1, hk2⟩ => hdisj' k ⟨by
      by_cases h : i = k
      · subst h; rw [hi_none] at hk1; cases hk1
      · rwa [get?_insert_ne h], hk2⟩
    refine (bigOpM_equiv Φ _ _ fun k => (union_insert_left k).symm).trans ?_
    refine (bigOpM_insert_equiv Φ (m ∪ m2) i x hi_union).trans ?_
    refine (op_congr_right (IH hdisj_inner)).trans ?_
    refine op_assoc.symm.trans ?_
    exact op_congr_left (bigOpM_insert_equiv Φ m i x hi_none).symm

theorem bigOpM_op_equiv (Φ Ψ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ m, op (Φ k x) (Ψ k x)) ≡
    op ([^ op map] k ↦ x ∈ m, Φ k x) ([^ op map] k ↦ x ∈ m, Ψ k x) := by
  simp only [bigOpM]; exact bigOpL_op_equiv _ _ _

theorem bigOpM_closed [DecidableEq K] (P : M → Prop) (Φ : K → V → M) (m : M' V)
    (hproper : ∀ x y, x ≡ y → (P x ↔ P y))
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ k x, get? m k = some x → P (Φ k x)) :
    P ([^ op map] k ↦ x ∈ m, Φ k x) := by
  let Q : M' V → Prop := fun m'' => (∀ k x, get? m'' k = some x → P (Φ k x)) →
                     P ([^ op map] k ↦ x ∈ m'', Φ k x)
  suffices h : Q m from h hf
  apply LawfulFiniteMap.induction_on (K := K) (P := Q)
  · intro m₁ m₂ heq hQ hf'
    apply (hproper _ _ (bigOpM_equiv Φ m₁ m₂ heq)).mp
    exact hQ fun k x hget => hf' k x ((heq k) ▸ hget)
  · show Q (∅ : M' V)
    intro _; show P ([^ op map] k ↦ x ∈ (∅ : M' V), Φ k x); rw [bigOpM_empty]; exact hunit
  · intro k x m'' hm'' IH hf''
    apply (hproper _ _ (bigOpM_insert_equiv Φ m'' k x hm'')).mpr
    apply hop _ _ (hf'' _ _ (get?_insert_eq rfl))
    apply IH; intro k' x' hget'
    by_cases heq : k = k'
    · subst heq; rw [hget'] at hm''; cases hm''
    · apply hf'' k' x'
      rw [get?_insert_ne heq]; exact hget'

-- TODO: kmap and map_seq are skipped for now

theorem bigOpM_sep_zipWith_equiv {A : Type _} {B : Type _} {C : Type _}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hg1 : ∀ x y, g1 (f x y) = x)
    (hg2 : ∀ x y, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([^ op map] k ↦ xy ∈ PartialMap.zipWith f m1 m2, op (h1 k (g1 xy)) (h2 k (g2 xy))) ≡
    op ([^ op map] k ↦ x ∈ m1, h1 k x) ([^ op map] k ↦ x ∈ m2, h2 k x) := by
  refine (bigOpM_op_equiv (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy))
    (PartialMap.zipWith f m1 m2)).trans ?_
  apply op_proper
  · refine (bigOpM_map_equiv g1 h1 (PartialMap.zipWith f m1 m2)).symm.trans ?_
    apply bigOpM_equiv h1 _ _
    intro k
    simp only [get?_map, get?_zipWith]
    cases h1k : get? m1 k with
    | none => simp [Option.bind]
    | some a =>
      have := (hdom k).mp (by rw [h1k]; simp)
      cases h2k : get? m2 k with
      | none => rw [h2k] at this; simp at this
      | some b => simp [Option.bind, Option.map, hg1]
  · refine (bigOpM_map_equiv g2 h2 (PartialMap.zipWith f m1 m2)).symm.trans ?_
    apply bigOpM_equiv h2 _ _
    intro k
    simp only [get?_map, get?_zipWith]
    cases h1k : get? m1 k with
    | none =>
      simp [Option.bind]
      cases h2k : get? m2 k with
      | none => rfl
      | some b =>
        have := (hdom k).mpr (by rw [h2k]; simp)
        rw [h1k] at this; simp at this
    | some a =>
      cases h2k : get? m2 k with
      | none =>
        have := (hdom k).mp (by rw [h1k]; simp)
        rw [h2k] at this; simp at this
      | some b => simp [Option.bind, Option.map, hg2]

theorem bigOpM_sep_zip_equiv {A : Type _} {B : Type _}
    (h1 : K → A → M) (h2 : K → B → M) (m1 : M' A) (m2 : M' B)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([^ op map] k ↦ xy ∈ PartialMap.zip m1 m2, op (h1 k xy.1) (h2 k xy.2)) ≡
    op ([^ op map] k ↦ x ∈ m1, h1 k x) ([^ op map] k ↦ x ∈ m2, h2 k x) := by
  simp only [PartialMap.zip]
  exact bigOpM_sep_zipWith_equiv _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) hdom

end BigOpM

end Iris.Algebra
