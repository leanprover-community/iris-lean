/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Markus de Medeiros, Sergei Stepanenko
-/
module

public import Iris.Algebra.Monoid
import Batteries.Data.List.Perm
public import Iris.Std.List
public import Iris.Std.PartialMap
public import Iris.Std.GenSets

namespace Iris.Algebra

/-! # Big Operators

This file defines big operators (fold operations) at the abstract OFE level.
These are parameterized by a monoid operation and include theorems about their properties.
-/

open OFE Iris.Std

@[expose] public def bigOpL {M : Type u} {A : Type v} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit]
    (Φ : Nat → A → M) (l : List A) : M :=
  match l with
  | [] => unit
  | x :: xs => op (Φ 0 x) (bigOpL op (fun n => Φ (n + 1)) xs)

@[expose] public def bigOpM {M : Type u} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit] {K : Type _}
    {V : Type _} (Φ : K → V → M) {M' : Type _ → Type _} [LawfulFiniteMap M' K] (m : M' V) : M :=
  bigOpL op (fun _ kv => Φ kv.1 kv.2) (toList (K := K) m)

@[expose] public def bigOpS {M : Type u} [OFE M] (op : M → M → M) {unit : M} [MonoidOps op unit]
    {A : Type _} {S : Type _} [FiniteSet S A] (Φ : A → M) (m : S) : M :=
  bigOpL op (fun _ x => Φ x) (toList m)

/-- Big op over list with index: `[^ op list] k ↦ x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ↦ " ident " ∈ " term ", " term : term
/-- Big op over list without index: `[^ op list] x ∈ l, P` -/
scoped syntax atomic("[^") term " list]" ident " ∈ " term ", " term : term

/-- Big op over map with key: `[^ op map] k ↦ x ∈ m, P` -/
scoped syntax atomic("[^") term " map]" ident " ↦ " ident " ∈ " term ", " term : term
/-- Big op over map without key: `[^ op map] x ∈ m, P` -/
scoped syntax atomic("[^") term " map]" ident " ∈ " term ", " term : term

/-- Big op over set without index: `[^ op set] x ∈ l, P` -/
scoped syntax atomic("[^") term " set]" ident " ∈ " term ", " term : term

scoped macro_rules
  | `([^ $o list] $k ↦ $x ∈ $l, $P) => `(bigOpL $o (fun $k $x => $P) $l)
  | `([^ $o list] $x ∈ $l, $P) => `(bigOpL $o (fun _ $x => $P) $l)
  | `([^ $o set] $x ∈ $l, $P) => `(bigOpS $o (fun $x => $P) $l)
  | `([^ $o map] $k ↦ $x ∈ $m, $P) => `(bigOpM $o (fun $k $x => $P) $m)
  | `([^ $o map] $x ∈ $m, $P) => `(bigOpM $o (fun _ $x => $P) $m)

public section
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

theorem bigOpL_filter_equiv (φ : A → Bool) (Φ : A → M) (l : List A) :
    ([^ op list] x ∈ l.filter φ, Φ x) ≡ ([^ op list] x ∈ l, if φ x then Φ x else unit) := by
  induction l with
  | nil => exact .rfl
  | cons x xs ih =>
    by_cases hp : φ x
    · simpa [hp] using op_congr_right ih
    · simpa [hp] using ih.trans op_left_id.symm

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

theorem bigOpL_zipWith_op_equiv {B C : Type _} {f : A → B → C} {g1 : C → A} {g2 : C → B}
    {l₁ : List A} {l₂ : List B} {Φ : Nat → A → M} {Ψ : Nat → B → M} (hg1 : ∀ {x y}, g1 (f x y) = x)
    (hg2 : ∀ {x y}, g2 (f x y) = y) (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ c ∈ List.zipWith f l₁ l₂, op (Φ k (g1 c)) (Ψ k (g2 c))) ≡
    op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) := by
  induction l₁ generalizing l₂ Φ Ψ with
  | nil => cases l₂ with | nil => exact op_left_id.symm | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons _ _ =>
      simp only [List.zipWith_cons_cons, bigOpL_cons, hg1, hg2]
      exact op_congr_right (ih (Nat.add_right_cancel hlen)) |>.trans op_op_op_comm

/-- Big op over zipped list with separated functions. -/
theorem bigOpL_zip_op_equiv {B : Type v} {l₁ : List A} {l₂ : List B} {Φ : Nat → A → M}
    {Ψ : Nat → B → M} (hlen : l₁.length = l₂.length) :
    ([^ op list] k ↦ xy ∈ l₁.zip l₂, op (Φ k xy.1) (Ψ k xy.2)) ≡
    op ([^ op list] k ↦ x ∈ l₁, Φ k x) ([^ op list] k ↦ x ∈ l₂, Ψ k x) :=
  bigOpL_zipWith_op_equiv rfl rfl hlen

section Hom

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]
variable {B : Type w} {R : M₂ → M₂ → Prop} {f : M₁ → M₂}

/-- Monoid homomorphisms distribute over big ops. -/
theorem bigOpL_hom [H : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f] (Φ : Nat → B → M₁) (l : List B) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) :=
  match l with
  | .nil => H.map_unit
  | .cons _ _ => H.rel_trans H.map_op <| H.op_proper H.rel_refl <| (bigOpL_hom (H := H) ..)

/-- Weak monoid homomorphisms distribute over non-empty big ops. -/
theorem bigOpL_hom_weak [H : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f] {l : List B}
    (Φ : Nat → B → M₁) (hne : l ≠ []) :
    R (f ([^ op₁ list] k ↦ x ∈ l, Φ k x)) ([^ op₂ list] k ↦ x ∈ l, f (Φ k x)) :=
  match l with
  | .nil => absurd rfl hne
  | .cons _ .nil => H.rel_proper (H.map_ne.eqv op_right_id) op_right_id |>.mpr H.rel_refl
  | .cons _ (.cons y ys) =>
    H.rel_trans (H.map_op) <| H.op_proper H.rel_refl <| bigOpL_hom_weak _ (List.cons_ne_nil y ys)

end Hom
end BigOpL

namespace BigOpM

open scoped PartialMap

variable {M : Type u} [OFE M] {op : M → M → M} {unit : M} [MonoidOps op unit]
variable {M' : Type _ → Type _} {K : Type _} {V : Type _}
variable [LawfulFiniteMap M' K]

open BigOpL MonoidOps LawfulPartialMap

theorem bigOpM_equiv_of_perm (Φ : K → V → M) {m₁ m₂ : M' V} (h : m₁ ≡ₘ m₂) :
    ([^ op map] k ↦ x ∈ m₁, Φ k x) ≡ ([^ op map] k ↦ x ∈ m₂, Φ k x) :=
  bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_perm_of_get?_eq h)

@[simp] theorem bigOpM_empty (Φ : K → V → M) : ([^ op map] k ↦ x ∈ (∅ : M' V), Φ k x) = unit := by
  simp [bigOpM, FiniteMap.toList, toList_empty]

theorem bigOpM_insert_equiv (Φ : K → V → M) {m : M' V} {i : K} (x : V) (hi : get? m i = none) :
    ([^ op map] k ↦ v ∈ insert m i x, Φ k v) ≡ op (Φ i x) ([^ op map] k ↦ v ∈ m, Φ k v) :=
  bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_insert hi)

theorem bigOpM_delete_equiv (Φ : K → V → M) {m : M' V} {i : K} {x : V} (hi : get? m i = some x) :
    ([^ op map] k ↦ v ∈ m, Φ k v) ≡ op (Φ i x) ([^ op map] k ↦ v ∈ delete m i, Φ k v) :=
  (bigOpM_equiv_of_perm Φ (insert_delete_cancel hi · |>.symm)).trans
    (bigOpM_insert_equiv Φ _ (get?_delete_eq rfl))

open Classical in
theorem bigOpM_gen_proper_2 {A : Type _} {B : Type _} {R : M → M → Prop}
    {Φ : K → A → M} {Ψ : K → B → M} {m1 : M' A} {m2 : M' B}
    (hR_sub : ∀ {x y}, x ≡ y → R x y) (hR_equiv : Equivalence R)
    (hR_op : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b'))
    (hdom : ∀ k, (get? m1 k).isSome = (get? m2 k).isSome)
    (hf : ∀ {k y1 y2}, get? m1 k = some y1 → get? m2 k = some y2 → R (Φ k y1) (Ψ k y2)) :
    R ([^ op map] k ↦ x ∈ m1, Φ k x) ([^ op map] k ↦ x ∈ m2, Ψ k x) := by
  let P : M' A → Prop := fun m1' =>
    ∀ (m2' : M' B),
    (∀ k, (get? m1' k).isSome = (get? m2' k).isSome) →
    (∀ {k y1 y2}, get? m1' k = some y1 → get? m2' k = some y2 → R (Φ k y1) (Ψ k y2)) →
    R ([^ op map] k ↦ x ∈ m1', Φ k x) ([^ op map] k ↦ x ∈ m2', Ψ k x)
  suffices h : P m1 from h m2 hdom hf
  apply LawfulFiniteMap.induction_on (K := K) (P := P)
  · intro m₁ m₂ heq hP m2' hdom' hf'
    refine hR_equiv.trans (hR_sub (bigOpM_equiv_of_perm Φ heq).symm) ?_
    exact hP m2' (fun k => heq k ▸ hdom' k) (hf' <| (heq _) ▸ ·)
  · show P (∅ : M' A)
    intro m2' hdom' _
    rw [bigOpM_empty]
    refine hR_sub <| (bigOpM_equiv_of_perm Ψ ?_).trans (.of_eq (bigOpM_empty Ψ)) |>.symm
    refine eq_empty_iff.mpr fun k => ?_
    simpa [show get? (∅ : M' A) k = none from get?_empty k] using hdom' k
  · intro k x1 m1' hm1'k IH m2' hdom' hf'
    obtain ⟨x2, hm2k⟩ := Option.isSome_iff_exists.mp <| by
      simpa [get?_insert_eq (k := k) rfl] using (hdom' k).symm
    refine hR_equiv.trans (hR_sub (bigOpM_insert_equiv Φ x1 hm1'k)) ?_
    refine hR_equiv.trans ?_ (hR_sub (bigOpM_delete_equiv Ψ hm2k).symm)
    exact hR_op (hf' (get?_insert_eq rfl) hm2k) <| IH _ (fun k' => by
      by_cases hkk' : k = k'
      · subst hkk'; simp [get?_delete_eq rfl, hm1'k]
      · rw [get?_delete_ne hkk']; simpa [get?_insert_ne hkk'] using hdom' k')
      (fun {k' _ _} h1' h2' => by
        have hkk' : k ≠ k' := fun h => by subst h; rw [hm1'k] at h1'; cases h1'
        exact hf' (by rwa [get?_insert_ne hkk']) (by rwa [get?_delete_ne hkk'] at h2'))

theorem bigOpM_gen_proper {R : M → M → Prop} {Φ Ψ : K → V → M} {m : M' V}
    (hR_refl : ∀ {x}, R x x) (hR_op : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ {k x}, get? m k = some x → R (Φ k x) (Ψ k x)) :
    R ([^ op map] k ↦ x ∈ m, Φ k x) ([^ op map] k ↦ x ∈ m, Ψ k x) := by
  refine bigOpL_gen_proper_2 R hR_refl hR_op rfl fun hx hy => ?_
  obtain ⟨rfl⟩ := hx ▸ hy
  exact hf <| toList_get.mp <| List.mem_iff_getElem?.mpr ⟨_, hx⟩

theorem bigOpM_ext {Φ Ψ : K → V → M} {m : M' V} (hf : ∀ {k x}, get? m k = some x → Φ k x = Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) = ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper rfl (· ▸ · ▸ rfl) hf

theorem bigOpM_dist {Φ Ψ : K → V → M} {m : M' V}
    (hf : ∀ {k x}, get? m k = some x → Φ k x ≡{n}≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡{n}≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper .rfl op_dist hf

theorem bigOpM_proper {Φ Ψ : K → V → M} {m : M' V} (hf : ∀ {k x}, get? m k = some x → Φ k x ≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_gen_proper .rfl op_proper hf

theorem bigOpM_proper_2 [OFE A] {Φ Ψ : K → A → M} {m1 m2 : M' A} (hm : ∀ k, get? m1 k = get? m2 k)
    (hf : ∀ {k y1 y2}, get? m1 k = some y1 → get? m2 k = some y2 → y1 ≡ y2 → Φ k y1 ≡ Ψ k y2) :
    ([^ op map] k ↦ x ∈ m1, Φ k x) ≡ ([^ op map] k ↦ x ∈ m2, Ψ k x) :=
  bigOpM_gen_proper_2 id equiv_eqv op_proper (fun k => by rw [hm k]) fun h1 h2 =>
    hf h1 h2 (by rw [hm _] at h1; exact (h1.symm.trans h2 |> Option.some.inj) ▸ .rfl)

theorem bigOpM_dist_pointwise {Φ Ψ : K → V → M} {n : Nat} (m : M' V)
    (hf : ∀ {k x}, Φ k x ≡{n}≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡{n}≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_dist fun _ => hf

theorem bigOpM_proper_pointwise {Φ Ψ : K → V → M} (m : M' V) (hf : ∀ {k x}, Φ k x ≡ Ψ k x) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡ ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpM_proper (fun _ => hf)

theorem bigOpM_toList_equiv (Φ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ m, Φ k x) ≡ ([^ op list] kx ∈ toList (K := K) m, Φ kx.1 kx.2) :=
  .rfl

theorem bigOpM_ofList_equiv [DecidableEq K] (Φ : K → V → M) (l : List (K × V)) (hd : NoDupKeys l) :
    ([^ op map] k ↦ x ∈ (PartialMap.ofList l : M' V), Φ k x) ≡ ([^ op list] kx ∈ l, Φ kx.1 kx.2) :=
  bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_ofList hd)

theorem bigOpM_singleton_equiv (Φ : K → V → M) (i : K) (x : V) :
    ([^ op map] k ↦ v ∈ ({[i := x]} : M' V), Φ k v) ≡ Φ i x := by
  refine bigOpM_insert_equiv _ (m := (∅ : M' V)) _ (get?_empty i) |>.trans ?_
  simpa only [bigOpM_empty] using op_right_id

theorem bigOpM_const_unit_equiv [DecidableEq K] (m : M' V) :
    bigOpM (K := K) op (fun _ _ => unit) m ≡ unit :=
  bigOpL_const_unit_equiv

theorem bigOpM_map_equiv (h : V → B) (Φ : K → B → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ PartialMap.map h m, Φ k x) ≡ ([^ op map] k ↦ v ∈ m, Φ k (h v)) :=
  bigOpL_equiv_of_perm _ LawfulFiniteMap.toList_map |>.trans (bigOpL_map_equiv ..)

theorem bigOpM_filterMap_equiv (Φ : K → V → M) (m : M' V) (hinj : Function.Injective h) :
    ([^ op map] k ↦ x ∈ PartialMap.filterMap h m, Φ k x) ≡
    ([^ op map] k ↦ v ∈ m, (h v).elim unit (Φ k)) := by
  refine (bigOpL_equiv_of_perm _ (LawfulFiniteMap.toList_filterMap hinj)).trans ?_
  refine (bigOpL_filterMap_equiv ..).trans ?_
  refine bigOpL_equiv_of_forall_equiv @fun _ ⟨_, v⟩ => ?_
  cases _ : h v <;> simp_all

theorem bigOpM_insert_delete_equiv (Φ : K → V → M) (m : M' V) (i : K) (x : V) :
    ([^ op map] k ↦ v ∈ insert m i x, Φ k v) ≡
    op (Φ i x) ([^ op map] k ↦ v ∈ delete m i, Φ k v) :=
  (bigOpM_equiv_of_perm _ (insert_delete · |>.symm)).trans
    (bigOpM_insert_equiv _ _ (get?_delete_eq rfl))

theorem bigOpM_insert_override_equiv {Φ : K → A → M} {m : M' A}
    (hi : get? m i = some x) (hΦ : Φ i x ≡ Φ i x') :
    ([^ op map] k ↦ v ∈ insert m i x', Φ k v) ≡ ([^ op map] k ↦ v ∈ m, Φ k v) :=
  (bigOpM_insert_delete_equiv Φ m i x').trans
    ((op_proper hΦ.symm .rfl).trans (bigOpM_delete_equiv _ hi).symm)

theorem bigOpM_fn_insert_equiv [DecidableEq K] {B : Type w} (g : K → V → B → M) (f : K → B)
    {m : M' V} {i : K} (x : V) (b : B) (hi : get? m i = none) :
    ([^ op map] k ↦ y ∈ insert m i x, g k y (if k = i then b else f k)) ≡
    op (g i x b) ([^ op map] k ↦ y ∈ m, g k y (f k)) :=
  (bigOpM_insert_equiv _ _ hi).trans
    (op_proper (by simp) (bigOpM_proper fun _ => by split <;> simp_all))

theorem bigOpM_fn_insert_equiv' [DecidableEq K] (f : K → M) {m : M' V} {i : K} (x : V) (P : M)
    (hi : get? m i = none) :
    ([^ op map] k ↦ _v ∈ insert m i x, if k = i then P else f k) ≡
    op P ([^ op map] k ↦ _v ∈ m, f k) :=
  (bigOpM_insert_equiv _ _ hi).trans
    (op_proper (by simp) (bigOpM_proper fun _ => by split <;> simp_all))

theorem bigOpM_filter_equiv (φ : K → V → Bool) (Φ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ PartialMap.filter φ m, Φ k x) ≡
    ([^ op map] k ↦ x ∈ m, if φ k x then Φ k x else unit) :=
  (bigOpL_equiv_of_perm _ LawfulFiniteMap.toList_filter).trans
    (bigOpL_filter_equiv (fun (k, v) => φ k v) (fun (k, v) => Φ k v) _)

theorem toList_union_perm [DecidableEq K] {m1 m2 : M' V} (hdisj : m1 ##ₘ m2) :
    (toList (K := K) (m1 ∪ m2)).Perm (toList (K := K) m1 ++ toList (K := K) m2) := by
  refine (List.perm_ext_iff_of_nodup LawfulFiniteMap.nodup_toList ?_).mpr fun ⟨k, v⟩ => ?_
  · refine List.nodup_append.mpr ⟨LawfulFiniteMap.nodup_toList, LawfulFiniteMap.nodup_toList, ?_⟩
    rintro ⟨k, _⟩ h1 _ h2 rfl
    refine (PartialMap.disjoint_iff m1 m2).mp hdisj k |>.elim ?_ ?_
    · exact (fun h => absurd (toList_get.mp h1) (by simp [h]))
    · exact (fun h => absurd (toList_get.mp h2) (by simp [h]))
  · rw [List.mem_append]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hg : get? (PartialMap.union m1 m2) k = some v := toList_get.mp h
      rw [get?_union] at hg
      cases hm1 : get? m1 k <;> simp_all [Option.orElse]
      · exact .inr (toList_get.mpr hg)
      · exact .inl (toList_get.mpr hm1)
    · refine toList_get.mpr ?_
      show get? (PartialMap.union m1 m2) k = some v
      rw [get?_union]
      rcases h with h | h
      · simp [toList_get.mp h, Option.orElse]
      · rcases (PartialMap.disjoint_iff m1 m2).mp hdisj k with h1 | h1
        · simp [h1, toList_get.mp h, Option.orElse]
        · exact absurd (toList_get.mp h) (by simp [h1])

theorem bigOpM_union_equiv [DecidableEq K] (Φ : K → V → M) (m1 m2 : M' V) (hdisj : m1 ##ₘ m2) :
    ([^ op map] k ↦ x ∈ m1 ∪ m2, Φ k x) ≡
    op ([^ op map] k ↦ x ∈ m1, Φ k x) ([^ op map] k ↦ x ∈ m2, Φ k x) :=
  (bigOpL_equiv_of_perm _ (toList_union_perm hdisj)).trans
    ((bigOpL_append_equiv ..).trans (op_congr_right (bigOpL_equiv_of_forall_equiv .rfl)))

theorem bigOpM_op_equiv (Φ Ψ : K → V → M) (m : M' V) :
    ([^ op map] k ↦ x ∈ m, op (Φ k x) (Ψ k x)) ≡
    op ([^ op map] k ↦ x ∈ m, Φ k x) ([^ op map] k ↦ x ∈ m, Ψ k x) :=
  bigOpL_op_equiv ..

theorem bigOpM_closed {P : M → Prop} {Φ : K → V → M} {m : M' V}
    (hunit : P unit) (hop : ∀ {x y}, P x → P y → P (op x y))
    (hf : ∀ {k x}, get? m k = some x → P (Φ k x)) :
    P ([^ op map] k ↦ x ∈ m, Φ k x) :=
  bigOpL_closed hunit hop fun h => hf <| toList_get.mp <| List.mem_iff_getElem?.mpr ⟨_, h⟩

-- TODO: kmap and map_seq are skipped for now

theorem bigOpM_sep_zipWith_equiv {A : Type _} {B : Type _} {C : Type _}
    {f : A → B → C} {g1 : C → A} {g2 : C → B}
    (h1 : K → A → M) (h2 : K → B → M) {m1 : M' A} {m2 : M' B}
    (hg1 : ∀ {x y}, g1 (f x y) = x) (hg2 : ∀ {x y}, g2 (f x y) = y)
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([^ op map] k ↦ xy ∈ PartialMap.zipWith f m1 m2, op (h1 k (g1 xy)) (h2 k (g2 xy))) ≡
    op ([^ op map] k ↦ x ∈ m1, h1 k x) ([^ op map] k ↦ x ∈ m2, h2 k x) := by
  refine (bigOpM_op_equiv (fun k xy => h1 k (g1 xy)) (fun k xy => h2 k (g2 xy)) _).trans ?_
  have hdom' : ∀ k, (get? m1 k).isSome = (get? m2 k).isSome := (Bool.eq_iff_iff.mpr <| hdom ·)
  apply op_proper <;> {
    refine (bigOpM_map_equiv _ _ _).symm.trans (bigOpM_equiv_of_perm _ fun k => ?_)
    simp only [get?_map, get?_zipWith]
    have _ := hdom' k
    cases h1k : get? m1 k <;> cases h2k : get? m2 k <;>
      simp_all [Option.bind, Option.map] }

theorem bigOpM_sep_zip_equiv {A : Type _} {B : Type _}
    (h1 : K → A → M) (h2 : K → B → M) {m1 : M' A} {m2 : M' B}
    (hdom : ∀ k, (get? m1 k).isSome ↔ (get? m2 k).isSome) :
    ([^ op map] k ↦ xy ∈ PartialMap.zip m1 m2, op (h1 k xy.1) (h2 k xy.2)) ≡
    op ([^ op map] k ↦ x ∈ m1, h1 k x) ([^ op map] k ↦ x ∈ m2, h2 k x) :=
  bigOpM_sep_zipWith_equiv _ _ rfl rfl hdom

end BigOpM

namespace BigOpS

variable {M : Type _} {A : Type _} {S : Type _} [OFE M] {op : M → M → M} {unit : M}
  [MonoidOps op unit] [LawfulFiniteSet S A]

open BigOpL MonoidOps LawfulSet FiniteSet

@[simp] theorem bigOpS_empty {Φ : A → M} :
    ([^ op set] x ∈ (∅ : S), Φ x) = unit := by
  simp only [bigOpS, toList_empty, bigOpL_nil]

theorem bigOpS_bigOpL (Φ : A → M) (s : S)
  : ([^ op set] x ∈ s, Φ x) ≡ ([^ op list] x ∈ toList s, Φ x) := by
  simp only [bigOpS]
  induction (toList s) with
  | nil => simp
  | cons x xs IH => simp only [bigOpL_cons]; exact op_congr_right IH

theorem bigOpS_insert {Φ : A → M} {s : S} {x : A} (Hnin : x ∉ s) :
  ([^ op set] x ∈ ({x} ∪ s), Φ x) ≡ op (Φ x) ([^ op set] x ∈ s, Φ x) := by
  refine (bigOpS_bigOpL Φ _).trans ?_
  refine (bigOpL_equiv_of_perm Φ (toList_insert_perm Hnin)).trans ?_
  simp only [bigOpL_cons]
  exact (op_congr_right (bigOpS_bigOpL Φ _).symm)

theorem bigOpS_const_unit (s : S) :
    ([^ op set] _x ∈ s, unit) ≡ unit := by
  induction s using set_ind with
  | hemp => simp [bigOpS_empty]
  | hadd x X hnin IH =>
    rw [insert_union]
    refine (bigOpS_insert hnin).trans ?_
    exact op_left_id.trans IH

theorem bigOpS_singleton {Φ : A → M} {a : A} :
    ([^ op set] x ∈ ({a} : S), Φ x) ≡ Φ a := by
  simp only [bigOpS, toList_singleton]; apply bigOpL_singleton_equiv

theorem bigOpS_union {Φ : A → M} {s₁ s₂ : S} (Hdisj : s₁ ## s₂) :
  ([^ op set] x ∈ (s₁ ∪ s₂), Φ x) ≡ op ([^ op set] x ∈ s₁, Φ x) ([^ op set] x ∈ s₂, Φ x) := by
  induction s₁ using set_ind with
  | hemp =>
    simp only [union_empty_left, bigOpS_empty]
    exact op_left_id.symm
  | hadd x X Hnin IH =>
    rw [insert_union, ←union_assoc]
    rw [insert_union, disjoint_union_left, disjoint_singleton_left] at Hdisj
    have nunion : x ∉ X ∪ s₂ := by
      rw [mem_union]; rintro (h|h)
      · apply Hnin h
      · apply Hdisj.left h
    refine (bigOpS_insert nunion).trans ?_
    refine (op_congr_right (IH Hdisj.right)).trans ?_
    refine ((op_congr_left (bigOpS_insert Hnin)).trans ?_).symm
    exact op_assoc

theorem bigOpS_equiv_of_forall_equiv {Φ Ψ : A → M} {s : S}
    (h : ∀ x, Φ x ≡ Ψ x) :
    ([^ op set] x ∈ s, Φ x) ≡ ([^ op set] x ∈ s, Ψ x) := by
  refine (bigOpS_bigOpL Φ _).trans ?_; refine ((bigOpS_bigOpL Ψ _).trans ?_).symm
  exact bigOpL_equiv_of_forall_equiv (fun {i x} => (h x).symm)

theorem bigOpS_dist {Φ Ψ : A → M} {s : S} {n : Nat}
    (h : ∀ x, x ∈ s → Φ x ≡{n}≡ Ψ x) :
    ([^ op set] x ∈ s, Φ x) ≡{n}≡ ([^ op set] x ∈ s, Ψ x) := by
  refine ((bigOpS_bigOpL Φ _).dist).trans ?_; refine (((bigOpS_bigOpL Ψ _).dist).trans ?_).symm
  refine bigOpL_dist (fun {i x} hin => (h x ?_).symm)
  rw [←Std.mem_toList, List.mem_iff_getElem?]
  exists i

theorem bigOpS_op_equiv (Φ Ψ : A → M) (s : S) :
    ([^ op set] x ∈ s, op (Φ x) (Ψ x)) ≡
      op ([^ op set] x ∈ s, Φ x) ([^ op set] x ∈ s, Ψ x) :=
        (bigOpS_bigOpL ..).trans (bigOpL_op_equiv ..)

theorem bigOpS_closed (P : M → Prop) (Φ : A → M) (s : S)
    (hunit : P unit)
    (hop : ∀ x y, P x → P y → P (op x y))
    (hf : ∀ x, x ∈ s → P (Φ x)) :
    P ([^ op set] x ∈ s, Φ x) := by
  unfold bigOpS
  generalize hg : toList s = l
  have htoList : ∀ x, x ∈ l → P (Φ x) := by
    intro x hx
    apply hf
    rw [←FiniteSet.mem_toList, hg]
    exact hx
  clear hf hg s
  suffices ∀ b, P b → P (bigOpL op (fun x x_1 => (fun x => Φ x) x_1) l) by exact this unit hunit
  intro b hb
  induction l generalizing b with
  | nil => simp only [bigOpL_nil]; exact hunit
  | cons y ys ih =>
    simp only [bigOpL_cons]
    apply hop; apply htoList _ (List.mem_cons.mpr (.inl rfl))
    apply ih
    · intro x Hxin
      exact htoList x (List.mem_cons.mpr (.inr Hxin))
    · exact hop _ _ (htoList y (List.mem_cons.mpr (.inl rfl))) hunit

theorem bigOpS_gen_proper (R : M → M → Prop) {Φ Ψ : A → M} {s : S}
    (hR_refl : ∀ {x}, R x x) (hR_op : ∀ {a a' b b'}, R a a' → R b b' → R (op a b) (op a' b'))
    (hf : ∀ {y}, y ∈ s → R (Φ y) (Ψ y)) :
    R ([^ op set] x ∈ s, Φ x) ([^ op set] x ∈ s, Ψ x) := by
  refine bigOpL_gen_proper R hR_refl hR_op (fun hy => hf ?_)
  rw [←FiniteSet.mem_toList]
  exact List.mem_of_getElem? hy

theorem bigOpS_ext {Φ Ψ : A → M} {s : S}
    (h : ∀ {x}, x ∈ s → Φ x = Ψ x) :
    ([^ op set] x ∈ s, Φ x) = ([^ op set] x ∈ s, Ψ x) :=
  bigOpS_gen_proper (· = ·) rfl (· ▸ · ▸ rfl) h

variable {M₁ : Type u} {M₂ : Type v} [OFE M₁] [OFE M₂]
variable {op₁ : M₁ → M₁ → M₁} {op₂ : M₂ → M₂ → M₂} {unit₁ : M₁} {unit₂ : M₂}
variable [MonoidOps op₁ unit₁] [MonoidOps op₂ unit₂]

theorem hom {B : Type w} {S' : Type _} [LawfulFiniteSet S' B] {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : MonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : B → M₁) (s : S') :
    R (f ([^ op₁ set] x ∈ s, Φ x)) ([^ op₂ set] x ∈ s, f (Φ x)) := by
  rw [hom.rel_proper (hom.map_ne.eqv (bigOpS_bigOpL Φ s)) Equiv.rfl]
  refine (hom.rel_trans (bigOpL_hom (H := hom) (fun x y => Φ y) (toList s))) ?_
  rw [hom.rel_proper (bigOpS_bigOpL _ s).symm Equiv.rfl]
  exact hom.rel_refl

theorem hom_weak {B : Type w} {S' : Type _} [LawfulFiniteSet S' B] {R : M₂ → M₂ → Prop} {f : M₁ → M₂}
    (hom : WeakMonoidHomomorphism op₁ op₂ unit₁ unit₂ R f)
    (Φ : B → M₁) (s : S') (hne : s ≠ ∅) :
    R (f ([^ op₁ set] x ∈ s, Φ x)) ([^ op₂ set] x ∈ s, f (Φ x)) := by
  rw [hom.rel_proper (hom.map_ne.eqv (bigOpS_bigOpL Φ s)) Equiv.rfl]
  refine (hom.rel_trans (bigOpL_hom_weak (H := hom) (fun x y => Φ y) ?_)) ?_
  · intro heq
    apply hne; ext i; simp [←FiniteSet.mem_toList, heq, toList_empty]
  · rw [hom.rel_proper (bigOpS_bigOpL _ s).symm Equiv.rfl]
    exact hom.rel_refl

end BigOpS

end

end Iris.Algebra
