/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.BigOp
public import Iris.Std.List
meta import Iris.Std.RocqPorting

@[expose] public section

/-! ## Generic `List.Forall₂` lemmas

These are stdpp-style properties of the heterogeneous list relation `List.Forall₂`, used to build
the list OFE. They correspond to lemmas in stdpp's `list.v` rather than to Iris, so they carry no
`rocq_alias`. -/

namespace List
open Iris.OFE

variable {α β γ δ : Type _}

theorem Forall₂.length_eq {R : α → β → Prop} {l : List α} {k : List β} :
    Forall₂ R l k → l.length = k.length
  | .nil => rfl
  | .cons _ h => congrArg (· + 1) h.length_eq

theorem Forall₂.imp {R S : α → β → Prop} (H : ∀ {a b}, R a b → S a b) {l : List α} {k : List β}
    (h : Forall₂ R l k) : Forall₂ S l k := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (H hab) ih

theorem Forall₂.refl {R : α → α → Prop} (H : ∀ a, R a a) : (l : List α) → Forall₂ R l l
  | [] => .nil
  | _ :: l => .cons (H _) (Forall₂.refl H l)

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

theorem Forall₂.append {R : α → β → Prop} {l₁ l₂ : List α} {k₁ k₂ : List β} :
    Forall₂ R l₁ k₁ → Forall₂ R l₂ k₂ → Forall₂ R (l₁ ++ l₂) (k₁ ++ k₂)
  | .nil, h => h
  | .cons hd t, h => .cons hd (t.append h)

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

theorem forall₂_of_getElem? {R : α → β → Prop} {l : List α} {k : List β}
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

theorem Forall₂.eraseIdx {R : α → β → Prop} {l : List α} {k : List β}
    (h : Forall₂ R l k) : (i : Nat) → Forall₂ R (l.eraseIdx i) (k.eraseIdx i)
  | 0 => by cases h with | nil => exact .nil | cons _ t => exact t
  | i + 1 => by cases h with | nil => exact .nil | cons hd t => exact .cons hd (t.eraseIdx i)

end List

namespace Iris
open OFE COFE Iris.Algebra

/-! ## The list OFE -/

section ofe
variable [OFE α]

theorem forall₂_equiv_of_forall₂_dist : ∀ {l k : List α},
    (∀ n, List.Forall₂ (Dist n) l k) → List.Forall₂ Equiv l k
  | [], [], _ => .nil
  | [], _ :: _, h => nomatch h 0
  | _ :: _, [], h => nomatch h 0
  | _ :: _, _ :: _, h =>
    .cons (equiv_dist.mpr fun n => (List.forall₂_cons.mp (h n)).1)
          (forall₂_equiv_of_forall₂_dist fun n => (List.forall₂_cons.mp (h n)).2)

/-- `l ≡ k` on lists is the pointwise equivalence `List.Forall₂ (· ≡ ·)`, and
`l ≡{n}≡ k` is `List.Forall₂ (· ≡{n}≡ ·)`. -/
@[rocq_alias list_ofe_mixin]
instance : OFE (List α) where
  Equiv := List.Forall₂ Equiv
  Dist n := List.Forall₂ (Dist n)
  dist_eqv := List.Forall₂.equivalence dist_eqv
  equiv_dist := ⟨fun h _ => h.imp Equiv.dist, forall₂_equiv_of_forall₂_dist⟩
  dist_lt h hlt := h.imp fun hab => hab.lt hlt
#rocq_ignore listO "Use List"
#rocq_ignore list_dist "Local Dist instance; folded into Lean's OFE (List α) instance."

@[rocq_alias list_dist_Forall2]
theorem list_dist_forall₂ {n} {l k : List α} : l ≡{n}≡ k ↔ List.Forall₂ (Dist n) l k := .rfl

@[rocq_alias list_dist_lookup]
theorem list_dist_lookup {n} {l k : List α} : l ≡{n}≡ k ↔ ∀ (i : Nat), l[i]? ≡{n}≡ k[i]? :=
  ⟨fun h i => h.getElem? i, List.forall₂_of_getElem?⟩

@[rocq_alias cons_ne]
instance cons_ne : NonExpansive₂ (α := α) List.cons where
  ne _ _ _ hx _ _ hl := .cons hx hl

@[rocq_alias app_ne]
instance app_ne : NonExpansive₂ (α := List α) (· ++ ·) where
  ne _ _ _ h1 _ _ h2 := h1.append h2

@[rocq_alias length_ne]
theorem length_dist {n} {l k : List α} (h : l ≡{n}≡ k) : l.length = k.length := h.length_eq

@[rocq_alias tail_ne]
instance tail_ne : NonExpansive (List.tail (α := α)) where
  ne _ _ _ h := match h with | .nil => .nil | .cons _ t => t

@[rocq_alias take_ne]
instance take_ne (m : Nat) : NonExpansive (List.take m (α := α)) where
  ne _ _ _ h := h.take m

@[rocq_alias drop_ne]
instance drop_ne (m : Nat) : NonExpansive (List.drop m (α := α)) where
  ne _ _ _ h := h.drop m

@[rocq_alias head_ne]
instance head_ne : NonExpansive (List.head? (α := α)) where
  ne _ _ _ h := match h with | .nil => trivial | .cons hh _ => hh

@[rocq_alias list_lookup_ne]
instance getElem?_ne (i : Nat) : NonExpansive (fun l : List α => l[i]?) where
  ne _ _ _ h := h.getElem? i

@[rocq_alias list_insert_ne]
instance set_ne (i : Nat) : NonExpansive₂ (fun (a : α) (l : List α) => l.set i a) where
  ne _ _ _ ha _ _ hl := hl.set ha i

@[rocq_alias list_delete_ne]
instance eraseIdx_ne (i : Nat) : NonExpansive (fun l : List α => l.eraseIdx i) where
  ne _ _ _ h := h.eraseIdx i

@[rocq_alias replicate_ne]
instance replicate_ne (m : Nat) : NonExpansive (List.replicate m (α := α)) where
  ne _ _ _ h := .replicate h m

@[rocq_alias reverse_ne]
instance reverse_ne : NonExpansive (List.reverse (α := α)) where
  ne _ _ _ h := h.reverse

@[rocq_alias last_ne]
instance getLast?_ne : NonExpansive (List.getLast? (α := α)) where
  ne _ _ _ h := h.getLast?

@[rocq_alias option_list_ne]
instance optionToList_ne : NonExpansive (Option.toList (α := α)) where
  ne _ o o' h := by
    cases o with
    | none => cases o' with | none => exact .nil | some _ => exact h.elim
    | some a => cases o' with | none => exact h.elim | some b => exact .cons h .nil

@[rocq_alias cons_dist_inj]
theorem cons_dist_inj {n} {x y : α} {l k : List α} (h : x :: l ≡{n}≡ y :: k) :
    x ≡{n}≡ y ∧ l ≡{n}≡ k := match h with | .cons hx ht => ⟨hx, ht⟩

@[rocq_alias nil_dist_eq]
theorem nil_dist_eq {n} {l : List α} : l ≡{n}≡ [] ↔ l = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .rfl⟩

@[rocq_alias cons_dist_eq]
theorem cons_dist_eq {n} {l k : List α} {y : α} (h : l ≡{n}≡ y :: k) :
    ∃ x l', x ≡{n}≡ y ∧ l' ≡{n}≡ k ∧ l = x :: l' :=
  match h with | .cons hx ht => ⟨_, _, hx, ht, rfl⟩

theorem app_dist_eq_mp {n} : ∀ (k1 l k2 : List α),
    l ≡{n}≡ k1 ++ k2 → ∃ k1' k2', l = k1' ++ k2' ∧ k1' ≡{n}≡ k1 ∧ k2' ≡{n}≡ k2
  | [], l, _, h => ⟨[], l, rfl, .nil, h⟩
  | a :: k1'', _, k2, h => by
      obtain ⟨x, l'', hx, hl, rfl⟩ := cons_dist_eq h
      obtain ⟨p, q, rfl, hp, hq⟩ := app_dist_eq_mp k1'' l'' k2 hl
      exact ⟨x :: p, q, rfl, .cons hx hp, hq⟩

@[rocq_alias app_dist_eq]
theorem app_dist_eq {n} {l k1 k2 : List α} :
    l ≡{n}≡ k1 ++ k2 ↔ ∃ k1' k2', l = k1' ++ k2' ∧ k1' ≡{n}≡ k1 ∧ k2' ≡{n}≡ k2 :=
  ⟨app_dist_eq_mp k1 l k2, fun ⟨_, _, h, h1, h2⟩ => h ▸ h1.append h2⟩

@[rocq_alias list_singleton_dist_eq]
theorem list_singleton_dist_eq {n} {l : List α} {x : α} :
    l ≡{n}≡ [x] ↔ ∃ x', l = [x'] ∧ x' ≡{n}≡ x := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x', l', hx, hl, rfl⟩ := cons_dist_eq h
    exact ⟨x', by rw [nil_dist_eq.mp hl], hx⟩
  · rintro ⟨x', rfl, hx⟩
    exact .cons hx .nil

@[rocq_alias list_ofe_discrete]
instance list_ofe_discrete [Discrete α] : Discrete (List α) where
  discrete_0 h := h.imp discrete_0

@[rocq_alias nil_discrete]
instance nil_discrete : DiscreteE ([] : List α) where
  discrete h := by cases h; exact .nil

@[rocq_alias cons_discrete]
instance cons_discrete (x : α) (l : List α) [DiscreteE x] [DiscreteE l] :
    DiscreteE (x :: l) where
  discrete h := by
    cases h with
    | cons hx hl => exact .cons (‹DiscreteE x›.discrete hx) (‹DiscreteE l›.discrete hl)

@[rocq_alias dist_Permutation]
theorem dist_Permutation {n} {l1 l2 l3 : List α} (hd : l1 ≡{n}≡ l2) (hp : l2.Perm l3) :
    ∃ l2', l1.Perm l2' ∧ l2' ≡{n}≡ l3 := by
  induction hp generalizing l1 with
  | nil => exact ⟨l1, .refl _, hd⟩
  | cons x _ ih =>
    obtain ⟨x', l2'', hx, hl, rfl⟩ := cons_dist_eq hd
    obtain ⟨m, hm1, hm2⟩ := ih hl
    exact ⟨x' :: m, hm1.cons x', .cons hx hm2⟩
  | swap x y l =>
    obtain ⟨y', r, hy, hr, rfl⟩ := cons_dist_eq hd
    obtain ⟨x', l2', hx, hl, rfl⟩ := cons_dist_eq hr
    exact ⟨x' :: y' :: l2', .swap _ _ _, .cons hx (.cons hy hl)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨m, hm1, hm2⟩ := ih1 hd
    obtain ⟨m2, hn1, hn2⟩ := ih2 hm2
    exact ⟨m2, hm1.trans hn1, hn2⟩

end ofe

/-! ## COFE structure -/

section cofe
variable [COFE α]

/-- Head of a chain of lists, defaulting to `x` on the empty list; used to project a chain of lists
onto a chain of its first elements. -/
def headGetDHom (x : α) : List α -n> α where
  f l := l.head?.getD x
  ne := ⟨fun _ _ _ h => match h with | .nil => .rfl | .cons hh _ => hh⟩

@[simp] theorem headGetDHom_apply {x : α} {l : List α} : headGetDHom x l = l.head?.getD x := rfl

/-- Tail of a list as a nonexpansive map, used to project a chain of lists onto a chain of tails. -/
def tailHom : List α -n> List α where
  f := List.tail
  ne := ⟨fun _ _ _ h => match h with | .nil => .nil | .cons _ t => t⟩

@[simp] theorem tailHom_apply {l : List α} : tailHom l = l.tail := rfl

/-- The shape of the chain is fixed by its first list `c0`; the completion takes the pointwise
completion of the first elements and recurses on the tails. -/
@[rocq_alias list_compl_go]
def listComplGo : List α → Chain (List α) → List α
  | [], _ => []
  | x :: c0, c => compl (c.map (headGetDHom x)) :: listComplGo c0 (c.map tailHom)

theorem listComplGo_conv_compl {n : Nat} (c : Chain (List α)) :
    ∀ (c0 : List α), c0 ≡{0}≡ c n → listComplGo c0 c ≡{n}≡ c n
  | [], H => by rw [nil_dist_eq.mp H.symm]; exact .rfl
  | x :: c0, H => by
    obtain ⟨x', xs', _, hxs, hcn⟩ := cons_dist_eq H.symm
    rw [hcn]
    show compl (c.map (headGetDHom x)) :: listComplGo c0 (c.map tailHom) ≡{n}≡ x' :: xs'
    refine .cons ?_ ?_
    · refine conv_compl.trans (Dist.of_eq ?_)
      simp [Chain.map_apply, headGetDHom_apply, hcn]
    · refine (listComplGo_conv_compl (c.map tailHom) c0 ?_).trans (Dist.of_eq ?_)
      · simp only [Chain.map_apply, tailHom_apply, hcn, List.tail_cons]
        exact hxs.symm
      · simp [Chain.map_apply, tailHom_apply, hcn]

@[rocq_alias list_cofe]
instance : IsCOFE (List α) where
  compl c := listComplGo (c 0) c
  conv_compl {n c} := listComplGo_conv_compl c (c 0) (c.cauchy (Nat.zero_le n)).symm

end cofe

/-! ## Nonexpansiveness of higher-order list functions -/

section higher_order

@[rocq_alias list_fmap_ne]
theorem list_fmap_ne [OFE α] [OFE β] {n} {f g : α → β}
    (Hf : ∀ a b, a ≡{n}≡ b → f a ≡{n}≡ g b) {l k : List α} (h : l ≡{n}≡ k) :
    l.map f ≡{n}≡ k.map g :=
  h.map fun hab => Hf _ _ hab

@[rocq_alias list_fmap_ext_ne]
theorem list_fmap_ext_ne [OFE α] [OFE β] {n} {f g : α → β} {l : List α}
    (Hf : ∀ x, f x ≡{n}≡ g x) : l.map f ≡{n}≡ l.map g :=
  match l with | [] => .nil | a :: _ => .cons (Hf a) (list_fmap_ext_ne Hf)

@[rocq_alias list_fmap_dist_inj]
theorem list_fmap_dist_inj [OFE α] [OFE β] {n} {f : α → β}
    (hf : ∀ {a b}, f a ≡{n}≡ f b → a ≡{n}≡ b) : ∀ {l k : List α},
    l.map f ≡{n}≡ k.map f → l ≡{n}≡ k
  | [], [], _ => .nil
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => by
      cases h with | cons hab ht => exact .cons (hf hab) (list_fmap_dist_inj hf ht)

@[rocq_alias list_omap_ne]
theorem list_omap_ne [OFE α] [OFE β] {n} {f g : α → Option β}
    (Hf : ∀ a b, a ≡{n}≡ b → f a ≡{n}≡ g b) {l k : List α} (h : l ≡{n}≡ k) :
    l.filterMap f ≡{n}≡ k.filterMap g := by
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    have ho := Hf a b hab
    rw [List.filterMap_cons, List.filterMap_cons]
    revert ho
    cases f a <;> cases g b <;> intro ho
    · exact ih
    · exact ho.elim
    · exact ho.elim
    · exact .cons ho ih

@[rocq_alias imap_ne]
theorem mapIdx_ne [OFE α] [OFE β] {n} : ∀ {f g : Nat → α → β},
    (∀ i a b, a ≡{n}≡ b → f i a ≡{n}≡ g i b) → ∀ {l k : List α}, l ≡{n}≡ k →
      l.mapIdx f ≡{n}≡ k.mapIdx g
  | _, _, _, _, _, .nil => .nil
  | f, g, Hf, _, _, .cons hab t => by
      simp only [List.mapIdx_cons]
      exact .cons (Hf 0 _ _ hab) (mapIdx_ne (fun i a b h => Hf (i + 1) a b h) t)

@[rocq_alias list_bind_ne]
theorem list_flatMap_ne [OFE α] [OFE β] {n} {f g : α → List β}
    (Hf : ∀ a b, a ≡{n}≡ b → f a ≡{n}≡ g b) {l k : List α} (h : l ≡{n}≡ k) :
    l.flatMap f ≡{n}≡ k.flatMap g := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => rw [List.flatMap_cons, List.flatMap_cons]; exact (Hf _ _ hab).append ih

@[rocq_alias list_join_ne]
theorem list_flatten_ne [OFE α] {n} {l k : List (List α)} (h : l ≡{n}≡ k) :
    l.flatten ≡{n}≡ k.flatten := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => rw [List.flatten_cons, List.flatten_cons]; exact hab.append ih

@[rocq_alias zip_with_ne]
theorem zipWith_ne [OFE α] [OFE β] [OFE γ] {n} {f g : α → β → γ}
    (Hf : ∀ a b c d, a ≡{n}≡ b → c ≡{n}≡ d → f a c ≡{n}≡ g b d) :
    ∀ {l1 l2 : List α} {k1 k2 : List β}, l1 ≡{n}≡ l2 → k1 ≡{n}≡ k2 →
      List.zipWith f l1 k1 ≡{n}≡ List.zipWith g l2 k2
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons _ _, .nil => .nil
  | _, _, _, _, .cons ha ta, .cons hb tb => .cons (Hf _ _ _ _ ha hb) (zipWith_ne Hf ta tb)

end higher_order

/-! ## Big operators -/

@[rocq_alias big_opL_ne_2]
theorem bigOpL_dist_2 {M α : Type _} [OFE M] [OFE α] {op : M → M → M} {unit : M} [MonoidOps op unit]
    {n : Nat} {l1 l2 : List α} (hl : l1 ≡{n}≡ l2) : ∀ {f g : Nat → α → M},
    (∀ (k : Nat) y1 y2, l1[k]? = some y1 → l2[k]? = some y2 → y1 ≡{n}≡ y2 → f k y1 ≡{n}≡ g k y2) →
    bigOpL op f l1 ≡{n}≡ bigOpL op g l2 := by
  induction hl with
  | nil => exact fun _ => .rfl
  | cons hx t ih =>
    intro f g hf
    rw [BigOpL.bigOpL_cons, BigOpL.bigOpL_cons]
    refine MonoidOps.op_dist (hf 0 _ _ rfl rfl hx) (ih ?_)
    exact fun k y1 y2 h1 h2 hy => hf (k + 1) y1 y2 h1 h2 hy

/-! ## The list functor -/

section functor
open COFE

/-- The list functor's action on morphisms: postcompose with `List.map`. -/
@[rocq_alias listO_map]
def listMap [OFE α] [OFE β] (f : α -n> β) : List α -n> List β where
  f := List.map f
  ne := ⟨fun _ _ _ h => h.map (fun hab => f.ne.ne hab)⟩

@[simp] theorem listMap_apply [OFE α] [OFE β] {f : α -n> β} {l : List α} :
    listMap f l = l.map f := rfl

@[rocq_alias listO_map_ne]
instance listMap_ne [OFE α] [OFE β] : NonExpansive (listMap (α := α) (β := β)) where
  ne _ _ _ h z := by simpa only [listMap_apply] using list_fmap_ext_ne (l := z) fun x => h x

abbrev ListOF (F : OFunctorPre) : OFunctorPre := fun A B _ _ => List (F A B)

variable (F : OFunctorPre)

@[rocq_alias listOF]
instance oFunctorList [OFunctor F] : OFunctor (ListOF F) where
  ofe := _
  map f g := listMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z := by
    simpa only [listMap_apply] using
      list_fmap_ext_ne (l := z) fun x => OFunctor.map_ne.ne Hx Hy x
  map_id z := by
    simp only [listMap_apply]
    induction z with
    | nil => exact .nil
    | cons a _ ih => exact .cons (OFunctor.map_id a) ih
  map_comp f g f' g' z := by
    simp only [listMap_apply, List.map_map]
    induction z with
    | nil => exact .nil
    | cons a _ ih => exact .cons (OFunctor.map_comp f g f' g' a) ih

@[rocq_alias listOF_contractive]
instance [OFunctorContractive F] : OFunctorContractive (ListOF F) where
  map_contractive.1 H z := by
    have h := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    simp only [Function.uncurry]
    induction z with
    | nil => exact .nil
    | cons a _ ih => exact .cons (h a) ih

end functor

end Iris
