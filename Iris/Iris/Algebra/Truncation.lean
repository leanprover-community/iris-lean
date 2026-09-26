/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.OFE

/-! # Truncations of OFEs

The truncation `TruncO α A` of an OFE `A` at a step-index `α` identifies elements that agree up to
`α`; its distance at `n` is the distance of `A` at `min n α`. This is the truncation `[A]_{α}` of
Transfinite Iris (`algebra/ofe.v`, class `Truncatable`), which the transfinite COFE solver uses to
make the approximations of the solution agree *exactly* instead of up to a step-index.

Transfinite Iris has to require truncations as extra structure (`Truncatable`, `ProtoTruncatable`)
because Rocq has no quotient types. In Lean every OFE has a truncation, given by a quotient.

This file also defines the uniqueness property `BcomplUniqueLim` of limits of bounded chains,
which the transfinite solver requires from the functor.
-/

@[expose] public section

namespace Iris
open OFE

variable {SI : Type _} [instSI : SIdx SI]
local stepindex SI

/-! ## Truncated OFEs -/

/-- An OFE is *truncated* at `α` if equality is already determined by the distance at `α`
(Transfinite Iris, `OfeTruncated`). -/
@[rocq_alias OfeTruncated]
class OFE.Truncated (A : Type _) [OFE A] (α : SI) : Prop where
  eq_of_dist {x y : A} : x ≡{α}≡ y → x = y

namespace OFE.Truncated

variable {A : Type _} [OFE A] {α : SI} [Truncated A α]

theorem dist_iff {x y : A} : x ≡{α}≡ y ↔ x = y := ⟨eq_of_dist, Dist.of_eq⟩

/-- In a truncated OFE, the distance at an index above the truncation index is equality. -/
theorem eq_of_dist_le {n : SI} (h : α ≤ n) {x y : A} (hxy : x ≡{n}≡ y) : x = y :=
  eq_of_dist (hxy.le h)

@[rocq_alias ofe_truncated_dist]
theorem dist_of_dist_le {n : SI} (_ : α ≤ n) {x y : A} (hxy : x ≡{α}≡ y) : x ≡{n}≡ y :=
  Dist.of_eq (eq_of_dist hxy)

/-- Non-expansive maps into an OFE truncated at `α` are equal if they agree up to `α`. -/
theorem hom_eq {B : Type _} [OFE B] {f g : B -n> A} (h : ∀ x, f x ≡{α}≡ g x) : f = g :=
  Hom.ext (funext fun x => eq_of_dist (h x))

instance hom {B : Type _} [OFE B] : Truncated (B -n> A) α where
  eq_of_dist h := hom_eq h

end OFE.Truncated

/-! ## The truncation of an OFE -/

/-- The setoid identifying elements that agree up to `α`. -/
def truncSetoid (A : Type _) [OFE A] (α : SI) : Setoid A where
  r x y := x ≡{α}≡ y
  iseqv := ⟨fun _ => .rfl, Dist.symm, Dist.trans⟩

/-- The truncation of `A` at `α` (Transfinite Iris, `[A]_{α}`). -/
def TruncO (α : SI) (A : Type _) [OFE A] : Type _ := Quotient (truncSetoid A α)

namespace TruncO

variable {A : Type _} [OFE A] {α : SI}

/-- The class of an element. -/
def mk (x : A) : TruncO α A := Quotient.mk _ x

/-- The representative of an element of the truncation (chosen classically). -/
noncomputable def out (q : TruncO α A) : A := Classical.choose (Quotient.exists_rep q)

@[simp] theorem mk_out (q : TruncO α A) : mk q.out = q :=
  Classical.choose_spec (Quotient.exists_rep q)

theorem mk_eq_mk {x y : A} : (mk x : TruncO α A) = mk y ↔ x ≡{α}≡ y :=
  ⟨fun h => (Quotient.exact h : _), fun h => Quotient.sound (s := truncSetoid A α) h⟩

theorem out_mk (x : A) : (mk x : TruncO α A).out ≡{α}≡ x := mk_eq_mk.mp (mk_out _)

instance [Inhabited A] : Inhabited (TruncO α A) := ⟨mk default⟩

theorem ext_out {q q' : TruncO α A} (h : q.out ≡{α}≡ q'.out) : q = q' := by
  rw [← mk_out q, ← mk_out q']
  exact mk_eq_mk.mpr h

noncomputable instance instOFE : OFE (TruncO α A) where
  Dist n q q' := ∀ m, m ≤ n → m ≤ α → q.out ≡{m}≡ q'.out
  dist_eqv := {
    refl _ _ _ _ := .rfl
    symm h m h1 h2 := (h m h1 h2).symm
    trans h h' m h1 h2 := (h m h1 h2).trans (h' m h1 h2)
  }
  eq_dist' := ⟨fun h => h ▸ fun _ _ _ _ => .rfl, fun h => ext_out (h α α SIdx.le_refl SIdx.le_refl)⟩
  dist_lt h hlt m h1 h2 := h m (SIdx.le_trans h1 (SIdx.lt_le_incl hlt)) h2

theorem dist_def {n : SI} {q q' : TruncO α A} :
    q ≡{n}≡ q' ↔ ∀ m, m ≤ n → m ≤ α → q.out ≡{m}≡ q'.out := .rfl

/-- The distance at `n ≤ α` is the distance of the representatives. -/
theorem dist_iff_of_le {n : SI} (hn : n ≤ α) {q q' : TruncO α A} :
    q ≡{n}≡ q' ↔ q.out ≡{n}≡ q'.out :=
  ⟨fun h => h n SIdx.le_refl hn, fun h _ h1 _ => h.le h1⟩

instance truncated : Truncated (TruncO α A) α where
  eq_of_dist h := ext_out (h α SIdx.le_refl SIdx.le_refl)

theorem mk_dist_mk {n : SI} {x y : A} (hn : n ≤ α) :
    (mk x : TruncO α A) ≡{n}≡ mk y ↔ x ≡{n}≡ y := by
  rw [dist_iff_of_le hn]
  exact ⟨fun h => ((out_mk x).le hn).symm.trans (h.trans ((out_mk y).le hn)),
    fun h => ((out_mk x).le hn).trans (h.trans ((out_mk y).le hn).symm)⟩

end TruncO

section Maps

variable {A B C : Type _} [OFE A] [OFE B] [OFE C]

/-- The truncation map `A → [A]_{α}` (Transfinite Iris, `⌊·⌋_{α}`). -/
noncomputable def truncate (α : SI) : A -n> TruncO α A where
  f := TruncO.mk
  ne := ⟨fun _ _ _ h _ h1 h2 =>
    ((TruncO.out_mk _).le h2).trans ((h.le h1).trans ((TruncO.out_mk _).le h2).symm)⟩

/-- The expansion map `[A]_{α} → A` choosing representatives (Transfinite Iris, `⌈·⌉_{α}`). -/
noncomputable def expand (α : SI) : TruncO α A -n> A where
  f := TruncO.out
  ne := ⟨fun n q q' h => by
    rcases SIdx.le_total (n := n) (m := α) with hle | hle
    · exact h n SIdx.le_refl hle
    · exact Dist.of_eq (congrArg TruncO.out (TruncO.ext_out (h α hle SIdx.le_refl)))⟩

@[simp] theorem truncate_expand (α : SI) (q : TruncO α A) : truncate α (expand α q) = q :=
  TruncO.mk_out q

@[rocq_alias ofe_trunc_expand_truncate_id]
theorem expand_truncate (α : SI) (x : A) : expand α (truncate α x) ≡{α}≡ x := TruncO.out_mk x

theorem expand_truncate_le {α n : SI} (h : n ≤ α) (x : A) : expand α (truncate α x) ≡{n}≡ x :=
  (expand_truncate α x).le h

theorem truncate_dist_truncate {α n : SI} (hn : n ≤ α) {x y : A} :
    truncate α x ≡{n}≡ truncate α y ↔ x ≡{n}≡ y := TruncO.mk_dist_mk hn

theorem truncate_eq_truncate {α : SI} {x y : A} :
    truncate α x = truncate α y ↔ x ≡{α}≡ y := TruncO.mk_eq_mk

/-- Maps between truncations (Transfinite Iris, `trunc_map`). -/
@[rocq_alias trunc_map]
noncomputable def truncMap (α β : SI) (f : A -n> B) : TruncO α A -n> TruncO β B :=
  (truncate β).comp (f.comp (expand α))

theorem truncMap_apply (α β : SI) (f : A -n> B) (q : TruncO α A) :
    truncMap α β f q = truncate β (f (expand α q)) := rfl

theorem truncMap_ne (α β : SI) : NonExpansive (truncMap (A := A) (B := B) α β) where
  ne _ _ _ h := fun _ => (truncate β).ne.1 (h _)

/-- Rocq: `trunc_map_compose`. -/
@[rocq_alias trunc_map_compose]
theorem truncMap_comp_dist (α β γ : SI) (f : A -n> B) (g : B -n> C) (q : TruncO α A) :
    truncMap α β (g.comp f) q ≡{γ}≡ truncMap γ β g (truncMap α γ f q) :=
  (truncate β).ne.1 (g.ne.1 (expand_truncate γ _).symm)

/-- `truncMap` preserves bounded inverses (Rocq: `trunc_map_inv`). -/
@[rocq_alias trunc_map_inv]
theorem truncMap_inv {α β : SI} (hle : α ≤ β) (f : A -n> B) (g : B -n> A)
    (h1 : ∀ x, f (g x) ≡{α}≡ x) (h2 : ∀ x, g (f x) ≡{α}≡ x) :
    (∀ q, truncMap α β f (truncMap β α g q) ≡{α}≡ q) ∧
      (∀ q, truncMap β α g (truncMap α β f q) ≡{α}≡ q) := by
  constructor
  · intro q
    refine ((truncate β).ne.1 ((f.ne.1 (expand_truncate α _)).trans (h1 _))).trans ?_
    exact Dist.of_eq (truncate_expand β q)
  · intro q
    refine ((truncate α).ne.1 ((g.ne.1 (expand_truncate_le hle _)).trans (h2 _))).trans ?_
    exact Dist.of_eq (truncate_expand α q)

end Maps

/-! ## Truncations of COFEs -/

namespace TruncO

variable {A : Type _} [COFE A] {α : SI}

@[rocq_alias Truncatable_cofe]
noncomputable instance instCOFE : IsCOFE (TruncO α A) where
  compl c := truncate α (COFE.compl (c.map (expand α)))
  conv_compl := ((truncate α).ne.1 COFE.conv_compl).trans (Dist.of_eq (truncate_expand α _))
  lbcompl hn c := truncate α (IsCOFE.lbcompl hn (c.map (expand α)))
  conv_lbcompl hn _ _ hm :=
    ((truncate α).ne.1 (IsCOFE.conv_lbcompl hn _ hm)).trans (Dist.of_eq (truncate_expand α _))
  lbcompl_ne hn _ _ _ h :=
    (truncate α).ne.1 (IsCOFE.lbcompl_ne hn _ _ fun p hp => (expand α).ne.1 (h p hp))

end TruncO

/-! ## Uniqueness of limits of bounded chains -/

/-- Limits of bounded chains of limit length `n` agree up to `n` if the chains agree pointwise
(Transfinite Iris, `BcomplUniqueLim`). The transfinite COFE solver requires this of the functor. -/
@[rocq_alias BcomplUniqueLim]
class BcomplUniqueLim (A : Type _) [COFE A] : Prop where
  lbcompl_unique {n : SI} (hn : SIdx.Limit n) (c d : BChain A n) :
    (∀ m (hm : m < n), c.bchain m hm ≡{m}≡ d.bchain m hm) → IsCOFE.lbcompl hn c ≡{n}≡ IsCOFE.lbcompl hn d

@[rocq_alias Truncatable_unique_lim]
instance TruncO.instBcomplUniqueLim {A : Type _} [COFE A] [BcomplUniqueLim A] {α : SI} :
    BcomplUniqueLim (TruncO α A) where
  lbcompl_unique hn _ _ h :=
    (truncate α).ne.1 (BcomplUniqueLim.lbcompl_unique hn _ _ fun m hm => (expand α).ne.1 (h m hm))

end Iris
