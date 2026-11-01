/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE

/-! # Approximations

The domain behind guarded fixpoints. An `Approx α` is a ball of `α`: everything that agrees with a
point at a downward-closed set of step-indices. Ordered by inclusion (smaller balls are more
precise), approximations form a `CCPO`, so `partial_fixpoint` can define functions into them.

`ApproxFun.lift G` turns a functional `G` on curried functions into one on curried approximations.
It is monotone for every `G`, and when `G` is contractive, its fixpoint is exact: `get` of it is
the fixpoint of `G` (`lift_fix_get`). -/

@[expose] public section

namespace Iris
open OFE Lean.Order

/-! ## Approximations of a single element -/

namespace Approx
variable {α : Type _} [OFE α]

/-- The ball around `c` determined by the set of levels `P`. -/
def ball (c : α) (P : Nat → Prop) : α → Prop := fun y => ∀ m, P m → c ≡{m}≡ y

/-- Levels at which all elements of `S` agree. -/
def prec (S : α → Prop) (m : Nat) : Prop := ∀ a b, S a → S b → a ≡{m}≡ b

def IsApprox (S : α → Prop) : Prop := ∃ c P, S = ball c P

end Approx

/-- Approximations of an element: a ball, of finite precision or a singleton. -/
def Approx (α : Type _) [OFE α] := {S : α → Prop // Approx.IsApprox S}

namespace Approx
variable {α : Type _} [OFE α]

instance : PartialOrder (Approx α) where
  rel S T := ∀ y, T.1 y → S.1 y
  rel_refl := fun _ h => h
  rel_trans h1 h2 := fun y h => h1 y (h2 y h)
  rel_antisymm h1 h2 := Subtype.ext (funext fun y => propext ⟨h2 y, h1 y⟩)

theorem ball_self (c : α) (P) : ball c P c := fun _ _ => .rfl

theorem IsApprox.nonempty {S : α → Prop} (h : IsApprox S) : ∃ a, S a := by
  obtain ⟨c, P, rfl⟩ := h
  exact ⟨c, ball_self c P⟩

theorem prec_mono {S : α → Prop} {m n} (h : prec S n) (hmn : m ≤ n) : prec S m :=
  fun a b ha hb => (h a b ha hb).le hmn

/-- Every approximation is the ball around any of its elements, at its own precision. -/
theorem IsApprox.eq_ball {S : α → Prop} (h : IsApprox S) {a} (ha : S a) : S = ball a (prec S) := by
  obtain ⟨c, P, rfl⟩ := h
  funext y
  apply propext
  constructor
  · intro hy m hm
    exact hm a y ha hy
  · intro hy m hm
    have hp : prec (ball c P) m := fun x z hx hz => (hx m hm).symm.trans (hz m hm)
    exact (hp c a (ball_self c P) ha).trans (hy m hp)

theorem IsApprox.subset_eq {S T : α → Prop} (hS : IsApprox S) (hT : IsApprox T)
    (hsub : ∀ y, S y → T y) (hprec : ∀ m, prec S m → prec T m) : S = T := by
  obtain ⟨a, ha⟩ := hS.nonempty
  rw [hS.eq_ball ha, hT.eq_ball (hsub a ha)]
  funext y
  apply propext
  constructor
  · intro hy m hm
    exact hy m fun x z hx hz => hm x z (hsub x hx) (hsub z hz)
  · intro hy m hm
    exact hy m (hprec m hm)

theorem exists_least_of_bounded {c : Approx α → Prop} (hne : ∃ S, c S) :
    ∀ k, (∀ T, c T → ¬ prec T.1 k) → ∃ S, c S ∧ ∀ m T, c T → prec T.1 m → prec S.1 m := by
  intro k
  induction k with
  | zero =>
    intro hk
    obtain ⟨S, hS⟩ := hne
    exact ⟨S, hS, fun m T hT hm => absurd (prec_mono hm (Nat.zero_le m)) (hk T hT)⟩
  | succ k ih =>
    intro hk
    by_cases h : ∃ T, c T ∧ prec T.1 k
    · obtain ⟨S, hS, hSk⟩ := h
      refine ⟨S, hS, fun m T hT hm => prec_mono hSk ?_⟩
      apply Nat.le_of_not_lt
      intro hlt
      exact hk T hT (prec_mono hm hlt)
    · exact ih fun T hT hTk => h ⟨T, hT, hTk⟩

variable [IsCOFE α] [Inhabited α]

def inter (c : Approx α → Prop) : α → Prop := fun y => ∀ S, c S → S.1 y

theorem inter_isApprox {c : Approx α → Prop} (hc : chain c) : IsApprox (inter c) := by
  by_cases hall : ∀ n, ∃ S, c S ∧ prec S.1 n
  · -- Unbounded precision: the intersection is the singleton of the limit.
    let S n := Classical.choose (hall n)
    have hS n : c (S n) := (Classical.choose_spec (hall n)).1
    have hprec n : prec (S n).1 n := (Classical.choose_spec (hall n)).2
    let x n := Classical.choose (S n).2.nonempty
    have hx n : (S n).1 (x n) := Classical.choose_spec (S n).2.nonempty
    let ch : Chain α := {
      chain := x
      cauchy := by
        intro n i hni
        rcases hc _ _ (hS n) (hS i) with h | h
        · exact hprec n _ _ (h _ (hx i)) (hx n)
        · exact prec_mono (hprec i) hni _ _ (hx i) (h _ (hx n)) }
    refine ⟨COFE.compl ch, fun _ => True, ?_⟩
    funext y
    apply propext
    constructor
    · intro hy m _
      exact COFE.conv_compl.trans (hprec m _ _ (hx m) (hy _ (hS m)))
    · intro hy T hT
      obtain ⟨a, ha⟩ := T.2.nonempty
      rw [T.2.eq_ball ha]
      intro m hm
      have hax : a ≡{m}≡ x m := by
        rcases hc _ _ hT (hS m) with h | h
        · exact hm _ _ ha (h _ (hx m))
        · exact hprec m _ _ (h _ ha) (hx m)
      exact hax.trans (COFE.conv_compl.symm.trans (hy m trivial))
  · -- Bounded precision: some element of the chain is below all others.
    by_cases hne : ∃ S, c S
    · obtain ⟨k, hk⟩ := Classical.not_forall.mp hall
      obtain ⟨S, hS, hmax⟩ := exists_least_of_bounded hne k fun T hT hTk => hk ⟨T, hT, hTk⟩
      have hmin : ∀ T, c T → ∀ y, S.1 y → T.1 y := by
        intro T hT y hy
        rcases hc _ _ hS hT with h | h
        · exact IsApprox.subset_eq T.2 S.2 h (fun m hm => hmax m T hT hm) ▸ hy
        · exact h y hy
      have : inter c = S.1 := by
        funext y
        exact propext ⟨fun h => h S hS, fun h T hT => hmin T hT y h⟩
      rw [this]
      exact S.2
    · refine ⟨default, fun _ => False, ?_⟩
      funext y
      apply propext
      exact ⟨fun _ _ h => h.elim, fun _ S hS => (hne ⟨S, hS⟩).elim⟩

instance : CCPO (Approx α) where
  has_csup {c} hc := ⟨⟨inter c, inter_isApprox hc⟩, fun _ =>
    ⟨fun h y hy z hz => h z hz y hy, fun h z hz y hy => h y hy z hz⟩⟩

end Approx

/-! ## Curried approximations -/

/-- `τA` approximates the curried type `τ`, pointwise: `α` by `Approx α`, and functions by
functions. -/
class ApproxFun (τ : Type _) (τA : Type _) [OFE τ] [PartialOrder τA] where
  /-- The elements of `τ` that `s` approximates. -/
  Sel : τA → τ → Prop
  /-- The pointwise hull of a set of elements. -/
  hull : (τ → Prop) → τA
  get : τA → τ
  /-- `s` agrees with itself at level `n`, everywhere. -/
  Precise : Nat → τA → Prop
  sel_mono {s s' : τA} (h : s ⊑ s') {f : τ} : Sel s' f → Sel s f
  sel_get (s : τA) : Sel s (get s)
  sel_hull {T : τ → Prop} {f : τ} : T f → Sel (hull T) f
  hull_mono {T T' : τ → Prop} : (∀ f, T' f → T f) → (∃ f, T' f) → hull T ⊑ hull T'
  sel_dist {n : Nat} {s : τA} {f g : τ} : Precise n s → Sel s f → Sel s g → f ≡{n}≡ g
  precise_hull {n : Nat} {T : τ → Prop} :
    (∀ f g, T f → T g → f ≡{n}≡ g) → (∃ f, T f) → Precise n (hull T)
  /-- An element that agrees with itself at every level is a singleton. -/
  sel_eq_get {s : τA} {f : τ} : (∀ n, Precise n s) → Sel s f → f = get s

namespace ApproxFun

section base
variable {α : Type _} [OFE α] [Inhabited α]

/-- The hull of a set: the smallest ball containing it, or everything when it is empty. -/
def hullOf (T : α → Prop) : α → Prop := fun z => ∀ m, Approx.prec T m → ∀ a, T a → a ≡{m}≡ z

theorem hullOf_isApprox (T : α → Prop) : Approx.IsApprox (hullOf T) := by
  by_cases hne : ∃ a, T a
  · obtain ⟨a, ha⟩ := hne
    refine ⟨a, Approx.prec T, ?_⟩
    funext z
    apply propext
    constructor
    · intro h m hm
      exact h m hm a ha
    · intro h m hm b hb
      exact (hm b a hb ha).trans (h m hm)
  · refine ⟨default, fun _ => False, ?_⟩
    funext z
    apply propext
    exact ⟨fun _ _ h => h.elim, fun _ _ _ a ha => (hne ⟨a, ha⟩).elim⟩

noncomputable instance : ApproxFun α (Approx α) where
  Sel S a := S.1 a
  hull T := ⟨hullOf T, hullOf_isApprox T⟩
  get S := Classical.choose S.2.nonempty
  Precise n S := Approx.prec S.1 n
  sel_mono h _ hf := h _ hf
  sel_get S := Classical.choose_spec S.2.nonempty
  sel_hull ha := fun _ hm _ hb => hm _ _ hb ha
  hull_mono hsub hne := by
    obtain ⟨a', ha'⟩ := hne
    intro z hz m hm a ha
    have hm' : Approx.prec _ m := fun b d hb hd => hm b d (hsub b hb) (hsub d hd)
    exact (hm a a' ha (hsub a' ha')).trans (hz m hm' a' ha')
  sel_dist h hf hg := h _ _ hf hg
  precise_hull hT hne := by
    obtain ⟨a, ha⟩ := hne
    intro y z hy hz
    exact (hy _ hT a ha).symm.trans (hz _ hT a ha)
  sel_eq_get h hf := OFE.eq_dist'.mpr fun n => h n _ _ hf (Classical.choose_spec _)

end base

section pi
variable {A : Type _} {β : A → Type _} {βA : A → Type _} [∀ a, OFE (β a)]
  [∀ a, PartialOrder (βA a)] [∀ a, ApproxFun (β a) (βA a)]

noncomputable instance : ApproxFun ((a : A) → β a) ((a : A) → βA a) where
  Sel s f := ∀ a, Sel (s a) (f a)
  hull T a := hull fun y => ∃ f, T f ∧ f a = y
  get s a := get (s a)
  Precise n s := ∀ a, Precise (β a) n (s a)
  sel_mono h _ hf a := sel_mono (h a) (hf a)
  sel_get s a := sel_get (s a)
  sel_hull hf a := sel_hull ⟨_, hf, rfl⟩
  hull_mono hsub hne a := by
    obtain ⟨f, hf⟩ := hne
    exact hull_mono (fun _ ⟨g, hg, h⟩ => ⟨g, hsub g hg, h⟩) ⟨_, f, hf, rfl⟩
  sel_dist h hf hg a := sel_dist (h a) (hf a) (hg a)
  precise_hull hT hne a := by
    obtain ⟨f, hf⟩ := hne
    refine precise_hull ?_ ⟨_, f, hf, rfl⟩
    rintro _ _ ⟨g, hg, rfl⟩ ⟨k, hk, rfl⟩
    exact hT g k hg hk a
  sel_eq_get h hf := funext fun a => sel_eq_get (fun n => h n a) (hf a)

end pi

/-! ## The lift of a functional -/

variable {τ τA : Type _} [OFE τ] [CCPO τA] [ApproxFun τ τA]

/-- Lift `G` to approximations: the hull of `G` applied to everything `s` approximates. -/
def lift (G : τ → τ) (s : τA) : τA := hull fun y => ∃ f, Sel s f ∧ y = G f

theorem sel_nonempty (s : τA) : ∃ f : τ, Sel s f := ⟨_, sel_get s⟩

/-- Lifting is monotone, for any `G`. -/
theorem lift_mono (G : τ → τ) : monotone (lift (τA := τA) G) := by
  intro s s' h
  obtain ⟨f, hf⟩ := sel_nonempty (τ := τ) s'
  exact hull_mono (fun _ ⟨g, hg, hy⟩ => ⟨g, sel_mono h hg, hy⟩) ⟨_, f, hf, rfl⟩

/-- For a contractive `G`, a fixpoint of `lift G` is exact, and `get` of it is a fixpoint of `G`. -/
theorem lift_fix_get (G : τ → τ) [Contractive G] {s : τA} (hs : lift G s = s) :
    get s = G (get s) := by
  have hprec : ∀ n, Precise τ n s := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rw [← hs]
      refine precise_hull ?_ ⟨_, _, sel_get s, rfl⟩
      rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact Contractive.distLater_dist fun m hm => sel_dist (ih m hm) hf hg
  have hmem : Sel (lift G s) (G (get s)) := sel_hull ⟨_, sel_get s, rfl⟩
  rw [hs] at hmem
  exact (sel_eq_get hprec hmem).symm

end ApproxFun

end Iris
