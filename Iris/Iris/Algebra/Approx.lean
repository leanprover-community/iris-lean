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
precise), approximations form a `CCPO`, so `partial_fixpoint` can define them by recursion.

`lift G` runs `G` on every point of an approximation. It is monotone for every `G`, and when `G` is
contractive, its fixpoint is exact: `get` of it is the fixpoint of `G` (`lift_fix_get`). -/

@[expose] public section

namespace Iris
open OFE Lean.Order

namespace Approx
variable {α : Type _} [OFE α]

/-- The ball around `c` determined by the set of levels `P`. -/
def ball (c : α) (P : Nat → Prop) : α → Prop := fun y => ∀ m, P m → c ≡{m}≡ y

/-- Levels at which all elements of `S` agree. -/
def prec (S : α → Prop) (m : Nat) : Prop := ∀ a b, S a → S b → a ≡{m}≡ b

/-- `S` is a ball. -/
def IsApprox (S : α → Prop) : Prop := ∃ c P, S = ball c P

end Approx

/-- Approximations of an element: a ball, of finite precision or a singleton. -/
def Approx (α : Type _) [OFE α] := {S : α → Prop // Approx.IsApprox S}

namespace Approx
variable {α : Type _} [OFE α]

/-! ## Approximations form a CCPO -/

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

/-- The intersection of a set of approximations: the sup of a chain. -/
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

/-! ## Lifting a function to approximations -/

/-- The smallest ball containing `T`, or everything when `T` is empty. -/
def hull (T : α → Prop) : Approx α :=
  ⟨fun z => ∀ m, prec T m → ∀ a, T a → a ≡{m}≡ z, by
    by_cases hne : ∃ a, T a
    · obtain ⟨a, ha⟩ := hne
      refine ⟨a, prec T, funext fun z => propext ⟨fun h m hm => h m hm a ha, ?_⟩⟩
      exact fun h m hm b hb => (hm b a hb ha).trans (h m hm)
    · refine ⟨default, fun _ => False, funext fun z => propext ⟨fun _ _ h => h.elim, ?_⟩⟩
      exact fun _ _ _ a ha => (hne ⟨a, ha⟩).elim⟩

omit [IsCOFE α] in
theorem mem_hull {T : α → Prop} {a : α} (ha : T a) : (hull T).1 a :=
  fun _ hm _ hb => hm _ _ hb ha

omit [IsCOFE α] in
theorem prec_hull {T : α → Prop} {n : Nat} (hT : prec T n) (hne : ∃ a, T a) :
    prec (hull T).1 n := by
  obtain ⟨a, ha⟩ := hne
  exact fun y z hy hz => (hy n hT a ha).symm.trans (hz n hT a ha)

/-- A point of an approximation. -/
noncomputable def get (S : Approx α) : α := Classical.choose S.2.nonempty

omit [IsCOFE α] [Inhabited α] in
theorem get_mem (S : Approx α) : S.1 (get S) := Classical.choose_spec S.2.nonempty

/-- Run `G` on every point of `S`. -/
def lift (G : α → α) (S : Approx α) : Approx α := hull fun y => ∃ x, S.1 x ∧ y = G x

omit [IsCOFE α] in
/-- Lifting is monotone, for any `G`. -/
theorem lift_mono (G : α → α) : monotone (lift G) := by
  intro S S' h z hz m hm a ha
  -- `S' ⊆ S`, so the image of `S'` under `G` is inside the image of `S`.
  have sub : ∀ y, (∃ x, S'.1 x ∧ y = G x) → ∃ x, S.1 x ∧ y = G x :=
    fun _ ⟨x, hx, e⟩ => ⟨x, h x hx, e⟩
  have hb : ∃ x, S'.1 x ∧ G (get S') = G x := ⟨_, get_mem S', rfl⟩
  exact (hm _ _ ha (sub _ hb)).trans (hz m (fun y z hy hz => hm y z (sub y hy) (sub z hz)) _ hb)

omit [IsCOFE α] in
/-- For a contractive `G`, a fixpoint of `lift G` is a single point, and a fixpoint of `G`. -/
theorem lift_fix_get (G : α → α) [Contractive G] {S : Approx α} (hS : lift G S = S) :
    get S = G (get S) := by
  have hprec : ∀ n, prec S.1 n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rw [← hS]
      refine prec_hull ?_ ⟨_, _, get_mem S, rfl⟩
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact Contractive.distLater_dist fun m hm => ih m hm x y hx hy
  have hG : (lift G S).1 (G (get S)) := mem_hull ⟨_, get_mem S, rfl⟩
  rw [hS] at hG
  exact OFE.eq_dist'.mpr fun n => hprec n _ _ (get_mem S) hG

end Approx

end Iris
